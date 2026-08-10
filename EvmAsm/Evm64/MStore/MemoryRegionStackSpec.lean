/-
  EvmAsm.Evm64.MStore.MemoryRegionStackSpec

  Write-direction region machinery for stating the public MSTORE stack spec
  against the `evmMemoryIs` interface (issue #10190 — the MSTORE analog of the
  MLOAD region migration #10180).

  ## Why MSTORE needs its own peel

  MLOAD's migration (`EvmAsm/Evm64/MLoad/MemoryRegionStackSpec.lean`) peels the
  adjacent dword pair one quarter at a time and folds the *unchanged* region
  back before the next quarter, so overlapping pairs stay satisfiable at every
  byte alignment. MSTORE cannot re-fold the same bytes: each quarter mutates
  its pair, and adjacent quarters *share* a dword, so the fold-back target is
  the partially-updated byte list. The keystone is therefore a pair peel that
  frames the SAME `front`/`rest` for both the original list and the spliced
  one — `bytesRegion_dword_pair_at_setBytes` below, the straddling-payload
  generalization of `Rv64.bytesRegion_dword_at_setBytes`
  (`EvmAsm/Rv64/MemRegionWriteWide.lean`), whose payload must stay inside a
  single cell.

  ## Byte preservation is structural, not assumed

  The emitted MSTORE (`EvmAsm/Evm64/MStore/Program.lean`) writes with 32
  individual `SB`s and never loads the destination, so at the separation-logic
  level each store is modelled as `replaceByte` on the containing dword
  (`mstoreDwordPairReplaceByte`). Expressing the whole 32-byte effect as
  `setBytes contents offset (evmWordBytesBE value)` therefore mutates exactly
  `[offset, offset+32)` by construction — the bytes outside that range,
  including the trailing guard band, are preserved by `List.set` semantics
  rather than by an extra hypothesis.

  ## Guard band

  `mstorePairGuardBytes = 8`: for a quarter at `w` with `offset % 8 ≠ 0` the
  written pair's hi dword reaches `8 * (offset / 8) + 40`, i.e. one dword past
  the semantic 32-byte word. The band is modelled exactly as MLOAD models it —
  an explicit adjacent resource, reducing the public access condition to the
  natural `offset + 32 ≤ capacity`. `Evm64.evmMemoryIs_append_guard` (already
  opcode-agnostic, in the MLOAD file) is the seam; the MSTORE-specific half is
  `evmMemoryWriteWord_append_guard` below.
-/

import EvmAsm.Evm64.StateAssertions
import EvmAsm.Evm64.MLoad.MemoryRegionStackSpec
import EvmAsm.Evm64.MStore.UnalignedFramedStackSpec
import EvmAsm.Rv64.MemRegionWriteWide

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-! ## Guard band constants -/

/-- One dword of trailing guard covers the pair-write tail. -/
abbrev mstorePairGuardBytes : Nat := 8

/-- Internal pair window: the semantic 32-byte word plus one guard dword. -/
abbrev mstorePairWindowBytes : Nat := 32 + mstorePairGuardBytes

/-! ## The MSTORE post-state as a function of the region contents -/

/-- The eight bytes one MSTORE limb writes, in program (big-endian) order:
    memory byte `i` of the limb window receives byte `7 - i` of the limb. -/
def mstoreLimbBytesBE (limb : Word) : List (BitVec 8) :=
  [extractByte limb 7, extractByte limb 6, extractByte limb 5, extractByte limb 4,
   extractByte limb 3, extractByte limb 2, extractByte limb 1, extractByte limb 0]

@[simp] theorem length_mstoreLimbBytesBE (limb : Word) :
    (mstoreLimbBytesBE limb).length = 8 := rfl

/-- The 32 bytes MSTORE writes for a 256-bit value: big-endian, so the most
    significant limb (`getLimbN 3`) lands at the lowest address. This is the
    byte order the emitted routine produces (`mstore_one_limb` stores limb `j`
    at window offset `8 * (3 - j)`). -/
def evmWordBytesBE (v : EvmWord) : List (BitVec 8) :=
  mstoreLimbBytesBE (v.getLimbN 3) ++ mstoreLimbBytesBE (v.getLimbN 2) ++
    mstoreLimbBytesBE (v.getLimbN 1) ++ mstoreLimbBytesBE (v.getLimbN 0)

@[simp] theorem length_evmWordBytesBE (v : EvmWord) :
    (evmWordBytesBE v).length = 32 := rfl

/-- **The MSTORE post-state region contents**: `bs` with the 32 big-endian
    bytes of `v` spliced in at byte `k`. The write-direction counterpart of
    `evmMemoryReadWord`; only `[k, k+32)` differs from `bs`. -/
def evmMemoryWriteWord (bs : List (BitVec 8)) (k : Nat) (v : EvmWord) :
    List (BitVec 8) :=
  setBytes bs k (evmWordBytesBE v)

/-- MSTORE does not resize the region — the capacity side condition of
    `evmMemoryIs` survives the write. -/
@[simp] theorem length_evmMemoryWriteWord (bs : List (BitVec 8)) (k : Nat) (v : EvmWord) :
    (evmMemoryWriteWord bs k v).length = bs.length := by
  simp only [evmMemoryWriteWord, length_setBytes]

/-- Bytes outside the spliced window are untouched: the write-direction
    statement of MSTORE's byte-preservation obligation. -/
theorem getByteAt_evmMemoryWriteWord (bs : List (BitVec 8)) (k j : Nat)
    (v : EvmWord) (hin : k + 32 ≤ bs.length) :
    getByteAt (evmMemoryWriteWord bs k v) j
      = if k ≤ j ∧ j < k + 32 then getByteAt (evmWordBytesBE v) (j - k)
        else getByteAt bs j := by
  rw [evmMemoryWriteWord, getByteAt_setBytes _ _ _ _ (by simpa using hin),
    length_evmWordBytesBE]

/-! ## Splicing across an appended guard band -/

/-- A write landing entirely inside the semantic region leaves an appended
    guard band byte-for-byte untouched. -/
theorem setBytes_append_left (ns bs cs : List (BitVec 8)) (i : Nat)
    (h : i + ns.length ≤ bs.length) :
    setBytes (bs ++ cs) i ns = setBytes bs i ns ++ cs := by
  induction ns generalizing bs i with
  | nil => simp only [setBytes_nil]
  | cons b rest ih =>
      simp only [List.length_cons] at h
      simp only [setBytes_cons]
      rw [List.set_append_left (s := bs) (t := cs) i b (by omega)]
      exact ih (bs.set i b) (i + 1) (by rw [List.length_set]; omega)

/-- The MSTORE analog of `evmMemoryReadWord_append_guard`: a semantic MSTORE
    whose 32 bytes lie in `contents` writes nothing into the trailing
    implementation guard. -/
theorem evmMemoryWriteWord_append_guard
    (contents guard : List (BitVec 8)) (k : Nat) (v : EvmWord)
    (hin : k + 32 ≤ contents.length) :
    evmMemoryWriteWord (contents ++ guard) k v
      = evmMemoryWriteWord contents k v ++ guard := by
  rw [evmMemoryWriteWord, evmMemoryWriteWord,
    setBytes_append_left _ _ _ _ (by simpa using hin)]

/-! ## The write-direction pair peel -/

/-- **Frame the adjacent dword pair `q`, `q+1` for both `bs` and
    `setBytes bs (8q+r) ns`, with shared `front`/`rest`.**

    This is the keystone of the MSTORE region migration and the straddling
    generalization of `Rv64.bytesRegion_dword_at_setBytes`: that lemma requires
    the payload to stay inside cell `q` (`r + ns.length ≤ 8`), whereas an
    unaligned 8-byte MSTORE limb spans the pair (`r + ns.length ≤ 16`).

    Because `front` and `rest` are shared, a caller may execute one limb
    against the peeled pair and fold the region back at the *updated* byte
    list — which is what lets adjacent MSTORE quarters share a dword.

    Rv64-generic (only `bytesRegion`/`setBytes` appear); it lives here rather
    than in `EvmAsm/Rv64/MemRegionWriteWide.lean` next to its sibling only to
    keep this migration a leaf. -/
theorem bytesRegion_dword_pair_at_setBytes (regionBase : Word)
    (bs ns : List (BitVec 8)) (q r : Nat)
    (hrns : r + ns.length ≤ 16) (hq : 8 * q + 16 ≤ bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegion regionBase bs
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * q)) ↦ₘ
            packBytes ((bs.drop (8 * q)).take 8)) **
            (((regionBase + BitVec.ofNat 64 (8 * q + 8)) ↦ₘ
              packBytes ((bs.drop (8 * q + 8)).take 8)) ** rest)))
      ∧ bytesRegion regionBase (setBytes bs (8 * q + r) ns)
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * q)) ↦ₘ
            packBytes (((setBytes bs (8 * q + r) ns).drop (8 * q)).take 8)) **
            (((regionBase + BitVec.ofNat 64 (8 * q + 8)) ↦ₘ
              packBytes (((setBytes bs (8 * q + r) ns).drop (8 * q + 8)).take 8)) **
             rest))) := by
  induction q generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by
      intro h; subst h; simp only [List.length_nil] at hq; omega
    have hne8 : bs.drop 8 ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [List.length_drop, List.length_nil] at hlen
      omega
    have hset_ne : setBytes bs (8 * 0 + r) ns ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [length_setBytes, List.length_nil] at hlen
      omega
    have hset_ne8 : (setBytes bs (8 * 0 + r) ns).drop 8 ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [List.length_drop, length_setBytes, List.length_nil] at hlen
      omega
    have haddr0 : regionBase + BitVec.ofNat 64 (8 * 0) = regionBase := by
      rw [show (8 * 0 : Nat) = 0 from rfl]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := regionBase.isLt
      omega
    have haddr8 : regionBase + BitVec.ofNat 64 (8 * 0 + 8) = regionBase + 8 := by
      rw [show (8 * 0 + 8 : Nat) = 8 from rfl]
      congr 1
    have hdrop16 : ((setBytes bs (8 * 0 + r) ns).drop 8).drop 8
        = (bs.drop 8).drop 8 := by
      rw [List.drop_drop, List.drop_drop]
      exact setBytes_drop_of_le ns bs (8 * 0 + r) (8 + 8) (by omega)
    refine ⟨empAssertion, bytesRegion (regionBase + 8 + 8) ((bs.drop 8).drop 8),
      pcFree_emp, bytesRegion_pcFree _ _, ?_, ?_⟩
    · rw [sepConj_emp_left', bytesRegion_eq_cons regionBase bs hne,
        bytesRegion_eq_cons (regionBase + 8) (bs.drop 8) hne8,
        haddr0, haddr8, show (8 * 0 : Nat) = 0 from rfl, List.drop_zero,
        show (8 * 0 + 8 : Nat) = 8 from rfl]
    · rw [sepConj_emp_left',
        bytesRegion_eq_cons regionBase (setBytes bs (8 * 0 + r) ns) hset_ne,
        bytesRegion_eq_cons (regionBase + 8) _ hset_ne8,
        hdrop16, haddr0, haddr8, show (8 * 0 : Nat) = 0 from rfl, List.drop_zero,
        show (8 * 0 + 8 : Nat) = 8 from rfl]
  | succ k ih =>
    have hne : bs ≠ [] := by
      intro h; subst h; simp only [List.length_nil] at hq; omega
    have hq' : 8 * k + 16 ≤ (bs.drop 8).length := by
      rw [List.length_drop]; omega
    obtain ⟨front', rest', hf', hr', heq', heqset'⟩ := ih (regionBase + 8) (bs.drop 8) hq'
    have haddr : (regionBase + 8) + BitVec.ofNat 64 (8 * k)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]
      omega
    have haddr' : (regionBase + 8) + BitVec.ofNat 64 (8 * k + 8)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1) + 8) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]
      omega
    have hdrop : (bs.drop 8).drop (8 * k) = bs.drop (8 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    have hdrop' : (bs.drop 8).drop (8 * k + 8) = bs.drop (8 * (k + 1) + 8) := by
      rw [List.drop_drop]; congr 1; omega
    have htake_first : (setBytes bs (8 * (k + 1) + r) ns).take 8 = bs.take 8 :=
      setBytes_take_of_ge ns bs _ 8 (by omega)
    have hdrop_first : (setBytes bs (8 * (k + 1) + r) ns).drop 8
        = setBytes (bs.drop 8) (8 * k + r) ns := by
      rw [setBytes_drop_of_ge ns bs _ 8 (by omega)]
      congr 1
      omega
    have hcell : (setBytes (bs.drop 8) (8 * k + r) ns).drop (8 * k)
        = (setBytes bs (8 * (k + 1) + r) ns).drop (8 * (k + 1)) := by
      rw [← hdrop_first, List.drop_drop]
      congr 1
      omega
    have hcell' : (setBytes (bs.drop 8) (8 * k + r) ns).drop (8 * k + 8)
        = (setBytes bs (8 * (k + 1) + r) ns).drop (8 * (k + 1) + 8) := by
      rw [← hdrop_first, List.drop_drop]
      congr 1
      omega
    have hset_ne : setBytes bs (8 * (k + 1) + r) ns ≠ [] :=
      List.ne_nil_of_length_pos
        (by rw [length_setBytes]; exact List.length_pos_of_ne_nil hne)
    refine ⟨(regionBase ↦ₘ packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIs hf', hr', ?_, ?_⟩
    · rw [bytesRegion_eq_cons regionBase bs hne, heq', haddr, haddr', hdrop, hdrop',
        ← sepConj_assoc']
    · rw [bytesRegion_eq_cons regionBase (setBytes bs (8 * (k + 1) + r) ns) hset_ne,
        htake_first, hdrop_first, heqset', hcell, hcell', haddr, haddr',
        ← sepConj_assoc']

/-! ## Byte-level MSTORE limb bridge

The pair peel above is only consumable once the eight `SB`s of one limb have
been folded back into the `setBytes` image.  Keep the conversion induction
separate from the topmost spec: this theorem is uniform in every residue
`start < 8`, and no Progress witness is re-pointed here.
-/

/-- Apply the first `k` byte stores of one MSTORE limb. -/
def mstoreLimbStoreK (lo hi limb : Word) (start k : Nat) : Word × Word :=
  match k with
  | 0 => (lo, hi)
  | k + 1 =>
      let p := mstoreLimbStoreK lo hi limb start k
      MStore.mstoreDwordPairReplaceByte p.1 p.2 start k
        (extractByte limb (7 - k))

/-- The first `k` bytes of one limb in emitted-store order. -/
def mstoreLimbPayloadK (limb : Word) : Nat → List (BitVec 8)
  | 0 => []
  | k + 1 => mstoreLimbPayloadK limb k ++ [extractByte limb (7 - k)]

theorem mstoreDwordPairReplaceByte_setBytes
    (xs : List (BitVec 8)) (start i : Nat) (b : BitVec 8)
    (hxs : 16 ≤ xs.length) (hstart : start < 8) (hi : start + i < 16) :
    MStore.mstoreDwordPairReplaceByte
        (packBytes (xs.take 8)) (packBytes ((xs.drop 8).take 8)) start i b =
      (packBytes ((setBytes xs (start + i) [b]).take 8),
       packBytes (((setBytes xs (start + i) [b]).drop 8).take 8)) := by
  by_cases hlow : start + i < 8
  · rw [MStore.mstoreDwordPairReplaceByte_low _ _ b hlow]
    have htake := setBytes_take_of_le [b] xs (start + i) 8 (by simp; omega)
    have hdrop := setBytes_drop_of_le [b] xs (start + i) 8 (by simp; omega)
    rw [htake, hdrop]
    simp only [setBytes_cons, setBytes_nil]
    rw [packBytes_set _ _ _ (by omega) (by rw [List.length_take]; omega)]
    congr 1
    rw [show (start + i) % 8 = start + i by omega]
  · have hhigh : 8 ≤ start + i := by omega
    rw [MStore.mstoreDwordPairReplaceByte_high _ _ b hhigh]
    have hdrop := setBytes_drop_of_ge [b] xs (start + i) 8 (by omega)
    have htake := setBytes_take_of_ge [b] xs (start + i) 8 (by omega)
    rw [htake, hdrop]
    simp only [setBytes_cons, setBytes_nil]
    rw [packBytes_set _ _ _ (by omega) (by
      simp only [List.length_take, List.length_drop]
      omega)]
    congr 1
    rw [show (start + i) % 8 = (start + i - 8) by omega]
    rw [List.take_set]

theorem mstore_setBytes_append (xs ys bs : List (BitVec 8)) (k : Nat) :
    setBytes bs k (xs ++ ys) = setBytes (setBytes bs k xs) (k + xs.length) ys := by
  induction xs generalizing bs k with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, setBytes_cons, List.length_cons]
      rw [ih]
      congr 1
      omega

theorem mstoreLimbPayloadK_length (limb : Word) (k : Nat) :
    (mstoreLimbPayloadK limb k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [mstoreLimbPayloadK, ih]

theorem mstoreLimbStoreK_eq_pack
    (xs : List (BitVec 8)) (limb : Word) (start k : Nat)
    (hxs : 16 ≤ xs.length) (hstart : start < 8) (hk : k ≤ 8) :
    mstoreLimbStoreK (packBytes (xs.take 8))
        (packBytes ((xs.drop 8).take 8)) limb start k =
      (packBytes ((setBytes xs start (mstoreLimbPayloadK limb k)).take 8),
       packBytes (((setBytes xs start (mstoreLimbPayloadK limb k)).drop 8).take 8)) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
      have hk8 : k < 8 := by omega
      have ih' := ih (xs := xs) hxs (by omega)
      simp only [mstoreLimbStoreK]
      rw [ih']
      have hstep := mstoreDwordPairReplaceByte_setBytes
        (setBytes xs start (mstoreLimbPayloadK limb k)) start k
        (extractByte limb (7 - k))
        (by rw [length_setBytes]; exact hxs) hstart (by omega)
      rw [hstep]
      rw [show mstoreLimbPayloadK limb (k + 1) =
        mstoreLimbPayloadK limb k ++ [extractByte limb (7 - k)] by rfl]
      rw [mstore_setBytes_append (mstoreLimbPayloadK limb k)
        [extractByte limb (7 - k)] xs start]
      simp only [mstoreLimbPayloadK_length]

theorem mstoreLimbPayloadK_eq_take (limb : Word) (k : Nat) (hk : k ≤ 8) :
    mstoreLimbPayloadK limb k = (mstoreLimbBytesBE limb).take k := by
  interval_cases k <;> simp [mstoreLimbPayloadK, mstoreLimbBytesBE]

/-- The complete eight-byte limb store equals the two dwords selected from the
    byte-level `setBytes` result, uniformly for every residue `start < 8`. -/
theorem mstoreDwordPairStoreLimb_eq_dwordAt_setBytes
    (bs : List (BitVec 8)) (limb : Word) (q start : Nat)
    (hstart : start < 8) (hq : 8 * q + 16 ≤ bs.length) :
    MStore.mstoreDwordPairStoreLimb (dwordAt bs (8 * q))
        (dwordAt bs (8 * q + 8)) limb start =
      (dwordAt (setBytes bs (8 * q + start) (mstoreLimbBytesBE limb)) (8 * q),
       dwordAt (setBytes bs (8 * q + start) (mstoreLimbBytesBE limb)) (8 * q + 8)) := by
  let xs := bs.drop (8 * q)
  have hxs : 16 ≤ xs.length := by
    dsimp [xs]
    rw [List.length_drop]
    omega
  have hpair := mstoreLimbStoreK_eq_pack xs limb start 8 hxs hstart (by omega)
  have hdrop : (setBytes bs (8 * q + start) (mstoreLimbBytesBE limb)).drop (8 * q) =
      setBytes xs start (mstoreLimbBytesBE limb) := by
    dsimp [xs]
    have h := setBytes_drop_of_ge (mstoreLimbBytesBE limb) bs
      (8 * q + start) (8 * q) (by omega)
    have hoff : 8 * q + start - 8 * q = start := by omega
    rw [hoff] at h
    exact h
  rw [show dwordAt bs (8 * q) = packBytes (xs.take 8) by rfl,
    show dwordAt bs (8 * q + 8) = packBytes ((xs.drop 8).take 8) by
      dsimp [dwordAt, xs]
      rw [List.drop_drop]]
  rw [show MStore.mstoreDwordPairStoreLimb
      (packBytes (xs.take 8)) (packBytes ((xs.drop 8).take 8)) limb start =
      mstoreLimbStoreK (packBytes (xs.take 8))
        (packBytes ((xs.drop 8).take 8)) limb start 8 by rfl]
  rw [hpair, mstoreLimbPayloadK_eq_take limb 8 (by omega)]
  have hp : (mstoreLimbBytesBE limb).take 8 = mstoreLimbBytesBE limb := by
    simp [mstoreLimbBytesBE]
  rw [hp]
  dsimp [dwordAt]
  rw [hdrop]
  apply Prod.ext
  · rfl
  · rw [← List.drop_drop, hdrop]

/-! ## The `evmMemoryIs`-level pair peel -/

/-- **One MSTORE limb's dword pair, peeled out of `evmMemoryIs` in both
    directions.** The pre form exposes the pair at its current values; the post
    form re-folds the *same* `front`/`rest` around the two updated cells, so
    the region interface is restored at the spliced contents. This is the
    write-direction analog of `evmMemoryIs_quarter_pair`
    (`EvmAsm/Evm64/MLoad/MemoryRegionStackSpec.lean`), and the bridge issue
    #10190 asks for: it relates the byte-level post
    (`setBytes` / `evmMemoryWriteWord`) to the interface-level one. -/
theorem evmMemoryIs_quarter_pair_setBytes
    (memBase : Word) (capacity : Nat) (contents ns : List (BitVec 8)) (q r : Nat)
    (hlen : contents.length = capacity)
    (hrns : r + ns.length ≤ 16) (hq : 8 * q + 16 ≤ contents.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      evmMemoryIs memBase capacity contents
        = (front ** (((memBase + BitVec.ofNat 64 (8 * q)) ↦ₘ dwordAt contents (8 * q)) **
            (((memBase + BitVec.ofNat 64 (8 * q + 8)) ↦ₘ dwordAt contents (8 * q + 8)) **
             rest)))
      ∧ evmMemoryIs memBase capacity (setBytes contents (8 * q + r) ns)
        = (front ** (((memBase + BitVec.ofNat 64 (8 * q)) ↦ₘ
              dwordAt (setBytes contents (8 * q + r) ns) (8 * q)) **
            (((memBase + BitVec.ofNat 64 (8 * q + 8)) ↦ₘ
              dwordAt (setBytes contents (8 * q + r) ns) (8 * q + 8)) ** rest))) := by
  have hlen' : (setBytes contents (8 * q + r) ns).length = capacity := by
    rw [length_setBytes]; exact hlen
  rw [evmMemoryIs_eq_bytesRegion hlen, evmMemoryIs_eq_bytesRegion hlen']
  exact bytesRegion_dword_pair_at_setBytes memBase contents ns q r hrns hq

/-! ## One-limb region-backed execution

The raw one-limb theorem in `LimbSpec` owns the two dword cells.  This
adapter peels those cells from `evmMemoryIs`, runs the same theorem, and folds
the updated pair back into the byte-list image.  Keeping this adapter
separate from the four-limb composition makes the residue argument explicit:
the only residue assumption is `start < 8`, while the pair payload is allowed
to straddle either cell.
-/

theorem mstore_one_limb_unaligned_spec_within_evmMemoryIs
    (addrReg byteReg accReg : Reg)
    (memBase offset sp byteOld accOld limbVal : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (w : Nat)
    (srcOff off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (h_window : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8))
      (offset.toNat % 8) off0 off1 off2 off3 off4 off5 off6 off7) :
    cpsTripleWithin 17 base (base + 68)
      (mstoreOneLimbCode addrReg byteReg accReg
        srcOff off0 off1 off2 off3 off4 off5 off6 off7 base)
      ((addrReg ↦ᵣ (memBase + offset)) ** (byteReg ↦ᵣ byteOld) **
        (accReg ↦ᵣ accOld) ** ((.x12 : Reg) ↦ᵣ sp) **
        ((sp + signExtend12 srcOff) ↦ₘ limbVal) **
        evmMemoryIs memBase capacity contents)
      ((addrReg ↦ᵣ (memBase + offset)) ** (byteReg ↦ᵣ limbVal) **
        (accReg ↦ᵣ limbVal) ** ((.x12 : Reg) ↦ᵣ sp) **
        ((sp + signExtend12 srcOff) ↦ₘ limbVal) **
        evmMemoryIs memBase capacity
          (setBytes contents
            (8 * ((offset.toNat + w) / 8) + offset.toNat % 8)
            (mstoreLimbBytesBE limbVal))) := by
  have hq : 8 * ((offset.toNat + w) / 8) + 16 ≤ contents.length := by
    simp only [mstorePairWindowBytes, mstorePairGuardBytes] at hin
    have hmod : offset.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  have hrns : offset.toNat % 8 + (mstoreLimbBytesBE limbVal).length ≤ 16 := by
    simp only [length_mstoreLimbBytesBE]
    omega
  obtain ⟨front, rest, h_front, h_rest, h_pre, h_post⟩ :=
    evmMemoryIs_quarter_pair_setBytes memBase capacity contents
      (mstoreLimbBytesBE limbVal) ((offset.toNat + w) / 8)
      (offset.toNat % 8) hlen hrns hq
  have h_core := mstore_one_limb_spec_within addrReg byteReg accReg
    (memBase + offset) byteOld accOld
    (dwordAt contents (8 * ((offset.toNat + w) / 8)))
    (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
    (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8)))
    (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8))
    sp limbVal (offset.toNat % 8)
    srcOff off0 off1 off2 off3 off4 off5 off6 off7 base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mstoreOneLimbPre_unfold, mstoreOneLimbPost_unfold] at h_core
  have h_bridge := mstoreDwordPairStoreLimb_eq_dwordAt_setBytes contents limbVal
    ((offset.toNat + w) / 8) (offset.toNat % 8)
    (by omega) hq
  dsimp only at h_core
  rw [h_bridge] at h_core
  dsimp only at h_core
  have h_frame := cpsTripleWithin_frameR (front ** rest)
    (pcFree_sepConj h_front h_rest) h_core
  exact cpsTripleWithin_weaken
    (fun _ hp => by rw [h_pre] at hp; sep_perm hp)
    (fun _ hp => by rw [h_post]; sep_perm hp)
    h_frame

/-! ## Four-limb region composition -/

private def mstoreRegionMid
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp memBase offset byteVal accVal limb32 limb40 limb48 limb56 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) : Assertion :=
  ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
  (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
  (sp ↦ₘ offset) ** (byteReg ↦ᵣ byteVal) ** (accReg ↦ᵣ accVal) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56) **
  evmMemoryIs memBase capacity contents

private theorem mstoreRegionMid_unfold
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp memBase offset byteVal accVal limb32 limb40 limb48 limb56 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) :
    mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
      sp memBase offset byteVal accVal limb32 limb40 limb48 limb56 capacity contents =
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
      (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
      (sp ↦ₘ offset) ** (byteReg ↦ᵣ byteVal) ** (accReg ↦ᵣ accVal) **
      ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
      ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
      ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
      ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56) **
      evmMemoryIs memBase capacity contents) := by
  rfl

private theorem mstore_region_step_q0
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp memBase offset byteOld accOld limb32 limb40 limb48 limb56 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (h_window : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8) + 8))
      (offset.toNat % 8) 24 25 26 27 28 29 30 31) :
    cpsTripleWithin 17 (base + 8) (base + 76)
      (mstoreOneLimbCode addrReg byteReg accReg
        32 24 25 26 27 28 29 30 31 (base + 8))
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset byteOld accOld limb32 limb40 limb48 limb56
        capacity contents)
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb32 limb32 limb32 limb40 limb48 limb56
        capacity (setBytes contents
          (8 * ((offset.toNat + 24) / 8) + offset.toNat % 8)
          (mstoreLimbBytesBE limb32))) := by
  have h_core := mstore_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp byteOld accOld limb32
    capacity contents 24 32 24 25 26 27 28 29 30 31
    (base + 8) h_byte_ne_x0 h_acc_ne_x0 hlen
    (by decide) (by decide) hin h_window
  rw [show (base + 8) + 68 = base + 76 from by bv_omega,
    signExtend12_32] at h_core
  have h_framed := cpsTripleWithin_frameR
    ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ offset) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) (by pcFree) h_core
  simp only [mstoreRegionMid_unfold, signExtend12_32] at h_framed ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h_framed

private theorem mstore_region_step_q1
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp memBase offset limb32 limb40 limb48 limb56 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (h_window : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8) + 8))
      (offset.toNat % 8) 16 17 18 19 20 21 22 23) :
    cpsTripleWithin 17 (base + 76) (base + 144)
      (mstoreOneLimbCode addrReg byteReg accReg
        40 16 17 18 19 20 21 22 23 (base + 76))
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb32 limb32 limb32 limb40 limb48 limb56
        capacity contents)
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb40 limb40 limb32 limb40 limb48 limb56
        capacity (setBytes contents
          (8 * ((offset.toNat + 16) / 8) + offset.toNat % 8)
          (mstoreLimbBytesBE limb40))) := by
  have h_core := mstore_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp limb32 limb32 limb40
    capacity contents 16 40 16 17 18 19 20 21 22 23
    (base + 76) h_byte_ne_x0 h_acc_ne_x0 hlen
    (by decide) (by decide) hin h_window
  rw [show (base + 76) + 68 = base + 144 from by bv_omega,
    signExtend12_40] at h_core
  have h_framed := cpsTripleWithin_frameR
    ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ offset) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) (by pcFree) h_core
  simp only [mstoreRegionMid_unfold, signExtend12_32, signExtend12_40] at h_framed ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h_framed

private theorem mstore_region_step_q2
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp memBase offset limb32 limb40 limb48 limb56 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (h_window : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8) + 8))
      (offset.toNat % 8) 8 9 10 11 12 13 14 15) :
    cpsTripleWithin 17 (base + 144) (base + 212)
      (mstoreOneLimbCode addrReg byteReg accReg
        48 8 9 10 11 12 13 14 15 (base + 144))
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb40 limb40 limb32 limb40 limb48 limb56
        capacity contents)
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb48 limb48 limb32 limb40 limb48 limb56
        capacity (setBytes contents
          (8 * ((offset.toNat + 8) / 8) + offset.toNat % 8)
          (mstoreLimbBytesBE limb48))) := by
  have h_core := mstore_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp limb40 limb40 limb48
    capacity contents 8 48 8 9 10 11 12 13 14 15
    (base + 144) h_byte_ne_x0 h_acc_ne_x0 hlen
    (by decide) (by decide) hin h_window
  rw [show (base + 144) + 68 = base + 212 from by bv_omega,
    signExtend12_48] at h_core
  have h_framed := cpsTripleWithin_frameR
    ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ offset) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) (by pcFree) h_core
  simp only [mstoreRegionMid_unfold, signExtend12_32, signExtend12_40,
    signExtend12_48] at h_framed ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h_framed

private theorem mstore_region_step_q3
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp memBase offset limb32 limb40 limb48 limb56 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (h_window : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8) + 8))
      (offset.toNat % 8) 0 1 2 3 4 5 6 7) :
    cpsTripleWithin 17 (base + 212) (base + 280)
      (mstoreOneLimbCode addrReg byteReg accReg
        56 0 1 2 3 4 5 6 7 (base + 212))
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb48 limb48 limb32 limb40 limb48 limb56
        capacity contents)
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb56 limb56 limb32 limb40 limb48 limb56
        capacity (setBytes contents
          (8 * ((offset.toNat + 0) / 8) + offset.toNat % 8)
          (mstoreLimbBytesBE limb56))) := by
  have h_core := mstore_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp limb48 limb48 limb56
    capacity contents 0 56 0 1 2 3 4 5 6 7
    (base + 212) h_byte_ne_x0 h_acc_ne_x0 hlen
    (by decide) (by decide) hin h_window
  rw [show (base + 212) + 68 = base + 280 from by bv_omega,
    signExtend12_56] at h_core
  have h_framed := cpsTripleWithin_frameR
    ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ offset) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48)) (by pcFree) h_core
  simp only [mstoreRegionMid_unfold, signExtend12_32, signExtend12_40,
    signExtend12_48, signExtend12_56] at h_framed ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h_framed

private theorem mstore_setBytes_commute_of_separated
    (bs x y : List (BitVec 8)) (i j : Nat)
    (hx : x.length = 8) (hy : y.length = 8)
    (hij : i + 8 ≤ j) (hbound : j + 8 ≤ bs.length) :
    setBytes (setBytes bs i x) j y = setBytes (setBytes bs j y) i x := by
  apply List.ext_getElem (by simp [length_setBytes])
  intro n hnL hnR
  have hxy : i + x.length ≤ j := by omega
  have hL := getByteAt_setBytes y (setBytes bs i x) j n (by
    rw [length_setBytes]
    omega)
  rw [getByteAt_setBytes x bs i n (by omega)] at hL
  have hR := getByteAt_setBytes x (setBytes bs j y) i n (by
    rw [length_setBytes]
    omega)
  rw [getByteAt_setBytes y bs j n (by omega)] at hR
  have hgl : getByteAt (setBytes (setBytes bs i x) j y) n =
      (setBytes (setBytes bs i x) j y)[n]'hnL := by
    unfold getByteAt
    rw [dif_pos hnL]
  have hgr : getByteAt (setBytes (setBytes bs j y) i x) n =
      (setBytes (setBytes bs j y) i x)[n]'hnR := by
    unfold getByteAt
    rw [dif_pos hnR]
  rw [← hgl, ← hgr]
  by_cases hxi : i ≤ n ∧ n < i + 8
  · have hny : ¬ (j ≤ n ∧ n < j + 8) := by
      intro h
      omega
    rw [hL, hR]
    simp [hxi, hny, hx, hy]
  · by_cases hyj : j ≤ n ∧ n < j + 8
    · have hni : ¬ (i ≤ n ∧ n < i + 8) := hxi
      rw [hL, hR]
      simp [hxi, hyj, hx, hy]
    · rw [hL, hR]
      simp [hxi, hyj, hx, hy]

private theorem mstoreLimbWindowOk_region
    (memBase offset : Word) (contents : List (BitVec 8)) (w : Nat)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (halignB : memBase.toNat % 8 = 0)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24)
    (h_se0 : signExtend12 off0 = BitVec.ofNat 64 (w + 0))
    (h_se1 : signExtend12 off1 = BitVec.ofNat 64 (w + 1))
    (h_se2 : signExtend12 off2 = BitVec.ofNat 64 (w + 2))
    (h_se3 : signExtend12 off3 = BitVec.ofNat 64 (w + 3))
    (h_se4 : signExtend12 off4 = BitVec.ofNat 64 (w + 4))
    (h_se5 : signExtend12 off5 = BitVec.ofNat 64 (w + 5))
    (h_se6 : signExtend12 off6 = BitVec.ofNat 64 (w + 6))
    (h_se7 : signExtend12 off7 = BitVec.ofNat 64 (w + 7)) :
    mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8))
      (offset.toNat % 8) off0 off1 off2 off3 off4 off5 off6 off7 := by
  have h := mloadLimbWindowOk_region memBase offset contents w
    off0 off1 off2 off3 off4 off5 off6 off7 halignB hbound hvalid
    (by simpa [mloadPairWindowBytes, mloadPairGuardBytes,
      mstorePairWindowBytes, mstorePairGuardBytes] using hin)
    h_w_mod h_w_le h_se0 h_se1 h_se2 h_se3 h_se4 h_se5 h_se6 h_se7
  simpa [mloadDwordPairAddr, MStore.mstoreDwordPairAddr] using h

private theorem mstore_setBytes_four_limb_reverse
    (bs a b c d : List (BitVec 8)) (k : Nat)
    (ha : a.length = 8) (hb : b.length = 8)
    (hc : c.length = 8) (hd : d.length = 8)
    (hbound : k + 32 ≤ bs.length) :
    setBytes (setBytes (setBytes (setBytes bs (k + 24) d) (k + 16) c)
      (k + 8) b) k a = setBytes bs k (a ++ b ++ c ++ d) := by
  have habcd : a ++ b ++ c ++ d = a ++ (b ++ c ++ d) := by
    simp [List.append_assoc]
  have hbcd : b ++ c ++ d = b ++ (c ++ d) := by
    simp [List.append_assoc]
  have hexpand : setBytes bs k (a ++ b ++ c ++ d) =
      setBytes (setBytes (setBytes (setBytes bs k a) (k + 8) b)
        (k + 16) c) (k + 24) d := by
    rw [habcd, hbcd]
    rw [mstore_setBytes_append a (b ++ (c ++ d)) bs k]
    rw [mstore_setBytes_append b (c ++ d) (setBytes bs k a) (k + a.length)]
    rw [mstore_setBytes_append c d
      (setBytes (setBytes bs k a) (k + a.length) b)
      (k + a.length + b.length)]
    simp [ha, hb, hc, Nat.add_left_comm, Nat.add_comm]
  rw [hexpand]
  conv_lhs =>
    rw [← mstore_setBytes_commute_of_separated
      (setBytes (setBytes bs (k + 24) d) (k + 16) c) a b k (k + 8)
      ha hb (by omega) (by rw [length_setBytes, length_setBytes]; omega)]
  conv_lhs =>
    rw [← mstore_setBytes_commute_of_separated
      (setBytes bs (k + 24) d) a c k (k + 16)
      ha hc (by omega) (by rw [length_setBytes]; omega)]
  conv_lhs =>
    rw [← mstore_setBytes_commute_of_separated
      bs a d k (k + 24) ha hd (by omega) hbound]
  conv_lhs =>
    rw [← mstore_setBytes_commute_of_separated
      (setBytes (setBytes bs k a) (k + 24) d) b c (k + 8) (k + 16)
      hb hc (by omega) (by rw [length_setBytes, length_setBytes]; omega)]
  conv_lhs =>
    rw [← mstore_setBytes_commute_of_separated
      (setBytes bs k a) b d (k + 8) (k + 24)
      hb hd (by omega) (by rw [length_setBytes]; omega)]
  conv_lhs =>
    rw [← mstore_setBytes_commute_of_separated
      (setBytes (setBytes bs k a) (k + 8) b) c d (k + 16) (k + 24)
      hc hd (by omega) (by rw [length_setBytes, length_setBytes]; omega)]

private theorem mstore_region_body_spec_within
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (limb32 limb40 limb48 limb56 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (h_window0 : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8) + 8))
      (offset.toNat % 8) 24 25 26 27 28 29 30 31)
    (h_window1 : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8) + 8))
      (offset.toNat % 8) 16 17 18 19 20 21 22 23)
    (h_window2 : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8) + 8))
      (offset.toNat % 8) 8 9 10 11 12 13 14 15)
    (h_window3 : mstoreLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8) + 8))
      (offset.toNat % 8) 0 1 2 3 4 5 6 7) :
    let c0 := setBytes contents
      (8 * ((offset.toNat + 24) / 8) + offset.toNat % 8)
      (mstoreLimbBytesBE limb32)
    let c1 := setBytes c0
      (8 * ((offset.toNat + 16) / 8) + offset.toNat % 8)
      (mstoreLimbBytesBE limb40)
    let c2 := setBytes c1
      (8 * ((offset.toNat + 8) / 8) + offset.toNat % 8)
      (mstoreLimbBytesBE limb48)
    let c3 := setBytes c2
      (8 * ((offset.toNat + 0) / 8) + offset.toNat % 8)
      (mstoreLimbBytesBE limb56)
    cpsTripleWithin 70 base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56) **
       evmMemoryIs memBase capacity contents)
      (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset limb56 limb56 limb32 limb40 limb48 limb56
        capacity c3) := by
  dsimp only
  let c0 := setBytes contents
    (8 * ((offset.toNat + 24) / 8) + offset.toNat % 8)
    (mstoreLimbBytesBE limb32)
  let c1 := setBytes c0
    (8 * ((offset.toNat + 16) / 8) + offset.toNat % 8)
    (mstoreLimbBytesBE limb40)
  let c2 := setBytes c1
    (8 * ((offset.toNat + 8) / 8) + offset.toNat % 8)
    (mstoreLimbBytesBE limb48)
  let c3 := setBytes c2
    (8 * ((offset.toNat + 0) / 8) + offset.toNat % 8)
    (mstoreLimbBytesBE limb56)
  have h0raw := mstore_region_step_q0
    offReg byteReg accReg addrReg memBaseReg sp memBase offset
    byteOld accOld limb32 limb40 limb48 limb56 capacity contents (base := base)
    h_byte_ne_x0 h_acc_ne_x0 hlen hin h_window0
  have h1raw := mstore_region_step_q1
    offReg byteReg accReg addrReg memBaseReg sp memBase offset
    limb32 limb40 limb48 limb56 capacity c0 (base := base)
    h_byte_ne_x0 h_acc_ne_x0
    (by dsimp [c0]; rw [length_setBytes]; exact hlen)
    (by simpa [c0] using hin) h_window1
  have h2raw := mstore_region_step_q2
    offReg byteReg accReg addrReg memBaseReg sp memBase offset
    limb32 limb40 limb48 limb56 capacity c1 (base := base)
    h_byte_ne_x0 h_acc_ne_x0
    (by dsimp [c1]; rw [length_setBytes, length_setBytes]; exact hlen)
    (by simpa [c1, c0] using hin) h_window2
  have h3raw := mstore_region_step_q3
    offReg byteReg accReg addrReg memBaseReg sp memBase offset
    limb32 limb40 limb48 limb56 capacity c2 (base := base)
    h_byte_ne_x0 h_acc_ne_x0
    (by dsimp [c2]; rw [length_setBytes, length_setBytes, length_setBytes]; exact hlen)
    (by simpa [c2, c1, c0] using hin) h_window3
  have h0 := cpsTripleWithin_evm_mstore_of_one_limb_q0
    offReg valReg byteReg accReg addrReg memBaseReg base h0raw
  have h1 := cpsTripleWithin_evm_mstore_of_one_limb_q1
    offReg valReg byteReg accReg addrReg memBaseReg base h1raw
  have h2 := cpsTripleWithin_evm_mstore_of_one_limb_q2
    offReg valReg byteReg accReg addrReg memBaseReg base h2raw
  have h3 := cpsTripleWithin_evm_mstore_of_one_limb_q3
    offReg valReg byteReg accReg addrReg memBaseReg base h3raw
  have hbody := evm_mstore_public_one_limb_sequence_spec_within
    offReg valReg byteReg accReg addrReg memBaseReg base h0 h1 h2 h3
  let F : Assertion :=
    (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56) **
    evmMemoryIs memBase capacity contents
  have hpre' :
      cpsTripleWithin (17 + 17 + 17 + 17) (base + 8) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset) ** F)
        (mstoreRegionMid offReg byteReg accReg addrReg memBaseReg
          sp memBase offset limb56 limb56 limb32 limb40 limb48 limb56
          capacity c3) := cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F, mstoreRegionMid] at hp ⊢; sep_perm hp)
    (fun _ hp => hp) hbody
  have hp := evm_mstore_prologue_stack_spec_within_framed
    offReg valReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base F (by dsimp [F]; pcFree)
    h_off_ne_x0 h_addr_ne_x0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hs => by sep_perm hs) hp hpre'
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F] at hp ⊢; sep_perm hp)
    (fun _ hp => by exact hp) hseq

private theorem evm_mstore_stack_spec_within_backing
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord valueWord : EvmWord) (rest : List EvmWord)
    (offsetHigh1 offsetHigh2 offsetHigh3 : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = offsetHigh1)
    (h_offset2 : offsetWord.getLimbN 2 = offsetHigh2)
    (h_offset3 : offsetWord.getLimbN 3 = offsetHigh3)
    (h_value0 : valueWord.getLimbN 0 = limb0)
    (h_value1 : valueWord.getLimbN 1 = limb1)
    (h_value2 : valueWord.getLimbN 2 = limb2)
    (h_value3 : valueWord.getLimbN 3 = limb3)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (halignB : memBase.toNat % 8 = 0)
    (hin : 8 * (offset.toNat / 8) + mstorePairWindowBytes ≤ contents.length)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (2 + (17 + 17 + 17 + 17) + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       evmStackIs sp (offsetWord :: valueWord :: rest) **
       (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       evmMemoryIs memBase capacity contents)
      (((.x12 : Reg) ↦ᵣ (sp + 64)) **
       evmStackIs (sp + 64) rest ** evmWordIs sp offsetWord **
       evmWordIs (sp + 32) valueWord ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
       evmMemoryIs memBase capacity
         (evmMemoryWriteWord contents offset.toNat valueWord)) := by
  have hw0 := mstoreLimbWindowOk_region memBase offset contents 24
    24 25 26 27 28 29 30 31 halignB
    (by simpa [hlen] using hbound) hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hw1 := mstoreLimbWindowOk_region memBase offset contents 16
    16 17 18 19 20 21 22 23 halignB
    (by simpa [hlen] using hbound) hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hw2 := mstoreLimbWindowOk_region memBase offset contents 8
    8 9 10 11 12 13 14 15 halignB
    (by simpa [hlen] using hbound) hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hw3 := mstoreLimbWindowOk_region memBase offset contents 0
    0 1 2 3 4 5 6 7 halignB
    (by simpa [hlen] using hbound) hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hbody := mstore_region_body_spec_within
    offReg valReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase byteOld accOld
    limb0 limb1 limb2 limb3 capacity contents base
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0 hlen hin hw0 hw1 hw2 hw3
  have hk0 : 8 * ((offset.toNat + 0) / 8) + offset.toNat % 8 = offset.toNat := by
    have h := Nat.mod_add_div offset.toNat 8
    omega
  have hk0' : 8 * (offset.toNat / 8) + offset.toNat % 8 = offset.toNat := by
    have h := Nat.mod_add_div offset.toNat 8
    omega
  have hk8 : 8 * ((offset.toNat + 8) / 8) + offset.toNat % 8 = offset.toNat + 8 := by
    have h := Nat.mod_add_div offset.toNat 8
    omega
  have hk16 : 8 * ((offset.toNat + 16) / 8) + offset.toNat % 8 = offset.toNat + 16 := by
    have h := Nat.mod_add_div offset.toNat 8
    omega
  have hk24 : 8 * ((offset.toNat + 24) / 8) + offset.toNat % 8 = offset.toNat + 24 := by
    have h := Nat.mod_add_div offset.toNat 8
    omega
  have hc3 :
      (setBytes (setBytes (setBytes (setBytes contents
        (8 * ((offset.toNat + 24) / 8) + offset.toNat % 8)
        (mstoreLimbBytesBE limb0))
        (8 * ((offset.toNat + 16) / 8) + offset.toNat % 8)
        (mstoreLimbBytesBE limb1))
        (8 * ((offset.toNat + 8) / 8) + offset.toNat % 8)
        (mstoreLimbBytesBE limb2))
        (8 * ((offset.toNat + 0) / 8) + offset.toNat % 8)
        (mstoreLimbBytesBE limb3)) =
      evmMemoryWriteWord contents offset.toNat valueWord := by
    rw [hk24, hk16, hk8, hk0]
    unfold evmMemoryWriteWord evmWordBytesBE
    rw [h_value0, h_value1, h_value2, h_value3]
    have hwin : offset.toNat + 32 ≤ contents.length := by
      have hin' := hin
      simp only [mstorePairWindowBytes, mstorePairGuardBytes] at hin'
      have h := Nat.mod_add_div offset.toNat 8
      omega
    have hsplice := mstore_setBytes_four_limb_reverse contents
      (mstoreLimbBytesBE limb3) (mstoreLimbBytesBE limb2)
      (mstoreLimbBytesBE limb1) (mstoreLimbBytesBE limb0)
      offset.toNat (by rfl) (by rfl) (by rfl) (by rfl)
      hwin
    have hsplice' := hsplice.symm
    rw [hsplice']
  have hc3' :
      (setBytes (setBytes (setBytes (setBytes contents
        (offset.toNat + 24) (mstoreLimbBytesBE limb0))
        (offset.toNat + 16) (mstoreLimbBytesBE limb1))
        (offset.toNat + 8) (mstoreLimbBytesBE limb2))
        offset.toNat (mstoreLimbBytesBE limb3)) =
      evmMemoryWriteWord contents offset.toNat valueWord := by
    rw [hk24, hk16, hk8, hk0] at hc3
    exact hc3
  let FPre : Assertion :=
    (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3) **
    evmMemoryIs memBase capacity contents
  let FPost : Assertion :=
    (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
    (addrReg ↦ᵣ (memBase + offset)) ** (sp ↦ₘ offset) **
    (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
      ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3) **
      evmMemoryIs memBase capacity
        (evmMemoryWriteWord contents offset.toNat valueWord)
  have hbody' := cpsTripleWithin_weaken
    (fun _ hp => by dsimp [FPre]; sep_perm hp)
    (fun _ hp => by
      dsimp [mstoreRegionMid, FPost] at hp ⊢
      rw [hk24, hk16, hk8, hk0'] at hp
      rw [hc3'] at hp
      sep_perm hp) hbody
  have hFPre : FPre.pcFree := by
    dsimp [FPre]
    pcFree
  have hFPost : FPost.pcFree := by
    dsimp [FPost]
    pcFree
  have hep := mstore_epilogue_evm_mstore_frame_spec_within
    offReg valReg byteReg accReg addrReg memBaseReg sp base FPost hFPost
  have hfull := cpsTripleWithin_seq_same_cr hbody' hep
  let offsetHighFrame : Assertion :=
    ((sp + 8) ↦ₘ offsetHigh1) **
    ((sp + 16) ↦ₘ offsetHigh2) **
    ((sp + 24) ↦ₘ offsetHigh3)
  let stackFrame : Assertion :=
    offsetHighFrame ** evmStackIs (sp + 64) rest
  have hstackFrame : stackFrame.pcFree := by
    dsimp [stackFrame, offsetHighFrame]
    pcFree
  have hstack := cpsTripleWithin_frameR
    stackFrame hstackFrame
    hfull
  have hsp32 : sp + signExtend12 (32 : BitVec 12) = sp + 32 := by
    rw [signExtend12_32]
  have hsp40 : sp + signExtend12 (40 : BitVec 12) = sp + 40 := by
    rw [signExtend12_40]
  have hsp48 : sp + signExtend12 (48 : BitVec 12) = sp + 48 := by
    rw [signExtend12_48]
  have hsp56 : sp + signExtend12 (56 : BitVec 12) = sp + 56 := by
    rw [signExtend12_56]
  have hsp64 : sp + (32 + 32 : Word) = sp + 64 := by
    have h : (32 + 32 : Word) = 64 := by decide
    rw [h]
  have hsp64a : (sp + 32 : Word) + 32 = sp + 64 := by
    bv_addr
  have hsp32_target : sp + (32#64) = sp + signExtend12 (32#12) := by
    have h : signExtend12 (32#12) = (32#64) := by decide
    exact (congrArg (fun x : Word => sp + x) h).symm
  have hsp40_target : sp + (40#64) = sp + signExtend12 (40#12) := by
    have h : signExtend12 (40#12) = (40#64) := by decide
    exact (congrArg (fun x : Word => sp + x) h).symm
  have hsp48_target : sp + (48#64) = sp + signExtend12 (48#12) := by
    have h : signExtend12 (48#12) = (48#64) := by decide
    exact (congrArg (fun x : Word => sp + x) h).symm
  have hsp56_target : sp + (56#64) = sp + signExtend12 (56#12) := by
    have h : signExtend12 (56#12) = (56#64) := by decide
    exact (congrArg (fun x : Word => sp + x) h).symm
  have hsp32_8 : sp + signExtend12 (32#12) + 8 =
      sp + signExtend12 (40#12) := by
    have h32 : signExtend12 (32#12) = (32#64) := by decide
    have h40 : signExtend12 (40#12) = (40#64) := by decide
    rw [h32, h40]
    bv_addr
  have hsp32_16 : sp + signExtend12 (32#12) + 16 =
      sp + signExtend12 (48#12) := by
    have h32 : signExtend12 (32#12) = (32#64) := by decide
    have h48 : signExtend12 (48#12) = (48#64) := by decide
    rw [h32, h48]
    bv_addr
  have hsp32_24 : sp + signExtend12 (32#12) + 24 =
      sp + signExtend12 (56#12) := by
    have h32 : signExtend12 (32#12) = (32#64) := by decide
    have h56 : signExtend12 (56#12) = (56#64) := by decide
    rw [h32, h56]
    bv_addr
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [stackFrame, offsetHighFrame] at hp ⊢
      rw [evmStackIs_cons] at hp
      rw [evmWordIs_sp_limbs_eq sp offsetWord
        offset offsetHigh1 offsetHigh2 offsetHigh3
        h_offset0 h_offset1 h_offset2 h_offset3] at hp
      rw [evmStackIs_cons] at hp
      rw [evmWordIs_sp32_limbs_eq sp valueWord limb0 limb1 limb2 limb3
        h_value0 h_value1 h_value2 h_value3] at hp
      try rw [hsp64a] at hp
      rw [← hsp32, ← hsp40, ← hsp48, ← hsp56] at hp
      sep_perm hp)
    (fun _ hp => by
      dsimp [stackFrame, offsetHighFrame] at hp ⊢
      dsimp [FPost] at hp
      rw [evmWordIs_sp_limbs_eq sp offsetWord
        offset offsetHigh1 offsetHigh2 offsetHigh3
        h_offset0 h_offset1 h_offset2 h_offset3]
      unfold evmWordIs at ⊢
      rw [h_value0, h_value1, h_value2, h_value3]
      rw [hsp32_target, hsp32_8, hsp32_16, hsp32_24] at ⊢
      sep_perm hp)
    hstack

/-! Canonical region-backed MSTORE stack specification. The implementation's
    pair-peel tail is supplied by an explicit adjacent guard resource, while
    the semantic post-state writes exactly the 32 requested bytes. -/
theorem evm_mstore_stack_spec_within_region
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord valueWord : EvmWord) (rest : List EvmWord)
    (offsetHigh1 offsetHigh2 offsetHigh3 : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (capacity : Nat) (contents guard : List (BitVec 8)) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = offsetHigh1)
    (h_offset2 : offsetWord.getLimbN 2 = offsetHigh2)
    (h_offset3 : offsetWord.getLimbN 3 = offsetHigh3)
    (h_value0 : valueWord.getLimbN 0 = limb0)
    (h_value1 : valueWord.getLimbN 1 = limb1)
    (h_value2 : valueWord.getLimbN 2 = limb2)
    (h_value3 : valueWord.getLimbN 3 = limb3)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity) (hcapacity8 : 8 ∣ capacity)
    (hguard : mstorePairGuardBytes ≤ guard.length)
    (halignB : memBase.toNat % 8 = 0)
    (hin : offset.toNat + 32 ≤ capacity)
    (hbound : memBase.toNat + (contents ++ guard).length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < (contents ++ guard).length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (2 + (17 + 17 + 17 + 17) + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       evmStackIs sp (offsetWord :: valueWord :: rest) **
       (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       evmMemoryIs memBase capacity contents **
       bytesRegion (memBase + BitVec.ofNat 64 capacity) guard)
      (((.x12 : Reg) ↦ᵣ (sp + 64)) **
       evmStackIs (sp + 64) rest ** evmWordIs sp offsetWord **
       evmWordIs (sp + 32) valueWord ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
       evmMemoryIs memBase capacity
         (evmMemoryWriteWord contents offset.toNat valueWord) **
       bytesRegion (memBase + BitVec.ofNat 64 capacity) guard) := by
  have h_window :
      8 * (offset.toNat / 8) + mstorePairWindowBytes ≤
        (contents ++ guard).length := by
    simp only [List.length_append, mstorePairWindowBytes,
      mstorePairGuardBytes] at hguard ⊢
    omega
  have h_backing := evmMemoryIs_append_guard memBase capacity contents guard
    hlen hcapacity8
  have h_write := evmMemoryWriteWord_append_guard contents guard offset.toNat
    valueWord (hlen ▸ hin)
  have h_backing_post := evmMemoryIs_append_guard memBase capacity
    (evmMemoryWriteWord contents offset.toNat valueWord) guard
    (by simp [hlen]) hcapacity8
  have h_body := evm_mstore_stack_spec_within_backing
    offReg valReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase byteOld accOld offsetWord valueWord rest
    offsetHigh1 offsetHigh2 offsetHigh3 limb0 limb1 limb2 limb3
    (capacity + guard.length) (contents ++ guard) base
    h_offset0 h_offset1 h_offset2 h_offset3
    h_value0 h_value1 h_value2 h_value3
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    (by simp [hlen]) halignB h_window hbound hvalid
  rw [h_backing, h_write] at h_body
  rw [h_backing_post] at h_body
  exact h_body

end EvmAsm.Evm64
