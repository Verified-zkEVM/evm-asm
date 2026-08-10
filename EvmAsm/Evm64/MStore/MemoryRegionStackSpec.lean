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

end EvmAsm.Evm64
