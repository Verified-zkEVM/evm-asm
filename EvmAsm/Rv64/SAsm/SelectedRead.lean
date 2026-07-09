/-
  EvmAsm.Rv64.SAsm.SelectedRead

  **The dynamic selected-read / copy-tail combinator** (bead evm-asm-otbab).

  After a compare/select join, a pointer register holds ONE OF K region
  bases chosen at runtime — `x5 = (a < b ? aPtr : bPtr)` — and a shared
  tail `LD`s through `x5 + {0, 8, …}` to copy the selected value into an
  output window.  SAsm's static read routing (`readAt` needs a fixed base)
  cannot express this; at `cpsTripleWithin` level the model is direct:

  * **The post-join region choice** is the pointer pinned to an
    `if`-value, `p ↦ᵣ (if cond then aPtr else bPtr)`, with BOTH candidate
    regions present as `**` atoms.  Which region the tail reads is decided
    by the (propositional) selector carried from the compare — no
    arbitrary/wrong-region read is derivable, because the copy lemma
    consumes `bytesRegion sel selBs` for the pointer's ACTUAL value `sel`.

  * **The shared copy tail is proven ONCE**, parameterized by the selected
    region (`selectedDwordCopy_spec`, generic in the three registers, the
    chunk count, and the start offset).  At the join each selector branch
    instantiates it with its own region — same tail bytes, two lemma
    instances, the other region framed — exactly `RetForwardJoin`'s
    shared-tail discipline, for a read+copy.  (Reads don't change bytes,
    so one machine-level tail reached from both branches is byte-fine.)

  Supporting single-instruction primitives (reusable on their own):

  * `bytesRegion_ld_within` — `LD rd, 8q(rs1)` with `rs1` at a region base
    reads dword chunk `q` (`packBytes` of bytes `8q..8q+7`), region framed;
  * `bytesRegion_sd_within` — `SD rs2, 8q(rs1)` splices the stored dword
    into chunk `q` (`setBytes bs (8q) (dwordBytes v)`);

  and `copyDwords`, the chunkwise-copy denotation, with `copyDwords_covers`
  (a full-width copy IS the source list — what makes a `u256_min` post the
  byte-for-byte selected operand).

  Consumers: `u256_min` / `u256_max`
  (`Codegen/Programs/U256MinSAsm.lean`).
-/

import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.MemRegionWriteWide
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.MultiRw

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  Small-immediate sign extension
-- ============================================================================

/-- Sign-extending a sub-`2¹¹` 12-bit immediate is the plain value. -/
theorem signExtend12_ofNat_small (k : Nat) (hk : k < 2 ^ 11) :
    signExtend12 (BitVec.ofNat 12 k) = BitVec.ofNat 64 k := by
  unfold signExtend12
  have hmsb : (BitVec.ofNat 12 k).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat]
    have : k % 2 ^ 12 = k := Nat.mod_eq_of_lt (by omega)
    rw [this]
    simp
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

-- ============================================================================
-- §2  Dword-chunk read / write through a base-pinned register
-- ============================================================================

/-- **`LD rd, 8q(rs1)` reads dword chunk `q` of the region at `rs1`**:
    the value is `packBytes` of bytes `8q..8q+7`, the region framed
    unchanged (a read) — the dword analogue of `bytesRegion_lbu_within`. -/
theorem bytesRegion_ld_within (rd rs1 : Reg) (regionBase vOld : Word)
    (base : Word) (bs : List (BitVec 8)) (q : Nat)
    (hrd : rd ≠ .x0) (hq : 8 * q < bs.length) (himm : 8 * q < 2 ^ 11) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD rd rs1 (BitVec.ofNat 12 (8 * q))))
      ((rs1 ↦ᵣ regionBase) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ regionBase) **
        (rd ↦ᵣ packBytes ((bs.drop (8 * q)).take 8)) **
        bytesRegion regionBase bs) := by
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs q hq
  have hld := ld_spec_within rd rs1 regionBase vOld
    (packBytes ((bs.drop (8 * q)).take 8)) (BitVec.ofNat 12 (8 * q)) base hrd
  rw [signExtend12_ofNat_small (8 * q) himm] at hld
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq' => by xperm_hyp hq')
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) hld)

/-- **`SD rs2, 8q(rs1)` writes dword chunk `q` of the region at `rs1`**:
    the stored word is spliced in little-endian
    (`setBytes bs (8q) (dwordBytes v)`) — the dword analogue of
    `bytesRegion_sb_within`. -/
theorem bytesRegion_sd_within (rs1 rs2 : Reg) (regionBase v_data : Word)
    (base : Word) (bs : List (BitVec 8)) (q : Nat)
    (hq : 8 * q + 8 ≤ bs.length) (himm : 8 * q < 2 ^ 11) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD rs1 rs2 (BitVec.ofNat 12 (8 * q))))
      ((rs1 ↦ᵣ regionBase) ** (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ regionBase) ** (rs2 ↦ᵣ v_data) **
        bytesRegion regionBase (setBytes bs (8 * q) (dwordBytes v_data))) := by
  obtain ⟨front, rest, hf, hr, heq, heqset⟩ :=
    bytesRegion_dword_at_setBytes regionBase bs (dwordBytes v_data) q 0
      (by simp [dwordBytes]) (by simp) (by simp only [length_dwordBytes]; omega)
  have hsd := sd_spec_within rs1 rs2 regionBase v_data
    (packBytes ((bs.drop (8 * q)).take 8)) (BitVec.ofNat 12 (8 * q)) base
  rw [signExtend12_ofNat_small (8 * q) himm] at hsd
  have hchunk : packBytes (setBytes ((bs.drop (8 * q)).take 8) 0 (dwordBytes v_data))
      = v_data :=
    (packBytes_setBytes_dword ((bs.drop (8 * q)).take 8) v_data
      (by rw [List.length_take, List.length_drop]; omega)).symm
  rw [show (8 * q + 0 : Nat) = 8 * q from by omega, hchunk] at heqset
  rw [heq, heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq' => by xperm_hyp hq')
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) hsd)

-- ============================================================================
-- §3  The shared copy tail, proven once
-- ============================================================================

/-- The emitted chunk-copy tail: `N` interleaved `LD tmp, 8k(src) ;
    SD tmp, 8k(dst)` pairs starting at chunk `j`. -/
def dwordCopyProgFrom (src dst tmp : Reg) (j : Nat) : Nat → List Instr
  | 0 => []
  | N + 1 =>
      .LD tmp src (BitVec.ofNat 12 (8 * j)) ::
      .SD dst tmp (BitVec.ofNat 12 (8 * j)) ::
      dwordCopyProgFrom src dst tmp (j + 1) N

/-- The chunkwise-copy denotation: chunks `j..j+N` of `selBs` spliced into
    `outBs`. -/
def copyDwords (selBs : List (BitVec 8)) (outBs : List (BitVec 8)) (j : Nat) :
    Nat → List (BitVec 8)
  | 0 => outBs
  | N + 1 =>
      copyDwords selBs
        (setBytes outBs (8 * j)
          (dwordBytes (packBytes ((selBs.drop (8 * j)).take 8))))
        (j + 1) N

@[simp] theorem copyDwords_length (selBs outBs : List (BitVec 8)) (j N : Nat) :
    (copyDwords selBs outBs j N).length = outBs.length := by
  induction N generalizing outBs j with
  | zero => rfl
  | succ n ih => simp [copyDwords, ih]

/-- **A full-width copy IS the source**: when the `N` chunks cover both
    lists exactly, the copied output is byte-for-byte the selected
    operand.  This is what turns a chunk-copy post into a genuine
    "output = selected value" post. -/
theorem copyDwords_covers (selBs outBs : List (BitVec 8)) (N : Nat)
    (hsel : selBs.length = 8 * N) (hout : outBs.length = 8 * N) :
    copyDwords selBs outBs 0 N = selBs := by
  suffices h : ∀ (M j : Nat) (ob : List (BitVec 8)),
      j + M = N → ob.length = 8 * N → ob.take (8 * j) = selBs.take (8 * j) →
      copyDwords selBs ob j M = selBs by
    exact h N 0 outBs (by omega) hout (by simp)
  intro M
  induction M with
  | zero =>
      intro j ob hjM hlen hpref
      have hj : j = N := by omega
      show ob = selBs
      have h1 : ob.take (8 * j) = ob := List.take_of_length_le (by omega)
      have h2 : selBs.take (8 * j) = selBs := List.take_of_length_le (by omega)
      rw [← h1, ← h2]
      exact hpref
  | succ n ih =>
      intro j ob hjM hlen hpref
      show copyDwords selBs
        (setBytes ob (8 * j)
          (dwordBytes (packBytes ((selBs.drop (8 * j)).take 8)))) (j + 1) n = selBs
      have hchunklen : ((selBs.drop (8 * j)).take 8).length = 8 := by
        rw [List.length_take, List.length_drop]
        omega
      have hchunk : dwordBytes (packBytes ((selBs.drop (8 * j)).take 8))
          = (selBs.drop (8 * j)).take 8 :=
        dwordBytes_packBytes _ hchunklen
      rw [hchunk]
      refine ih (j + 1) _ (by omega) (by simp [hlen]) ?_
      -- prefix extends by the spliced chunk
      have hns : (8 * j) + ((selBs.drop (8 * j)).take 8).length ≤ ob.length := by
        rw [hchunklen]; omega
      apply List.ext_getElem
      · simp only [List.length_take, length_setBytes]
        omega
      intro k hk1 hk2
      simp only [List.length_take, length_setBytes] at hk1
      have hkN : k < 8 * (j + 1) := by omega
      have hkOb : k < ob.length := by omega
      have hkSel : k < selBs.length := by omega
      have hkSet : k < (setBytes ob (8 * j) ((selBs.drop (8 * j)).take 8)).length := by
        rw [length_setBytes]; omega
      rw [List.getElem_take, List.getElem_take]
      have hgl : getByteAt (setBytes ob (8 * j) ((selBs.drop (8 * j)).take 8)) k
          = (setBytes ob (8 * j) ((selBs.drop (8 * j)).take 8))[k]'hkSet := by
        unfold getByteAt
        rw [dif_pos]
      have hg := getByteAt_setBytes ((selBs.drop (8 * j)).take 8) ob (8 * j) k hns
      by_cases hkj : k < 8 * j
      · -- inside the untouched prefix
        rw [if_neg (by rw [hchunklen]; omega)] at hg
        have e2 : getByteAt ob k = ob[k]'hkOb := by
          unfold getByteAt; rw [dif_pos]
        have e3 : ob[k]'hkOb = selBs[k]'hkSel := by
          have t1 : getByteAt (ob.take (8 * j)) k = getByteAt ob k := by
            unfold getByteAt
            rw [dif_pos (by rw [List.length_take]; omega), dif_pos hkOb,
              List.getElem_take]
          have t2 : getByteAt (selBs.take (8 * j)) k = getByteAt selBs k := by
            unfold getByteAt
            rw [dif_pos (by rw [List.length_take]; omega), dif_pos hkSel,
              List.getElem_take]
          have ht := congrArg (fun l => getByteAt l k) hpref
          simp only at ht
          rw [t1, t2] at ht
          unfold getByteAt at ht
          rw [dif_pos hkOb, dif_pos hkSel] at ht
          exact ht
        rw [← hgl, hg, e2, e3]
      · -- inside the freshly spliced chunk
        have hk8 : 8 * j ≤ k := by omega
        rw [if_pos ⟨hk8, by rw [hchunklen]; omega⟩] at hg
        have hgr : getByteAt ((selBs.drop (8 * j)).take 8) (k - 8 * j)
            = selBs[k]'hkSel := by
          unfold getByteAt
          rw [dif_pos (by rw [hchunklen]; omega)]
          rw [List.getElem_take, List.getElem_drop]
          congr 1
          omega
        rw [← hgl, hg, hgr]

@[simp] theorem dwordCopyProgFrom_length (src dst tmp : Reg) (j N : Nat) :
    (dwordCopyProgFrom src dst tmp j N).length = 2 * N := by
  induction N generalizing j with
  | zero => rfl
  | succ n ih => simp [dwordCopyProgFrom, ih]; omega

/-- **The shared copy tail, proven once** — generic in the three registers,
    the chunk range `j..j+N`, and (crucially) the SELECTED region: `src` is
    pinned at `sel`, whichever base the selector chose; instantiating this
    one lemma per selector branch (other candidate region framed) gives the
    dynamically-selected copy with no wrong-region read. -/
theorem selectedDwordCopy_spec (src dst tmp : Reg)
    (htmp0 : tmp ≠ .x0)
    (sel out tv : Word) (selBs outBs : List (BitVec 8)) (j N : Nat)
    (hsel : 8 * (j + N) ≤ selBs.length) (hout : 8 * (j + N) ≤ outBs.length)
    (himm : 8 * (j + N) < 2 ^ 11) (base : Word) :
    cpsTripleWithin (2 * N) base (base + BitVec.ofNat 64 (4 * (2 * N)))
      (CodeReq.ofProg base (dwordCopyProgFrom src dst tmp j N))
      ((src ↦ᵣ sel) ** (dst ↦ᵣ out) ** (tmp ↦ᵣ tv) **
        bytesRegion sel selBs ** bytesRegion out outBs)
      ((src ↦ᵣ sel) ** (dst ↦ᵣ out) ** regOwn tmp **
        bytesRegion sel selBs ** bytesRegion out (copyDwords selBs outBs j N)) := by
  induction N generalizing j outBs tv base with
  | zero =>
      have hrefl : cpsTripleWithin 0 base base
          (CodeReq.ofProg base (dwordCopyProgFrom src dst tmp j 0))
          ((src ↦ᵣ sel) ** (dst ↦ᵣ out) ** (tmp ↦ᵣ tv) **
            bytesRegion sel selBs ** bytesRegion out outBs)
          ((src ↦ᵣ sel) ** (dst ↦ᵣ out) ** (tmp ↦ᵣ tv) **
            bytesRegion sel selBs ** bytesRegion out outBs) :=
        fun R hR s hcr hPR hpc => ⟨0, Nat.le_refl 0, s, rfl, hpc, hPR⟩
      rw [show base + BitVec.ofNat 64 (4 * (2 * 0)) = base from by bv_omega]
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => sepConj_mono_right (sepConj_mono_right (sepConj_mono
          (regIs_to_regOwn tmp tv) (fun _ hh => hh))) h hq)
        hrefl
  | succ n ih =>
      set chunk := packBytes ((selBs.drop (8 * j)).take 8) with hchunkDef
      -- LD tmp, 8j(src)
      have hld := bytesRegion_ld_within tmp src sel tv base selBs j htmp0
        (by omega) (by omega)
      have hldF := cpsTripleWithin_frameR
        ((dst ↦ᵣ out) ** bytesRegion out outBs) (by pcf) hld
      -- SD tmp, 8j(dst)
      have hsd := bytesRegion_sd_within dst tmp out chunk (base + 4) outBs j
        (by omega) (by omega)
      have hsdF := cpsTripleWithin_frameR
        ((src ↦ᵣ sel) ** bytesRegion sel selBs) (by pcf) hsd
      -- IH on the remaining chunks
      have hihStep := ih (j := j + 1)
        (outBs := setBytes outBs (8 * j) (dwordBytes chunk)) (tv := chunk)
        (base := base + 8)
        (by omega) (by simp only [length_setBytes]; omega) (by omega)
      rw [show (base + 8 : Word) = base + 4 + 4 from by bv_omega] at hihStep
      -- code-map plumbing: peel the two leading singletons off the ofProg
      have hlen1 : 4 * (dwordCopyProgFrom src dst tmp (j + 1) n).length < 2 ^ 64 := by
        rw [dwordCopyProgFrom_length]
        omega
      have hd2 : (CodeReq.singleton (base + 4)
          (.SD dst tmp (BitVec.ofNat 12 (8 * j)))).Disjoint
          (CodeReq.ofProg (base + 4 + 4) (dwordCopyProgFrom src dst tmp (j + 1) n)) := by
        apply CodeReq.Disjoint.singleton_ofProg
        apply CodeReq.ofProg_none_range
        intro k hk heq
        rw [dwordCopyProgFrom_length] at hk
        have hk4 : 8 + 4 * k < 2 ^ 64 := by omega
        bv_omega
      have hd1 : (CodeReq.singleton base
          (.LD tmp src (BitVec.ofNat 12 (8 * j)))).Disjoint
          ((CodeReq.singleton (base + 4)
            (.SD dst tmp (BitVec.ofNat 12 (8 * j)))).union
            (CodeReq.ofProg (base + 4 + 4) (dwordCopyProgFrom src dst tmp (j + 1) n))) := by
        intro a
        by_cases ha : a = base
        · subst ha
          right
          rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega))]
          apply CodeReq.ofProg_none_range
          intro k hk heq
          rw [dwordCopyProgFrom_length] at hk
          have hk4 : 8 + 4 * k < 2 ^ 64 := by omega
          bv_omega
        · left
          simp [CodeReq.singleton, ha]
      -- glue: LD post → SD pre (permute), SD post → IH pre (definitional)
      have hpair := cpsTripleWithin_seq hd2
        (cpsTripleWithin_weaken
          (Q' := (src ↦ᵣ sel) ** (dst ↦ᵣ out) ** (tmp ↦ᵣ chunk) **
            bytesRegion sel selBs **
            bytesRegion out (setBytes outBs (8 * j) (dwordBytes chunk)))
          (fun _ hp => hp)
          (fun _ hq => by xperm_hyp hq) hsdF)
        hihStep
      have hall := cpsTripleWithin_seq hd1
        (cpsTripleWithin_weaken
          (Q' := ((dst ↦ᵣ out) ** (tmp ↦ᵣ chunk) ** bytesRegion out outBs) **
            ((src ↦ᵣ sel) ** bytesRegion sel selBs))
          (fun _ hp => hp)
          (fun _ hq => by xperm_hyp hq) hldF)
        hpair
      rw [show (dwordCopyProgFrom src dst tmp j (n + 1))
        = .LD tmp src (BitVec.ofNat 12 (8 * j)) ::
          .SD dst tmp (BitVec.ofNat 12 (8 * j)) ::
          dwordCopyProgFrom src dst tmp (j + 1) n from rfl]
      rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons]
      have hsteps : 1 + (1 + 2 * n) = 2 * (n + 1) := by omega
      have hexit : (base + 4 + 4) + BitVec.ofNat 64 (4 * (2 * n))
          = base + BitVec.ofNat 64 (4 * (2 * (n + 1))) := by
        bv_omega
      rw [hexit, hsteps] at hall
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hall

#print axioms bytesRegion_ld_within
#print axioms bytesRegion_sd_within
#print axioms selectedDwordCopy_spec
#print axioms copyDwords_covers

end EvmAsm.Rv64.SAsm
