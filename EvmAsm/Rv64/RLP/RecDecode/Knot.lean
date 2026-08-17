/-
  EvmAsm.Rv64.RLP.RecDecode.Knot

  The recursion knot: the handle contracts of the decoder pair hold at
  every budget, by the mutual ladder

    DecSound 0           (items call arm dead: the budget check rejects)
    DecSound d  (fp+32)  ⟹  ItemsSound d fp    (child = widened decoder)
    ItemsSound d (fp+8)  ⟹  DecSound (d+1) fp  (items = widened loop)

  Each step packages the body specification (`decFnV_spec` /
  `itemsFnV_spec`) through `Fn.retSpecR` (the `ra`-spill wrapper) at the
  ghost-indexed pre/post families, and repackages the callee handles by
  `FnHandleS.widenPrefix` so the caller's own frame rides across the call.
-/

import EvmAsm.Rv64.RLP.RecDecode.ItemsBody

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open EvmAsm.EL.RLP (Byte)

-- ============================================================================
-- Small helpers
-- ============================================================================

/-- A dead snapshot handle with a chosen entry (unreachable call arms whose
    `entry` hypothesis is still demanded by the body spec). -/
def deadHandleSNE (entry : Word) (reg : Region) (rw : RwRegion) (n : Nat) :
    FnHandleS where
  entry := entry
  code := CodeReq.empty
  nSteps := n
  region := reg
  rw := rw
  pre := fun _ _ _ => False
  post := fun _ _ _ _ _ _ => False
  sound := fun _ _ _ _ _ hpre => hpre.elim

private theorem idxOf_ofNat (inBase : Word) (k bnd : Nat)
    (hk : k ≤ bnd) (hb : inBase.toNat + bnd < 2 ^ 64) :
    idxOf inBase (inBase + BitVec.ofNat 64 k) = k := by
  unfold idxOf
  have haddr : (inBase + BitVec.ofNat 64 k).toNat = inBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.toNat_sub, haddr]
  omega

/-- Shift a layout to an interior sub-window of the writable region. -/
theorem RdLayout.shift {inBase : Word} {bs : List Byte} {fp : Word}
    {bigLen : Nat} (L : RdLayout inBase bs fp bigLen)
    (k small : Nat) (hk8 : k % 8 = 0) (hks : k + small ≤ bigLen) :
    RdLayout inBase bs (fp + BitVec.ofNat 64 k) small := by
  have hw := L.rwWf
  have hal : fp.toNat % 8 = 0 := hw.1
  have hb2 : fp.toNat + bigLen < 2 ^ 64 := hw.2.1
  have hva : ∀ j, j < bigLen →
      isValidMemAddr (fp + BitVec.ofNat 64 j) = true := hw.2.2
  have hbase : (fp + BitVec.ofNat 64 k).toNat = fp.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨L.regWf, ⟨?_, ?_, ?_⟩, ?_⟩
  · show (fp + BitVec.ofNat 64 k).toNat % 8 = 0
    rw [hbase]
    omega
  · show (fp + BitVec.ofNat 64 k).toNat + small < 2 ^ 64
    rw [hbase]
    omega
  · intro j hj
    have hj' : j < small := hj
    have haddr : fp + BitVec.ofNat 64 k + BitVec.ofNat 64 j
        = fp + BitVec.ofNat 64 (k + j) := by
      bv_omega
    show isValidMemAddr (fp + BitVec.ofNat 64 k + BitVec.ofNat 64 j) = true
    rw [haddr]
    exact hva (k + j) (by omega)
  · rcases L.disj with h | h
    · left
      rw [hbase]
      omega
    · right
      rw [hbase]
      omega

-- ============================================================================
-- Code routing inside `decCr`
-- ============================================================================

private theorem rdbe_flatten_pin (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) :
    (readBeFn inBase bs rwBase rwLen).programRet rdbeEntry = rdbeProg := rfl

private theorem decCr_of_rdbe (a : Word) (i : Instr)
    (h : CodeReq.ofProg rdbeEntry rdbeProg a = some i) :
    decCr a = some i := by
  have hdecNone : CodeReq.ofProg decEntry decProg a = none := by
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hkk : kk < 9 := by
      rw [show rdbeProg.length = 9 from rfl] at hk
      exact hk
    apply CodeReq.ofProg_none_range
    intro k' hk2 heq
    have hkk2 : k' < 106 := by
      rw [show decProg.length = 106 from rfl] at hk2
      exact hk2
    have heq' : (0x1800 : Word) + BitVec.ofNat 64 (4 * kk)
        = (0x1000 : Word) + BitVec.ofNat 64 (4 * k') := heq
    exact absurd heq' (by bv_omega)
  have hitemsNone : CodeReq.ofProg itemsEntry itemsProg a = none := by
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hkk : kk < 9 := by
      rw [show rdbeProg.length = 9 from rfl] at hk
      exact hk
    apply CodeReq.ofProg_none_range
    intro k' hk2 heq
    have hkk2 : k' < 93 := by
      rw [show itemsProg.length = 93 from rfl] at hk2
      exact hk2
    have heq' : (0x1800 : Word) + BitVec.ofNat 64 (4 * kk)
        = (0x1400 : Word) + BitVec.ofNat 64 (4 * k') := heq
    exact absurd heq' (by bv_omega)
  simp only [decCr, CodeReq.union, hdecNone, hitemsNone, h]

-- ============================================================================
-- The read-BE leaf handle at a given frame
-- ============================================================================

private theorem rdbe_hsz (inBase : Word) (bs : List Byte) (rwBase : Word)
    (rwLen : Nat) :
    4 * ((readBeFn inBase bs rwBase rwLen).body.size + 1) ≤ 2 ^ 64 := by
  show 4 * ((readBeFn 0 [] 0 0).body.size + 1) ≤ 2 ^ 64
  decide +kernel

/-- The verified leaf, packaged for a caller with frame `⟨rwBase, rwLen⟩`. -/
def beHandleAt (inBase : Word) (bs : List Byte) (rwBase : Word) (rwLen : Nat)
    (L : RdLayout inBase bs rwBase rwLen) : FnHandleS :=
  readBeHandleS inBase bs rwBase rwLen L rdbeEntry
    (rdbe_hsz inBase bs rwBase rwLen)

private theorem beHandleAt_nSteps (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    (beHandleAt inBase bs rwBase rwLen L).nSteps = rdbeSteps := rfl

private theorem beHandleAt_code (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    ∀ a i, (beHandleAt inBase bs rwBase rwLen L).code a = some i →
      decCr a = some i := by
  intro a i h
  exact decCr_of_rdbe a i h

private theorem beHandleAt_pre (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion) (j n : Nat),
      rf.get .x29 = inBase + BitVec.ofNat 64 j →
      rf.get .x30 = BitVec.ofNat 64 n → n ≤ 8 → j + n ≤ bs.length →
      (beHandleAt inBase bs rwBase rwLen L).pre rf ws A :=
  fun _ _ _ j n h29 h30 hn hjn => ⟨j, n, h29, h30, hn, hjn⟩

private theorem beHandleAt_post (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
      (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
      (beHandleAt inBase bs rwBase rwLen L).post rf₁ ws₁ A₁ rf ws A →
      rf.get .x31 = BitVec.ofNat 64
          (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
        ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
            rf.get r = rf₁.get r)
        ∧ ws = ws₁ ∧ A = A₁ :=
  fun _ _ _ _ _ _ h => h

end RecDecode
end SAsm
end EvmAsm.Rv64
