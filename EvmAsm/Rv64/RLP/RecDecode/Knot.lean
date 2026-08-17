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

-- ============================================================================
-- The packaged decoder at a snapshot entry state
-- ============================================================================

private theorem se12k_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  decide

/-- The decoder `Fn` packaged at the snapshot ghosts `(rf₀, ws₀, A₀)`:
    the contract shape `Fn.retSpecR` consumes to produce `DecSound`. -/
private def decFnR (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (beS itemsS : FnHandleS) : Fn where
  name := "rlpdec"
  region := ⟨inBase, bs⟩
  rw := decRw d fp
  pre := Reach.exact rf₀ ws₀ A₀
  post := decPostS bs inBase d fp rf₀ ws₀ A₀
  body := decBody beS itemsS

private theorem dec_hsz (beS itemsS : FnHandleS) :
    4 * ((decBody beS itemsS).size + 3) ≤ 2 ^ 64 := by
  rw [show (decBody beS itemsS).size = decFnPin.body.size from rfl]
  decide +kernel

private theorem dec_hcode (beS itemsS : FnHandleS)
    (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion) :
    ∀ a i, CodeReq.ofProg decEntry
        ((decFnR bs inBase d fp rf₀ ws₀ A₀ beS itemsS).programRetR
          .x13 0 decEntry) a = some i →
      decCr a = some i := by
  intro a i h
  have h' : CodeReq.ofProg decEntry decProg a = some i := h
  simp only [decCr, CodeReq.union, h']

/-- The inner body of `DecSound` from the two handle contracts and the
    step budget. -/
private theorem decSound_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (beS itemsS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hbeE : beS.entry = rdbeEntry)
    (hbeCode : ∀ a i, beS.code a = some i → decCr a = some i)
    (hbeReg : beS.region = (⟨inBase, bs⟩ : Region))
    (hbeRw : beS.rw = decRw d fp)
    (hbePre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion)
        (j n : Nat), rf.get .x29 = inBase + BitVec.ofNat 64 j →
        rf.get .x30 = BitVec.ofNat 64 n → n ≤ 8 → j + n ≤ bs.length →
        beS.pre rf ws A)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (hitE : itemsS.entry = itemsEntry)
    (hitCode : ∀ a i, itemsS.code a = some i → decCr a = some i)
    (hitReg : itemsS.region = (⟨inBase, bs⟩ : Region))
    (hitRw : itemsS.rw = decRw d fp)
    (hitPre : 1 ≤ d → ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsPreS bs inBase (d - 1) (fp + 8) rf ws A → itemsS.pre rf ws A)
    (hitPost : 1 ≤ d → ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = itemsStatus bs (pStartOf inBase rf₁)
            (pEndOf inBase rf₁ - pStartOf inBase rf₁) (d - 1)
          ∧ rf.get .x13 = fp + 8
          ∧ ws.take 8 = ws₁.take 8
          ∧ A = A₁)
    (hsteps : 1 + (decBody beS itemsS).steps + 2 ≤ decSteps bs.length d) :
    ∀ rf₀ ws₀ A₀, ws₀.length = 40 * d + 8 → Assertion.pcFree A₀ →
      decPreS bs inBase d fp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
        cpsTripleWithin (decSteps bs.length d) decEntry ret decCr
          (((.x1 : Reg) ↦ᵣ ret)
            ** asrtM ⟨inBase, bs⟩ (decRw d fp) (Reach.exact rf₀ ws₀ A₀))
          (((.x1 : Reg) ↦ᵣ ret)
            ** asrtM ⟨inBase, bs⟩ (decRw d fp)
                (decPostS bs inBase d fp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hpc hpre ret halign
  obtain ⟨off, len, hx10, hx11, hx12, hx13, hoff⟩ := hpre
  have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hfpb : fp.toNat + (40 * d + 8) < 2 ^ 64 := L.rwWf.2.1
  have hd64 : d < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  have ho : offOf inBase rf₀ = off := by
    unfold offOf
    rw [hx10]
    exact idxOf_ofNat inBase off bs.length (by omega) hb
  have hl : lenOf rf₀ = len := by
    unfold lenOf
    rw [hx11, BitVec.toNat_ofNat]
    omega
  refine cpsTripleWithin_mono_nSteps hsteps ?_
  exact Fn.retSpecR (decFnR bs inBase d fp rf₀ ws₀ A₀ beS itemsS)
    decEntry decCr .x13 0 0
    (fun v => (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS).pre)
    (fun v => (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS).post)
    (by decide)
    L.rwWf
    ⟨0, rfl⟩
    (by show 0 + 8 ≤ 40 * d + 8; omega)
    (dec_hsz beS itemsS)
    (fun v => decFnV_spec bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS
      L hoff hx10 hx11 hx12 hx13 hd64 hbeE hbeCode hbeReg hbeRw hbePre
      hbePost hitE hitCode hitReg hitRw hitPre hitPost)
    (dec_hcode beS itemsS bs inBase d fp rf₀ ws₀ A₀)
    (by
      rintro rf ws A ⟨h1, -, -⟩
      rw [h1, hx13, se12k_0]
      show fp + 0 = fp + BitVec.ofNat 64 0
      bv_omega)
    (by
      rintro v rf ws A ⟨-, h13, -, -⟩
      rw [h13, se12k_0]
      show fp + 0 = fp + BitVec.ofNat 64 0
      bv_omega)
    (by
      rintro v rf ws A ⟨h1, h2, h3⟩ hwsl
      exact ⟨h1, by rw [h2], h3⟩)
    (by
      rintro v rf ws A ⟨h10, h13, -, hA⟩
      exact ⟨by rw [h10, ho, hl], h13, hA⟩)
    (by
      rintro v rf ws A ⟨-, -, htk, -⟩ hwsl
      rw [List.drop_zero]
      exact htk)
    ret halign

end RecDecode
end SAsm
end EvmAsm.Rv64
