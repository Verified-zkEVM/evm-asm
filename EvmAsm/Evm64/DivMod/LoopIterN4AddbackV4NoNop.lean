/-
  EvmAsm.Evm64.DivMod.LoopIterN4AddbackV4NoNop

  No-NOP/v4 replay for the n=4 call+addback loop-body spec.
-/

module

public import EvmAsm.Evm64.DivMod.LoopIterN4CallV4NoNop
public import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def loopBodyN4CallAddbackJ0PostV4
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v3
  let divUn0 := divKTrialCallV4Un0 u3
  let qHat := divKTrialCallV4QHat uTop u3 v3
  let scratchOut := divKTrialCallV4ScratchOut uTop u3 v3 scratchMem
  loopBodyN4AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v3) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

@[irreducible]
def loopBodyN4CallAddbackBorrowV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV4QHat uTop u3 v3
  let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3
  (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word)

@[irreducible]
def loopBodyN4CallAddbackCarry2NzV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV4QHat uTop u3 v3
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  carry = 0 →
    addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0

/-- No-NOP/v4 loop body cpsTripleWithin for n=4, call+addback, j=0.
    This consumes the v4 div128 call path and exits to denorm. -/
theorem divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN4CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN4CallSkipJ0PreV4
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v3
  let dLo := divKTrialCallV4DLo v3
  let divUn0 := divKTrialCallV4Un0 u3
  let q1'' := divKTrialCallV4Q1dd uTop u3 v3
  let q0'' := divKTrialCallV4Q0dd uTop u3 v3
  let x7Exit := divKTrialCallV4X7Exit uTop u3 v3
  let x9Exit := divKTrialCallV4X9Exit uTop u3 v3
  let qHat := divKTrialCallV4QHat uTop u3 v3
  let scratchOut := divKTrialCallV4ScratchOut uTop u3 v3 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop sp (0 : Word) (4 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    uTop u3 v3 retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n4] at TF
  rw [u_addr8_eq_n4] at TF
  rw [vtop_eq_v3_n4] at TF
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  let carryOut := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  unfold loopBodyN4CallAddbackCarry2NzV4 at hcarry2_nz
  unfold loopBodyN4CallAddbackBorrowV4 at hborrow
  have MCA0 := MCA hcarry2_nz hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) MCA0
  have SL := divK_store_loop_j0_v4_spec_within_noNop sp q_out u4_out carryOut qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCA0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v3) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN4CallSkipJ0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN4CallAddbackJ0PostV4
      unfold loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost loopExitPost
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- DIV no-NOP v4 code-surface lift of the n=4 call+addback loop-body path. -/
theorem divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_divCode_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN4CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_noNop sp jOld v5Old v6Old v7Old
      v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem
      scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- MOD no-NOP v4 code-surface lift of the n=4 call+addback loop-body path. -/
theorem divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_modCode_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN4CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_noNop sp jOld v5Old v6Old v7Old
      v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem
      scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Full DIV v4 code-surface lift of the n=4 call+addback loop-body path. -/
theorem divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_divCode
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN4CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_divCode_noNop sp jOld v5Old
      v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem
      dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Full MOD v4 code-surface lift of the n=4 call+addback loop-body path. -/
theorem divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_modCode
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      (loopBodyN4CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_modCode_noNop sp jOld v5Old
      v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem
      dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)


end EvmAsm.Evm64
