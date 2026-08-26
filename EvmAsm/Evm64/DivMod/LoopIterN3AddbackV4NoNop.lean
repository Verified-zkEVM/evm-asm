/-
  EvmAsm.Evm64.DivMod.LoopIterN3AddbackV4NoNop

  No-NOP/v4 replays for n=3 max+addback loop-body specs.
-/

module

public import EvmAsm.Evm64.DivMod.LoopIterN3CallV4NoNop
public import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq

@[expose] public section

open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.DivMod.AddrNorm (slt_jpos_1)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def loopBodyN3CallAddbackJ0PostV4
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
  loopBodyN3AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

@[irreducible]
def loopBodyN3CallAddbackJ0PostV4NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
  loopBodyN3AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

@[irreducible]
def loopBodyN3CallAddbackJgt0PreV4
    (j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN3CallSkipPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

@[irreducible]
def loopBodyN3CallAddbackJgt0PostV4
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
  loopBodyN3AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

@[irreducible]
def loopBodyN3CallAddbackJgt0PostV4NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
  loopBodyN3AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ divUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

@[irreducible]
def loopBodyN3CallAddbackBorrowV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3
  (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word)

@[irreducible]
def loopBodyN3CallAddbackCarry2NzV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  carry = 0 →
    addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0

/-- No-NOP/v4 variant of `divK_loop_body_n3_max_addback_j0_beq_spec_within_noNop`. -/
theorem divK_loop_body_n3_max_addback_j0_beq_v4_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN3MaxSkipPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qHat : Word := signExtend12 4095
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
  let vtopBase := sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_v4_spec_within_noNop sp (0 : Word) (3 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old u3 u2 v2 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    (0 : Word) u2 vtopBase u3 v2 v2Old base
  unfold isAddbackCarry2NzN3Max isAddbackCarry2Nz at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have SL := divK_store_loop_j0_v4_spec_within_noNop sp q_out u4_out carryOut qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN3MaxSkipPre_unfold] at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- No-NOP/v4 variant of `divK_loop_body_n3_max_addback_jgt0_beq_spec_within_noNop`. -/
theorem divK_loop_body_n3_max_addback_jgt0_beq_v4_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN3MaxSkipPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3AddbackBeqPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  let qHat : Word := signExtend12 4095
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
  let vtopBase := sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_v4_spec_within_noNop sp j (3 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old u3 u2 v2 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop sp qHat j
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    j u2 vtopBase u3 v2 v2Old base
  unfold isAddbackCarry2NzN3Max isAddbackCarry2Nz at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have SL := divK_store_loop_jgt0_v4_spec_within_noNop sp j q_out u4_out carryOut qOld base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN3MaxSkipPre_unfold] at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- No-NOP/v4 variant of `divK_loop_body_n3_call_addback_j0_beq_spec_within_noNop`. -/
theorem divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN3CallSkipJ0PreV4
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v2
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let q1'' := divKTrialCallV4Q1dd u3 u2 v2
  let q0'' := divKTrialCallV4Q0dd u3 u2 v2
  let x7Exit := divKTrialCallV4X7Exit u3 u2 v2
  let x9Exit := divKTrialCallV4X9Exit u3 u2 v2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
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
  have TF := divK_trial_call_full_v4_spec_within_noNop sp (0 : Word) (3 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u3 u2 v2 retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  unfold loopBodyN3CallAddbackCarry2NzV4 at hcarry2_nz
  unfold loopBodyN3CallAddbackBorrowV4 at hborrow
  have MCA0 := MCA hcarry2_nz hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) MCA0
  have SL := divK_store_loop_j0_v4_spec_within_noNop sp q_out u4_out carryOut qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
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
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3CallSkipPre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN3CallAddbackJ0PostV4
      unfold loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPost
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- No-NOP/v4 n=3 call+addback j=0 spec preserving the concrete caller `x1`
    through trial-call, addback, and store-loop exit. -/
theorem divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN3CallAddbackJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN3CallSkipJ0PreV4NoX1
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v2
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let q1'' := divKTrialCallV4Q1dd u3 u2 v2
  let q0'' := divKTrialCallV4Q0dd u3 u2 v2
  let x7Exit := divKTrialCallV4X7Exit u3 u2 v2
  let x9Exit := divKTrialCallV4X9Exit u3 u2 v2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
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
  have TF := divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp (0 : Word) (3 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u3 u2 v2 retMem dMem dloMem scratchUn0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV4ExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  unfold loopBodyN3CallAddbackCarry2NzV4 at hcarry2_nz
  unfold loopBodyN3CallAddbackBorrowV4 at hborrow
  have MCA0 := MCA hcarry2_nz hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
    (by pcFree) MCA0
  have SL := divK_store_loop_j0_v4_spec_within_noNop_exact_x1 sp q_out u4_out carryOut qOld raVal base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
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
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN3CallAddbackJ0PostV4NoX1
      unfold loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPost
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- No-NOP/v4 variant of `divK_loop_body_n3_call_addback_jgt0_beq_spec_within_noNop`. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN3CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN3CallAddbackJgt0PreV4
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v2
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let q1'' := divKTrialCallV4Q1dd u3 u2 v2
  let q0'' := divKTrialCallV4Q0dd u3 u2 v2
  let x7Exit := divKTrialCallV4X7Exit u3 u2 v2
  let x9Exit := divKTrialCallV4X9Exit u3 u2 v2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
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
  have TF := divK_trial_call_full_v4_spec_within_noNop sp j (3 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u3 u2 v2 retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop sp qHat j
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  unfold loopBodyN3CallAddbackCarry2NzV4 at hcarry2_nz
  unfold loopBodyN3CallAddbackBorrowV4 at hborrow
  have MCA0 := MCA hcarry2_nz hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) MCA0
  have SL := divK_store_loop_jgt0_v4_spec_within_noNop sp j q_out u4_out carryOut qOld base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCA0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3CallSkipPre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN3CallAddbackJgt0PostV4
      unfold loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPost
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- No-NOP/v4 n=3 call+addback j>0 spec preserving the concrete caller
    `x1` through trial-call, addback, and store-loop loop-back. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN3CallAddbackJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN3CallSkipJgt0PreV4NoX1
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v2
  let dLo := divKTrialCallV4DLo v2
  let divUn0 := divKTrialCallV4Un0 u2
  let q1'' := divKTrialCallV4Q1dd u3 u2 v2
  let q0'' := divKTrialCallV4Q0dd u3 u2 v2
  let x7Exit := divKTrialCallV4X7Exit u3 u2 v2
  let x9Exit := divKTrialCallV4X9Exit u3 u2 v2
  let qHat := divKTrialCallV4QHat u3 u2 v2
  let scratchOut := divKTrialCallV4ScratchOut u3 u2 v2 scratchMem
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
  have TF := divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp j (3 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u3 u2 v2 retMem dMem dloMem scratchUn0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV4ExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop sp qHat j
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  unfold loopBodyN3CallAddbackCarry2NzV4 at hcarry2_nz
  unfold loopBodyN3CallAddbackBorrowV4 at hborrow
  have MCA0 := MCA hcarry2_nz hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
    (by pcFree) MCA0
  have SL := divK_store_loop_jgt0_v4_spec_within_noNop_exact_x1 sp j q_out u4_out carryOut qOld
    raVal base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCA0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ divUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN3CallAddbackJgt0PostV4NoX1
      unfold loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPost
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- DIV no-NOP v4 code-surface lift of the n=3 call+addback loop-body j=0 path. -/
theorem divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_divCode_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_noNop sp jOld v5Old v6Old v7Old
      v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem
      scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- MOD no-NOP v4 code-surface lift of the n=3 call+addback loop-body j=0 path. -/
theorem divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_modCode_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_noNop sp jOld v5Old v6Old v7Old
      v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem
      scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Full DIV v4 code-surface lift of the n=3 call+addback loop-body j=0 path. -/
theorem divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_divCode
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN3CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_divCode_noNop sp jOld v5Old
      v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem
      dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Full MOD v4 code-surface lift of the n=3 call+addback loop-body j=0 path. -/
theorem divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_modCode
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      (loopBodyN3CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_modCode_noNop sp jOld v5Old
      v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem
      dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- DIV no-NOP v4 code-surface lift of the n=3 call+addback loop-body j>0 path. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_divCode_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN3CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_noNop j hpos sp jOld v5Old
      v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem
      dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- MOD no-NOP v4 code-surface lift of the n=3 call+addback loop-body j>0 path. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_modCode_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_noNop j hpos sp jOld v5Old
      v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem
      dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Full DIV v4 code-surface lift of the n=3 call+addback loop-body j>0 path. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_divCode (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN3CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_divCode_noNop j hpos sp jOld
      v5Old v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Full MOD v4 code-surface lift of the n=3 call+addback loop-body j>0 path. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_modCode (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (modCode_v4 base)
      (loopBodyN3CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_modCode_noNop j hpos sp jOld
      v5Old v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

end EvmAsm.Evm64
