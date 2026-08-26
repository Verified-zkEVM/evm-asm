module

public import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeqV4NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN1.CallV4NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def loopBodyN1CallAddbackBeqJ0PostV4
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  loopBodyN1AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

@[irreducible]
def loopBodyN1CallAddbackBeqJ0PostV4NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  loopBodyN1AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

theorem loopBodyN1CallAddbackBeqJ0PostV4NoX1_pcFree
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    (loopBodyN1CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem).pcFree := by
  delta loopBodyN1CallAddbackBeqJ0PostV4NoX1 loopBodyN1AddbackBeqPost
        loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
  pcFree

instance pcFreeInst_loopBodyN1CallAddbackBeqJ0PostV4NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    Assertion.PCFree
      (loopBodyN1CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  ⟨loopBodyN1CallAddbackBeqJ0PostV4NoX1_pcFree sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem⟩

theorem loopBodyN1CallAddbackBeqJ0PostV4NoX1_to_loopBodyN1CallAddbackBeqJ0PostV4
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    ∀ h,
      (loopBodyN1CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) h →
      loopBodyN1CallAddbackBeqJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem h := by
  intro h hp
  delta loopBodyN1CallAddbackBeqJ0PostV4NoX1 loopBodyN1CallAddbackBeqJ0PostV4 at hp ⊢
  simpa only [sepConj_assoc'] using hp

theorem loopBodyN1CallAddbackBeqJ0PostV4NoX1_eq_scratch
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN1CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN1CallAddbackBeqPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN1CallAddbackBeqJ0PostV4NoX1 loopBodyN1CallAddbackBeqPostJScratchNoX1
  rfl

@[irreducible]
def loopBodyN1CallAddbackBeqJgt0PostV4
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  loopBodyN1AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

@[irreducible]
def loopBodyN1CallAddbackBeqJgt0PostV4NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  loopBodyN1AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

theorem loopBodyN1CallAddbackBeqJgt0PostV4NoX1_pcFree
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    (loopBodyN1CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem).pcFree := by
  delta loopBodyN1CallAddbackBeqJgt0PostV4NoX1 loopBodyN1AddbackBeqPost
        loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
  pcFree

instance pcFreeInst_loopBodyN1CallAddbackBeqJgt0PostV4NoX1
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    Assertion.PCFree
      (loopBodyN1CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  ⟨loopBodyN1CallAddbackBeqJgt0PostV4NoX1_pcFree sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem⟩

theorem loopBodyN1CallAddbackBeqJgt0PostV4NoX1_to_loopBodyN1CallAddbackBeqJgt0PostV4
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    ∀ h,
      (loopBodyN1CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) h →
      loopBodyN1CallAddbackBeqJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem h := by
  intro h hp
  delta loopBodyN1CallAddbackBeqJgt0PostV4NoX1 loopBodyN1CallAddbackBeqJgt0PostV4 at hp ⊢
  simpa only [sepConj_assoc'] using hp

theorem loopBodyN1CallAddbackBeqJgt0PostV4NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN1CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN1CallAddbackBeqPostJScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN1CallAddbackBeqJgt0PostV4NoX1 loopBodyN1CallAddbackBeqPostJScratchNoX1
  rfl

/-- No-NOP/v4 loop body cpsTripleWithin for n=1, call+addback, j=0. -/
theorem divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
      (loopBodyN1CallAddbackBeqJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN1CallSkipJ0PreV4
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop sp (0 : Word) (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
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
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop
    sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  intro_lets at MCA
  have hcarry2_nz' :
      carry = 0 →
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
    dsimp only [] at hcarry2_nz
    exact hcarry2_nz
  have MCA0 := MCA hcarry2_nz' hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) MCA0
  have SL := divK_store_loop_j0_v4_spec_within_noNop sp q_out u4_out carryOut qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
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
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallAddbackBeqJ0PostV4
      change (loopBodyN1AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v0) **
        (sp + signExtend12 3952 ↦ₘ dLo) **
        (sp + signExtend12 3944 ↦ₘ div_un0) **
        (sp + signExtend12 3936 ↦ₘ scratchOut) **
        regOwn .x1) h
      unfold loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost
      rw [loopExitPost_unfold]
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+addback j=0 spec preserving the concrete caller
    `x1` through trial-call, addback, and store-loop exit. -/
theorem divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN1CallSkipJ0PreV4NoX1
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp (0 : Word) (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV4ExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
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
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop
    sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  intro_lets at MCA
  have hcarry2_nz' :
      carry = 0 →
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
    dsimp only [] at hcarry2_nz
    exact hcarry2_nz
  have MCA0 := MCA hcarry2_nz' hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
    (by pcFree) MCA0
  have SL := divK_store_loop_j0_v4_spec_within_noNop_exact_x1 sp q_out u4_out carryOut qOld raVal base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
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
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallAddbackBeqJ0PostV4NoX1
      change ((loopBodyN1AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v0) **
        (sp + signExtend12 3952 ↦ₘ dLo) **
        (sp + signExtend12 3944 ↦ₘ div_un0) **
        (sp + signExtend12 3936 ↦ₘ scratchOut)) **
        (.x1 ↦ᵣ raVal)) h
      unfold loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost
      rw [loopExitPost_unfold]
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+addback j=0 exact-`x1` spec exposing the
    scratch-parameterized post used by the callable loop surface. -/
theorem divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop_exact_x1_scratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallAddbackBeqPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopBodyN1CallAddbackBeqJ0PostV4NoX1_eq_scratch] at hp
      exact hp)
    (divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- No-NOP/v4 n=1 call+addback j=0 exact-`x1` spec lifted to the
    scratch-parameterized loop-iteration post. -/
theorem divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop_exact_x1_loopIterScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3) := by
    by_cases h_lt :
        BitVec.ult uTop
          (mulsubN4_c3 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)
    · exact h_lt
    · unfold mulsubN4_c3 at h_lt
      rw [if_neg h_lt] at hborrow
      exact False.elim (hborrow rfl)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopIterPostN1CallScratchNoX1_addback hb] at hp
      exact hp)
    (divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop_exact_x1_scratch
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- No-NOP/v4 n=1 call+addback j=0 spec with the call frame split so future
    callers can keep `x1` outside the loop-body assertion. -/
theorem divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop_noX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        regOwn .x1)
      (loopBodyN1CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) := by
  exact cpsTripleWithin_weaken
    (loopBodyN1CallSkipJ0PreV4NoX1_to_loopBodyN1CallSkipJ0PreV4
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
    (fun h hp => by
      unfold loopBodyN1CallAddbackBeqJ0PostV4 at hp
      unfold loopBodyN1CallAddbackBeqJ0PostV4NoX1
      simpa only [sepConj_assoc'] using hp)
    (divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- No-NOP/v4 loop body cpsTripleWithin for n=1, call+addback, j>0. -/
theorem divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (loopBodyN1CallAddbackBeqJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  intro uBase qAddr
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop sp j (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
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
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop
    sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  intro_lets at MCA
  have hcarry2_nz' :
      carry = 0 →
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
    dsimp only [] at hcarry2_nz
    exact hcarry2_nz
  have MCA0 := MCA hcarry2_nz' hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) MCA0
  have SL := divK_store_loop_jgt0_v4_spec_within_noNop sp j q_out u4_out carryOut qOld base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
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
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallAddbackBeqJgt0PostV4
      change (loopBodyN1AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v0) **
        (sp + signExtend12 3952 ↦ₘ dLo) **
        (sp + signExtend12 3944 ↦ₘ div_un0) **
        (sp + signExtend12 3936 ↦ₘ scratchOut) **
        regOwn .x1) h
      unfold loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost
      rw [loopExitPost_unfold]
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+addback j>0 spec preserving the concrete caller
    `x1` through trial-call, addback, and store-loop loop-back. -/
theorem divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  unfold loopBodyN1CallSkipJgt0PreV4NoX1
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp j (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem raVal base
    halign hbltu
  unfold divKTrialCallFullPostV4ExactX1 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
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
  have MCA := divK_mulsub_correction_addback_beq_v4_spec_within_noNop
    sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  intro_lets at MCA
  have hcarry2_nz' :
      carry = 0 →
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
    dsimp only [] at hcarry2_nz
    exact hcarry2_nz
  have MCA0 := MCA hcarry2_nz' hborrow
  have MCA0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
    (by pcFree) MCA0
  have SL := divK_store_loop_jgt0_v4_spec_within_noNop_exact_x1 sp j q_out u4_out carryOut qOld raVal base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
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
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut))
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallAddbackBeqJgt0PostV4NoX1
      change ((loopBodyN1AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v0) **
        (sp + signExtend12 3952 ↦ₘ dLo) **
        (sp + signExtend12 3944 ↦ₘ div_un0) **
        (sp + signExtend12 3936 ↦ₘ scratchOut)) **
        (.x1 ↦ᵣ raVal)) h
      unfold loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost
      rw [loopExitPost_unfold]
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP/v4 n=1 call+addback j>0 exact-`x1` spec exposing the
    scratch-parameterized post used by the callable loop surface. -/
theorem divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1_scratch (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN1CallAddbackBeqPostJScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopBodyN1CallAddbackBeqJgt0PostV4NoX1_eq_scratch] at hp
      exact hp)
    (divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1 j hpos
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- No-NOP/v4 n=1 call+addback j>0 exact-`x1` spec lifted to the
    scratch-parameterized loop-iteration post. -/
theorem divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1_loopIterScratch (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3) := by
    by_cases h_lt :
        BitVec.ult uTop
          (mulsubN4_c3 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)
    · exact h_lt
    · unfold mulsubN4_c3 at h_lt
      rw [if_neg h_lt] at hborrow
      exact False.elim (hborrow rfl)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      rw [loopIterPostN1CallScratchNoX1_addback hb] at hp
      exact hp)
    (divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1_scratch j hpos
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- No-NOP/v4 n=1 call+addback j>0 spec with the call frame split so future
    callers can keep `x1` outside the loop-body assertion. -/
theorem divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop_noX1 (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        regOwn .x1)
      (loopBodyN1CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) := by
  have legacy := divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratch_un0 scratchMem base halign hbltu hborrow hcarry2_nz
  dsimp only [] at legacy
  exact cpsTripleWithin_weaken
    (loopBodyN1CallSkipJgt0PreV4NoX1_to_legacy
      sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
    (fun h hp => by
      unfold loopBodyN1CallAddbackBeqJgt0PostV4 at hp
      unfold loopBodyN1CallAddbackBeqJgt0PostV4NoX1
      simpa only [sepConj_assoc'] using hp)
    legacy

end EvmAsm.Evm64
