/-
  EvmAsm.Evm64.DivMod.LoopComposeN3

  Two-iteration loop composition for n=3: composes j=1 (loop-back) with
  j=0 (loop-exit) to produce a cpsTripleWithin from base+448 to base+904.

  For n=3, the loop runs 2 iterations. The j=1 iteration modifies u[1]..u[4]
  and stores q[1]. The j=0 iteration reads u[0]..u[4] (where u[1]..u[4]
  are the updated values from j=1) and stores q[0].

  The compose surfaces in this file still thread the legacy universal
  Carry2NzAll package. They are compatibility surfaces for older callers; new
  v4 N3 stack/callable work should use selected/reachable carry wrappers.
-/

import EvmAsm.Evm64.DivMod.LoopIterN3
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
import EvmAsm.Rv64.Tactics.XPermChunked

/- No-NOP n=3 loop-body adapters, colocated with their composition consumers. -/

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (slt_jpos_1)

/-- No-NOP variant of `divK_loop_body_n3_max_addback_beq_j1_spec_within`. -/
theorem divK_loop_body_n3_max_addback_beq_j1_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopBodyN3AddbackBeqPost sp (1 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr hborrow
  let qHat : Word := signExtend12 4095
  unfold isAddbackCarry2NzN3Max isAddbackCarry2Nz at hcarry2_nz
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
  have TF := divK_trial_max_full_spec_within_noNop sp (1 : Word) (3 : Word) jOld v5Old v6Old v7Old v10Old v11Old
    u3 u2 v2 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_spec_within_noNop sp qHat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    (1 : Word) u2 vtopBase u3 v2 v2Old base
  intro_lets at MCA
  have MCA0 := MCA hcarry2_nz hborrow
  have SL := divK_store_loop_jgt0_spec_within_noNop sp (1 : Word) q_out u4_out carryOut qOld base slt_jpos_1
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
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
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
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP variant of `divK_loop_body_n3_call_addback_beq_j0_spec_within`. -/
theorem divK_loop_body_n3_call_addback_beq_j0_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (loopBodyN3CallAddbackBeqPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  let dHi := v2 >>> (32 : BitVec 6).toNat
  let dLo := (v2 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u2 >>> (32 : BitVec 6).toNat
  let div_un0 := (u2 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u3 dHi; let rhat := u3 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN3Call div128Quot at hborrow
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
  have TF := divK_trial_call_full_spec_within_noNop sp (0 : Word) (3 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u3 u2 v2 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_spec_within_noNop sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + div128CallRetOff) base
  intro_lets at MCA
  unfold isAddbackCarry2NzN3Call isAddbackCarry2Nz div128Quot at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have MCA0f := cpsTripleWithin_frameR (regOwn .x1) (by pcFree) MCA0
  have SL := divK_store_loop_j0_spec_within_noNop sp q_out u4_out carryOut qOld base
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
     (sp + signExtend12 3944 ↦ₘ div_un0) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN3CallAddbackBeqPost div128Quot div128DLo div128Un0
            loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP variant of `divK_loop_body_n3_call_addback_beq_j1_spec_within`. -/
theorem divK_loop_body_n3_call_addback_beq_j1_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 202 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (loopBodyN3CallAddbackBeqPostJ sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  let dHi := v2 >>> (32 : BitVec 6).toNat
  let dLo := (v2 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u2 >>> (32 : BitVec 6).toNat
  let div_un0 := (u2 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u3 dHi; let rhat := u3 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN3Call div128Quot at hborrow
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
  have TF := divK_trial_call_full_spec_within_noNop sp (1 : Word) (3 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u3 u2 v2 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n3] at TF
  rw [u_addr8_eq_n3] at TF
  rw [vtop_eq_v2_n3] at TF
  have MCA := divK_mulsub_correction_addback_beq_spec_within_noNop sp qHat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + div128CallRetOff) base
  intro_lets at MCA
  unfold isAddbackCarry2NzN3Call isAddbackCarry2Nz div128Quot at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have MCA0f := cpsTripleWithin_frameR (regOwn .x1) (by pcFree) MCA0
  have SL := divK_store_loop_jgt0_spec_within_noNop sp (1 : Word) q_out u4_out carryOut qOld base slt_jpos_1
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
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN3CallAddbackBeqPostJ div128Quot div128DLo div128Un0
            loopBodyN3AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN3 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

end EvmAsm.Evm64


open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1)

-- ============================================================================
-- Address equality lemmas for j=1 output → j=0 input transition
--
-- j=1 postcondition uses uBase(1) = sp + signExtend12(4056) - 8
-- j=0 precondition uses uBase(0) = sp + signExtend12(4056)
-- The overlap: uBase(1) + offset_k = uBase(0) + offset_{k-1}
-- ============================================================================

/-- j=1 un0 at uBase(1)+0 = j=0 u1 at uBase(0)-8 -/
theorem u_j1_0_eq_j0_4088 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- j=1 un1 at uBase(1)-8 = j=0 u2 at uBase(0)-16 -/
theorem u_j1_4088_eq_j0_4080 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- j=1 un2 at uBase(1)-16 = j=0 u3 at uBase(0)-24 -/
theorem u_j1_4080_eq_j0_4072 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- j=1 un3 at uBase(1)-24 = j=0 uTop at uBase(0)-32 -/
theorem u_j1_4072_eq_j0_4064 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

@[irreducible] def loopBodyN3MaxUnifiedPre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
   (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
   (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
   (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
   (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
   ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
   ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
   ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
   ((uBase + signExtend12 4064) ↦ₘ uTop) **
   (qAddr ↦ₘ qOld))

theorem loopBodyN3MaxUnifiedPre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) :
    loopBodyN3MaxUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld =
    (let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
      (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
      (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
      (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
      ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
      ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
      ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
      ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
      ((uBase + signExtend12 4064) ↦ₘ uTop) **
      (qAddr ↦ₘ qOld)) : Assertion) := by
  unfold loopBodyN3MaxUnifiedPre
  rfl

@[irreducible] def loopBodyN3CallUnifiedPre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
     retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
   (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
   (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
   (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
   (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
   ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
   ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
   ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
   ((uBase + signExtend12 4064) ↦ₘ uTop) **
   (qAddr ↦ₘ qOld) **
   (sp + signExtend12 3968 ↦ₘ retMem) **
   (sp + signExtend12 3960 ↦ₘ dMem) **
   (sp + signExtend12 3952 ↦ₘ dloMem) **
   ((sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1))

theorem loopBodyN3CallUnifiedPre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
     retMem dMem dloMem scratch_un0 : Word) :
    loopBodyN3CallUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 =
    (let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
      (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
      (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
      (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
      ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
      ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
      ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
      ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
      ((uBase + signExtend12 4064) ↦ₘ uTop) **
      (qAddr ↦ₘ qOld) **
      (sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      ((sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)) : Assertion) := by
  unfold loopBodyN3CallUnifiedPre
  rfl

-- ============================================================================
-- Double-addback () unified j=1 max-path spec
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN3Max.
-- ============================================================================

theorem divK_loop_body_n3_max_unified_j1_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyN3MaxUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN3Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n3_max_addback_beq_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu hcarry2_nz
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J1 hborrow))
  · -- skip path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n3_max_skip_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        rw [loopBodyN3MaxSkipPre_unfold]
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_skip hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J1 hborrow))

/-- No-NOP variant of `divK_loop_body_n3_max_unified_j1_spec_within`. -/
theorem divK_loop_body_n3_max_unified_j1_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      (loopBodyN3MaxUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN3Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n3_max_addback_beq_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu hcarry2_nz
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J1 hborrow))
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n3_max_skip_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        rw [loopBodyN3MaxSkipPre_unfold]
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_skip hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J1 hborrow))

-- ============================================================================
-- Double-addback () unified j=0 max-path spec
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN3Max.
-- ============================================================================

theorem divK_loop_body_n3_max_unified_j0_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopBodyN3MaxUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n3_max_addback_beq_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu hcarry2_nz
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J0 hborrow))
  · -- skip path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n3_max_skip_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        rw [loopBodyN3MaxSkipPre_unfold]
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_skip hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J0 hborrow))

/-- No-NOP variant of `divK_loop_body_n3_max_unified_j0_spec_within`. -/
theorem divK_loop_body_n3_max_unified_j0_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopBodyN3MaxUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n3_max_addback_beq_j0_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu hcarry2_nz
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J0 hborrow))
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n3_max_skip_j0_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3MaxUnifiedPre_unfold] at hp
        rw [loopBodyN3MaxSkipPre_unfold]
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Max_skip hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) (J0 hborrow))

-- ============================================================================
-- Double-addback () unified j=1 call-path spec
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN3Call.
-- ============================================================================

theorem divK_loop_body_n3_call_unified_j1_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyN3CallUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN3Call sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN3Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n3_call_addback_beq_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow hcarry2_nz
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        rw [loopBodyN3CallPre_unfold]
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Call_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J1)
  · -- skip path
    have hborrow : isSkipBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J1 := divK_loop_body_n3_call_skip_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        rw [loopBodyN3CallPre_unfold]
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Call_skip hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J1)

/-- No-NOP variant of `divK_loop_body_n3_call_unified_j1_spec_within`. -/
theorem divK_loop_body_n3_call_unified_j1_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      (loopBodyN3CallUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN3Call sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN3Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n3_call_addback_beq_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow hcarry2_nz
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Call_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J1)
  · have hborrow : isSkipBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J1 := divK_loop_body_n3_call_skip_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J1
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        rw [loopBodyN3CallPre_unfold]
        exact hp)
      (fun h hp => by rw [← loopIterPostN3Call_skip hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J1)

-- ============================================================================
-- Double-addback () unified j=0 call-path spec
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN3Call.
-- ============================================================================

theorem divK_loop_body_n3_call_unified_j0_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopBodyN3CallUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN3Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n3_call_addback_beq_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow hcarry2_nz
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        rw [loopBodyN3CallPre_unfold]
        exact hp)
      (fun h hp => by
        rw [loopBodyN3CallAddbackBeqPost_eq_J] at hp
        rw [← loopIterPostN3Call_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J0)
  · -- skip path
    have hborrow : isSkipBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J0 := divK_loop_body_n3_call_skip_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        rw [loopBodyN3CallPre_unfold]
        exact hp)
      (fun h hp => by
        delta loopIterPostN3Call iterN3Call iterWithDoubleAddback
              loopBodyN3CallSkipPost loopBodyN3SkipPost loopBodySkipPost
              loopExitPostN3 loopExitPost at hp ⊢
        unfold mulsubN4_c3 at hb; simp only [if_neg hb] at hp ⊢; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J0)

/-- No-NOP variant of `divK_loop_body_n3_call_unified_j0_spec_within`. -/
theorem divK_loop_body_n3_call_unified_j0_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopBodyN3CallUnifiedPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN3Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n3_call_addback_beq_j0_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow hcarry2_nz
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        exact hp)
      (fun h hp => by
        rw [loopBodyN3CallAddbackBeqPost_eq_J] at hp
        rw [← loopIterPostN3Call_addback hb]; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J0)
  · have hborrow : isSkipBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J0 := divK_loop_body_n3_call_skip_j0_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J0
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [loopBodyN3CallUnifiedPre_unfold] at hp
        rw [loopBodyN3CallPre_unfold]
        exact hp)
      (fun h hp => by
        delta loopIterPostN3Call iterN3Call iterWithDoubleAddback
              loopBodyN3CallSkipPost loopBodyN3SkipPost loopBodySkipPost
              loopExitPostN3 loopExitPost at hp ⊢
        unfold mulsubN4_c3 at hb; simp only [if_neg hb] at hp ⊢; exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) J0)

-- ============================================================================
-- Double-addback () two-iteration max×max composition
-- Case-splits on j=1 borrow to use raw skip/beq specs, then composes with
-- j=0  spec. Uses iterN3Max (non-irreducible) for postcondition matching.
-- ============================================================================

theorem divK_loop_n3_max_max_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (base : Word)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 304 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN3Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old)
      (loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1  iteration spec
  have J1 := divK_loop_body_n3_max_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  -- Frame j=1 with u0Orig and q0Old
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- 3. j=0  iteration spec (inputs from j=1 via iterN3Max)
  have J0 := divK_loop_body_n3_max_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base

    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1  postcondition → j=0 precondition
  --    loopIterPostN3Max unfolds to if-then-else, so we case-split on borrow
  --    then unfold the branch to get concrete assertions for xperm_hyp.
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      -- iterN3Max is @[irreducible] so projections stay opaque after delta
      delta loopIterPostN3Max loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_chunked hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3MaxPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)

/-- No-NOP variant of `divK_loop_n3_max_max_spec_within`. -/
theorem divK_loop_n3_max_max_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (base : Word)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 304 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN3Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old)
      (loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n3_max_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_max_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base
    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN3Max loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_chunked hp)
    J1f J0f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3MaxPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)

-- ============================================================================
-- Double-addback () two-iteration call×call composition
-- Case-splits on j=1 borrow to use raw skip/beq specs, then composes with
-- j=0  spec. Uses iterN3Call (non-irreducible) for postcondition matching.
-- ============================================================================

theorem divK_loop_n3_call_call_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 call  iteration spec
  have J1 := divK_loop_body_n3_call_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base halign
    hbltu_1
    (hcarry2 (div128Quot u3 u2 v2) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  -- Frame j=1 with u0Orig and q0Old
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- 3. j=0 call  iteration spec (inputs from j=1 via iterN3Call)
  have J0 := divK_loop_body_n3_call_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    (base + div128CallRetOff) v2 (div128DLo v2) (div128Un0 u2)
    base
    halign

    hbltu_0
    (hcarry2 (div128Quot (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
                          (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v2)
      u0Orig
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1  postcondition → j=0 precondition
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      -- iterN3Call is @[irreducible] so projections stay opaque after delta
      delta loopIterPostN3Call loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3CallCallPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)

/-- No-NOP variant of `divK_loop_n3_call_call_spec_within`. -/
theorem divK_loop_n3_call_call_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n3_call_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base halign
    hbltu_1
    (hcarry2 (div128Quot u3 u2 v2) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_call_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    (base + div128CallRetOff) v2 (div128DLo v2) (div128Un0 u2)
    base
    halign
    hbltu_0
    (hcarry2 (div128Quot (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
                          (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v2)
      u0Orig
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN3Call loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3CallCallPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)

-- ============================================================================
-- Double-addback () two-iteration max×call composition
-- j=1 max path, j=0 call path. Scratch cells are in the frame for j=1,
-- consumed/written by j=0 call.
-- ============================================================================

theorem divK_loop_n3_max_call_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    -- Branch conditions: j=1 max (BLTU not taken), j=0 call (BLTU taken)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 max  spec (no scratch cells)
  have J1 := divK_loop_body_n3_max_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  -- Frame j=1 with u0Orig, q0Old, AND scratch cells (max doesn't touch scratch)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
    (by pcFree) J1
  -- 3. j=0 call  spec (inputs from j=1 via iterN3Max, scratch from frame)
  have J0 := divK_loop_body_n3_call_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    retMem dMem dloMem scratch_un0
    base
    halign

    hbltu_0
    (hcarry2 (div128Quot (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
                          (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v2)
      u0Orig
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1 max  postcondition → j=0 precondition
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN3Max loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3MaxCallPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)

/-- No-NOP variant of `divK_loop_n3_max_call_spec_within`. -/
theorem divK_loop_n3_max_call_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n3_max_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
    (by pcFree) J1
  have J0 := divK_loop_body_n3_call_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    retMem dMem dloMem scratch_un0
    base
    halign
    hbltu_0
    (hcarry2 (div128Quot (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
                          (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v2)
      u0Orig
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN3Max loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3MaxCallPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)

-- ============================================================================
-- Double-addback () two-iteration call×max composition
-- j=1 call path, j=0 max path. Scratch cells from j=1 call are carried
-- through in the frame since j=0 max doesn't touch them.
-- ============================================================================

theorem divK_loop_n3_call_max_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    -- Branch conditions: j=1 call (BLTU taken), j=0 max (BLTU not taken)
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 call  spec (with scratch cells)
  have J1 := divK_loop_body_n3_call_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base
    halign hbltu_1
    (hcarry2 (div128Quot u3 u2 v2) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  -- Frame j=1 with u0Orig and q0Old
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- 3. j=0 max  spec (inputs from j=1 via iterN3Call)
  have J0 := divK_loop_body_n3_max_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base

    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1]) AND j=1's scratch cells
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u2) ** regOwn .x1)
    (by pcFree) J0
  -- 4. Compose: rewrite j=1 call  postcondition → j=0 precondition
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN3Call loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3CallMaxPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)

/-- No-NOP variant of `divK_loop_n3_call_max_spec_within`. -/
theorem divK_loop_n3_call_max_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n3_call_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base
    halign hbltu_1
    (hcarry2 (div128Quot u3 u2 v2) u0 u1 u2 u3 uTop : isAddbackCarry2NzN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J1
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_max_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base
    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  intro_lets at J0
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u2) ** regOwn .x1)
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN3Call loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      rw [loopBodyN3MaxUnifiedPre_unfold]
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [loopBodyN3CallUnifiedPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN3CallMaxPost
      exact hp)
    (cpsTripleWithin_mono_nSteps (by decide) full)


end EvmAsm.Evm64
