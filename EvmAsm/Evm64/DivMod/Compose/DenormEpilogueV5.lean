/-
  EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5

  v5 mirror of the DIV denorm preamble+body+div-epilogue tail (denormOff → nopOff).
  The denorm block (block 9) and DIV epilogue block (block 10) are byte-identical
  across the div128 v4/v5 migration, so these are exact copies of the v4 mirrors
  with the code subsumptions re-pointed at `sharedNoNop_v5_b9_div` /
  `divNoNop_v5_b10_divEpilogue` (over `divCode_noNop_v5`).  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPath
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv64_4mul_3)

theorem divK_denorm_preamble_spec_within_v5_noNop
    (sp shift v5 v6 v7 v2 v10 : Word) (base : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 2 (base + denormOff) (base + denormOff + 8) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  -- 1. LD x6 x12 3992 at base+908 (denorm instr [0])
  have hld := ld_spec_gen_within .x6 .x12 sp v6 shift (3992 : BitVec 12) (base + denormOff) (by nofun)
  have hlde := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff) divK_denorm
        [.LD .x6 .x12 3992] 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hld
  -- 2. BEQ x6 x0 96 at base+912 (denorm instr [1])
  have hbeq := beq_spec_gen_within .x6 .x0 (96 : BitVec 13) shift (0 : Word) (base + denormOff + 4)
  rw [show (base + denormOff + 4 : Word) + signExtend13 (96 : BitVec 13) = base + epilogueOff from by rv64_addr,
      show (base + denormOff + 4 : Word) + 4 = base + denormOff + 8 from by bv_addr] at hbeq
  have hbeqe := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 4) divK_denorm
        [.BEQ .x6 .x0 96] 1 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hbeq
  have hbeq_exit := cpsBranchWithin_ntakenPath hbeqe
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
      exact hshift_nz hpure)
  have hbeq_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbeq_exit
  have hldf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10))
    (by pcFree) hlde
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq_clean
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hldf hbeqf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

theorem divK_denorm_body_spec_within_v5_noNop
    (sp u0 u1 u2 u3 v2 v5 v7 shift : Word) (base : Word) :
    cpsTripleWithin 23 (base + denormOff + 8) (base + epilogueOff) (divCode_noNop_v5 base)
      (divKDenormBodyPre sp u0 u1 u2 u3 v2 v5 v7 shift)
      (divKDenormBodyPost sp u0 u1 u2 u3 shift) := by
  rw [divKDenormBodyPre_unfold, divKDenormBodyPost_unfold]
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  have haddi := addi_x0_spec_gen_within .x2 v2 0 (base + denormOff + 8) (by nofun)
  rw [show (base + denormOff + 8 : Word) + 4 = base + denormOff + 12 from by bv_addr] at haddi
  have haddie := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 8) divK_denorm
        [.ADDI .x2 .x0 0] 2
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) haddi
  have haddief := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ shift) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) haddie
  have hsub := sub_spec_gen_rd_eq_rs1_within .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + denormOff + 12) (by nofun)
  rw [show (base + denormOff + 12 : Word) + 4 = base + denormOff + 16 from by bv_addr] at hsub
  have hsube := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v5_b9_div a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + denormOff) divK_denorm 3
          (by decide) (by decide)
        rw [bv64_4mul_3] at hlookup
        exact hlookup) a i h)) hsub
  have hsubf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hsube
  have h_anti := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddief hsubf
  have hm0 := divK_denorm_merge_spec_within 4056 4048 sp u0 u1 v5 v7 shift antiShift (base + denormOff + 16)
  rw [show (base + denormOff + 16 : Word) + 24 = base + denormOff + 40 from by bv_addr] at hm0
  have hm0e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 16) divK_denorm
        (divK_denorm_merge_prog 4056 4048) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm0
  have hm0ef := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm0e
  have h_m0 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_anti hm0ef
  have hm1 := divK_denorm_merge_spec_within 4048 4040 sp u1 u2
    u0' (u1 <<< (antiShift.toNat % 64)) shift antiShift (base + denormOff + 40)
  rw [show (base + denormOff + 40 : Word) + 24 = base + denormOff + 64 from by bv_addr] at hm1
  have hm1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 40) divK_denorm
        (divK_denorm_merge_prog 4048 4040) 10
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm1
  have hm1ef := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm1e
  have h_m1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m0 hm1ef
  have hm2 := divK_denorm_merge_spec_within 4040 4032 sp u2 u3
    u1' (u2 <<< (antiShift.toNat % 64)) shift antiShift (base + denormOff + 64)
  rw [show (base + denormOff + 64 : Word) + 24 = base + denormOff + 88 from by bv_addr] at hm2
  have hm2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 64) divK_denorm
        (divK_denorm_merge_prog 4040 4032) 16
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm2
  have hm2ef := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1'))
    (by pcFree) hm2e
  have h_m2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m1 hm2ef
  have hl := divK_denorm_last_spec_within 4032 sp u3 u2' shift (base + denormOff + 88)
  rw [show (base + denormOff + 88 : Word) + 12 = base + epilogueOff from by bv_addr] at hl
  have hle := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 88) divK_denorm
        (divK_denorm_last_prog 4032) 22
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hl
  have hlef := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (u3 <<< (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
     ((sp + signExtend12 4040) ↦ₘ u2'))
    (by pcFree) hle
  have h_all := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m2 hlef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_all

-- ============================================================================
-- Section 10m: DIV Epilogue composition (10 instructions at base+1008)
-- Load q[0..3], ADDI sp+32, store to output, JAL to NOP
-- ============================================================================


theorem divK_div_epilogue_spec_within_v5_noNop (sp : Word) (base : Word)
    (q0 q1 q2 q3 v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin 10 (base + epilogueOff) (base + nopOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) ** (.x10 ↦ᵣ q3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
       ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) := by
  have hload := divK_epilogue_load_spec_within 4088 4080 4072 4064 sp q0 q1 q2 q3 v5 v6 v7 v10
    (base + epilogueOff)
  have hloade := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divNoNop_v5_b10_divEpilogue a i
      (CodeReq.ofProg_mono_sub (base + epilogueOff) (base + epilogueOff) (divK_div_epilogue 24)
        (divK_epilogue_load_prog 4088 4080 4072 4064) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hload
  have hstore := divK_epilogue_store_spec_within sp (base + epilogueOff + 16) q0 q1 q2 q3 m0 m8 m16 m24 24
  rw [show (base + epilogueOff + 16 : Word) + 20 + signExtend21 24 = base + nopOff from by rv64_addr]
    at hstore
  have hstoree := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divNoNop_v5_b10_divEpilogue a i
      (CodeReq.ofProg_mono_sub (base + epilogueOff) (base + epilogueOff + 16) (divK_div_epilogue 24)
        (divK_epilogue_store_prog 24) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hstore
  have hloadef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) ** ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hloade
  have hstoref := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3))
    (by pcFree) hstoree
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hloadef hstoref
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

theorem evm_div_denorm_epilogue_spec_v5_noNop (sp base : Word)
    (u0 u1 u2 u3 v2 v5 v7 v10 shift : Word)
    (q0 q1 q2 q3 m0 m8 m16 m24 : Word) :
    cpsTripleWithin (23 + 10) (base + denormOff + 8) (base + nopOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3) := by
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  have hDenorm := divK_denorm_body_spec_within_v5_noNop sp u0 u1 u2 u3 v2 v5 v7 shift base
  rw [divKDenormBodyPre_unfold, divKDenormBodyPost_unfold] at hDenorm
  have hDenormF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hDenorm
  have hEpi := divK_div_epilogue_spec_within_v5_noNop sp base q0 q1 q2 q3
    u3' shift (u3 <<< (antiShift.toNat % 64)) v10 m0 m8 m16 m24
  have hEpiF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
     ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3'))
    (by pcFree) hEpi
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hDenormF hEpiF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta denormDivPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- Post-loop chain with preamble: Preamble → Denorm → DIV Epilogue (base+908 → base+1068)
-- Loads shift from memory, denormalizes u[], then loads q[] to output.
-- ============================================================================


theorem evm_div_preamble_denorm_epilogue_spec_v5_noNop (sp base : Word)
    (u0 u1 u2 u3 shift v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 m0 m8 m16 m24 : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3 **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hPre := divK_denorm_preamble_spec_within_v5_noNop sp shift v5 v6 v7 v2 v10 base hshift_nz
  have hPreF := cpsTripleWithin_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  have hDE := evm_div_denorm_epilogue_spec_v5_noNop sp base u0 u1 u2 u3 v2 v5 v7 v10 shift
    q0 q1 q2 q3 m0 m8 m16 m24
  have hDEF := cpsTripleWithin_frameR
    (((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hDE
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hDEF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

/-- v5 shift=0 post-loop tail (denormOff → nopOff): LD shift + BEQ taken → DIV epilogue. -/
theorem evm_div_shift0_epilogue_spec_v5_noNop (sp base : Word)
    (_u0 _u1 _u2 _u3 shift v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 m0 m8 m16 m24 : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 12 (base + denormOff) (base + nopOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
       ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) := by
  -- 1. LD x6 x12 3992 at base+908 (denorm instr [0])
  have hld := ld_spec_gen_within .x6 .x12 sp v6 shift (3992 : BitVec 12) (base + denormOff) (by nofun)
  have hlde := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff) divK_denorm
        [.LD .x6 .x12 3992] 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hld
  -- 2. BEQ x6 x0 96 at base+912 (denorm instr [1])
  have hbeq := beq_spec_gen_within .x6 .x0 (96 : BitVec 13) shift (0 : Word) (base + denormOff + 4)
  rw [show (base + denormOff + 4 : Word) + signExtend13 (96 : BitVec 13) = base + epilogueOff from by rv64_addr,
      show (base + denormOff + 4 : Word) + 4 = base + denormOff + 8 from by bv_addr] at hbeq
  have hbeqe := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v5_b9_div a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 4) divK_denorm
        [.BEQ .x6 .x0 96] 1 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hbeq
  -- 3. Eliminate not-taken branch: shift = 0 means BEQ taken
  --    BEQ not-taken postcondition: (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ 0) ** ⌜shift ≠ 0⌝
  have hbeq_exit := cpsBranchWithin_takenStripPure2 hbeqe
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  -- 4. Frame LD with x0, x5, x7, x2, x10
  have hldf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10))
    (by pcFree) hlde
  -- 5. Frame BEQ taken with x12, x5, x7, x2, x10, shiftMem
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq_exit
  -- 6. Compose LD → BEQ taken: base+908 → base+1008
  have hPre := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hldf hbeqf
  -- Frame preamble with q[], output memory
  have hPreF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  -- 7. DIV epilogue (base+1008 → base+1068)
  have hEpi := divK_div_epilogue_spec_within_v5_noNop sp base q0 q1 q2 q3
    v5 shift v7 v10 m0 m8 m16 m24

  -- Frame epilogue with x2, x0, shiftMem
  have hEpiF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hEpi
  -- 8. Compose preamble → epilogue: base+908 → base+1068
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hEpiF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
