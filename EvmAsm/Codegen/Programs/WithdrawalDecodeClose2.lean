/-
  `withdrawalDecode_prog` caller-contract composition, part 2.

  This module hosts the middle straight-line/branch blocks of the 60-instruction
  accessor:

    * `wdCopySetup`  — instructions [34]-[38]: `la x5, wd_offset`, load the
      selected content offset, compute the source cursor `x28 = listBase +
      offset` and the destination cursor `x29 = outBase + 16`.
    * `wdLenCheck`   — instructions [29]-[33]: `la x5, wd_length`, load the
      selected length, and branch on `len ≠ 20` to the failure tail (`WB+212`)
      or fall through to the copy setup (`WB+136`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeClose
import EvmAsm.Codegen.Programs.WithdrawalDecodeLoop
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Guest data-section cells written by the field-2 `rlp_list_nth_item` call -/

/-- The `wd_offset` data cell (holds the selected content's relative offset). -/
abbrev wdOffsetAddr : Word := (GuestAddrs.wd_offset : Word)
/-- The `wd_length` data cell (holds the selected content's length). -/
abbrev wdLengthAddr : Word := (GuestAddrs.wd_length : Word)

/-! ## `la` materialize helpers -/

/-- `la x5, wd_length` at [29]-[30] (`WB+116 → WB+124`). -/
theorem wdLaLen116 (v : Word) :
    cpsTripleWithin 2 (WB + 116) (WB + 124) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ wdLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (WB + 116)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 116)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 116) withdrawalDecode_prog 29
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 116)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (WB + 120)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 116)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 120) withdrawalDecode_prog 30
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 116)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (WB + 116) wdLengthAddr (by decide) (by decide) hau had
  rw [show (WB + 116 : Word) + 8 = WB + 124 from by bv_omega] at h
  exact h

/-- `la x5, wd_offset` at [34]-[35] (`WB+136 → WB+144`). -/
theorem wdLaOff136 (v : Word) :
    cpsTripleWithin 2 (WB + 136) (WB + 144) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ wdOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (WB + 136)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 136)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 136) withdrawalDecode_prog 34
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 136)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (WB + 140)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 136)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 140) withdrawalDecode_prog 35
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 136)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (WB + 136) wdOffsetAddr (by decide) (by decide) hau had
  rw [show (WB + 136 : Word) + 8 = WB + 144 from by bv_omega] at h
  exact h

/-! ## Copy setup (instructions [34]-[38]) -/

set_option maxRecDepth 8000 in
/-- Copy setup: `la x5, wd_offset` ([34]-[35]), load the selected content offset
    from the `wd_offset` cell ([36]), compute the source cursor
    `x28 = listBase + offset` ([37]) and the destination cursor
    `x29 = outBase + 16` ([38]). -/
theorem wdCopySetup (v5old v28old v29old listBase outBase offset : Word) :
    cpsTripleWithin 5 (WB + 136) (WB + 156) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x28 : Reg) ↦ᵣ v28old) **
       ((.x29 : Reg) ↦ᵣ v29old) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x18 : Reg) ↦ᵣ outBase) ** (wdOffsetAddr ↦ₘ offset))
      (((.x5 : Reg) ↦ᵣ wdOffsetAddr) ** ((.x28 : Reg) ↦ᵣ (listBase + offset)) **
       ((.x29 : Reg) ↦ᵣ (outBase + 16)) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x18 : Reg) ↦ᵣ outBase) ** (wdOffsetAddr ↦ₘ offset)) := by
  -- [34]-[35] la x5, wd_offset
  have hla := wdLaOff136 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x18 : Reg) ↦ᵣ outBase) **
     (wdOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  -- [36] LD x28 x5 0 : x28 := *wd_offset = offset
  have hld := ld_spec_gen_within .x28 .x5 wdOffsetAddr v28old offset (0 : BitVec 12)
    (WB + 144) (by decide)
  rw [show wdOffsetAddr + signExtend12 (0 : BitVec 12) = wdOffsetAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (WB + 144 : Word) + 4 = WB + 148 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 144) withdrawalDecode_prog 36
        (.LD .x28 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR
    (((.x29 : Reg) ↦ᵣ v29old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlde
  -- [37] ADD x28 x8 x28 : x28 := listBase + offset
  have hadd := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase offset (WB + 148) (by decide)
  rw [show (WB + 148 : Word) + 4 = WB + 152 from by bv_omega] at hadd
  have hadde := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 148) withdrawalDecode_prog 37
        (.ADD .x28 .x8 .x28) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) hadd)
  have haddf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ wdOffsetAddr) ** ((.x29 : Reg) ↦ᵣ v29old) **
     ((.x18 : Reg) ↦ᵣ outBase) ** (wdOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hadde
  -- [38] ADDI x29 x18 16 : x29 := outBase + 16
  have haddi := addi_spec_gen_within .x29 .x18 v29old outBase (16 : BitVec 12) (WB + 152)
    (by decide)
  rw [show outBase + signExtend12 (16 : BitVec 12) = outBase + 16 from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide],
    show (WB + 152 : Word) + 4 = WB + 156 from by bv_omega] at haddi
  have haddie := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 152) withdrawalDecode_prog 38
        (.ADDI .x29 .x18 (16 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) haddi)
  have haddif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ wdOffsetAddr) ** ((.x28 : Reg) ↦ᵣ (listBase + offset)) **
     ((.x8 : Reg) ↦ᵣ listBase) ** (wdOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) haddie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 haddf
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 haddif
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) s3)

#print axioms wdCopySetup

/-! ## Length check (instructions [29]-[33]) -/

set_option maxRecDepth 8000 in
/-- Length check: `la x5, wd_length` ([29]-[30]), load the selected length into
    `x6` ([31]), `li x7, 20` ([32]), then `bne x6, x7` at [33] branches to the
    failure tail (`WB+212`, `len ≠ 20`) or falls through to the copy setup
    (`WB+136`, `len = 20`). -/
theorem wdLenCheck (v5old v6old v7old len : Word) :
    cpsBranchWithin 5 (WB + 116) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** (wdLengthAddr ↦ₘ len))
      (WB + 212)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (20 : Word)) ** ⌜len ≠ (20 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ wdLengthAddr) ** (wdLengthAddr ↦ₘ len))
      (WB + 136)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (20 : Word)) ** ⌜len = (20 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ wdLengthAddr) ** (wdLengthAddr ↦ₘ len)) := by
  -- [29]-[30] la x5, wd_length
  have hla := wdLaLen116 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** (wdLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  -- [31] LD x6 x5 0 : x6 := *wd_length = len
  have hld := ld_spec_gen_within .x6 .x5 wdLengthAddr v6old len (0 : BitVec 12)
    (WB + 124) (by decide)
  rw [show wdLengthAddr + signExtend12 (0 : BitVec 12) = wdLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (WB + 124 : Word) + 4 = WB + 128 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 124) withdrawalDecode_prog 31
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ v7old)) pcFree_regIs hlde
  -- [32] LI x7 20
  have hli := li_spec_gen_within .x7 v7old (20 : Word) (WB + 128) (by decide)
  rw [show (WB + 128 : Word) + 4 = WB + 132 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 128) withdrawalDecode_prog 32
        (.LI .x7 (20 : Word)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ wdLengthAddr) ** ((.x6 : Reg) ↦ᵣ len) ** (wdLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  -- straight-line [29]-[32] : WB+116 → WB+132
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hlif
  -- [33] BNE x6 x7 80 : taken (len ≠ 20) → WB+212, else → WB+136
  have hbne := bne_spec_gen_within .x6 .x7 (80 : BitVec 13) len (20 : Word) (WB + 132)
  rw [show (WB + 132 : Word) + signExtend13 (80 : BitVec 13) = WB + 212 from by
    rw [show signExtend13 (80 : BitVec 13) = (80 : Word) from by decide]; bv_omega,
    show (WB + 132 : Word) + 4 = WB + 136 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code wd_mono
    (cpsBranchWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 132) withdrawalDecode_prog 33
        (.BNE .x6 .x7 (80 : BitVec 13)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) hbne)
  have hbnef := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ wdLengthAddr) ** (wdLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hbnee
  -- compose straight ;; branch, permuting the midpoint
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) sStraight hbnef
  exact cpsBranchWithin_mono_nSteps (by omega) hcomposed

#print axioms wdLenCheck

/-! ## Per-field argument shuffles (call setups) -/

set_option maxRecDepth 8000 in
/-- Field-0 call setup [8]-[11] (`WB+32 → WB+48`): `mv a0,s0 ; mv a1,s1 ;
    li a2,0 ; mv a3,s2` — arrange `rlp_field_to_u64(listBase, len, 0, outBase)`. -/
theorem wdField0Setup (v10 v11 v12 v13 listBase len outBase : Word) :
    cpsTripleWithin 4 (WB + 32) (WB + 48) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ outBase) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
       ((.x18 : Reg) ↦ᵣ outBase)) := by
  have h8 := mv_spec_gen_within .x10 .x8 listBase v10 (WB + 32) (by decide)
  have h8e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 32) withdrawalDecode_prog 8 (.MV .x10 .x8)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h8)
  have h9 := mv_spec_gen_within .x11 .x9 len v11 (WB + 36) (by decide)
  have h9e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 36) withdrawalDecode_prog 9 (.MV .x11 .x9)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h9)
  have h10 := li_spec_gen_within .x12 v12 (0 : Word) (WB + 40) (by decide)
  have h10e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 40) withdrawalDecode_prog 10 (.LI .x12 (0 : Word))
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h10)
  have h11 := mv_spec_gen_within .x13 .x18 outBase v13 (WB + 44) (by decide)
  have h11e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 44) withdrawalDecode_prog 11 (.MV .x13 .x18)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h11)
  have f8 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h8e
  have f9 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h9e
  have f10 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h10e
  have f11 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h11e
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f8 f9
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f10
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f11
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s3

#print axioms wdField0Setup

set_option maxRecDepth 8000 in
/-- Field-1 call setup [14]-[17] (`WB+56 → WB+72`): `mv a0,s0 ; mv a1,s1 ;
    li a2,1 ; addi a3,s2,8` — `rlp_field_to_u64(listBase, len, 1, outBase+8)`. -/
theorem wdField1Setup (v10 v11 v12 v13 listBase len outBase : Word) :
    cpsTripleWithin 4 (WB + 56) (WB + 72) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (1 : Word)) ** ((.x13 : Reg) ↦ᵣ (outBase + 8)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
       ((.x18 : Reg) ↦ᵣ outBase)) := by
  have h14 := mv_spec_gen_within .x10 .x8 listBase v10 (WB + 56) (by decide)
  have h14e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 56) withdrawalDecode_prog 14 (.MV .x10 .x8)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h14)
  have h15 := mv_spec_gen_within .x11 .x9 len v11 (WB + 60) (by decide)
  have h15e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 60) withdrawalDecode_prog 15 (.MV .x11 .x9)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h15)
  have h16 := li_spec_gen_within .x12 v12 (1 : Word) (WB + 64) (by decide)
  have h16e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 64) withdrawalDecode_prog 16 (.LI .x12 (1 : Word))
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h16)
  have h17 := addi_spec_gen_within .x13 .x18 v13 outBase (8 : BitVec 12) (WB + 68) (by decide)
  rw [show outBase + signExtend12 (8 : BitVec 12) = outBase + 8 from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]] at h17
  have h17e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 68) withdrawalDecode_prog 17
        (.ADDI .x13 .x18 (8 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h17)
  have f14 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h14e
  have f15 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h15e
  have f16 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h16e
  have f17 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (1 : Word)) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h17e
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f14 f15
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f16
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f17
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s3

#print axioms wdField1Setup

set_option maxRecDepth 8000 in
/-- Field-3 call setup [45]-[48] (`WB+180 → WB+196`): `mv a0,s0 ; mv a1,s1 ;
    li a2,3 ; addi a3,s2,40` — `rlp_field_to_u64(listBase, len, 3, outBase+40)`. -/
theorem wdField3Setup (v10 v11 v12 v13 listBase len outBase : Word) :
    cpsTripleWithin 4 (WB + 180) (WB + 196) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (3 : Word)) ** ((.x13 : Reg) ↦ᵣ (outBase + 40)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
       ((.x18 : Reg) ↦ᵣ outBase)) := by
  have h45 := mv_spec_gen_within .x10 .x8 listBase v10 (WB + 180) (by decide)
  have h45e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 180) withdrawalDecode_prog 45 (.MV .x10 .x8)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h45)
  have h46 := mv_spec_gen_within .x11 .x9 len v11 (WB + 184) (by decide)
  have h46e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 184) withdrawalDecode_prog 46 (.MV .x11 .x9)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h46)
  have h47 := li_spec_gen_within .x12 v12 (3 : Word) (WB + 188) (by decide)
  have h47e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 188) withdrawalDecode_prog 47 (.LI .x12 (3 : Word))
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h47)
  have h48 := addi_spec_gen_within .x13 .x18 v13 outBase (40 : BitVec 12) (WB + 192) (by decide)
  rw [show outBase + signExtend12 (40 : BitVec 12) = outBase + 40 from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]] at h48
  have h48e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 192) withdrawalDecode_prog 48
        (.ADDI .x13 .x18 (40 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h48)
  have f45 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h45e
  have f46 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h46e
  have f47 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ outBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h47e
  have f48 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (3 : Word)) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h48e
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f45 f46
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f47
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f48
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s3

#print axioms wdField3Setup

/-- `la x13, wd_offset` at [23]-[24] (`WB+92 → WB+100`). -/
theorem wdLaOff92 (v : Word) :
    cpsTripleWithin 2 (WB + 92) (WB + 100) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ wdOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (WB + 92)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 92)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 92) withdrawalDecode_prog 23
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 92)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (WB + 96)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 92)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 96) withdrawalDecode_prog 24
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.wd_offset (GuestAddrs.withdrawal_decode + 92)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (WB + 92) wdOffsetAddr (by decide) (by decide) hau had
  rw [show (WB + 92 : Word) + 8 = WB + 100 from by bv_omega] at h
  exact h

/-- `la x14, wd_length` at [25]-[26] (`WB+100 → WB+108`). -/
theorem wdLaLen100 (v : Word) :
    cpsTripleWithin 2 (WB + 100) (WB + 108) fullCode
      (.x14 ↦ᵣ v) (.x14 ↦ᵣ wdLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (WB + 100)
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 100)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 100) withdrawalDecode_prog 25
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 100)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (WB + 104)
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 100)))
        a = some i → fullCode a = some i := fun a i hi => wd_mono a i
    (CodeReq.ofProg_mem_at WB (WB + 104) withdrawalDecode_prog 26
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.wd_length (GuestAddrs.withdrawal_decode + 100)))
      (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi)
  have h := la_materialize_within .x14 v (WB + 100) wdLengthAddr (by decide) (by decide) hau had
  rw [show (WB + 100 : Word) + 8 = WB + 108 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Field-2 call setup [20]-[26] (`WB+80 → WB+108`): `mv a0,s0 ; mv a1,s1 ;
    li a2,2 ; la a3,wd_offset ; la a4,wd_length` — arrange
    `rlp_list_nth_item(listBase, len, 2, &wd_offset, &wd_length)`. -/
theorem wdField2Setup (v10 v11 v12 v13 v14 listBase len : Word) :
    cpsTripleWithin 7 (WB + 80) (WB + 108) fullCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len))
      (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ (2 : Word)) ** ((.x13 : Reg) ↦ᵣ wdOffsetAddr) **
       ((.x14 : Reg) ↦ᵣ wdLengthAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x9 : Reg) ↦ᵣ len)) := by
  have h20 := mv_spec_gen_within .x10 .x8 listBase v10 (WB + 80) (by decide)
  have h20e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 80) withdrawalDecode_prog 20 (.MV .x10 .x8)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h20)
  have h21 := mv_spec_gen_within .x11 .x9 len v11 (WB + 84) (by decide)
  have h21e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 84) withdrawalDecode_prog 21 (.MV .x11 .x9)
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h21)
  have h22 := li_spec_gen_within .x12 v12 (2 : Word) (WB + 88) (by decide)
  have h22e := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 88) withdrawalDecode_prog 22 (.LI .x12 (2 : Word))
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide)) h22)
  have h23 := wdLaOff92 v13
  have h25 := wdLaLen100 v14
  have f20 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h20e
  have f21 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h21e
  have f22 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h22e
  have f23 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (2 : Word)) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h23
  have f25 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ (2 : Word)) **
     ((.x13 : Reg) ↦ᵣ wdOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) h25
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f20 f21
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f22
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f23
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f25
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) s4)

#print axioms wdField2Setup

/-! ## Field-0 call adapter: arg shuffle ;; jal ;; strict K34 selector -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
/-- Field-0 RLP call adapter [8]-[12] + the strict `rlp_field_to_u64` selector:
    the arg shuffle establishes K34's `flatPre` for index 0 / output `outBase`,
    the `jal` at [12] links `ra := WB+52` and enters the selector, whose
    `flatPost` (success/failure with the field-0 `Result` pinned) is returned. -/
theorem wdField0Call
    (spW newSp raIn listBase len outBase oldOut oldOffset oldLen old14
      s3 s4 s5 v10 v11 v12 v13 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := { ra := WB + 52, s0 := listBase, s1 := len }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outBase, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsTripleWithin (4 + (1 + n34)) (WB + 32) (WB + 52) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (outBase ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      (((.x1 : Reg) ↦ᵣ (WB + 52)) **
        flatPost spW newSp listBase oldOffset oldLen outer saved bytes listLen 0) := by
  intro outer saved callSteps tailSteps n34
  -- [8]-[11] arg shuffle → K34's flatPre
  have hsetup := wdField0Setup v10 v11 v12 v13 listBase len outBase
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
     stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (outBase ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | exact pcFree_regOwn | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
        | apply pcFree_sepConj) hsetup
  have hhead : cpsTripleWithin 4 (WB + 32) (WB + 48) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (outBase ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      ((.x1 ↦ᵣ raIn) **
       flatPre spW newSp listBase len (0 : Word) outBase oldOut oldOffset oldLen old14
         outer outBase s3 s4 s5 bytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold flatPre wholeRest outer; xperm_hyp hq) hsetupF
  -- [12] jal rlp_field_to_u64 + strict K34.
  have hflat := rlpFieldToU64_flat_spec_within spW newSp listBase len (0 : Word) outBase
    oldOut oldOffset oldLen old14 outer outBase s3 s4 s5 bytes listLen 0 hnewSp hlenW
    (by decide) (by decide) hsalign hslack hover hvalid
    (by show (WB + 52) &&& ~~~(1 : Word) = WB + 52; decide)
  have hflatC := cpsTripleWithin_extend_code k34_mono hflat
  have hcall := callWithin_spec (WB + 48) B raIn
    (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.withdrawal_decode + 48))
    n34 (by show (WB + 48) + signExtend21 _ = B; decide)
    (fun a i hi => wd_mono a i
      (CodeReq.ofProg_mem_at WB (WB + 48) withdrawalDecode_prog 12
        (.JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.withdrawal_decode + 48)))
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi))
    (by unfold flatPre wholeRest; pcf) hflatC
  rw [show (WB + 48 + 4 : Word) = WB + 52 from by bv_omega] at hcall
  -- Compose head ;; call.
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhead hcall

#print axioms wdField0Call

/-! ## Field-1 call adapter [14]-[18] + K34 -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
/-- Field-1 RLP call adapter [14]-[18] + `rlp_field_to_u64` (index 1, output
    `outBase+8`), `ra := WB+76`. -/
theorem wdField1Call
    (spW newSp raIn listBase len outBase oldOut oldOffset oldLen old14
      s3 s4 s5 v10 v11 v12 v13 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := { ra := WB + 76, s0 := listBase, s1 := len }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outBase + 8, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsTripleWithin (4 + (1 + n34)) (WB + 56) (WB + 76) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 8) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      (((.x1 : Reg) ↦ᵣ (WB + 76)) **
        flatPost spW newSp listBase oldOffset oldLen outer saved bytes listLen 1) := by
  intro outer saved callSteps tailSteps n34
  have hsetup := wdField1Setup v10 v11 v12 v13 listBase len outBase
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
     stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     ((outBase + 8) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | exact pcFree_regOwn | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
        | apply pcFree_sepConj) hsetup
  have hhead : cpsTripleWithin 4 (WB + 56) (WB + 72) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 8) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      ((.x1 ↦ᵣ raIn) **
       flatPre spW newSp listBase len (1 : Word) (outBase + 8) oldOut oldOffset oldLen
         old14 outer outBase s3 s4 s5 bytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold flatPre wholeRest outer; xperm_hyp hq) hsetupF
  have hflat := rlpFieldToU64_flat_spec_within spW newSp listBase len (1 : Word) (outBase + 8)
    oldOut oldOffset oldLen old14 outer outBase s3 s4 s5 bytes listLen 1 hnewSp hlenW
    (by decide) (by decide) hsalign hslack hover hvalid
    (by show (WB + 76) &&& ~~~(1 : Word) = WB + 76; decide)
  have hflatC := cpsTripleWithin_extend_code k34_mono hflat
  have hcall := callWithin_spec (WB + 72) B raIn
    (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.withdrawal_decode + 72))
    n34 (by show (WB + 72) + signExtend21 _ = B; decide)
    (fun a i hi => wd_mono a i
      (CodeReq.ofProg_mem_at WB (WB + 72) withdrawalDecode_prog 18
        (.JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.withdrawal_decode + 72)))
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi))
    (by unfold flatPre wholeRest; pcf) hflatC
  rw [show (WB + 72 + 4 : Word) = WB + 76 from by bv_omega] at hcall
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhead hcall

#print axioms wdField1Call

/-! ## Field-3 call adapter [45]-[49] + K34 -/

open EvmAsm.Codegen.RlpFieldToU64SAsm in
set_option maxRecDepth 8000 in
/-- Field-3 RLP call adapter [45]-[49] + `rlp_field_to_u64` (index 3, output
    `outBase+40`), `ra := WB+200`. -/
theorem wdField3Call
    (spW newSp raIn listBase len outBase oldOut oldOffset oldLen old14
      s3 s4 s5 v10 v11 v12 v13 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12))
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let outer : Saved := { ra := WB + 200, s0 := listBase, s1 := len }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outBase + 40, s2 := outBase, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsTripleWithin (4 + (1 + n34)) (WB + 180) (WB + 200) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 40) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      (((.x1 : Reg) ↦ᵣ (WB + 200)) **
        flatPost spW newSp listBase oldOffset oldLen outer saved bytes listLen 3) := by
  intro outer saved callSteps tailSteps n34
  have hsetup := wdField3Setup v10 v11 v12 v13 listBase len outBase
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
     stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     ((outBase + 40) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
    (by repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | exact pcFree_regOwn | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
        | apply pcFree_sepConj) hsetup
  have hhead : cpsTripleWithin 4 (WB + 180) (WB + 196) fullCode
      (((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ old14) ** frameSlotsOwn frame newSp **
        stackFree newSp 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        ((outBase + 40) ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen))
      ((.x1 ↦ᵣ raIn) **
       flatPre spW newSp listBase len (3 : Word) (outBase + 40) oldOut oldOffset oldLen
         old14 outer outBase s3 s4 s5 bytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold flatPre wholeRest outer; xperm_hyp hq) hsetupF
  have hflat := rlpFieldToU64_flat_spec_within spW newSp listBase len (3 : Word) (outBase + 40)
    oldOut oldOffset oldLen old14 outer outBase s3 s4 s5 bytes listLen 3 hnewSp hlenW
    (by decide) (by decide) hsalign hslack hover hvalid
    (by show (WB + 200) &&& ~~~(1 : Word) = WB + 200; decide)
  have hflatC := cpsTripleWithin_extend_code k34_mono hflat
  have hcall := callWithin_spec (WB + 196) B raIn
    (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.withdrawal_decode + 196))
    n34 (by show (WB + 196) + signExtend21 _ = B; decide)
    (fun a i hi => wd_mono a i
      (CodeReq.ofProg_mem_at WB (WB + 196) withdrawalDecode_prog 49
        (.JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.withdrawal_decode + 196)))
        (by bv_omega) (by rw [wd_length]; decide) rfl (by rw [wd_length]; decide) a i hi))
    (by unfold flatPre wholeRest; pcf) hflatC
  rw [show (WB + 196 + 4 : Word) = WB + 200 from by bv_omega] at hcall
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhead hcall

#print axioms wdField3Call

end EvmAsm.Codegen.WithdrawalDecodeSpec
