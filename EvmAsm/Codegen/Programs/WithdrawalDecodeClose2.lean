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

end EvmAsm.Codegen.WithdrawalDecodeSpec
