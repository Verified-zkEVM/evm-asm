/-
  EvmAsm.Codegen.Proofs.ExtractDepositDataFailSpec

  First tranche of #12989: the length-guard fail arm of
  `extract_deposit_data` at its linked guest address, as a flat
  whole-path `cpsTripleWithin`.  A malformed DepositEvent payload whose
  length is not the canonical 576 takes the guard at instruction index 7
  straight to the shared fail tail: `a0 = 1`, callee-saved registers and
  `sp` restored, no memory outside the three frame slots touched.

  The ok path (ten `edd_be32_eq` checks and five `edd_memcpy` field
  extractions, composing the verified leaves over the shared bundle
  image `extractDepositDataBundle_prog`) is the next tranche; this arm
  is call-free, so its `CodeReq` is the main body's own program.
-/

import EvmAsm.Codegen.Programs.ExtractDepositData
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.ExtractDepositDataFailSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The main body's own image at the guest entry. -/
abbrev eddCode : CodeReq :=
  CodeReq.ofProg (GuestAddrs.extract_deposit_data : Word)
    extractDepositData_prog

abbrev EddB : Word := (GuestAddrs.extract_deposit_data : Word)

private theorem eddProg_len :
    (extractDepositData_prog : List Instr).length = 76 := by decide

private theorem edd_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = EddB + BitVec.ofNat 64 (4 * k))
    (hk : k < 76)
    (hins : (extractDepositData_prog : List Instr)[k]'(by
      rw [eddProg_len]; omega) = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → eddCode a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at EddB A extractDepositData_prog k ins hA
      (by rw [eddProg_len]; omega) hins
      (by rw [eddProg_len]; norm_num) a i h

set_option maxRecDepth 8000 in
/-- **The length-guard fail arm of `extract_deposit_data`** (#12989,
    tranche 1): entered with a payload length other than the canonical
    576 in `a1`, three owned dword frame slots below `sp`, and an
    aligned return address, it returns `a0 = 1` with `sp`, `ra`, `s0`,
    `s1` restored to their entry values and nothing else written. -/
theorem extractDepositData_lenFail_spec
    (sp0 ret a0v lenW outv : Word)
    (v5 v8 v9 : Word) (m0 m1 m2 : Word)
    (hne : lenW ≠ (576 : Word))
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 14 EddB (ret &&& ~~~1) eddCode
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ a0v) ** ((.x11 : Reg) ↦ᵣ lenW) **
        ((.x12 : Reg) ↦ᵣ outv) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2))
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ lenW) **
        ((.x12 : Reg) ↦ᵣ outv) ** ((.x5 : Reg) ↦ᵣ (576 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ ret) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ v8) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ v9)) := by
  set nsp := sp0 + signExtend12 (-32 : BitVec 12) with hnsp
  -- ---- idx 0-6: frame prologue, argument stashes, guard constant ----
  have haddisp := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12)
    EddB (by decide)
  rw [← hnsp] at haddisp
  have hsd1 := sd_spec_gen_within .x2 .x1 nsp ret m0 (0 : BitVec 12) (EddB + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show nsp + (0 : Word) = nsp from by bv_omega] at hsd1
  have hsd2 := sd_spec_gen_within .x2 .x8 nsp v8 m1 (8 : BitVec 12) (EddB + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hsd2
  have hsd3 := sd_spec_gen_within .x2 .x9 nsp v9 m2 (16 : BitVec 12) (EddB + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hsd3
  have hmv8 := mv_spec_gen_within .x8 .x10 a0v v8 (EddB + 16) (by decide)
  have hmv9 := mv_spec_gen_within .x9 .x12 outv v9 (EddB + 20) (by decide)
  have hli5 := li_spec_gen_within .x5 v5 (576 : Word) (EddB + 24) (by decide)
  have hProl : cpsTripleWithin 7 EddB (EddB + 28) eddCode
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ a0v) ** ((.x12 : Reg) ↦ᵣ outv) **
        ((.x5 : Reg) ↦ᵣ v5) **
        (nsp ↦ₘ m0) ** ((nsp + 8) ↦ₘ m1) ** ((nsp + 16) ↦ₘ m2))
      (((.x2 : Reg) ↦ᵣ nsp) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ a0v) ** ((.x9 : Reg) ↦ᵣ outv) **
        ((.x10 : Reg) ↦ᵣ a0v) ** ((.x12 : Reg) ↦ᵣ outv) **
        ((.x5 : Reg) ↦ᵣ (576 : Word)) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9)) := by
    runBlock haddisp hsd1 hsd2 hsd3 hmv8 hmv9 hli5
  -- ---- idx 7: bne a1, t0 TAKEN (lenW ≠ 576) → EddB + 280 ----
  have hbne := bne_spec_gen_within .x11 .x5 (252 : BitVec 13) lenW
    (576 : Word) (EddB + 28)
  rw [show (EddB + 28 : Word) + signExtend13 (252 : BitVec 13)
        = EddB + 280 from by
        rw [show signExtend13 (252 : BitVec 13) = (252 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hbne
  have hBne := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code
      (edd_mem 7 _ (EddB + 28)
        (by rw [show (4 * 7 : Nat) = 28 from rfl]; rfl) (by omega) rfl)
      hbne)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hne)
  -- ---- idx 70: li a0, 1 ----
  have hli1 := li_spec_gen_within .x10 a0v (1 : Word) (EddB + 280) (by decide)
  have hLi1 := cpsTripleWithin_extend_code
    (edd_mem 70 _ (EddB + 280)
      (by rw [show (4 * 70 : Nat) = 280 from rfl]; rfl) (by omega) rfl) hli1
  rw [show (EddB + 280 : Word) + 4 = EddB + 284 from by
        rw [BitVec.add_assoc]; rfl] at hLi1
  -- ---- idx 71-75: epilogue ----
  have hld1 := ld_spec_gen_within .x1 .x2 nsp ret ret (0 : BitVec 12)
    (EddB + 284) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show nsp + (0 : Word) = nsp from by bv_omega] at hld1
  have hld8 := ld_spec_gen_within .x8 .x2 nsp a0v v8 (8 : BitVec 12)
    (EddB + 288) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hld8
  have hld9 := ld_spec_gen_within .x9 .x2 nsp outv v9 (16 : BitVec 12)
    (EddB + 292) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hld9
  have haddisp2 := addi_spec_gen_same_within .x2 nsp (32 : BitVec 12)
    (EddB + 296) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
      show nsp + (32 : Word) = sp0 from by
        rw [hnsp, show signExtend12 (-32 : BitVec 12)
          = (0xFFFFFFFFFFFFFFE0 : Word) from by decide]
        bv_omega] at haddisp2
  have hret := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (EddB + 300)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (ret + 0 : Word) = ret from by bv_omega] at hret
  have hEpi : cpsTripleWithin 5 (EddB + 284) (ret &&& ~~~1) eddCode
      (((.x2 : Reg) ↦ᵣ nsp) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ a0v) ** ((.x9 : Reg) ↦ᵣ outv) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9))
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9)) := by
    runBlock hld1 hld8 hld9 haddisp2 hret
  -- ---- frame and compose ----
  have hProlF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ lenW) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFree) hProl
  have hBneF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x8 : Reg) ↦ᵣ a0v) ** ((.x9 : Reg) ↦ᵣ outv) **
      ((.x10 : Reg) ↦ᵣ a0v) ** ((.x12 : Reg) ↦ᵣ outv) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9))
    (by pcFree) hBne
  have hLi1F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x8 : Reg) ↦ᵣ a0v) ** ((.x9 : Reg) ↦ᵣ outv) **
      ((.x11 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ outv) **
      ((.x5 : Reg) ↦ᵣ (576 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9))
    (by pcFree) hLi1
  have hEpiF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ lenW) **
      ((.x12 : Reg) ↦ᵣ outv) ** ((.x5 : Reg) ↦ᵣ (576 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFree) hEpi
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hProlF hBneF
    intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hLi1F
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hEpiF
    intro h hp; xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s3

end EvmAsm.Codegen.ExtractDepositDataFailSpec
