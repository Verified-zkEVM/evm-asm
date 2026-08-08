/-
  The balance right-align setup block of `accountDecode_prog`
  (`Programs/State.lean`), instructions after the field-1 value check accepts
  `sigLen ≤ 32` (`AB+284 → AB+308`):

    sd x0, 0/8/16/24(x19)   -- zero the 32-byte balance slot
    sub  x7, x7, x6         -- x7 := 32 - sigLen
    add  x29, x19, x7       -- dst cursor = balanceOut + (32 - sigLen)

  The significant-byte source cursor is already in `x28` from the value-check
  strip; there is no second offset load.  The four `sd x0` stores collapse the
  four dwords of the output slot to the zeroed 32-byte `bytesRegion`
  (`bytesRegion_replicate32_zero`), and the destination cursor feeds
  `adBalLoop` with `dstOff = 32 - sigLen`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeCall
import EvmAsm.Rv64.RLP.ContentToU256Be

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP (bytesRegion_replicate32_zero)

set_option maxRecDepth 8000 in
/-- The balance right-align setup (`AB+284 → AB+308`): zero the 32-byte output
    slot, compute `x7 = 32 - sigLen`, and the destination cursor
    `x29 = balanceOut + (32 - sigLen)`.  Source cursor `x28` is preserved. -/
theorem adBalanceSetup (balanceOut sigLen v29 ob0 ob1 ob2 ob3 : Word) :
    cpsTripleWithin 6 (AB + 284) (AB + 308) fullCode
      (((.x19 : Reg) ↦ᵣ balanceOut) **
       ((.x6 : Reg) ↦ᵣ sigLen) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
       ((.x29 : Reg) ↦ᵣ v29) **
       (balanceOut ↦ₘ ob0) ** ((balanceOut + 8) ↦ₘ ob1) **
       ((balanceOut + 16) ↦ₘ ob2) ** ((balanceOut + 24) ↦ₘ ob3))
      (((.x19 : Reg) ↦ᵣ balanceOut) **
       ((.x6 : Reg) ↦ᵣ sigLen) ** ((.x7 : Reg) ↦ᵣ ((32 : Word) - sigLen)) **
       ((.x29 : Reg) ↦ᵣ (balanceOut + ((32 : Word) - sigLen))) **
       bytesRegion balanceOut (List.replicate 32 (0 : BitVec 8))) := by
  have hz0 : balanceOut + signExtend12 (0 : BitVec 12) = balanceOut := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have hz8 : balanceOut + signExtend12 (8 : BitVec 12) = balanceOut + 8 := by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
  have hz16 : balanceOut + signExtend12 (16 : BitVec 12) = balanceOut + 16 := by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
  have hz24 : balanceOut + signExtend12 (24 : BitVec 12) = balanceOut + 24 := by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]
  have h55 := sd_x0_spec_gen_within .x19 balanceOut ob0 (0 : BitVec 12) (AB + 284)
  rw [hz0, show (AB + 284 : Word) + 4 = AB + 288 from by bv_omega] at h55
  have h55e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 284) accountDecode_prog 71 (.SD .x19 .x0 (0 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h55)
  have h56 := sd_x0_spec_gen_within .x19 balanceOut ob1 (8 : BitVec 12) (AB + 288)
  rw [hz8, show (AB + 288 : Word) + 4 = AB + 292 from by bv_omega] at h56
  have h56e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 288) accountDecode_prog 72 (.SD .x19 .x0 (8 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h56)
  have h57 := sd_x0_spec_gen_within .x19 balanceOut ob2 (16 : BitVec 12) (AB + 292)
  rw [hz16, show (AB + 292 : Word) + 4 = AB + 296 from by bv_omega] at h57
  have h57e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 292) accountDecode_prog 73 (.SD .x19 .x0 (16 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h57)
  have h58 := sd_x0_spec_gen_within .x19 balanceOut ob3 (24 : BitVec 12) (AB + 296)
  rw [hz24, show (AB + 296 : Word) + 4 = AB + 300 from by bv_omega] at h58
  have h58e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 296) accountDecode_prog 74 (.SD .x19 .x0 (24 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h58)
  have h59 := sub_spec_gen_rd_eq_rs1_within .x7 .x6 (32 : Word) sigLen (AB + 300) (by decide)
  rw [show (AB + 300 : Word) + 4 = AB + 304 from by bv_omega] at h59
  have h59e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 300) accountDecode_prog 75 (.SUB .x7 .x7 .x6)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h59)
  have h60 := add_spec_gen_within .x29 .x19 .x7 balanceOut ((32 : Word) - sigLen) v29 (AB + 304)
    (by decide)
  rw [show (AB + 304 : Word) + 4 = AB + 308 from by bv_omega] at h60
  have h60e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 304) accountDecode_prog 76 (.ADD .x29 .x19 .x7)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h60)
  have f55 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ sigLen) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((balanceOut + 8) ↦ₘ ob1) ** ((balanceOut + 16) ↦ₘ ob2) ** ((balanceOut + 24) ↦ₘ ob3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h55e
  have f56 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ sigLen) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 16) ↦ₘ ob2) ** ((balanceOut + 24) ↦ₘ ob3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h56e
  have f57 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ sigLen) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 24) ↦ₘ ob3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h57e
  have f58 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ sigLen) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h58e
  have f59 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** ((balanceOut + 24) ↦ₘ (0 : Word)))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h59e
  have f60 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ sigLen) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** ((balanceOut + 24) ↦ₘ (0 : Word)))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h60e
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f55 f56
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f57
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f58
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f59
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 f60
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by rw [bytesRegion_replicate32_zero]; xperm_hyp hq) c5

#print axioms adBalanceSetup

end EvmAsm.Codegen.AccountDecodeSpec
