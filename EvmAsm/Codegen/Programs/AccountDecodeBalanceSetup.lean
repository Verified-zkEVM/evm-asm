/-
  The balance right-align setup block of `accountDecode_prog`
  (`Programs/State.lean`, PR-K27), instructions [55]-[64] (`AB+220 → AB+260`),
  run after field 1's length check accepts `len ≤ 32`:

    [55]-[58]  sd x0, 0/8/16/24(x19)   -- zero the 32-byte balance slot
    [59]       sub  x7, x7, x6         -- x7 := 32 - len
    [60]       add  x29, x19, x7       -- dst cursor = balanceOut + (32 - len)
    [61]-[62]  la   x5, ad_offset
    [63]       ld   x28, 0(x5)         -- offset
    [64]       add  x28, x8, x28       -- src cursor = listBase + offset

  The four `sd x0` stores collapse the four dwords of the output slot to the
  zeroed 32-byte `bytesRegion` (`bytesRegion_replicate32_zero`), and the two
  cursors feed `adBalLoop` with `dstOff = 32 - len`, `srcOff = offset`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeCall
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.RLP.ContentToU256Be

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP (bytesRegion_replicate32_zero)

/-- `la x5, ad_offset` at balance setup [61]-[62] (`AB+244 → AB+252`). -/
private theorem adLaOffX5_244 (v : Word) :
    cpsTripleWithin 2 (AB + 244) (AB + 252) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 244)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 244)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 244) accountDecode_prog 61
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 244)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 248)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 244)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 248) accountDecode_prog 62
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 244)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 244) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 244 : Word) + 8 = AB + 252 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- The balance right-align setup [55]-[64] (`AB+220 → AB+260`): zero the 32-byte
    output slot, compute `x7 = 32 - len`, the destination cursor
    `x29 = balanceOut + (32 - len)`, load the content `offset`, and the source
    cursor `x28 = listBase + offset`.  Feeds `adBalLoop`. -/
theorem adBalanceSetup (balanceOut listBase len offset v5 v28 v29 ob0 ob1 ob2 ob3 : Word) :
    cpsTripleWithin 10 (AB + 220) (AB + 260) fullCode
      (((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       (balanceOut ↦ₘ ob0) ** ((balanceOut + 8) ↦ₘ ob1) **
       ((balanceOut + 16) ↦ₘ ob2) ** ((balanceOut + 24) ↦ₘ ob3) **
       (adOffsetAddr ↦ₘ offset))
      (((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ ((32 : Word) - len)) **
       ((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x28 : Reg) ↦ᵣ (listBase + offset)) **
       ((.x29 : Reg) ↦ᵣ (balanceOut + ((32 : Word) - len))) **
       bytesRegion balanceOut (List.replicate 32 (0 : BitVec 8)) **
       (adOffsetAddr ↦ₘ offset)) := by
  have hz0 : balanceOut + signExtend12 (0 : BitVec 12) = balanceOut := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have hz8 : balanceOut + signExtend12 (8 : BitVec 12) = balanceOut + 8 := by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
  have hz16 : balanceOut + signExtend12 (16 : BitVec 12) = balanceOut + 16 := by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
  have hz24 : balanceOut + signExtend12 (24 : BitVec 12) = balanceOut + 24 := by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]
  -- [55] sd x0, 0(x19)
  have h55 := sd_x0_spec_gen_within .x19 balanceOut ob0 (0 : BitVec 12) (AB + 220)
  rw [hz0, show (AB + 220 : Word) + 4 = AB + 224 from by bv_omega] at h55
  have h55e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 220) accountDecode_prog 55 (.SD .x19 .x0 (0 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h55)
  -- [56] sd x0, 8(x19)
  have h56 := sd_x0_spec_gen_within .x19 balanceOut ob1 (8 : BitVec 12) (AB + 224)
  rw [hz8, show (AB + 224 : Word) + 4 = AB + 228 from by bv_omega] at h56
  have h56e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 224) accountDecode_prog 56 (.SD .x19 .x0 (8 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h56)
  -- [57] sd x0, 16(x19)
  have h57 := sd_x0_spec_gen_within .x19 balanceOut ob2 (16 : BitVec 12) (AB + 228)
  rw [hz16, show (AB + 228 : Word) + 4 = AB + 232 from by bv_omega] at h57
  have h57e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 228) accountDecode_prog 57 (.SD .x19 .x0 (16 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h57)
  -- [58] sd x0, 24(x19)
  have h58 := sd_x0_spec_gen_within .x19 balanceOut ob3 (24 : BitVec 12) (AB + 232)
  rw [hz24, show (AB + 232 : Word) + 4 = AB + 236 from by bv_omega] at h58
  have h58e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 232) accountDecode_prog 58 (.SD .x19 .x0 (24 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h58)
  -- [59] sub x7, x7, x6
  have h59 := sub_spec_gen_rd_eq_rs1_within .x7 .x6 (32 : Word) len (AB + 236) (by decide)
  rw [show (AB + 236 : Word) + 4 = AB + 240 from by bv_omega] at h59
  have h59e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 236) accountDecode_prog 59 (.SUB .x7 .x7 .x6)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h59)
  -- [60] add x29, x19, x7
  have h60 := add_spec_gen_within .x29 .x19 .x7 balanceOut ((32 : Word) - len) v29 (AB + 240)
    (by decide)
  rw [show (AB + 240 : Word) + 4 = AB + 244 from by bv_omega] at h60
  have h60e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 240) accountDecode_prog 60 (.ADD .x29 .x19 .x7)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h60)
  -- [61]-[62] la x5, ad_offset
  have h61 := adLaOffX5_244 v5
  -- [63] ld x28, 0(x5)
  have h63 := ld_spec_gen_within .x28 .x5 adOffsetAddr v28 offset (0 : BitVec 12)
    (AB + 252) (by decide)
  rw [show adOffsetAddr + signExtend12 (0 : BitVec 12) = adOffsetAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 252 : Word) + 4 = AB + 256 from by bv_omega] at h63
  have h63e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 252) accountDecode_prog 63 (.LD .x28 .x5 (0 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h63)
  -- [64] add x28, x8, x28
  have h64 := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase offset (AB + 256) (by decide)
  rw [show (AB + 256 : Word) + 4 = AB + 260 from by bv_omega] at h64
  have h64e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 256) accountDecode_prog 64 (.ADD .x28 .x8 .x28)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h64)
  -- Frame each store/op with the untouched carriers and compose.
  have f55 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ listBase) ** ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((balanceOut + 8) ↦ₘ ob1) ** ((balanceOut + 16) ↦ₘ ob2) **
     ((balanceOut + 24) ↦ₘ ob3) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h55e
  have f56 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ listBase) ** ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 16) ↦ₘ ob2) **
     ((balanceOut + 24) ↦ₘ ob3) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h56e
  have f57 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ listBase) ** ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 24) ↦ₘ ob3) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h57e
  have f58 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ listBase) ** ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h58e
  have f59 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x5 : Reg) ↦ᵣ v5) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** ((balanceOut + 24) ↦ₘ (0 : Word)) **
     (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h59e
  have f60 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ listBase) ** ((.x6 : Reg) ↦ᵣ len) ** ((.x5 : Reg) ↦ᵣ v5) **
     ((.x28 : Reg) ↦ᵣ v28) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** ((balanceOut + 24) ↦ₘ (0 : Word)) **
     (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h60e
  have f61 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x6 : Reg) ↦ᵣ len) **
     ((.x7 : Reg) ↦ᵣ ((32 : Word) - len)) ** ((.x28 : Reg) ↦ᵣ v28) **
     ((.x29 : Reg) ↦ᵣ (balanceOut + ((32 : Word) - len))) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** ((balanceOut + 24) ↦ₘ (0 : Word)) **
     (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h61
  have f63 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x6 : Reg) ↦ᵣ len) **
     ((.x7 : Reg) ↦ᵣ ((32 : Word) - len)) **
     ((.x29 : Reg) ↦ᵣ (balanceOut + ((32 : Word) - len))) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** ((balanceOut + 24) ↦ₘ (0 : Word)))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h63e
  have f64 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x6 : Reg) ↦ᵣ len) **
     ((.x7 : Reg) ↦ᵣ ((32 : Word) - len)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
     ((.x29 : Reg) ↦ᵣ (balanceOut + ((32 : Word) - len))) **
     (balanceOut ↦ₘ (0 : Word)) ** ((balanceOut + 8) ↦ₘ (0 : Word)) **
     ((balanceOut + 16) ↦ₘ (0 : Word)) ** ((balanceOut + 24) ↦ₘ (0 : Word)) **
     (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h64e
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f55 f56
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f57
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f58
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f59
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 f60
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c5 f61
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c6 f63
  have c8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c7 f64
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by rw [bytesRegion_replicate32_zero]; xperm_hyp hq) c8

#print axioms adBalanceSetup

end EvmAsm.Codegen.AccountDecodeSpec
