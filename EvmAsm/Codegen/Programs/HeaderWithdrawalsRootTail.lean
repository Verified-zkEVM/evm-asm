/-
  EvmAsm.Codegen.Programs.HeaderWithdrawalsRootTail

  The withdrawals-extractor success tail (`hewrSuccessTailBundled`), concrete at the
  `header_extract_withdrawals_root` guest addresses.  The `la`-materialize steps have
  address-specific AUIPC hi/lo immediates, so the tail is proven concretely per
  extractor (its cost is O(1), independent of the field index); the generic stage
  spine plugs this in as `hfStageSel`'s success-tail continuation hypothesis.

  This mirrors `HeaderReceiptsRootTail`'s receipts success tail with the
  withdrawals base, program, scratch addresses (`hewr_offset`/`hewr_length`), and a
  +220-byte / +55-index tail shift (133-instruction program vs 78).

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderFieldsGenericInit

namespace EvmAsm.Codegen.HeaderWithdrawalsRootSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.HeaderFieldsSpec
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

-- The 133-instruction program needs a deeper recursion limit than the default for
-- list-length `rfl`s and the `decide`-checked `ofProg_mem_at` membership facts.
set_option maxRecDepth 8000

local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-- Guest entry of `header_extract_withdrawals_root`. -/
def hewrBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.header_extract_withdrawals_root
/-- The `header_extract_withdrawals_root` body at its linked guest address. -/
abbrev hewrCode : CodeReq := CodeReq.ofProg hewrBase Codegen.headerExtractWithdrawalsRoot_prog
theorem hewr_prog_length : Codegen.headerExtractWithdrawalsRoot_prog.length = 133 := rfl
/-- The two global scratch cells `header_extract_withdrawals_root` round-trips through. -/
abbrev hewrOffAddr : Word := (Codegen.GuestAddrs.hewr_offset : Word)
abbrev hewrLenAddr : Word := (Codegen.GuestAddrs.hewr_length : Word)

/-! ## `la` materialize helpers (address-specific AUIPC hi/lo) -/

private theorem hewrLaOff180 (v : Word) :
    cpsTripleWithin 2 (hewrBase + 400) (hewrBase + 408) hewrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hewrOffAddr) := by
  have hau := CodeReq.ofProg_mem_at hewrBase (hewrBase + 400)
    Codegen.headerExtractWithdrawalsRoot_prog 100
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hewr_offset
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 400))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hewrBase (hewrBase + 404)
    Codegen.headerExtractWithdrawalsRoot_prog 101
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hewr_offset
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 400))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hewrBase + 400) hewrOffAddr
    (by decide) (by unfold hewrBase hewrOffAddr; decide) hau had
  rw [show (hewrBase + 400 : Word) + 8 = hewrBase + 408 from by bv_omega] at h
  exact h

private theorem hewrLaLen192 (v : Word) :
    cpsTripleWithin 2 (hewrBase + 412) (hewrBase + 420) hewrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hewrLenAddr) := by
  have hau := CodeReq.ofProg_mem_at hewrBase (hewrBase + 412)
    Codegen.headerExtractWithdrawalsRoot_prog 103
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hewr_length
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 412))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hewrBase (hewrBase + 416)
    Codegen.headerExtractWithdrawalsRoot_prog 104
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hewr_length
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 412))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hewrBase + 412) hewrLenAddr
    (by decide) (by unfold hewrBase hewrLenAddr; decide) hau had
  rw [show (hewrBase + 412 : Word) + 8 = hewrBase + 420 from by bv_omega] at h
  exact h

private theorem hewrLaLen208 (v : Word) :
    cpsTripleWithin 2 (hewrBase + 428) (hewrBase + 436) hewrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hewrLenAddr) := by
  have hau := CodeReq.ofProg_mem_at hewrBase (hewrBase + 428)
    Codegen.headerExtractWithdrawalsRoot_prog 107
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hewr_length
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 428))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hewrBase (hewrBase + 432)
    Codegen.headerExtractWithdrawalsRoot_prog 108
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hewr_length
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 428))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hewrBase + 428) hewrLenAddr
    (by decide) (by unfold hewrBase hewrLenAddr; decide) hau had
  rw [show (hewrBase + 428 : Word) + 8 = hewrBase + 436 from by bv_omega] at h
  exact h

private theorem hewrLaOff228 (v : Word) :
    cpsTripleWithin 2 (hewrBase + 448) (hewrBase + 456) hewrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hewrOffAddr) := by
  have hau := CodeReq.ofProg_mem_at hewrBase (hewrBase + 448)
    Codegen.headerExtractWithdrawalsRoot_prog 112
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hewr_offset
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 448))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hewrBase (hewrBase + 452)
    Codegen.headerExtractWithdrawalsRoot_prog 113
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hewr_offset
      (Codegen.GuestAddrs.header_extract_withdrawals_root + 448))) (by bv_omega)
    (by rw [hewr_prog_length]; decide) rfl (by rw [hewr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hewrBase + 448) hewrOffAddr
    (by decide) (by unfold hewrBase hewrOffAddr; decide) hau had
  rw [show (hewrBase + 448 : Word) + 8 = hewrBase + 456 from by bv_omega] at h
  exact h

/-! ## Copy-loop helpers -/

private theorem hewr_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem hewr_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

private theorem hewr_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

set_option maxRecDepth 8000 in
/-- One copy-loop iteration ([61]-[65], `hewrBase+244 → hewrBase+264`). -/
private theorem hewrCopyBody (srcBase dstBase x29old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i m : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_lt : srcOff + i < srcBytes.length)
    (h_dst_lt : dstOff + i < dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 5 (hewrBase + 464) (hewrBase + 484) hewrCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x29 : Reg) ↦ᵣ x29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) := by
  set bval := srcBytes[srcOff + i]'h_src_lt with hbval
  have htrunc : (bval.zeroExtend 64).truncate 8 = bval := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := bval.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hgetd : srcBytes.getD (srcOff + i) 0 = bval := by
    rw [hbval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_src_lt]; rfl
  have hstep : copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)
      = (copyIntoRegion dstBytes srcBytes dstOff srcOff i).set (dstOff + i) bval := by
    simp only [copyIntoRegion, hgetd]
  have hlbu := bytesRegion_lbu_within .x29 .x28 srcBase x29old (hewrBase + 464)
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [show (hewrBase + 464 : Word) + 4 = hewrBase + 468 from by bv_omega, ← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 464) Codegen.headerExtractWithdrawalsRoot_prog 116
      (.LBU .x29 .x28 (0 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) hlbu
  have hlbuf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by pcFreeR) hlbue
  have hsb := bytesRegion_sb_within .x18 .x29 dstBase (bval.zeroExtend 64) (hewrBase + 468)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (hewrBase + 468 : Word) + 4 = hewrBase + 472 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 468) Codegen.headerExtractWithdrawalsRoot_prog 117
      (.SB .x18 .x29 (0 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) hsb
  have hsbf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by pcFreeR) hsbe
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (hewrBase + 472) (by decide)
  rw [hewr_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (hewrBase + 472 : Word) + 4 = hewrBase + 476 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 472) Codegen.headerExtractWithdrawalsRoot_prog 118
      (.ADDI .x28 .x28 (1 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h3
  have h3f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h3e
  have h4 := addi_spec_gen_same_within .x18
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (hewrBase + 476) (by decide)
  rw [hewr_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (hewrBase + 476 : Word) + 4 = hewrBase + 480 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 476) Codegen.headerExtractWithdrawalsRoot_prog 119
      (.ADDI .x18 .x18 (1 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h4
  have h4f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h4e
  have h5 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (hewrBase + 480) (by decide)
  rw [hewr_succ_dec m, show (hewrBase + 480 : Word) + 4 = hewrBase + 484 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 480) Codegen.headerExtractWithdrawalsRoot_prog 120
      (.ADDI .x6 .x6 (-1 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h5
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h5e
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345)

set_option maxRecDepth 8000 in
/-- The copy-loop closure ([61]-[66], `hewrBase+244 → hewrBase+268`). -/
private theorem hewrCopyLoop (srcBase dstBase x29old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff n i : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + i + (n + 1) ≤ srcBytes.length)
    (h_dst_bound : dstOff + i + (n + 1) ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * (n + 1)) (hewrBase + 464) (hewrBase + 488) hewrCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x29 : Reg) ↦ᵣ x29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i + (n + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i + (n + 1)))) **
       regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + (n + 1)))) := by
  have ha_back : (hewrBase + 484 : Word) + signExtend13 (-20 : BitVec 13) = hewrBase + 464 := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have ha_fall : (hewrBase + 484 : Word) + 4 = hewrBase + 488 := by bv_omega
  have hmono6 : ∀ a i', CodeReq.singleton (hewrBase + 484) (.BNE .x6 .x0 (-20 : BitVec 13)) a = some i'
      → hewrCode a = some i' :=
    CodeReq.ofProg_mem_at hewrBase (hewrBase + 484) Codegen.headerExtractWithdrawalsRoot_prog 121
      (.BNE .x6 .x0 (-20 : BitVec 13)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)
  induction n generalizing i x29old with
  | zero =>
    have hbody := hewrCopyBody srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i 0
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (hewrBase + 484)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono6 hbne
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by pcFreeR) hnt
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hbody hntf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          simp only [show srcOff + i + (0 + 1) = srcOff + (i + 1) from by omega,
                     show dstOff + i + (0 + 1) = dstOff + (i + 1) from by omega,
                     show i + (0 + 1) = i + 1 from by omega]
          have hq2 : (((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
              ((.x6 : Reg) ↦ᵣ (0 : Word)) **
              ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
              ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes **
              bytesRegion dstBase
                (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x29) _ hq2
          xperm_chunked hq3) sfull)
  | succ k ih =>
    have hbody := hewrCopyBody srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i (k + 1)
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (hewrBase + 484)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono6 hbne
    have htaken := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hewr_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by pcFreeR) htaken
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hbody htf
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show srcOff + (i + 1) + (k + 1) = srcOff + i + (k + 1 + 1) from by omega,
                     show dstOff + (i + 1) + (k + 1) = dstOff + i + (k + 1 + 1) from by omega,
                     show i + 1 + (k + 1) = i + (k + 1 + 1) from by omega] at hq
          xperm_chunked hq) sfull)

private theorem hewr_ofNat_toNat (fo : Word) : (BitVec.ofNat 64 fo.toNat : Word) = fo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt fo.isLt

/-! ## Success-tail: offset/length compute + global-cell store ([43]-[51]) -/

private theorem hewrOffsetStore
    (next len listBase v5old v6old offOld lenOld : Word) :
    cpsTripleWithin 9 (hewrBase + 392) (hewrBase + 428) hewrCode
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
       (.x6 ↦ᵣ v6old) ** (.x5 ↦ᵣ v5old) **
       (hewrOffAddr ↦ₘ offOld) ** (hewrLenAddr ↦ₘ lenOld))
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
       (.x6 ↦ᵣ (next - len - listBase)) ** (.x5 ↦ᵣ hewrLenAddr) **
       (hewrOffAddr ↦ₘ (next - len - listBase)) ** (hewrLenAddr ↦ₘ len)) := by
  have h33 := sub_spec_gen_within .x6 .x10 .x12 next len v6old (hewrBase + 392) (by decide)
  rw [show (hewrBase + 392 : Word) + 4 = hewrBase + 396 from by bv_omega] at h33
  have e33 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 392) Codegen.headerExtractWithdrawalsRoot_prog 98
      (.SUB .x6 .x10 .x12) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h33
  have f33 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x5 ↦ᵣ v5old) ** (hewrOffAddr ↦ₘ offOld) ** (hewrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e33
  have h34 := sub_spec_gen_rd_eq_rs1_within .x6 .x8 (next - len) listBase (hewrBase + 396) (by decide)
  rw [show (hewrBase + 396 : Word) + 4 = hewrBase + 400 from by bv_omega] at h34
  have e34 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 396) Codegen.headerExtractWithdrawalsRoot_prog 99
      (.SUB .x6 .x6 .x8) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h34
  have f34 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x5 ↦ᵣ v5old) **
     (hewrOffAddr ↦ₘ offOld) ** (hewrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e34
  have f35 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
     (.x6 ↦ᵣ (next - len - listBase)) ** (hewrOffAddr ↦ₘ offOld) ** (hewrLenAddr ↦ₘ lenOld))
    (by pcFreeR) (hewrLaOff180 v5old)
  have h37 := sd_spec_gen_within .x5 .x6 hewrOffAddr (next - len - listBase) offOld
    (0 : BitVec 12) (hewrBase + 408)
  rw [signExtend12_0, show (hewrOffAddr + 0 : Word) = hewrOffAddr from by bv_omega,
      show (hewrBase + 408 : Word) + 4 = hewrBase + 412 from by bv_omega] at h37
  have e37 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 408) Codegen.headerExtractWithdrawalsRoot_prog 102
      (.SD .x5 .x6 (0 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h37
  have f37 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (hewrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e37
  have f38 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
     (.x6 ↦ᵣ (next - len - listBase)) ** (hewrOffAddr ↦ₘ (next - len - listBase)) **
     (hewrLenAddr ↦ₘ lenOld))
    (by pcFreeR) (hewrLaLen192 hewrOffAddr)
  have h40 := sd_spec_gen_within .x5 .x12 hewrLenAddr len lenOld (0 : BitVec 12) (hewrBase + 420)
  rw [signExtend12_0, show (hewrLenAddr + 0 : Word) = hewrLenAddr from by bv_omega,
      show (hewrBase + 420 : Word) + 4 = hewrBase + 424 from by bv_omega] at h40
  have e40 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 420) Codegen.headerExtractWithdrawalsRoot_prog 105
      (.SD .x5 .x12 (0 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h40
  have f40 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ (next - len - listBase)) **
     (hewrOffAddr ↦ₘ (next - len - listBase)))
    (by pcFreeR) e40
  have h41 := jal_x0_spec_gen_within (4 : BitVec 21) (hewrBase + 424)
  rw [show hewrBase + 424 + signExtend21 (4 : BitVec 21) = hewrBase + 428 from by
      rw [show signExtend21 (4 : BitVec 21) = (4 : Word) from by decide]; bv_omega] at h41
  have e41 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 424) Codegen.headerExtractWithdrawalsRoot_prog 106
      (.JAL .x0 (4 : BitVec 21)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h41
  have f41 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ (next - len - listBase)) **
     (.x5 ↦ᵣ hewrLenAddr) ** (hewrOffAddr ↦ₘ (next - len - listBase)) ** (hewrLenAddr ↦ₘ len))
    (by pcFreeR) e41
  rw [sepConj_emp_left'] at f41
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f33 f34
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f35
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f37
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f38
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s4 f40
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s5 f41
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s6

/-! ## Success-tail: reload offset + form content pointer ([57]-[60]) -/

private theorem hewrOffsetLoadAdd (fo listBase v5old v28old : Word) :
    cpsTripleWithin 4 (hewrBase + 448) (hewrBase + 464) hewrCode
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hewrOffAddr ↦ₘ fo))
      ((.x5 ↦ᵣ hewrOffAddr) ** (.x28 ↦ᵣ (listBase + fo)) ** (.x8 ↦ᵣ listBase) **
       (hewrOffAddr ↦ₘ fo)) := by
  have f47 := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hewrOffAddr ↦ₘ fo))
    (by pcFreeR) (hewrLaOff228 v5old)
  have h49 := ld_spec_gen_within .x28 .x5 hewrOffAddr v28old fo (0 : BitVec 12)
    (hewrBase + 456) (by decide)
  rw [signExtend12_0, show (hewrOffAddr + 0 : Word) = hewrOffAddr from by bv_omega,
      show (hewrBase + 456 : Word) + 4 = hewrBase + 460 from by bv_omega] at h49
  have e49 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 456) Codegen.headerExtractWithdrawalsRoot_prog 114
      (.LD .x28 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h49
  have f49 := cpsTripleWithin_frameR ((.x8 ↦ᵣ listBase))
    (by pcFreeR) e49
  have h50 := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase fo (hewrBase + 460) (by decide)
  rw [show (hewrBase + 460 : Word) + 4 = hewrBase + 464 from by bv_omega] at h50
  have e50 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 460) Codegen.headerExtractWithdrawalsRoot_prog 115
      (.ADD .x28 .x8 .x28) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h50
  have f50 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ hewrOffAddr) ** (hewrOffAddr ↦ₘ fo))
    (by pcFreeR) e50
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f47 f49
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f50
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-! ## Success-tail: reload length + load compare constant ([52]-[55]) -/

private theorem hewrLenLoad (len v5old v6old v7old : Word) :
    cpsTripleWithin 4 (hewrBase + 428) (hewrBase + 444) hewrCode
      ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (hewrLenAddr ↦ₘ len))
      ((.x5 ↦ᵣ hewrLenAddr) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (hewrLenAddr ↦ₘ len)) := by
  have f42 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (hewrLenAddr ↦ₘ len))
    (by pcFreeR) (hewrLaLen208 v5old)
  have h44 := ld_spec_gen_within .x6 .x5 hewrLenAddr v6old len (0 : BitVec 12)
    (hewrBase + 436) (by decide)
  rw [signExtend12_0, show (hewrLenAddr + 0 : Word) = hewrLenAddr from by bv_omega,
      show (hewrBase + 436 : Word) + 4 = hewrBase + 440 from by bv_omega] at h44
  have e44 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 436) Codegen.headerExtractWithdrawalsRoot_prog 109
      (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h44
  have f44 := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7old))
    (by pcFreeR) e44
  have h45 := li_spec_gen_within .x7 v7old (32 : Word) (hewrBase + 440) (by decide)
  rw [show (hewrBase + 440 : Word) + 4 = hewrBase + 444 from by bv_omega] at h45
  have e45 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hewrBase (hewrBase + 440) Codegen.headerExtractWithdrawalsRoot_prog 110
      (.LI .x7 (32 : Word)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)) h45
  have f45 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ hewrLenAddr) ** (.x6 ↦ᵣ len) ** (hewrLenAddr ↦ₘ len))
    (by pcFreeR) e45
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f42 f44
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f45
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-- The 8 epilogue-and-finish code-membership facts (success-finish tail, `+268`). -/
private theorem hewrFinishMem :
    (∀ a i, CodeReq.singleton (hewrBase + 488) (.LI .x10 (0 : Word)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 492) (.JAL .x0 (16 : BitVec 21)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 508) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 512) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 516) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 520) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 524) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 528) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → hewrCode a = some i) :=
  ⟨CodeReq.ofProg_mem_at hewrBase (hewrBase + 488) Codegen.headerExtractWithdrawalsRoot_prog 122
     (.LI .x10 (0 : Word)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 492) Codegen.headerExtractWithdrawalsRoot_prog 123
     (.JAL .x0 (16 : BitVec 21)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 508) Codegen.headerExtractWithdrawalsRoot_prog 127
     (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 512) Codegen.headerExtractWithdrawalsRoot_prog 128
     (.LD .x8 .x2 (8 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 516) Codegen.headerExtractWithdrawalsRoot_prog 129
     (.LD .x9 .x2 (16 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 520) Codegen.headerExtractWithdrawalsRoot_prog 130
     (.LD .x18 .x2 (24 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 524) Codegen.headerExtractWithdrawalsRoot_prog 131
     (.ADDI .x2 .x2 (48 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 528) Codegen.headerExtractWithdrawalsRoot_prog 132
     (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)⟩

/-! ## Success-tail: copy 32 content bytes then finish ([61]-[68]) -/

set_option maxRecDepth 8000 in
private theorem hewrCopyThenFinish
    (fo listBase outPtr newSp x29old v1 v9 a0old : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : fo.toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * 32 + (2 + 6)) (hewrBase + 464) (saved.ra &&& ~~~(1 : Word)) hewrCode
      (((.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 fo.toNat)) **
        (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes) **
       ((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ listBase) **
        (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr))
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) **
       ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
        regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
        bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ** Fr)) := by
  have hcopy := hewrCopyLoop listBase outPtr x29old headerBytes outBytes fo.toNat 0 31 0
    h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd] at hcopy
  rw [show (outPtr + BitVec.ofNat 64 0 : Word) = outPtr from by bv_omega,
      show copyIntoRegion outBytes headerBytes 0 fo.toNat 0 = outBytes from rfl] at hcopy
  have hcopyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) **
     savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hcopy
  obtain ⟨fm0, fm1, fm2, fm3, fm4, fm5, fm6, fm7⟩ := hewrFinishMem
  have hfin := hfSuccessFinish (code := hewrCode) (hewrBase + 488) newSp a0old v1 listBase v9
    (outPtr + BitVec.ofNat 64 32) saved
    ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
     regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
     bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    fm0 fm1 fm2 fm3 fm4 fm5 fm6 fm7
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hcopyF hfin
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-! ## Success-tail: the a0=0 continuation ([57]-[68]) -/

set_option maxRecDepth 8000 in
private theorem hewrSuccessContinue
    (fo listBase outPtr newSp v5old v28old x29old v1 v9 a0old : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : fo.toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (4 + (6 * 32 + (2 + 6))) (hewrBase + 448) (saved.ra &&& ~~~(1 : Word)) hewrCode
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hewrOffAddr ↦ₘ fo) **
       (.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved **
       Fr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
       ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
        regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
        bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) **
        ((.x5 ↦ᵣ hewrOffAddr) ** (hewrOffAddr ↦ₘ fo) ** Fr))) := by
  have hola := hewrOffsetLoadAdd fo listBase v5old v28old
  have holaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hola
  have hctf := hewrCopyThenFinish fo listBase outPtr newSp x29old v1 v9 a0old saved
    headerBytes outBytes ((.x5 ↦ᵣ hewrOffAddr) ** (hewrOffAddr ↦ₘ fo) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
  rw [hewr_ofNat_toNat fo] at hctf
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) holaF hctf
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-- The status-2 code-membership facts (`li a0,2` at `+284` + shared epilogue). -/
private theorem hewrStatus2Mem :
    (∀ a i, CodeReq.singleton (hewrBase + 504) (.LI .x10 (2 : Word)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 508) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 512) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 516) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 520) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 524) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → hewrCode a = some i) ∧
    (∀ a i, CodeReq.singleton (hewrBase + 528) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → hewrCode a = some i) :=
  ⟨CodeReq.ofProg_mem_at hewrBase (hewrBase + 504) Codegen.headerExtractWithdrawalsRoot_prog 126
     (.LI .x10 (2 : Word)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 508) Codegen.headerExtractWithdrawalsRoot_prog 127
     (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 512) Codegen.headerExtractWithdrawalsRoot_prog 128
     (.LD .x8 .x2 (8 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 516) Codegen.headerExtractWithdrawalsRoot_prog 129
     (.LD .x9 .x2 (16 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 520) Codegen.headerExtractWithdrawalsRoot_prog 130
     (.LD .x18 .x2 (24 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 524) Codegen.headerExtractWithdrawalsRoot_prog 131
     (.ADDI .x2 .x2 (48 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num),
   CodeReq.ofProg_mem_at hewrBase (hewrBase + 528) Codegen.headerExtractWithdrawalsRoot_prog 132
     (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)⟩

/-! ## Length-check dispatch ([56]→ret) -/

set_option maxRecDepth 8000 in
private theorem hewrLenDispatch
    (fo listBase outPtr newSp len v5old v28old x29old v1 v9 a0old : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : fo.toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + 204) (hewrBase + 444) (saved.ra &&& ~~~(1 : Word)) hewrCode
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
       (.x8 ↦ᵣ listBase) ** (hewrOffAddr ↦ₘ fo) ** (hewrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) **
       (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
       bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) **
       (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)),
        ((((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
           (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
           memOwn hewrLenAddr ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           bytesRegion outPtr finalOut ** (hewrOffAddr ↦ₘ fo) ** Fr)) **
         ⌜(a0v = (0 : Word) ∧ len = (32 : Word) ∧
              finalOut = copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ∨
           (a0v = (2 : Word) ∧ len ≠ (32 : Word) ∧ finalOut = outBytes)⌝) h) := by
  have ha_t : (hewrBase + 444 : Word) + signExtend13 (60 : BitVec 13) = hewrBase + 504 := by
    rw [show signExtend13 (60 : BitVec 13) = (60 : Word) from by decide]; bv_omega
  have ha_f : (hewrBase + 444 : Word) + 4 = hewrBase + 448 := by bv_omega
  have hmono : ∀ a i', CodeReq.singleton (hewrBase + 444) (.BNE .x6 .x7 (60 : BitVec 13)) a = some i'
      → hewrCode a = some i' :=
    CodeReq.ofProg_mem_at hewrBase (hewrBase + 444) Codegen.headerExtractWithdrawalsRoot_prog 111
      (.BNE .x6 .x7 (60 : BitVec 13)) (by bv_omega)
      (by rw [hewr_prog_length]; norm_num) rfl (by rw [hewr_prog_length]; norm_num)
  have hbne := bne_spec_gen_within .x6 .x7 (60 : BitVec 13) len (32 : Word) (hewrBase + 444)
  rw [ha_t, ha_f] at hbne
  have hbnee := cpsBranchWithin_extend_code hmono hbne
  by_cases hlen : len = (32 : Word)
  · have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 hlen)
    have hntF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hewrOffAddr ↦ₘ fo) **
       (hewrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (by unfold savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hnt
    have hlen2 : len = BitVec.ofNat 64 32 := by rw [hlen]; decide
    have hsucc := hewrSuccessContinue fo listBase outPtr newSp v5old v28old x29old v1 v9 a0old saved
      headerBytes outBytes ((.x7 ↦ᵣ (32 : Word)) ** (hewrLenAddr ↦ₘ len) ** Fr)
      (by repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
      h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
    have s := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by rw [← hlen2]; xperm_chunked hp) hntF hsucc
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun h hq => by
        refine ⟨(0 : Word), copyIntoRegion outBytes headerBytes 0 fo.toNat 32, ?_⟩
        refine (sepConj_pure_right h).2 ⟨?_, Or.inl ⟨rfl, hlen, rfl⟩⟩
        have hq2 : (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
            (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
           ((.x5 ↦ᵣ hewrOffAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (32 : Word)) **
            (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) ** regOwn .x29 **
            (hewrLenAddr ↦ₘ len) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
            bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) **
            (hewrOffAddr ↦ₘ fo) ** Fr)) h := by xperm_chunked hq
        exact sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x6)
              (sepConj_mono (regIs_implies_regOwn .x7)
                (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (fun _ hh => hh)
                    (sepConj_mono_left memIs_implies_memOwn)))))) h hq2) s
  · have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hlen ((sepConj_pure_right _).1 hQ).2)
    have htkF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hewrOffAddr ↦ₘ fo) **
       (hewrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (by unfold savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) htk
    obtain ⟨sm0, sm1, sm2, sm3, sm4, sm5, sm6⟩ := hewrStatus2Mem
    have hs2 := hfStatus2Return (code := hewrCode) (hewrBase + 504) newSp a0old v1 listBase v9 outPtr saved
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
       (hewrOffAddr ↦ₘ fo) ** (hewrLenAddr ↦ₘ len) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** Fr)
      (by repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj)
      sm0 sm1 sm2 sm3 sm4 sm5 sm6
    have hs2' := cpsTripleWithin_mono_nSteps (show (1 + 6) ≤ 204 by omega) hs2
    have s := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) htkF hs2'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun h hq => by
        refine ⟨(2 : Word), outBytes, ?_⟩
        refine (sepConj_pure_right h).2 ⟨?_, Or.inr ⟨rfl, hlen, rfl⟩⟩
        have hq2 : (((.x10 ↦ᵣ (2 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
            (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
           ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x28 ↦ᵣ v28old) **
            (.x29 ↦ᵣ x29old) ** (hewrLenAddr ↦ₘ len) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
            (hewrOffAddr ↦ₘ fo) ** Fr)) h := by xperm_chunked hq
        exact sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x6)
              (sepConj_mono (regIs_implies_regOwn .x7)
                (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (regIs_implies_regOwn .x29)
                    (sepConj_mono_left memIs_implies_memOwn)))))) h hq2) s

/-! ## Full success tail ([43]→ret) -/

set_option maxRecDepth 8000 in
private theorem hewrSuccessTail
    (next len listBase outPtr newSp v5old v6old v7old v28old x29old offOld lenOld v1 v9 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : (next - len - listBase).toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (9 + 4 + (1 + 204)) (hewrBase + 392) (saved.ra &&& ~~~(1 : Word)) hewrCode
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ v6old) **
       (.x5 ↦ᵣ v5old) ** (.x7 ↦ᵣ v7old) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) **
       (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) ** (hewrOffAddr ↦ₘ offOld) **
       (hewrLenAddr ↦ₘ lenOld) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)),
        ((((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
           (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
           memOwn hewrLenAddr ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           bytesRegion outPtr finalOut ** (hewrOffAddr ↦ₘ (next - len - listBase)) **
           ((.x12 ↦ᵣ len) ** Fr))) **
         ⌜(a0v = (0 : Word) ∧ len = (32 : Word) ∧
              finalOut = copyIntoRegion outBytes headerBytes 0 (next - len - listBase).toNat 32) ∨
           (a0v = (2 : Word) ∧ len ≠ (32 : Word) ∧ finalOut = outBytes)⌝) h) := by
  have hoffF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7old) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ x29old) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    (hewrOffsetStore next len listBase v5old v6old offOld lenOld)
  have hllF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
     (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
     (hewrOffAddr ↦ₘ (next - len - listBase)) ** bytesRegion listBase headerBytes **
     bytesRegion outPtr outBytes ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) **
     savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    (hewrLenLoad len hewrLenAddr (next - len - listBase) v7old)
  have hdisp := hewrLenDispatch (next - len - listBase) listBase outPtr newSp len hewrLenAddr
    v28old x29old v1 v9 next saved headerBytes outBytes ((.x12 ↦ᵣ len) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | apply pcFree_sepConj)
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hoffF hllF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hdisp
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => hp) s2

/-- Bundled-entry success tail matching `hfStageSel`'s success-tail hypothesis
    (index 16, withdrawals scratch addresses): ambient registers folded
    (`hesrAmbRegs`), scratch folded (`hfScratchConst`), touched scratch registers
    exposed only as `regOwn`.  Emits the shared 3-way `hfRetPost`, injecting the
    supplied `Success` fact. -/
theorem hewrSuccessTailBundled
    (next len listBase outPtr newSp v1 v9 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8)) (listLen : Nat)
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : (next - len - listBase).toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hsucc : RlpListNthItemSAsm.Success headerBytes listBase listLen 16
      (next - len - listBase) len) :
    cpsTripleWithin (9 + 4 + (1 + 204)) (hewrBase + 392) (saved.ra &&& ~~~(1 : Word)) hewrCode
      ((((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ v1) **
         bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
         hesrAmbRegs newSp listBase v9 outPtr saved ** Fr) ** hfScratchConst hewrOffAddr hewrLenAddr) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29)
      (hfRetPost hewrOffAddr hewrLenAddr newSp listBase outPtr saved headerBytes outBytes listLen 16 Fr) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn5 (fun v5 v6 v7 v28 v29 => ?_)
  refine cpsTripleWithin_weaken
    (fun _ hp => by unfold hfScratchConst at hp; xperm_chunked hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn2
      (P := ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ v1) **
        bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        hesrAmbRegs newSp listBase v9 outPtr saved ** Fr) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29))
      (fun voff vlen => ?_))
  refine cpsTripleWithin_weaken
    (fun _ hp => by unfold hesrAmbRegs at hp; xperm_chunked hp)
    (fun _ hq => ?_)
    (hewrSuccessTail next len listBase outPtr newSp v5 v6 v7 v28 v29 voff vlen v1 v9
      saved headerBytes outBytes Fr hFr h_src_align h_dst_align h_src_bound h_dst_bound
      h_src_over h_dst_over h_src_valid h_dst_valid)
  obtain ⟨a0v, finalOut, hq⟩ := hq
  refine ⟨a0v, finalOut, next - len - listBase, len, ?_⟩
  obtain ⟨hs1, hs2, hd, hu, hsp, hpu⟩ := hq
  refine ⟨hs1, hs2, hd, hu, ?_, ?_⟩
  · unfold hesrAmbRegsRestored hfScratchConst
    have hsp' := sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono_left (regIs_implies_regOwn .x12))))))))))))
      hs1 hsp
    xperm_chunked hsp'
  · obtain ⟨hemp, h2way⟩ := hpu
    refine ⟨hemp, ?_⟩
    rcases h2way with ⟨ha0, hlen, hfin⟩ | ⟨ha0, hlen, hfin⟩
    · exact Or.inl ⟨ha0, hsucc, hlen, hfin⟩
    · exact Or.inr (Or.inl ⟨ha0, hsucc, hlen, hfin⟩)


end EvmAsm.Codegen.HeaderWithdrawalsRootSpec
