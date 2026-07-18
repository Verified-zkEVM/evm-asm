import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Codegen.Programs.HeaderFieldsSpecBlocks

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells (local re-declaration of the `mset_memcpy` helper macro). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-- `la x5, hesr_offset` at [35]-[36] (`+140 → +148`): materialize `hesrOffAddr`.
    (Also confirms the codegen-`laHi` ↔ `Rv64.laHi` defeq at these addresses.) -/
private theorem hesrLaOff140 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 140) (hesrBase + 148) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrOffAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 140)
    Codegen.headerExtractStateRoot_prog 35
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 140))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 144)
    Codegen.headerExtractStateRoot_prog 36
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 140))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 140) hesrOffAddr
    (by decide) (by unfold hesrBase hesrOffAddr; decide) hau had
  rw [show (hesrBase + 140 : Word) + 8 = hesrBase + 148 from by bv_omega] at h
  exact h

/-- `la x5, hesr_length` at [38]-[39] (`+152 → +160`): materialize `hesrLenAddr`. -/
private theorem hesrLaLen152 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 152) (hesrBase + 160) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrLenAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 152)
    Codegen.headerExtractStateRoot_prog 38
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 152))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 156)
    Codegen.headerExtractStateRoot_prog 39
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 152))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 152) hesrLenAddr
    (by decide) (by unfold hesrBase hesrLenAddr; decide) hau had
  rw [show (hesrBase + 152 : Word) + 8 = hesrBase + 160 from by bv_omega] at h
  exact h

/-- `la x5, hesr_length` at [42]-[43] (`+168 → +176`): materialize `hesrLenAddr`. -/
private theorem hesrLaLen168 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 168) (hesrBase + 176) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrLenAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 168)
    Codegen.headerExtractStateRoot_prog 42
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 168))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 172)
    Codegen.headerExtractStateRoot_prog 43
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 168))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 168) hesrLenAddr
    (by decide) (by unfold hesrBase hesrLenAddr; decide) hau had
  rw [show (hesrBase + 168 : Word) + 8 = hesrBase + 176 from by bv_omega] at h
  exact h

/-- `la x5, hesr_offset` at [47]-[48] (`+188 → +196`): materialize `hesrOffAddr`. -/
private theorem hesrLaOff188 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 188) (hesrBase + 196) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrOffAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 188)
    Codegen.headerExtractStateRoot_prog 47
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 188))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 192)
    Codegen.headerExtractStateRoot_prog 48
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 188))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 188) hesrOffAddr
    (by decide) (by unfold hesrBase hesrOffAddr; decide) hau had
  rw [show (hesrBase + 188 : Word) + 8 = hesrBase + 196 from by bv_omega] at h
  exact h

/-! ## The success-tail LBU/SB byte-copy loop ([51]-[56])

    The alignment-free re-emit: `x28` = source pointer (`listBase + fieldOffset`,
    an absolute content pointer), `x18` = destination (output buffer), `x6` =
    byte countdown (32 on entry, from the length check), `x29` = per-byte temp.
    Structurally identical to the verified `mset_memcpy` loop (LBU/SB body +
    `BNE` back-edge) but over the header-caller registers and inline code, so it
    is re-derived here reusing the `copyIntoRegion` content model. -/

/-- Word decrement of a successor counter. -/
private theorem hesr_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem hesr_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- Pointer advance by 1 byte. -/
private theorem hesr_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-- **One copy-loop iteration** ([51]-[55], `hesrBase+204 → hesrBase+224`):
    copy the byte at `src[srcOff+i]` into `dst[dstOff+i]`, advance both pointers
    and decrement the countdown. -/
private theorem hesrCopyBody (srcBase dstBase x29old : Word)
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
    cpsTripleWithin 5 (hesrBase + 204) (hesrBase + 224) hesrCode
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
  -- [51] LBU x29 ← src[srcOff+i].
  have hlbu := bytesRegion_lbu_within .x29 .x28 srcBase x29old (hesrBase + 204)
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [show (hesrBase + 204 : Word) + 4 = hesrBase + 208 from by bv_omega, ← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 204) Codegen.headerExtractStateRoot_prog 51
      (.LBU .x29 .x28 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hlbu
  have hlbuf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by pcFreeR) hlbue
  -- [52] SB dst[dstOff+i] ← x29 (= bval).
  have hsb := bytesRegion_sb_within .x18 .x29 dstBase (bval.zeroExtend 64) (hesrBase + 208)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (hesrBase + 208 : Word) + 4 = hesrBase + 212 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 208) Codegen.headerExtractStateRoot_prog 52
      (.SB .x18 .x29 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hsb
  have hsbf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by pcFreeR) hsbe
  -- [53] ADDI x28 += 1 (src++).
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (hesrBase + 212) (by decide)
  rw [hesr_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (hesrBase + 212 : Word) + 4 = hesrBase + 216 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 212) Codegen.headerExtractStateRoot_prog 53
      (.ADDI .x28 .x28 (1 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h3
  have h3f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h3e
  -- [54] ADDI x18 += 1 (dst++).
  have h4 := addi_spec_gen_same_within .x18
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (hesrBase + 216) (by decide)
  rw [hesr_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (hesrBase + 216 : Word) + 4 = hesrBase + 220 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 216) Codegen.headerExtractStateRoot_prog 54
      (.ADDI .x18 .x18 (1 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h4
  have h4f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h4e
  -- [55] ADDI x6 -= 1 (count--).
  have h5 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (hesrBase + 220) (by decide)
  rw [hesr_succ_dec m, show (hesrBase + 220 : Word) + 4 = hesrBase + 224 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 220) Codegen.headerExtractStateRoot_prog 55
      (.ADDI .x6 .x6 (-1 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h5
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h5e
  -- Compose the five body steps.
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345)

/-- **The copy-loop closure** ([51]-[56], `hesrBase+204 → hesrBase+228`): by
    induction on the byte countdown, copy the remaining `n+1` bytes and fall
    through past the `BNE` back-edge with `x6 = 0`. -/
private theorem hesrCopyLoop (srcBase dstBase x29old : Word)
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
    cpsTripleWithin (6 * (n + 1)) (hesrBase + 204) (hesrBase + 228) hesrCode
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
  have ha_back : (hesrBase + 224 : Word) + signExtend13 (-20 : BitVec 13) = hesrBase + 204 := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have ha_fall : (hesrBase + 224 : Word) + 4 = hesrBase + 228 := by bv_omega
  have hmono6 : ∀ a i', CodeReq.singleton (hesrBase + 224) (.BNE .x6 .x0 (-20 : BitVec 13)) a = some i'
      → hesrCode a = some i' :=
    CodeReq.ofProg_mem_at hesrBase (hesrBase + 224) Codegen.headerExtractStateRoot_prog 56
      (.BNE .x6 .x0 (-20 : BitVec 13)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)
  induction n generalizing i x29old with
  | zero =>
    have hbody := hesrCopyBody srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i 0
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (hesrBase + 224)
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
    have hbody := hesrCopyBody srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i (k + 1)
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (hesrBase + 224)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono6 hbne
    have htaken := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hesr_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
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

/-! ## Success-tail: offset/length compute + global-cell store ([33]-[41])

    `SUB x6,x10,x12` (`next-len`), `SUB x6,x6,x8` (`next-len-listBase` =
    fieldOffset), then `la x5,hesr_offset ; sd x6,0(x5)` and
    `la x5,hesr_length ; sd x12,0(x5)` round-trip the decoded offset and length
    through the two global scratch cells; `jal x0,+4` falls through to [42]. -/
private theorem hesrOffsetStore
    (next len listBase v5old v6old offOld lenOld : Word) :
    cpsTripleWithin 9 (hesrBase + 132) (hesrBase + 168) hesrCode
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
       (.x6 ↦ᵣ v6old) ** (.x5 ↦ᵣ v5old) **
       (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
       (.x6 ↦ᵣ (next - len - listBase)) ** (.x5 ↦ᵣ hesrLenAddr) **
       (hesrOffAddr ↦ₘ (next - len - listBase)) ** (hesrLenAddr ↦ₘ len)) := by
  -- [33] sub x6, x10, x12  → x6 = next - len
  have h33 := sub_spec_gen_within .x6 .x10 .x12 next len v6old (hesrBase + 132) (by decide)
  rw [show (hesrBase + 132 : Word) + 4 = hesrBase + 136 from by bv_omega] at h33
  have e33 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 132) Codegen.headerExtractStateRoot_prog 33
      (.SUB .x6 .x10 .x12) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h33
  have f33 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x5 ↦ᵣ v5old) ** (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e33
  -- [34] sub x6, x6, x8  → x6 = (next-len) - listBase
  have h34 := sub_spec_gen_rd_eq_rs1_within .x6 .x8 (next - len) listBase (hesrBase + 136) (by decide)
  rw [show (hesrBase + 136 : Word) + 4 = hesrBase + 140 from by bv_omega] at h34
  have e34 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 136) Codegen.headerExtractStateRoot_prog 34
      (.SUB .x6 .x6 .x8) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h34
  have f34 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x5 ↦ᵣ v5old) **
     (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e34
  -- [35-36] la x5, hesr_offset
  have f35 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
     (.x6 ↦ᵣ (next - len - listBase)) ** (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) (hesrLaOff140 v5old)
  -- [37] sd x6, 0(x5)  → *hesr_offset := next-len-listBase
  have h37 := sd_spec_gen_within .x5 .x6 hesrOffAddr (next - len - listBase) offOld
    (0 : BitVec 12) (hesrBase + 148)
  rw [signExtend12_0, show (hesrOffAddr + 0 : Word) = hesrOffAddr from by bv_omega,
      show (hesrBase + 148 : Word) + 4 = hesrBase + 152 from by bv_omega] at h37
  have e37 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 148) Codegen.headerExtractStateRoot_prog 37
      (.SD .x5 .x6 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h37
  have f37 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e37
  -- [38-39] la x5, hesr_length
  have f38 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
     (.x6 ↦ᵣ (next - len - listBase)) ** (hesrOffAddr ↦ₘ (next - len - listBase)) **
     (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) (hesrLaLen152 hesrOffAddr)
  -- [40] sd x12, 0(x5)  → *hesr_length := len
  have h40 := sd_spec_gen_within .x5 .x12 hesrLenAddr len lenOld (0 : BitVec 12) (hesrBase + 160)
  rw [signExtend12_0, show (hesrLenAddr + 0 : Word) = hesrLenAddr from by bv_omega,
      show (hesrBase + 160 : Word) + 4 = hesrBase + 164 from by bv_omega] at h40
  have e40 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 160) Codegen.headerExtractStateRoot_prog 40
      (.SD .x5 .x12 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h40
  have f40 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ (next - len - listBase)) **
     (hesrOffAddr ↦ₘ (next - len - listBase)))
    (by pcFreeR) e40
  -- [41] jal x0, +4  → hesrBase+168
  have h41 := jal_x0_spec_gen_within (4 : BitVec 21) (hesrBase + 164)
  rw [show hesrBase + 164 + signExtend21 (4 : BitVec 21) = hesrBase + 168 from by
      rw [show signExtend21 (4 : BitVec 21) = (4 : Word) from by decide]; bv_omega] at h41
  have e41 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 164) Codegen.headerExtractStateRoot_prog 41
      (.JAL .x0 (4 : BitVec 21)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h41
  have f41 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ (next - len - listBase)) **
     (.x5 ↦ᵣ hesrLenAddr) ** (hesrOffAddr ↦ₘ (next - len - listBase)) ** (hesrLenAddr ↦ₘ len))
    (by pcFreeR) e41
  rw [sepConj_emp_left'] at f41
  -- compose the seven steps
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f33 f34
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f35
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f37
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f38
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s4 f40
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s5 f41
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s6

/-! ## Success-tail: reload offset + form content pointer ([47]-[50])

    `la x5,hesr_offset ; ld x28,0(x5)` reloads the stored field offset into `x28`,
    then `add x28,x8,x28` forms the absolute content pointer `listBase + fo`. -/
private theorem hesrOffsetLoadAdd (fo listBase v5old v28old : Word) :
    cpsTripleWithin 4 (hesrBase + 188) (hesrBase + 204) hesrCode
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo))
      ((.x5 ↦ᵣ hesrOffAddr) ** (.x28 ↦ᵣ (listBase + fo)) ** (.x8 ↦ᵣ listBase) **
       (hesrOffAddr ↦ₘ fo)) := by
  -- [47-48] la x5, hesr_offset
  have f47 := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo))
    (by pcFreeR) (hesrLaOff188 v5old)
  -- [49] ld x28, 0(x5)  → x28 = fo
  have h49 := ld_spec_gen_within .x28 .x5 hesrOffAddr v28old fo (0 : BitVec 12)
    (hesrBase + 196) (by decide)
  rw [signExtend12_0, show (hesrOffAddr + 0 : Word) = hesrOffAddr from by bv_omega,
      show (hesrBase + 196 : Word) + 4 = hesrBase + 200 from by bv_omega] at h49
  have e49 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 196) Codegen.headerExtractStateRoot_prog 49
      (.LD .x28 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h49
  have f49 := cpsTripleWithin_frameR ((.x8 ↦ᵣ listBase))
    (by pcFreeR) e49
  -- [50] add x28, x8, x28  → x28 = listBase + fo
  have h50 := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase fo (hesrBase + 200) (by decide)
  rw [show (hesrBase + 200 : Word) + 4 = hesrBase + 204 from by bv_omega] at h50
  have e50 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 200) Codegen.headerExtractStateRoot_prog 50
      (.ADD .x28 .x8 .x28) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h50
  have f50 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ hesrOffAddr) ** (hesrOffAddr ↦ₘ fo))
    (by pcFreeR) e50
  -- compose
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f47 f49
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f50
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-! ## Success-tail: reload length + load compare constant ([42]-[45])

    `la x5,hesr_length ; ld x6,0(x5)` reloads the stored length into `x6`, then
    `li x7,32` loads the expected 32-byte root length; the `bne x6,x7` at [46]
    dispatches on whether the decoded length is exactly 32. -/
private theorem hesrLenLoad (len v5old v6old v7old : Word) :
    cpsTripleWithin 4 (hesrBase + 168) (hesrBase + 184) hesrCode
      ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (hesrLenAddr ↦ₘ len))
      ((.x5 ↦ᵣ hesrLenAddr) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (hesrLenAddr ↦ₘ len)) := by
  -- [42-43] la x5, hesr_length
  have f42 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (hesrLenAddr ↦ₘ len))
    (by pcFreeR) (hesrLaLen168 v5old)
  -- [44] ld x6, 0(x5)  → x6 = len
  have h44 := ld_spec_gen_within .x6 .x5 hesrLenAddr v6old len (0 : BitVec 12)
    (hesrBase + 176) (by decide)
  rw [signExtend12_0, show (hesrLenAddr + 0 : Word) = hesrLenAddr from by bv_omega,
      show (hesrBase + 176 : Word) + 4 = hesrBase + 180 from by bv_omega] at h44
  have e44 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 176) Codegen.headerExtractStateRoot_prog 44
      (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h44
  have f44 := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7old))
    (by pcFreeR) e44
  -- [45] li x7, 32
  have h45 := li_spec_gen_within .x7 v7old (32 : Word) (hesrBase + 180) (by decide)
  rw [show (hesrBase + 180 : Word) + 4 = hesrBase + 184 from by bv_omega] at h45
  have e45 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 180) Codegen.headerExtractStateRoot_prog 45
      (.LI .x7 (32 : Word)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h45
  have f45 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ hesrLenAddr) ** (.x6 ↦ᵣ len) ** (hesrLenAddr ↦ₘ len))
    (by pcFreeR) e45
  -- compose
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f42 f44
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f45
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-- Round-trip identity: `ofNat 64 fo.toNat = fo` for a 64-bit word. -/
private theorem hesr_ofNat_toNat (fo : Word) : (BitVec.ofNat 64 fo.toNat : Word) = fo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt fo.isLt

/-! ## Success-tail: copy 32 content bytes then finish ([51]-[58])

    The `hesrCopyLoop` 32-byte LBU/SB copy (`bytesRegion outPtr` becomes the field
    content `copyIntoRegion outBytes headerBytes 0 fo.toNat 32`) composed with the
    `hesrSuccessFinish` `li a0,0`/`jal`/epilogue tail.  This is the a0=0 arm's
    load-bearing "output = the 32 field-content bytes" claim. -/
private theorem hesrCopyThenFinish
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
    cpsTripleWithin (6 * 32 + (2 + 6)) (hesrBase + 204) (saved.ra &&& ~~~(1 : Word)) hesrCode
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
  -- The copy loop over 32 bytes (n = 31), starting at src offset fo.toNat, dst offset 0.
  have hcopy := hesrCopyLoop listBase outPtr x29old headerBytes outBytes fo.toNat 0 31 0
    h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
  -- Normalize the copy loop's `ofNat` indices to the entry form.
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd] at hcopy
  rw [show (outPtr + BitVec.ofNat 64 0 : Word) = outPtr from by bv_omega,
      show copyIntoRegion outBytes headerBytes 0 fo.toNat 0 = outBytes from rfl] at hcopy
  -- Frame the copy loop with the finish-tail registers/frame.
  have hcopyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) **
     savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hcopy
  -- The finish tail with a0 := 0, framed by the copy residual + Fr.
  have hfin := hesrSuccessFinish newSp a0old v1 listBase v9 (outPtr + BitVec.ofNat 64 32) saved
    ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
     regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
     bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
  -- compose copy ;; finish
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hcopyF hfin
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-! ## Success-tail: the a0=0 continuation ([47]-[58])

    The length-check not-taken (`len = 32`) arm: reload the offset and form the
    content pointer (`hesrOffsetLoadAdd`), then copy the 32 content bytes and
    return with `a0 = 0` (`hesrCopyThenFinish`).  Entry `x6 = 32` comes from the
    reloaded length on the success path. -/
private theorem hesrSuccessContinue
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
    cpsTripleWithin (4 + (6 * 32 + (2 + 6))) (hesrBase + 188) (saved.ra &&& ~~~(1 : Word)) hesrCode
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) **
       (.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved **
       Fr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
       ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
        regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
        bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) **
        ((.x5 ↦ᵣ hesrOffAddr) ** (hesrOffAddr ↦ₘ fo) ** Fr))) := by
  -- [47]-[50] reload offset + form content pointer.
  have hola := hesrOffsetLoadAdd fo listBase v5old v28old
  have holaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hola
  -- [51]-[58] copy + finish, framed by the offset residual + Fr.
  have hctf := hesrCopyThenFinish fo listBase outPtr newSp x29old v1 v9 a0old saved
    headerBytes outBytes ((.x5 ↦ᵣ hesrOffAddr) ** (hesrOffAddr ↦ₘ fo) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
  rw [hesr_ofNat_toNat fo] at hctf
  -- compose
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) holaF hctf
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-! ## Length-check dispatch ([46]→ret)

    `BNE x6, x7, +60` (`hesrBase+184`): if the decoded field length `len` differs
    from 32, jump to the `status2` return (`a0 = 2`); otherwise fall through to the
    success continuation (`a0 = 0`, copy the 32 content bytes).  Both arms embed the
    epilogue and merge at `ret`.  The post is the two-way disjunction pinning the
    genuine result: on `a0 = 0` (`len = 32`) the output region holds the extracted
    32 field-content bytes (`copyIntoRegion`), on `a0 = 2` (`len ≠ 32`) it is
    unchanged. -/
private theorem hesrLenDispatch
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
    cpsTripleWithin (1 + 204) (hesrBase + 184) (saved.ra &&& ~~~(1 : Word)) hesrCode
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
       (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) ** (hesrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) **
       (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
       bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) **
       (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)),
        ((((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
           (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
           memOwn hesrLenAddr ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           bytesRegion outPtr finalOut ** (hesrOffAddr ↦ₘ fo) ** Fr)) **
         ⌜(a0v = (0 : Word) ∧ len = (32 : Word) ∧
              finalOut = copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ∨
           (a0v = (2 : Word) ∧ len ≠ (32 : Word) ∧ finalOut = outBytes)⌝) h) := by
  -- [46] BNE x6, x7, +60 : taken (len ≠ 32) → status2 (+244), fall-through (len = 32) → +188.
  have ha_t : (hesrBase + 184 : Word) + signExtend13 (60 : BitVec 13) = hesrBase + 244 := by
    rw [show signExtend13 (60 : BitVec 13) = (60 : Word) from by decide]; bv_omega
  have ha_f : (hesrBase + 184 : Word) + 4 = hesrBase + 188 := by bv_omega
  have hmono : ∀ a i', CodeReq.singleton (hesrBase + 184) (.BNE .x6 .x7 (60 : BitVec 13)) a = some i'
      → hesrCode a = some i' :=
    CodeReq.ofProg_mem_at hesrBase (hesrBase + 184) Codegen.headerExtractStateRoot_prog 46
      (.BNE .x6 .x7 (60 : BitVec 13)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)
  have hbne := bne_spec_gen_within .x6 .x7 (60 : BitVec 13) len (32 : Word) (hesrBase + 184)
  rw [ha_t, ha_f] at hbne
  have hbnee := cpsBranchWithin_extend_code hmono hbne
  by_cases hlen : len = (32 : Word)
  · -- Fall-through arm: len = 32, run the success continuation; taken arm is vacuous.
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 hlen)
    have hntF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) **
       (hesrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (by unfold savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hnt
    have hlen2 : len = BitVec.ofNat 64 32 := by rw [hlen]; decide
    have hsucc := hesrSuccessContinue fo listBase outPtr newSp v5old v28old x29old v1 v9 a0old saved
      headerBytes outBytes ((.x7 ↦ᵣ (32 : Word)) ** (hesrLenAddr ↦ₘ len) ** Fr)
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
           ((.x5 ↦ᵣ hesrOffAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (32 : Word)) **
            (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) ** regOwn .x29 **
            (hesrLenAddr ↦ₘ len) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
            bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) **
            (hesrOffAddr ↦ₘ fo) ** Fr)) h := by xperm_chunked hq
        exact sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x6)
              (sepConj_mono (regIs_implies_regOwn .x7)
                (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (fun _ hh => hh)
                    (sepConj_mono_left memIs_implies_memOwn)))))) h hq2) s
  · -- Taken arm: len ≠ 32, run status2 return; fall-through arm is vacuous.
    have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hlen ((sepConj_pure_right _).1 hQ).2)
    have htkF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) **
       (hesrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (by unfold savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) htk
    have hs2 := hesrStatus2Return newSp a0old v1 listBase v9 outPtr saved
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
       (hesrOffAddr ↦ₘ fo) ** (hesrLenAddr ↦ₘ len) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** Fr)
      (by repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj)
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
            (.x29 ↦ᵣ x29old) ** (hesrLenAddr ↦ₘ len) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
            (hesrOffAddr ↦ₘ fo) ** Fr)) h := by xperm_chunked hq
        exact sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x6)
              (sepConj_mono (regIs_implies_regOwn .x7)
                (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (regIs_implies_regOwn .x29)
                    (sepConj_mono_left memIs_implies_memOwn)))))) h hq2) s

/-! ## Full success tail ([33]→ret)

    All five RLP walks succeeded: `x10 = next` (final cursor), `x12 = len` (field
    length), `x8 = listBase`.  Compute the field offset `fo = next − len − listBase`,
    round-trip `fo`/`len` through the two global scratch cells (`hesrOffsetStore`),
    reload the length and set the copy counter (`hesrLenLoad`), then dispatch on the
    length check (`hesrLenDispatch`).  The post pins the genuine result:
    `a0 = 0` with the output region holding the extracted 32 field-content bytes when
    `len = 32`, else `a0 = 2` with the output unchanged. -/
private theorem hesrSuccessTail
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
    cpsTripleWithin (9 + 4 + (1 + 204)) (hesrBase + 132) (saved.ra &&& ~~~(1 : Word)) hesrCode
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ v6old) **
       (.x5 ↦ᵣ v5old) ** (.x7 ↦ᵣ v7old) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) **
       (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) ** (hesrOffAddr ↦ₘ offOld) **
       (hesrLenAddr ↦ₘ lenOld) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)),
        ((((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
           (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
           memOwn hesrLenAddr ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           bytesRegion outPtr finalOut ** (hesrOffAddr ↦ₘ (next - len - listBase)) **
           ((.x12 ↦ᵣ len) ** Fr))) **
         ⌜(a0v = (0 : Word) ∧ len = (32 : Word) ∧
              finalOut = copyIntoRegion outBytes headerBytes 0 (next - len - listBase).toNat 32) ∨
           (a0v = (2 : Word) ∧ len ≠ (32 : Word) ∧ finalOut = outBytes)⌝) h) := by
  -- [33]-[41] offset/length compute + global-cell store, framed by the ambient state.
  have hoffF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7old) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ x29old) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    (hesrOffsetStore next len listBase v5old v6old offOld lenOld)
  -- [42]-[45] reload length + set copy counter, framed by the rest.
  have hllF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
     (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
     (hesrOffAddr ↦ₘ (next - len - listBase)) ** bytesRegion listBase headerBytes **
     bytesRegion outPtr outBytes ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) **
     savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    (hesrLenLoad len hesrLenAddr (next - len - listBase) v7old)
  -- [46]→ret length-check dispatch.
  have hdisp := hesrLenDispatch (next - len - listBase) listBase outPtr newSp len hesrLenAddr
    v28old x29old v1 v9 next saved headerBytes outBytes ((.x12 ↦ᵣ len) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | apply pcFree_sepConj)
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
  -- compose offsetStore ;; lenLoad ;; lenDispatch.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hoffF hllF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hdisp
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => hp) s2

/-- Bundled-entry wrapper for the status-1 return: the ambient registers stay
    folded as `hesrAmbRegs`/`hesrAmbRegsRestored` (un-interleaved from `x10`/`x1`)
    so the dispatch's feeding permutation stays well under the atom cliff.  The
    small reshape to `hesrStatus1Return`'s explicit-register entry is done here,
    in isolation over ~7 atoms. -/
theorem hesrStatus1Bundled (newSp listBase v9 outPtr a0old v1 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin (2 + 6) (hesrBase + 236) (saved.ra &&& ~~~(1 : Word)) hesrCode
      (((.x10 ↦ᵣ a0old) ** (.x1 ↦ᵣ v1)) ** hesrAmbRegs newSp listBase v9 outPtr saved ** Fr)
      (((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra)) **
        hesrAmbRegsRestored newSp saved ** Fr) := by
  have h := hesrStatus1Return newSp a0old v1 listBase v9 outPtr saved Fr hFr
  refine cpsTripleWithin_weaken
    (fun _ hp => by unfold hesrAmbRegs at hp; xperm_hyp hp)
    (fun _ hq => by unfold hesrAmbRegsRestored; xperm_hyp hq) h

/-- The single shared function-return postcondition of the whole dispatch: a
    3-way disjunction pinning the genuine `Success`/`Failure` semantics.
    `a0 = 0` = the selected field's 32 content bytes copied to the output;
    `a0 = 2` = same field found but `len ≠ 32` so the output is untouched;
    `a0 = 1` = a strict parse/walk `Failure`.  The ambient registers are folded
    (`hesrAmbRegsRestored`) and the two scratch cells (`hesrScratchConst`) so the
    dispatch arms reach this over few atoms; `fo`/`len`/`finalOut` are
    existential and the written scratch cell / `x12` are weakened back to `memOwn`
    / `regOwn`. -/
def hesrRetPost (newSp listBase outPtr : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLen index : Nat)
    (Fr : Assertion) : Assertion :=
  fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)) (fo len : Word),
    ((((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** hesrAmbRegsRestored newSp saved) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
       hesrScratchConst ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr finalOut ** Fr)) **
     ⌜(a0v = (0 : Word) ∧ RlpListNthItemSAsm.Success headerBytes listBase listLen index fo len ∧
          len = (32 : Word) ∧ finalOut = copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ∨
       (a0v = (2 : Word) ∧ RlpListNthItemSAsm.Success headerBytes listBase listLen index fo len ∧
          len ≠ (32 : Word) ∧ finalOut = outBytes) ∨
       (a0v = (1 : Word) ∧ RlpListNthItemSAsm.Failure headerBytes listBase listLen index)⌝) h

set_option maxRecDepth 8000 in
/-- Bundled-entry wrapper for the success tail: ambient registers folded
    (`hesrAmbRegs`) and scratch cells folded (`hesrScratchConst`), touched
    scratch registers exposed only as `regOwn`, so the stage feeds it over few
    atoms.  Emits the shared 3-way return post directly, injecting the supplied
    `Success` fact (both the `a0 = 0`/`len = 32` copy case and the `a0 = 2`
    wrong-length case). -/
theorem hesrSuccessTailBundled
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
    (hsucc : RlpListNthItemSAsm.Success headerBytes listBase listLen 3
      (next - len - listBase) len) :
    cpsTripleWithin (9 + 4 + (1 + 204)) (hesrBase + 132) (saved.ra &&& ~~~(1 : Word)) hesrCode
      ((((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ v1) **
         bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
         hesrAmbRegs newSp listBase v9 outPtr saved ** Fr) ** hesrScratchConst) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29)
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3 Fr) := by
  -- peel the five owned scratch registers to concrete values
  refine cpsTripleWithin_of_forall_regIs_to_regOwn5 (fun v5 v6 v7 v28 v29 => ?_)
  -- peel the two owned scratch memory cells
  refine cpsTripleWithin_weaken
    (fun _ hp => by unfold hesrScratchConst at hp; xperm_chunked hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn2
      (P := ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ v1) **
        bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        hesrAmbRegs newSp listBase v9 outPtr saved ** Fr) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29))
      (fun voff vlen => ?_))
  -- feed the concrete success tail
  refine cpsTripleWithin_weaken
    (fun _ hp => by unfold hesrAmbRegs at hp; xperm_chunked hp)
    (fun _ hq => ?_)
    (hesrSuccessTail next len listBase outPtr newSp v5 v6 v7 v28 v29 voff vlen v1 v9
      saved headerBytes outBytes Fr hFr h_src_align h_dst_align h_src_bound h_dst_bound
      h_src_over h_dst_over h_src_valid h_dst_valid)
  -- bridge the two-way success post to the shared three-way return post,
  -- injecting the supplied `Success` fact and folding the ambient/scratch descriptors.
  obtain ⟨a0v, finalOut, hq⟩ := hq
  refine ⟨a0v, finalOut, next - len - listBase, len, ?_⟩
  obtain ⟨hs1, hs2, hd, hu, hsp, hpu⟩ := hq
  refine ⟨hs1, hs2, hd, hu, ?_, ?_⟩
  · -- spatial: weaken the written scratch cell + `x12`, fold the descriptors
    unfold hesrAmbRegsRestored hesrScratchConst
    have hsp' := sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono_left (regIs_implies_regOwn .x12))))))))))))
      hs1 hsp
    xperm_chunked hsp'
  · -- pure: inject `Success` into the 3-way disjunction
    obtain ⟨hemp, h2way⟩ := hpu
    refine ⟨hemp, ?_⟩
    rcases h2way with ⟨ha0, hlen, hfin⟩ | ⟨ha0, hlen, hfin⟩
    · exact Or.inl ⟨ha0, hsucc, hlen, hfin⟩
    · exact Or.inr (Or.inl ⟨ha0, hsucc, hlen, hfin⟩)


end EvmAsm.Codegen.HeaderFieldsSpec
