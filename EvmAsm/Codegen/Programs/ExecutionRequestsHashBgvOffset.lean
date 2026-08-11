/-
  ExecutionRequestsHashBgvOffset — offset-form `bgv_u32le` under aligned parent.

  `bgvU32leFlat_spec` needs `Region.wf` ⇒ pointer base % 8 = 0. Production
  callers (including `execution_requests_hash` offs 4 and 12) pass unaligned
  `a0`. Re-root the four LBUs on aligned `bytesRegion listBase bs` with
  `a0 = listBase + off` (RlpItemSpanSizeOffset / ParentHeaderFrame pattern).

  Parent: #11578 rescope.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.BgvU32leSpec
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.ExecutionRequestsHashBgvOffset

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm (signExtend12_ofNat_small)
open EvmAsm.Codegen
open EvmAsm.Codegen.BgvU32leSpec
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32 leByte)

set_option maxRecDepth 8000

private abbrev BgvB : Word := BitVec.ofNat 64 GuestAddrs.bgv_u32le
private abbrev bgvProgL : List Instr := bgvU32le_prog
private abbrev bgvCr : CodeReq := CodeReq.ofProg BgvB bgvProgL

private theorem bgvProg_len : bgvProgL.length = 12 := by
  simp only [bgvProgL, bgvU32le_prog]; decide

private theorem bgvProg_bound : 4 * bgvProgL.length < 2 ^ 64 := by
  rw [bgvProg_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = BgvB + BitVec.ofNat 64 (4 * k))
    (hk : k < bgvProgL.length)
    (hins : bgvProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → bgvCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at BgvB A bgvProgL k ins hA hk hins bgvProg_bound a i h

/-- LBU with imm ∈ {0,1,2,3}: `rs1 = regionBase + i`, load byte `i + immN`. -/
theorem bytesRegion_lbu_cursor_imm_within
    (rd rs1 : Reg) (regionBase vOld : Word) (pc : Word)
    (bs : List (BitVec 8)) (i immN : Nat)
    (hrd : rd ≠ .x0)
    (halign : regionBase.toNat % 8 = 0)
    (himm : immN ≤ 3)
    (hi : i + immN < bs.length)
    (hover : regionBase.toNat + (i + immN) < 2 ^ 64)
    (hvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64 (i + immN)) = true) :
    cpsTripleWithin 1 pc (pc + 4)
      (CodeReq.singleton pc (.LBU rd rs1 (BitVec.ofNat 12 immN)))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rd ↦ᵣ vOld) **
        bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
        (rd ↦ᵣ ((bs[i + immN]'hi).zeroExtend 64)) **
        bytesRegion regionBase bs) := by
  have hse : signExtend12 (BitVec.ofNat 12 immN) = BitVec.ofNat 64 immN :=
    signExtend12_ofNat_small immN (by omega)
  have hptr :
      (regionBase + BitVec.ofNat 64 i) + signExtend12 (BitVec.ofNat 12 immN) =
        regionBase + BitVec.ofNat 64 (i + immN) := by
    rw [hse]
    apply BitVec.eq_of_toNat_eq
    have ha := regionBase.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hq : 8 * ((i + immN) / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegion_dword_at regionBase bs ((i + immN) / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * ((i + immN) / 8))
  set wordVal := packBytes ((bs.drop (8 * ((i + immN) / 8))).take 8)
  set vAddr := regionBase + BitVec.ofNat 64 i
  have halign' :
      alignToDword (vAddr + signExtend12 (BitVec.ofNat 12 immN)) = dwordAddr := by
    rw [hptr]
    exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess (vAddr + signExtend12 (BitVec.ofNat 12 immN)) = true := by
    rw [hptr]; exact hvalid
  have lbu := generic_lbu_spec_within rd rs1 vAddr vOld (BitVec.ofNat 12 immN) pc
    dwordAddr wordVal hrd halign' hvalid'
  have hbyte :
      extractByte wordVal (byteOffset (vAddr + signExtend12 (BitVec.ofNat 12 immN))) =
        bs[i + immN]'hi := by
    rw [hptr, byteOffset_add_ofNat_of_aligned halign hover]
    simp only [wordVal]
    rw [extractByte_packBytes _ _ (by omega)
      (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

private theorem leU32_at_off (bs : List (BitVec 8)) (off : Nat)
    (h0 : off < bs.length) (h1 : off + 1 < bs.length)
    (h2 : off + 2 < bs.length) (h3 : off + 3 < bs.length) :
    leU32 (bs.drop off) 0 =
      ((bs[off]'h0).zeroExtend 64) |||
      (((bs[off + 1]'h1).zeroExtend 64) <<< 8) |||
      (((bs[off + 2]'h2).zeroExtend 64) <<< 16) |||
      (((bs[off + 3]'h3).zeroExtend 64) <<< 24) := by
  simp only [leU32, leByte]
  have e0 : (bs.drop off).getD 0 0 = bs[off]'h0 := by
    have : 0 < (bs.drop off).length := by simp [List.length_drop]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, List.getElem_drop]
    rfl
  have e1 : (bs.drop off).getD 1 0 = bs[off + 1]'h1 := by
    have : 1 < (bs.drop off).length := by simp [List.length_drop]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, List.getElem_drop]
    congr 1
  have e2 : (bs.drop off).getD 2 0 = bs[off + 2]'h2 := by
    have : 2 < (bs.drop off).length := by simp [List.length_drop]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, List.getElem_drop]
    congr 1
  have e3 : (bs.drop off).getD 3 0 = bs[off + 3]'h3 := by
    have : 3 < (bs.drop off).length := by simp [List.length_drop]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, List.getElem_drop]
    congr 1
  simp only [e0, e1, e2, e3]

/-- Offset-form `bgv_u32le` at guest PC. Fuel 12 (body+ret).
    `a0 = listBase + off` may be unaligned; region base is aligned. -/
theorem bgv_u32le_offset_spec_within
    (listBase : Word) (off : Nat) (bs : List (BitVec 8))
    (raVal v5 v6 : Word)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : off + 4 ≤ bs.length)
    (h_over : listBase.toNat + (off + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 12 BgvB (raVal &&& ~~~(1 : Word)) bgvCr
      (((.x1 ↦ᵣ raVal) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs))
      (((.x1 ↦ᵣ raVal) **
        (.x10 ↦ᵣ leU32 (bs.drop off) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
  have h0 : off < bs.length := by omega
  have h1 : off + 1 < bs.length := by omega
  have h2 : off + 2 < bs.length := by omega
  have h3 : off + 3 < bs.length := by omega
  have hover0 : listBase.toNat + off < 2 ^ 64 := by omega
  have hover1 : listBase.toNat + (off + 1) < 2 ^ 64 := by omega
  have hover2 : listBase.toNat + (off + 2) < 2 ^ 64 := by omega
  have hover3 : listBase.toNat + (off + 3) < 2 ^ 64 := by omega
  set cursor := listBase + BitVec.ofNat 64 off
  set b0 := (bs[off]'h0).zeroExtend 64
  set b1 := (bs[off + 1]'h1).zeroExtend 64
  set b2 := (bs[off + 2]'h2).zeroExtend 64
  set b3 := (bs[off + 3]'h3).zeroExtend 64
  have hsh8 : ((8 : BitVec 6)).toNat = 8 := rfl
  have hsh16 : ((16 : BitVec 6)).toNat = 16 := rfl
  have hsh24 : ((24 : BitVec 6)).toNat = 24 := rfl
  -- 0: LBU x5, 0(x10) — use imm-0 helper so post index is `off` not `off+0`
  have t0 := cpsTripleWithin_extend_code
    (mem_at 0 (.LBU .x5 .x10 0) BgvB (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (bytesRegion_lbu_within .x5 .x10 listBase v5 BgvB bs off
      (by decide) h_align h0 hover0 (h_valid off h0))
  -- 1: LBU x6, 1(x10)
  have t1 := cpsTripleWithin_extend_code
    (mem_at 1 (.LBU .x6 .x10 1) (BgvB + 4) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (bytesRegion_lbu_cursor_imm_within .x6 .x10 listBase v6 (BgvB + 4) bs off 1
      (by decide) h_align (by decide) (by omega) hover1 (h_valid (off + 1) h1))
  rw [show (BgvB + 4 : Word) + 4 = BgvB + 8 from by decide] at t1
  -- 2: SLLI x6, x6, 8  (pin post to <<< 8, not <<< shamt.toNat)
  have t2 := cpsTripleWithin_extend_code
    (mem_at 2 (.SLLI .x6 .x6 8) (BgvB + 8) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (slli_spec_gen_same_within .x6 b1 (8 : BitVec 6) (BgvB + 8) (by decide))
  rw [show (BgvB + 8 : Word) + 4 = BgvB + 12 from by decide, hsh8] at t2
  -- 3: OR x5, x5, x6
  have t3 := cpsTripleWithin_extend_code
    (mem_at 3 (.OR .x5 .x5 .x6) (BgvB + 12) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (or_spec_gen_rd_eq_rs1_within .x5 .x6 b0 (b1 <<< 8) (BgvB + 12) (by decide))
  rw [show (BgvB + 12 : Word) + 4 = BgvB + 16 from by decide] at t3
  -- 4: LBU x6, 2(x10)
  have t4 := cpsTripleWithin_extend_code
    (mem_at 4 (.LBU .x6 .x10 2) (BgvB + 16) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (bytesRegion_lbu_cursor_imm_within .x6 .x10 listBase (b1 <<< 8) (BgvB + 16)
      bs off 2 (by decide) h_align (by decide) (by omega) hover2
      (h_valid (off + 2) h2))
  rw [show (BgvB + 16 : Word) + 4 = BgvB + 20 from by decide] at t4
  -- 5: SLLI x6, x6, 16
  have t5 := cpsTripleWithin_extend_code
    (mem_at 5 (.SLLI .x6 .x6 16) (BgvB + 20) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (slli_spec_gen_same_within .x6 b2 (16 : BitVec 6) (BgvB + 20) (by decide))
  rw [show (BgvB + 20 : Word) + 4 = BgvB + 24 from by decide, hsh16] at t5
  -- 6: OR x5, x5, x6
  have t6 := cpsTripleWithin_extend_code
    (mem_at 6 (.OR .x5 .x5 .x6) (BgvB + 24) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (or_spec_gen_rd_eq_rs1_within .x5 .x6 (b0 ||| b1 <<< 8) (b2 <<< 16)
      (BgvB + 24) (by decide))
  rw [show (BgvB + 24 : Word) + 4 = BgvB + 28 from by decide] at t6
  -- 7: LBU x6, 3(x10)
  have t7 := cpsTripleWithin_extend_code
    (mem_at 7 (.LBU .x6 .x10 3) (BgvB + 28) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (bytesRegion_lbu_cursor_imm_within .x6 .x10 listBase (b2 <<< 16) (BgvB + 28)
      bs off 3 (by decide) h_align (by decide) (by omega) hover3
      (h_valid (off + 3) h3))
  rw [show (BgvB + 28 : Word) + 4 = BgvB + 32 from by decide] at t7
  -- 8: SLLI x6, x6, 24
  have t8 := cpsTripleWithin_extend_code
    (mem_at 8 (.SLLI .x6 .x6 24) (BgvB + 32) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (slli_spec_gen_same_within .x6 b3 (24 : BitVec 6) (BgvB + 32) (by decide))
  rw [show (BgvB + 32 : Word) + 4 = BgvB + 36 from by decide, hsh24] at t8
  -- 9: OR x5, x5, x6
  have t9 := cpsTripleWithin_extend_code
    (mem_at 9 (.OR .x5 .x5 .x6) (BgvB + 36) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (or_spec_gen_rd_eq_rs1_within .x5 .x6
      (b0 ||| b1 <<< 8 ||| b2 <<< 16) (b3 <<< 24) (BgvB + 36) (by decide))
  rw [show (BgvB + 36 : Word) + 4 = BgvB + 40 from by decide] at t9
  -- 10: MV x10, x5
  have t10 := cpsTripleWithin_extend_code
    (mem_at 10 (.MV .x10 .x5) (BgvB + 40) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (mv_spec_gen_within .x10 .x5
      (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24) cursor (BgvB + 40)
      (by decide))
  rw [show (BgvB + 40 : Word) + 4 = BgvB + 44 from by decide] at t10
  -- 11: JALR ret
  have t11 := cpsTripleWithin_extend_code
    (mem_at 11 (.JALR .x0 .x1 0) (BgvB + 44) (by decide)
      (by rw [bgvProg_len]; decide) (by rfl))
    (EvmAsm.Evm64.ret_spec_within' (BgvB + 44) raVal)
  -- Frames (inline, SizeOffset style). Focus atoms omitted from frame.
  have s0 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) t0
  have s1 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ b0) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) t1
  have s2 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ b0) ** ((.x10 : Reg) ↦ᵣ cursor) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) t2
  have s3 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) t3
  have s4 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ (b0 ||| b1 <<< 8)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) t4
  have s5 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ (b0 ||| b1 <<< 8)) **
      ((.x10 : Reg) ↦ᵣ cursor) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion listBase bs)
    (by pcf) t5
  have s6 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) t6
  have s7 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
      ((.x5 : Reg) ↦ᵣ (b0 ||| b1 <<< 8 ||| b2 <<< 16)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) t7
  have s8 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
      ((.x5 : Reg) ↦ᵣ (b0 ||| b1 <<< 8 ||| b2 <<< 16)) **
      ((.x10 : Reg) ↦ᵣ cursor) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion listBase bs)
    (by pcf) t8
  have s9 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) t9
  have s10 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ (b3 <<< 24)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) t10
  have s11 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24)) **
      ((.x5 : Reg) ↦ᵣ (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24)) **
      ((.x6 : Reg) ↦ᵣ (b3 <<< 24)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion listBase bs)
    (by pcf) t11
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0] at hp ⊢; xperm_chunked hp) s0 s1
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1] at hp ⊢; xperm_chunked hp) c01 s2
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1] at hp ⊢; xperm_chunked hp) c02 s3
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1] at hp ⊢; xperm_chunked hp) c03 s4
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1, b2] at hp ⊢; xperm_chunked hp) c04 s5
  have c06 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1, b2] at hp ⊢; xperm_chunked hp) c05 s6
  have c07 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1, b2] at hp ⊢; xperm_chunked hp) c06 s7
  have c08 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1, b2, b3] at hp ⊢; xperm_chunked hp) c07 s8
  have c09 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1, b2, b3] at hp ⊢; xperm_chunked hp) c08 s9
  have c10 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1, b2, b3] at hp ⊢; xperm_chunked hp) c09 s10
  have c11 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [b0, b1, b2, b3] at hp ⊢; xperm_chunked hp) c10 s11
  have hfuel : 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 12 := by decide
  have c12 : cpsTripleWithin 12 BgvB (raVal &&& ~~~(1 : Word)) bgvCr
      ((((.x10 : Reg) ↦ᵣ cursor) ** ((.x5 : Reg) ↦ᵣ v5) ** bytesRegion listBase bs) **
        (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
      ((((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24)) **
        ((.x5 : Reg) ↦ᵣ (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24)) **
        ((.x6 : Reg) ↦ᵣ (b3 <<< 24)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion listBase bs)) := by
    simpa [hfuel] using c11
  refine cpsTripleWithin_weaken
    (fun _ hp => by simp only [cursor] at hp ⊢; xperm_chunked hp)
    (fun h hq => by
      have hle := leU32_at_off bs off h0 h1 h2 h3
      have hq1 :
          (((.x1 : Reg) ↦ᵣ raVal) **
            ((.x10 : Reg) ↦ᵣ leU32 (bs.drop off) 0) **
            ((.x5 : Reg) ↦ᵣ leU32 (bs.drop off) 0) **
            ((.x6 : Reg) ↦ᵣ (b3 <<< 24)) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) h := by
        simpa [b0, b1, b2, b3, hle] using hq
      exact (sepConj_mono (fun _ hx => hx)
        (sepConj_mono (fun _ hx => hx)
          (sepConj_mono (regIs_implies_regOwn (r := .x5))
            (sepConj_mono (regIs_implies_regOwn (r := .x6))
              (fun _ hx => hx))))) h hq1) c12

/-- coverRef: `h_align` is satisfiable (listBase = 0, off = 0, 4 zero bytes).
    Alignment is a caller hyp on the region base (ABI a0 framing), not a static
    GuestAddrs pin discharged by decide — hence `.conditional`, not `.proven`. -/
theorem bgv_u32le_offset_precondition_reachable :
    ∃ (listBase : Word) (off : Nat) (bs : List (BitVec 8)),
      listBase.toNat % 8 = 0 ∧ off + 4 ≤ bs.length ∧
      listBase.toNat + (off + 3) < 2 ^ 64 :=
  ⟨0, 0, [0, 0, 0, 0], by decide, by decide, by decide⟩

end EvmAsm.Codegen.ExecutionRequestsHashBgvOffset
