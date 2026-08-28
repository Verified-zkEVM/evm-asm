/-
  EvmAsm.Codegen.Programs.BlockAccessListHashBahOffset

  Offset-form `bah_u32le` under an aligned parent region.

  ## Why this exists

  `bahU32leFlat_spec` (`BlockAccessListHashSAsm.lean`) is derived through the
  SAsm `Fn` framework, whose `Region.wf` obligation (`Rv64/SAsm/Sym.lean`) pins
  the region base — and hence `a0` — to a DWORD-ALIGNED address.  `bah_u32le`
  itself requires no such thing: its body is four `LBU`s, byte loads with no
  alignment condition at the machine level.  The alignment is an artefact of the
  contract SHAPE, not a property of the routine.

  It bites at both call sites in the image.  `block_access_list_hash`
  (`BlockAccessListHash.lean`) reads its two `u32` navigation fields at
  `exec_payload + 528` and `NPR + 4`, i.e. at `sszBase + 588` and `sszBase + 20`
  — both `≡ 4 (mod 8)` — while the SSZ base is `INPUT_MEM_START = 0x40000000`
  (`li s0, 0x40000000` in `BlockVerdictStateRoot.lean`), which is 8-aligned.  So
  at BOTH sites `a0 % 8 = 4` and `bahU32leFlat_spec` does not apply.  Composing
  it would have meant assuming `sszBase % 8 = 4`: satisfiable, but false at the
  linked call site — a non-vacuous and useless hypothesis.

  This module re-roots the four `LBU`s on an aligned parent
  `bytesRegion listBase bs` with `a0 = listBase + off` for arbitrary `off`.  It
  is the `bah_u32le` twin of `bgv_u32le_offset_spec_within`
  (`ExecutionRequestsHashBgvOffset.lean`, #11578), whose single-instruction
  engine `bytesRegion_lbu_cursor_imm_within` is REUSED here rather than
  reproved.  The twelve-step chain is re-run at `GuestAddrs.bah_u32le` because
  the `CodeReq` is the image claim: `CodeReq.ofProg` of this program at ITS
  linked address is a different proposition from the same program at
  `GuestAddrs.bgv_u32le`, and one base-generic theorem would be a statement
  about a model rather than about either linked routine — the argument spelled
  out at length in `BlockAccessListHashCoreSpec.lean`.

  Unblocks the `block_access_list_hash` whole-routine composition (#12318).
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.BlockAccessListHashSAsm
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgvOffset
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.BlockAccessListHashBahOffset

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashBgvOffset (bytesRegion_lbu_cursor_imm_within)
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32 leByte)

set_option maxRecDepth 8000

/-- `bah_u32le` at its linked guest address. -/
abbrev BahB : Word := (GuestAddrs.bah_u32le : Word)

abbrev bahProgL : List Instr := bahU32le_prog

/-- The image claim: byte-for-byte the `guestImageEntries` pairing
    `(GuestAddrs.bah_u32le, bahU32le_prog)`, and definitionally the `CodeReq`
    the flat contract in `BlockAccessListHashSAsm` already uses. -/
abbrev bahCr : CodeReq := CodeReq.ofProg BahB bahProgL

theorem bahCr_eq_flatCr :
    BlockAccessListHashSAsm.bahU32leCr = bahCr := rfl

private theorem bahProg_len : bahProgL.length = 12 := by
  simp only [bahProgL, bahU32le_prog]; decide

private theorem bahProg_bound : 4 * bahProgL.length < 2 ^ 64 := by
  rw [bahProg_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = BahB + BitVec.ofNat 64 (4 * k))
    (hk : k < bahProgL.length)
    (hins : bahProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → bahCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at BahB A bahProgL k ins hA hk hins bahProg_bound a i h

/-- The four bytes at `off` reassembled little-endian.  A local copy: the
    `bgv_u32le` twin of this lemma is `private` in its module. -/
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

/-- **Offset-form `bah_u32le` at its guest PC.**  `a0 = listBase + off` may be
    unaligned; only the PARENT region base carries the alignment obligation.
    Fuel 12 (eleven body instructions + `JALR`).

    This is the form both image call sites need: at `block_access_list_hash`
    the pointers are `sszBase + 588` and `sszBase + 20`, neither dword-aligned
    for the linked `sszBase = 0x40000000`. -/
theorem bah_u32le_offset_spec_within
    (listBase : Word) (off : Nat) (bs : List (BitVec 8))
    (raVal v5 v6 : Word)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : off + 4 ≤ bs.length)
    (h_over : listBase.toNat + (off + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 12 BahB (raVal &&& ~~~(1 : Word)) bahCr
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
  -- 0: LBU x5, 0(x10) — imm-0 helper, so the post index is `off`, not `off+0`
  have t0 := cpsTripleWithin_extend_code
    (mem_at 0 (.LBU .x5 .x10 0) BahB (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (bytesRegion_lbu_within .x5 .x10 listBase v5 BahB bs off
      (by decide) h_align h0 hover0 (h_valid off h0))
  -- 1: LBU x6, 1(x10)
  have t1 := cpsTripleWithin_extend_code
    (mem_at 1 (.LBU .x6 .x10 1) (BahB + 4) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (bytesRegion_lbu_cursor_imm_within .x6 .x10 listBase v6 (BahB + 4) bs off 1
      (by decide) h_align (by decide) (by omega) hover1 (h_valid (off + 1) h1))
  rw [show (BahB + 4 : Word) + 4 = BahB + 8 from by decide] at t1
  -- 2: SLLI x6, x6, 8  (pin the post to `<<< 8`, not `<<< shamt.toNat`)
  have t2 := cpsTripleWithin_extend_code
    (mem_at 2 (.SLLI .x6 .x6 8) (BahB + 8) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (slli_spec_gen_same_within .x6 b1 (8 : BitVec 6) (BahB + 8) (by decide))
  rw [show (BahB + 8 : Word) + 4 = BahB + 12 from by decide, hsh8] at t2
  -- 3: OR x5, x5, x6
  have t3 := cpsTripleWithin_extend_code
    (mem_at 3 (.OR .x5 .x5 .x6) (BahB + 12) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (or_spec_gen_rd_eq_rs1_within .x5 .x6 b0 (b1 <<< 8) (BahB + 12) (by decide))
  rw [show (BahB + 12 : Word) + 4 = BahB + 16 from by decide] at t3
  -- 4: LBU x6, 2(x10)
  have t4 := cpsTripleWithin_extend_code
    (mem_at 4 (.LBU .x6 .x10 2) (BahB + 16) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (bytesRegion_lbu_cursor_imm_within .x6 .x10 listBase (b1 <<< 8) (BahB + 16)
      bs off 2 (by decide) h_align (by decide) (by omega) hover2
      (h_valid (off + 2) h2))
  rw [show (BahB + 16 : Word) + 4 = BahB + 20 from by decide] at t4
  -- 5: SLLI x6, x6, 16
  have t5 := cpsTripleWithin_extend_code
    (mem_at 5 (.SLLI .x6 .x6 16) (BahB + 20) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (slli_spec_gen_same_within .x6 b2 (16 : BitVec 6) (BahB + 20) (by decide))
  rw [show (BahB + 20 : Word) + 4 = BahB + 24 from by decide, hsh16] at t5
  -- 6: OR x5, x5, x6
  have t6 := cpsTripleWithin_extend_code
    (mem_at 6 (.OR .x5 .x5 .x6) (BahB + 24) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (or_spec_gen_rd_eq_rs1_within .x5 .x6 (b0 ||| b1 <<< 8) (b2 <<< 16)
      (BahB + 24) (by decide))
  rw [show (BahB + 24 : Word) + 4 = BahB + 28 from by decide] at t6
  -- 7: LBU x6, 3(x10)
  have t7 := cpsTripleWithin_extend_code
    (mem_at 7 (.LBU .x6 .x10 3) (BahB + 28) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (bytesRegion_lbu_cursor_imm_within .x6 .x10 listBase (b2 <<< 16) (BahB + 28)
      bs off 3 (by decide) h_align (by decide) (by omega) hover3
      (h_valid (off + 3) h3))
  rw [show (BahB + 28 : Word) + 4 = BahB + 32 from by decide] at t7
  -- 8: SLLI x6, x6, 24
  have t8 := cpsTripleWithin_extend_code
    (mem_at 8 (.SLLI .x6 .x6 24) (BahB + 32) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (slli_spec_gen_same_within .x6 b3 (24 : BitVec 6) (BahB + 32) (by decide))
  rw [show (BahB + 32 : Word) + 4 = BahB + 36 from by decide, hsh24] at t8
  -- 9: OR x5, x5, x6
  have t9 := cpsTripleWithin_extend_code
    (mem_at 9 (.OR .x5 .x5 .x6) (BahB + 36) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (or_spec_gen_rd_eq_rs1_within .x5 .x6
      (b0 ||| b1 <<< 8 ||| b2 <<< 16) (b3 <<< 24) (BahB + 36) (by decide))
  rw [show (BahB + 36 : Word) + 4 = BahB + 40 from by decide] at t9
  -- 10: MV x10, x5
  have t10 := cpsTripleWithin_extend_code
    (mem_at 10 (.MV .x10 .x5) (BahB + 40) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (mv_spec_gen_within .x10 .x5
      (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24) cursor (BahB + 40)
      (by decide))
  rw [show (BahB + 40 : Word) + 4 = BahB + 44 from by decide] at t10
  -- 11: JALR — return
  have t11 := cpsTripleWithin_extend_code
    (mem_at 11 (.JALR .x0 .x1 0) (BahB + 44) (by decide)
      (by rw [bahProg_len]; decide) (by rfl))
    (EvmAsm.Evm64.ret_spec_within' (BahB + 44) raVal)
  -- Frames: the atoms each step does not touch.
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
  have c12 : cpsTripleWithin 12 BahB (raVal &&& ~~~(1 : Word)) bahCr
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

/-! ## Non-vacuity

    The hypothesis bundle is satisfied at the REAL call-site geometry, and the
    alignment premise is shown to bite. -/

/-- **Satisfiability at the linked call site.**  The parent region is the SSZ
    input arena at `INPUT_MEM_START`, and `off` is the offset of
    `block_access_list_hash`'s second navigation field, `NPR + 4 = sszBase + 20`
    — the very pointer whose misalignment (`20 % 8 = 4`) puts it out of reach of
    `bahU32leFlat_spec`.  All four premises hold simultaneously. -/
theorem bah_u32le_offset_precondition_reachable :
    ∃ (listBase : Word) (off : Nat) (bs : List (BitVec 8)),
      listBase.toNat % 8 = 0
        ∧ off + 4 ≤ bs.length
        ∧ listBase.toNat + (off + 3) < 2 ^ 64
        ∧ ¬ ((listBase + BitVec.ofNat 64 off).toNat % 8 = 0) :=
  ⟨BitVec.ofNat 64 EvmAsm.Rv64.INPUT_MEM_START, 20,
    List.replicate 24 (0 : BitVec 8), by decide, by decide, by decide, by decide⟩

/-- **Negative control for the parent-alignment premise.**  `h_align` is a real
    restriction, not a formality: a parent region based one byte into a dword
    fails it.  Without a control like this, "the region base is aligned" could
    be a hypothesis that holds everywhere and constrains nothing. -/
theorem bah_u32le_offset_align_bites :
    ¬ ((BitVec.ofNat 64 (EvmAsm.Rv64.INPUT_MEM_START + 1) : Word).toNat % 8 = 0) := by
  decide

/-- **The call-site fact this module exists for**, stated so it cannot rot: the
    two `u32` navigation pointers `block_access_list_hash` hands to `bah_u32le`
    are `sszBase + 588` and `sszBase + 20`, and at the linked
    `sszBase = INPUT_MEM_START` NEITHER is dword-aligned — so the `Region.wf`
    of `bahU32leFlat_spec` is unavailable at both, while this module's
    `h_align` (on the PARENT) holds at both. -/
theorem bah_u32le_call_site_pointers_unaligned :
    (EvmAsm.Rv64.INPUT_MEM_START % 8 = 0)
      ∧ ¬ ((EvmAsm.Rv64.INPUT_MEM_START + 588) % 8 = 0)
      ∧ ¬ ((EvmAsm.Rv64.INPUT_MEM_START + 20) % 8 = 0) := by
  decide

end EvmAsm.Codegen.BlockAccessListHashBahOffset
