/-
  ExecutionRequestsHashReads — five bgv_u32le offset reads with MV/ADDI setup.

  Geometry (executionRequestsHash_prog @ GuestAddrs.execution_requests_hash):
    B+72  MV a0,s0;     B+76  JAL bgv;  B+80  MV s2,a0   -- dep  @ base+0
    B+84  ADDI a0,s0,4; B+88  JAL bgv;  B+92  MV s3,a0   -- wdr  @ base+4
    B+96  ADDI a0,s0,8; B+100 JAL bgv;  B+104 MV s4,a0  -- con  @ base+8
    B+108 ADDI a0,s0,12;B+112 JAL bgv;  B+116 MV s5,a0  -- bdep @ base+12
    B+120 ADDI a0,s0,16;B+124 JAL bgv;  B+128 MV s6,a0  -- bexit@ base+16
  → B+132 mono entry.

  Uses offset-form callWithin (Bgv.lean); NOT aligned flat_spec.
  Parent: #11578 rescope.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.BgvU32leSpec
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgv
import EvmAsm.Codegen.Programs.ExecutionRequestsHashGates
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.ExecutionRequestsHashReads

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ExecutionRequestsHashBgv
open EvmAsm.Codegen.ExecutionRequestsHashGates

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash
private abbrev erhProgL : List Instr := executionRequestsHash_prog

private theorem erhProgL_len : erhProgL.length = 135 := by
  simp only [erhProgL, executionRequestsHash_prog]; decide

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < erhProgL.length)
    (hins : erhProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i :=
  erhMem A k ins hk hA hins

private theorem se12_4 : signExtend12 (4 : BitVec 12) = (4 : Word) := by decide
private theorem se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se12_12 : signExtend12 (12 : BitVec 12) = (12 : Word) := by decide
private theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide

/-- Offsets decoded from the SSZ offset table at `listBase`. -/
def erhOffsetsFromBytes (bs : List (BitVec 8)) (endW : Word) : ErhOffsets where
  dep := leU32 (bs.drop 0) 0
  wdr := leU32 (bs.drop 4) 0
  con := leU32 (bs.drop 8) 0
  bdep := leU32 (bs.drop 12) 0
  bexit := leU32 (bs.drop 16) 0
  end_ := endW

/-- Deposit offset read: MV+JAL+MV @ B+72 → B+84. Fuel 15. -/
theorem erh_read_dep
    (listBase : Word) (bs : List (BitVec 8))
    (vOld v5 v6 v10 vDest : Word) (F : Assertion) (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 0 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (0 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 15 (B + 72) (B + 84) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (.x19 ↦ᵣ vDest) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + 80)) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ leU32 (bs.drop 0) 0) **
        (.x19 ↦ᵣ leU32 (bs.drop 0) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
  let val := leU32 (bs.drop 0) 0
  have hpcF : ∀ {P : Assertion}, P.pcFree →
      ((.x1 ↦ᵣ vOld) ** (.x19 ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** P).pcFree := by
    intro P hP
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs |
      exact (bytesRegion_pcFree _ _) | exact hP)
  have hpcF2 : ∀ {P : Assertion}, P.pcFree →
      ((.x8 ↦ᵣ listBase) ** (.x19 ↦ᵣ vDest) ** P).pcFree := by
    intro P hP
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hP)
  have hpcF3 : ∀ {P : Assertion}, P.pcFree →
      ((.x1 ↦ᵣ (B + 80)) ** (.x8 ↦ᵣ listBase) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** P).pcFree := by
    intro P hP
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs |
      exact pcFree_regOwn | exact (bytesRegion_pcFree _ _) | exact hP)
  -- MV a0,s0 @72
  have hmv0 := mv_spec_gen_within .x10 .x8 listBase v10 (B + 72) (by decide)
  rw [show (B + 72 : Word) + 4 = B + 76 from by decide] at hmv0
  have lmv := cpsTripleWithin_extend_code
    (mem_at 18 (.MV .x10 .x8) (B + 72) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) hmv0
  have hmvF := cpsTripleWithin_frameR _
    (hpcF hF) lmv
  have hmvW : cpsTripleWithin 1 (B + 72) (B + 76) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (.x19 ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
        (.x19 ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hmvF
  -- callWithin @76
  have hcall := erh_bgv_call_76 listBase bs vOld v5 v6
    ((.x8 ↦ᵣ listBase) ** (.x19 ↦ᵣ vDest) ** F) (hpcF2 hF)
    h_align h_fit h_over h_valid
  have hcallW : cpsTripleWithin 13 (B + 76) (B + 80) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
        (.x19 ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + 80)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ val) **
        (.x19 ↦ᵣ vDest) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
    have hcall' : cpsTripleWithin 13 (B + 76) ((B + 76) + 4) fullCode
        (((((.x1 ↦ᵣ vOld) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 0)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (.x19 ↦ᵣ vDest) ** F)))
        (((((.x1 ↦ᵣ ((B + 76) + 4)) **
          (.x10 ↦ᵣ val) **
          regOwn .x5 ** regOwn .x6 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (.x19 ↦ᵣ vDest) ** F))) := by
      simpa [val, BitVec.add_zero] using hcall
    have hcall'' : cpsTripleWithin 13 (B + 76) (B + 80) fullCode
        (((((.x1 ↦ᵣ vOld) **
          (.x10 ↦ᵣ listBase) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (.x19 ↦ᵣ vDest) ** F)))
        (((((.x1 ↦ᵣ (B + 80)) **
          (.x10 ↦ᵣ val) **
          regOwn .x5 ** regOwn .x6 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (.x19 ↦ᵣ vDest) ** F))) := by
      simpa [BitVec.add_zero, show (B + 76 : Word) + 4 = B + 80 from by decide]
        using hcall'
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hcall''
  -- MV s2,a0 @80
  have hst0 := mv_spec_gen_within .x19 .x10 val vDest (B + 80) (by decide)
  rw [show (B + 80 : Word) + 4 = B + 84 from by decide] at hst0
  have lst := cpsTripleWithin_extend_code
    (mem_at 20 (.MV .x19 .x10) (B + 80) (by decide)
      (by rw [erhProgL_len]; decide) (by rfl)) hst0
  have hstF := cpsTripleWithin_frameR _ (hpcF3 hF) lst
  have hstW : cpsTripleWithin 1 (B + 80) (B + 84) fullCode
      ((.x1 ↦ᵣ (B + 80)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ val) **
        (.x19 ↦ᵣ vDest) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + 80)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ val) **
        (.x19 ↦ᵣ val) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hstF
  have c01 := cpsTripleWithin_seq_same_cr hmvW hcallW
  have c012 := cpsTripleWithin_seq_same_cr c01 hstW
  simpa [val, show (1 + 13 + 1 : Nat) = 15 from rfl] using c012

/-- Helper: ADDI a0,s0,imm + callWithin + MV dest,a0. Specialized per site. -/
private theorem erh_read_addi_site
    (setupK jalK storeK off : Nat) (dest : Reg)
    (imm : BitVec 12) (listBase : Word) (bs : List (BitVec 8))
    (vOld v5 v6 v10 vDest : Word) (F : Assertion) (hF : F.pcFree)
    (hse : signExtend12 imm = BitVec.ofNat 64 off)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : off + 4 ≤ bs.length)
    (h_over : listBase.toNat + (off + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hjalByte : 4 * jalK = 88 ∨ 4 * jalK = 100 ∨ 4 * jalK = 112 ∨ 4 * jalK = 124)
    (hgeo : setupK + 1 = jalK ∧ jalK + 1 = storeK)
    (hkS : setupK < erhProgL.length)
    (hinsS : erhProgL[setupK]'hkS = .ADDI .x10 .x8 imm)
    (hkJ : jalK < erhProgL.length)
    (hinsJ : erhProgL[jalK]'hkJ =
      .JAL .x1 (jalOff GuestAddrs.bgv_u32le
        (GuestAddrs.execution_requests_hash + 4 * jalK)))
    (hkT : storeK < erhProgL.length)
    (hinsT : erhProgL[storeK]'hkT = .MV dest .x10)
    (hdest : dest ≠ .x0) :
    cpsTripleWithin 15 (B + BitVec.ofNat 64 (4 * setupK))
      (B + BitVec.ofNat 64 (4 * (storeK + 1))) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (dest ↦ᵣ vDest) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + BitVec.ofNat 64 (4 * storeK))) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ leU32 (bs.drop off) 0) **
        (dest ↦ᵣ leU32 (bs.drop off) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
  obtain ⟨hg1, hg2⟩ := hgeo
  let setupPc : Word := B + BitVec.ofNat 64 (4 * setupK)
  let jalPc : Word := B + BitVec.ofNat 64 (4 * jalK)
  let storePc : Word := B + BitVec.ofNat 64 (4 * storeK)
  let exitPc : Word := B + BitVec.ofNat 64 (4 * (storeK + 1))
  let val := leU32 (bs.drop off) 0
  have hsetup_jal : setupPc + 4 = jalPc := by
    unfold setupPc jalPc; rw [← hg1];
    simp only [Nat.mul_add, Nat.mul_one]; bv_omega
  have hjal_store : jalPc + 4 = storePc := by
    unfold jalPc storePc; rw [← hg2];
    simp only [Nat.mul_add, Nat.mul_one]; bv_omega
  have hstore_exit : storePc + 4 = exitPc := by
    unfold storePc exitPc
    simp only [Nat.mul_add, Nat.mul_one]; bv_omega
  -- ADDI
  have haddi0 := addi_spec_gen_within .x10 .x8 v10 listBase imm setupPc (by decide)
  rw [hse, hsetup_jal] at haddi0
  have laddi := cpsTripleWithin_extend_code
    (mem_at setupK (.ADDI .x10 .x8 imm) setupPc (by rfl) hkS hinsS) haddi0
  have hpcFa : ((.x1 ↦ᵣ vOld) ** (dest ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs |
      exact (bytesRegion_pcFree _ _) | exact hF)
  have haddiF := cpsTripleWithin_frameR _ hpcFa laddi
  have haddiW : cpsTripleWithin 1 setupPc jalPc fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (dest ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        (dest ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      haddiF
  -- callWithin
  have hjalN : 4 * jalK = 88 ∨ 4 * jalK = 100 ∨ 4 * jalK = 112 ∨
      4 * jalK = 124 := hjalByte
  have hpcFc : ((.x8 ↦ᵣ listBase) ** (dest ↦ᵣ vDest) ** F).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hF)
  have hcall0 := erh_bgv_callWithin_offset (4 * jalK) off listBase bs vOld v5 v6
    ((.x8 ↦ᵣ listBase) ** (dest ↦ᵣ vDest) ** F) hpcFc
    h_align h_fit h_over h_valid (Or.inr hjalN)
    (by
      have : 4 * jalK / 4 = jalK := by omega
      simpa [this] using hkJ)
    (by
      have : 4 * jalK / 4 = jalK := by omega
      simpa [this] using hinsJ)
  have hcallW : cpsTripleWithin 13 jalPc storePc fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        (dest ↦ᵣ vDest) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ storePc) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ val) **
        (dest ↦ᵣ vDest) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
    have hcall' : cpsTripleWithin 13 jalPc (jalPc + 4) fullCode
        (((((.x1 ↦ᵣ vOld) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (dest ↦ᵣ vDest) ** F)))
        (((((.x1 ↦ᵣ (jalPc + 4)) **
          (.x10 ↦ᵣ val) **
          regOwn .x5 ** regOwn .x6 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (dest ↦ᵣ vDest) ** F))) := by
      simpa [jalPc, val, B] using hcall0
    have hcall'' : cpsTripleWithin 13 jalPc storePc fullCode
        (((((.x1 ↦ᵣ vOld) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (dest ↦ᵣ vDest) ** F)))
        (((((.x1 ↦ᵣ storePc) **
          (.x10 ↦ᵣ val) **
          regOwn .x5 ** regOwn .x6 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) **
          ((.x8 ↦ᵣ listBase) ** (dest ↦ᵣ vDest) ** F))) := by
      simpa [hjal_store.symm] using hcall'
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hcall''
  -- MV store
  have hst0 := mv_spec_gen_within dest .x10 val vDest storePc hdest
  rw [hstore_exit] at hst0
  have lst := cpsTripleWithin_extend_code
    (mem_at storeK (.MV dest .x10) storePc (by rfl) hkT hinsT) hst0
  have hpcFs : ((.x1 ↦ᵣ storePc) ** (.x8 ↦ᵣ listBase) **
      regOwn .x5 ** regOwn .x6 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs |
      exact pcFree_regOwn | exact (bytesRegion_pcFree _ _) | exact hF)
  have hstF := cpsTripleWithin_frameR _ hpcFs lst
  have hstW : cpsTripleWithin 1 storePc exitPc fullCode
      ((.x1 ↦ᵣ storePc) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ val) **
        (dest ↦ᵣ vDest) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ storePc) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ val) **
        (dest ↦ᵣ val) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hstF
  have c01 := cpsTripleWithin_seq_same_cr haddiW hcallW
  have c012 := cpsTripleWithin_seq_same_cr c01 hstW
  simpa [val, setupPc, exitPc, storePc,
    show (1 + 13 + 1 : Nat) = 15 from rfl] using c012

theorem erh_read_wdr
    (listBase : Word) (bs : List (BitVec 8))
    (vOld v5 v6 v10 vDest : Word) (F : Assertion) (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 4 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (4 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 15 (B + 84) (B + 96) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (.x20 ↦ᵣ vDest) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + 92)) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ leU32 (bs.drop 4) 0) **
        (.x20 ↦ᵣ leU32 (bs.drop 4) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
  simpa using erh_read_addi_site 21 22 23 4 .x20 (4 : BitVec 12)
    listBase bs vOld v5 v6 v10 vDest F hF se12_4
    h_align h_fit h_over h_valid
    (Or.inl rfl) ⟨rfl, rfl⟩
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl) (by decide)

theorem erh_read_con
    (listBase : Word) (bs : List (BitVec 8))
    (vOld v5 v6 v10 vDest : Word) (F : Assertion) (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 8 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (8 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 15 (B + 96) (B + 108) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (.x21 ↦ᵣ vDest) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + 104)) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ leU32 (bs.drop 8) 0) **
        (.x21 ↦ᵣ leU32 (bs.drop 8) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
  simpa using erh_read_addi_site 24 25 26 8 .x21 (8 : BitVec 12)
    listBase bs vOld v5 v6 v10 vDest F hF se12_8
    h_align h_fit h_over h_valid
    (Or.inr (Or.inl rfl)) ⟨rfl, rfl⟩
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl) (by decide)

theorem erh_read_bdep
    (listBase : Word) (bs : List (BitVec 8))
    (vOld v5 v6 v10 vDest : Word) (F : Assertion) (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 12 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (12 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 15 (B + 108) (B + 120) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (.x22 ↦ᵣ vDest) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + 116)) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ leU32 (bs.drop 12) 0) **
        (.x22 ↦ᵣ leU32 (bs.drop 12) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
  simpa using erh_read_addi_site 27 28 29 12 .x22 (12 : BitVec 12)
    listBase bs vOld v5 v6 v10 vDest F hF se12_12
    h_align h_fit h_over h_valid
    (Or.inr (Or.inr (Or.inl rfl))) ⟨rfl, rfl⟩
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl) (by decide)

theorem erh_read_bexit
    (listBase : Word) (bs : List (BitVec 8))
    (vOld v5 v6 v10 vDest : Word) (F : Assertion) (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 16 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (16 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 15 (B + 120) (B + 132) fullCode
      ((.x1 ↦ᵣ vOld) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ v10) **
        (.x23 ↦ᵣ vDest) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F)
      ((.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) **
        (.x10 ↦ᵣ leU32 (bs.drop 16) 0) **
        (.x23 ↦ᵣ leU32 (bs.drop 16) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** F) := by
  simpa using erh_read_addi_site 30 31 32 16 .x23 (16 : BitVec 12)
    listBase bs vOld v5 v6 v10 vDest F hF se12_16
    h_align h_fit h_over h_valid
    (Or.inr (Or.inr (Or.inr rfl))) ⟨rfl, rfl⟩
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl)
    (by rw [erhProgL_len]; decide) (by rfl) (by decide)

end EvmAsm.Codegen.ExecutionRequestsHashReads
