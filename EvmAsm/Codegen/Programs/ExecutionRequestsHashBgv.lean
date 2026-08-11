/-
  ExecutionRequestsHashBgv — five `bgv_u32le` callWithin reads of SSZ offsets.

  Geometry (executionRequestsHash_prog @ GuestAddrs.execution_requests_hash):
    B+72  MV a0,s0;     B+76  JAL bgv;  B+80  MV s2,a0   -- dep  @ base+0
    B+84  ADDI a0,s0,4; B+88  JAL bgv;  B+92  MV s3,a0   -- wdr  @ base+4
    … three more ADDI+4 / JAL / MV …

  Callee: `bgv_u32le_offset_spec_within` (BgvOffset) — covers unaligned a0
  (offs 4, 12). Aligned `bgvU32leFlat_spec` is NOT used: Region.wf forces
  p%8=0 and production callers pass unaligned pointers.

  Parent: #11578 rescope (execution_requests_hash validation prefix).
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.BgvU32leSpec
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgvOffset
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.ExecutionRequestsHashBgv

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BgvU32leSpec
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ExecutionRequestsHashBgvOffset

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash
private abbrev BgvB : Word := BitVec.ofNat 64 GuestAddrs.bgv_u32le
private abbrev erhProgL : List Instr := executionRequestsHash_prog

private theorem erhProgL_len : erhProgL.length = 135 := by
  simp only [erhProgL, executionRequestsHash_prog]; decide

private theorem bgvProg_len : bgvU32le_prog.length = 12 := by
  simp only [bgvU32le_prog]; decide

/-- Full code region: wrapper ∪ bgv_u32le. -/
def fullCode : CodeReq :=
  (CodeReq.ofProg B erhProgL).union (CodeReq.ofProg BgvB bgvU32le_prog)

set_option maxRecDepth 8000 in
theorem wrapper_bgv_disjoint :
    (CodeReq.ofProg B erhProgL).Disjoint (CodeReq.ofProg BgvB bgvU32le_prog) := by
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [erhProgL_len]; decide
  · rw [bgvProg_len]; decide
  · rw [erhProgL_len, bgvProg_len]; decide

theorem erhMem (A : Word) (k : Nat) (ins : Instr)
    (hk : k < erhProgL.length)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hins : erhProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  intro a i hs
  unfold fullCode
  exact CodeReq.union_mono_left a i
    (CodeReq.ofProg_mem_at B A erhProgL k ins hA hk hins
      (by rw [erhProgL_len]; decide) a i hs)

theorem bgvCalleeMem : ∀ a i,
    CodeReq.ofProg BgvB bgvU32le_prog a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right wrapper_bgv_disjoint (fun _ _ h => h) a i hi

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < erhProgL.length)
    (hins : erhProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i :=
  erhMem A k ins hk hA hins

/-- JAL target at linked byte offset is always `BgvB`. -/
private theorem jal_target_at (jalByte : Nat)
    (h : jalByte = 76 ∨ jalByte = 88 ∨ jalByte = 100 ∨
         jalByte = 112 ∨ jalByte = 124) :
    B + BitVec.ofNat 64 jalByte +
      signExtend21 (jalOff GuestAddrs.bgv_u32le
        (GuestAddrs.execution_requests_hash + jalByte)) = BgvB := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals (unfold B BgvB jalOff signExtend21; decide)

/-- Return PCs are even. -/
private theorem ret_even_at (retByte : Nat)
    (h : retByte = 80 ∨ retByte = 92 ∨ retByte = 104 ∨
         retByte = 116 ∨ retByte = 128) :
    ((B + BitVec.ofNat 64 retByte : Word) &&& ~~~(1 : Word)) =
      B + BitVec.ofNat 64 retByte := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals (unfold B; decide)

/-- Generic frameless offset-form `bgv_u32le` callWithin at JAL PC `B+jalByte`.

    `a0 = listBase + off` may be unaligned; region is aligned `bytesRegion listBase bs`.
    Association: `((ra ** a0 ** x5 ** x6 ** x0 ** bytes) ** F)`. -/
theorem erh_bgv_callWithin_offset
    (jalByte off : Nat) (listBase : Word) (bs : List (BitVec 8))
    (vOld v5 v6 : Word) (F : Assertion)
    (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : off + 4 ≤ bs.length)
    (h_over : listBase.toNat + (off + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hjal : jalByte = 76 ∨ jalByte = 88 ∨ jalByte = 100 ∨
            jalByte = 112 ∨ jalByte = 124)
    (hk : jalByte / 4 < erhProgL.length)
    (hins : erhProgL[jalByte / 4]'hk =
      .JAL .x1 (jalOff GuestAddrs.bgv_u32le
        (GuestAddrs.execution_requests_hash + jalByte))) :
    cpsTripleWithin 13
      (B + BitVec.ofNat 64 jalByte)
      ((B + BitVec.ofNat 64 jalByte) + 4) fullCode
      (((((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F))
      (((((.x1 ↦ᵣ ((B + BitVec.ofNat 64 jalByte) + 4)) **
        (.x10 ↦ᵣ leU32 (bs.drop off) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F)) := by
  let A : Word := B + BitVec.ofNat 64 jalByte
  let ret : Word := A + 4
  have hretByte : jalByte + 4 = 80 ∨ jalByte + 4 = 92 ∨ jalByte + 4 = 104 ∨
      jalByte + 4 = 116 ∨ jalByte + 4 = 128 := by
    rcases hjal with rfl | rfl | rfl | rfl | rfl <;> decide
  have hretEq : ret = B + BitVec.ofNat 64 (jalByte + 4) := by
    unfold ret A; bv_omega
  have hret : (ret &&& ~~~(1 : Word)) = ret := by
    rw [hretEq]; exact ret_even_at (jalByte + 4) hretByte
  have hcallee0 := bgv_u32le_offset_spec_within listBase off bs ret v5 v6
    h_align h_fit h_over h_valid
  have hcallee1 := cpsTripleWithin_extend_code bgvCalleeMem hcallee0
  -- Exit PC of offset_spec is ret&&&~~~1; pin to ret via hret
  have hcallee2 : cpsTripleWithin 12 BgvB ret fullCode
      (((.x1 ↦ᵣ ret) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs))
      (((.x1 ↦ᵣ ret) **
        (.x10 ↦ᵣ leU32 (bs.drop off) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
    convert hcallee1 using 1
    · exact hret.symm
  have hP :
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs).pcFree := by
    pcf
  have hA : A = B + BitVec.ofNat 64 (4 * (jalByte / 4)) := by
    have : 4 * (jalByte / 4) = jalByte := by
      rcases hjal with rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [A, this]
  have hcall := callWithin_spec A BgvB vOld
    (jalOff GuestAddrs.bgv_u32le (GuestAddrs.execution_requests_hash + jalByte)) 12
    (by
      show A + signExtend21 (jalOff GuestAddrs.bgv_u32le
        (GuestAddrs.execution_requests_hash + jalByte)) = BgvB
      exact jal_target_at jalByte hjal)
    (mem_at (jalByte / 4)
      (.JAL .x1 (jalOff GuestAddrs.bgv_u32le
        (GuestAddrs.execution_requests_hash + jalByte)))
      A hA hk hins)
    hP hcallee2
  have hcallF := cpsTripleWithin_frameR F hF hcall
  -- Fuel 1+12 = 13; A = B+jalByte definitionally via let.
  simpa [A, show (1 + 12 : Nat) = 13 from rfl] using hcallF

theorem erh_bgv_call_76
    (listBase : Word) (bs : List (BitVec 8)) (vOld v5 v6 : Word) (F : Assertion)
    (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 0 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (0 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 13 (B + 76) ((B + 76) + 4) fullCode
      (((((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 0)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F))
      (((((.x1 ↦ᵣ ((B + 76) + 4)) **
        (.x10 ↦ᵣ leU32 (bs.drop 0) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F)) :=
  erh_bgv_callWithin_offset 76 0 listBase bs vOld v5 v6 F hF
    h_align h_fit h_over h_valid (Or.inl rfl)
    (by rw [erhProgL_len]; decide) (by rfl)

theorem erh_bgv_call_88
    (listBase : Word) (bs : List (BitVec 8)) (vOld v5 v6 : Word) (F : Assertion)
    (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 4 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (4 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 13 (B + 88) ((B + 88) + 4) fullCode
      (((((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 4)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F))
      (((((.x1 ↦ᵣ ((B + 88) + 4)) **
        (.x10 ↦ᵣ leU32 (bs.drop 4) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F)) :=
  erh_bgv_callWithin_offset 88 4 listBase bs vOld v5 v6 F hF
    h_align h_fit h_over h_valid (Or.inr (Or.inl rfl))
    (by rw [erhProgL_len]; decide) (by rfl)

theorem erh_bgv_call_100
    (listBase : Word) (bs : List (BitVec 8)) (vOld v5 v6 : Word) (F : Assertion)
    (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 8 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (8 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 13 (B + 100) ((B + 100) + 4) fullCode
      (((((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 8)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F))
      (((((.x1 ↦ᵣ ((B + 100) + 4)) **
        (.x10 ↦ᵣ leU32 (bs.drop 8) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F)) :=
  erh_bgv_callWithin_offset 100 8 listBase bs vOld v5 v6 F hF
    h_align h_fit h_over h_valid (Or.inr (Or.inr (Or.inl rfl)))
    (by rw [erhProgL_len]; decide) (by rfl)

theorem erh_bgv_call_112
    (listBase : Word) (bs : List (BitVec 8)) (vOld v5 v6 : Word) (F : Assertion)
    (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 12 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (12 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 13 (B + 112) ((B + 112) + 4) fullCode
      (((((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 12)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F))
      (((((.x1 ↦ᵣ ((B + 112) + 4)) **
        (.x10 ↦ᵣ leU32 (bs.drop 12) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F)) :=
  erh_bgv_callWithin_offset 112 12 listBase bs vOld v5 v6 F hF
    h_align h_fit h_over h_valid (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by rw [erhProgL_len]; decide) (by rfl)

theorem erh_bgv_call_124
    (listBase : Word) (bs : List (BitVec 8)) (vOld v5 v6 : Word) (F : Assertion)
    (hF : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 16 + 4 ≤ bs.length)
    (h_over : listBase.toNat + (16 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 13 (B + 124) ((B + 124) + 4) fullCode
      (((((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 16)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F))
      (((((.x1 ↦ᵣ ((B + 124) + 4)) **
        (.x10 ↦ᵣ leU32 (bs.drop 16) 0) **
        regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) ** F)) :=
  erh_bgv_callWithin_offset 124 16 listBase bs vOld v5 v6 F hF
    h_align h_fit h_over h_valid (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by rw [erhProgL_len]; decide) (by rfl)

end EvmAsm.Codegen.ExecutionRequestsHashBgv
