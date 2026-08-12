/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedCallees

  Lift existing `widx_cmp32` / `widx_record_ptr` machine triples onto guest-
  linked PCs and into `WitnessLookupByHashIndexedSpec.fullCode` for callWithin.

  **Depends on PR #12169.** NEW file only — does not edit any #12169 path.
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec
import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.LaResolve
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedCallees

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
open EvmAsm.Crypto
open EvmAsm.Evm64
open EvmAsm.Codegen (laHi laLo)

/-- Guest-linked `widx_cmp32` triple, CodeReq widened to the indexed full image. -/
theorem widx_cmp32_guest_spec
    (ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64)
    (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 293 (Cmp32B : Word) ret fullCode
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
      (widxCmp32Post ptrA ptrB ret as bs) := by
  have h0 := widx_cmp32_spec (Cmp32B : Word) ret ptrA ptrB as bs
    hlenA hlenB halignA halignB hovA hovB hvalidA hvalidB halignRet
  have hcr :
      CodeReq.ofProg (Cmp32B : Word) widxCmp32Prog =
      CodeReq.ofProg (Cmp32B : Word) widxCmp32_prog := by
    rw [widxCmp32Prog_eq_guest]
  have h0' :
      cpsTripleWithin 293 (Cmp32B : Word) ret
        (CodeReq.ofProg (Cmp32B : Word) widxCmp32_prog)
        (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
        (widxCmp32Post ptrA ptrB ret as bs) := by
    rw [← hcr]; exact h0
  exact cpsTripleWithin_extend_code cmp32_in_fullCode h0'

/-! ## `widx_record_ptr` guest lift -/

private abbrev recordPtrHi : BitVec 20 :=
  laHi GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)

private abbrev recordPtrLo : BitVec 12 :=
  laLo GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)

/-- Guest Program is the parameterized body at this linked layout. -/
theorem widxRecordPtr_prog_eq_param :
    widxRecordPtr_prog = widxRecordPtrProg recordPtrHi recordPtrLo := by
  rfl

/-- `widx_record_ptr` at the guest PC, CodeReq widened to fullCode. -/
theorem widx_record_ptr_guest_spec
    (ret : Word) (rf : RegFile)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7 (RecordPtrB : Word) ret fullCode
      (regAtoms rf exposedRegs ** ((.x1 : Reg) ↦ᵣ ret))
      (regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf)
        exposedRegs ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have h0 := widx_record_ptr_spec (RecordPtrB : Word) ret recordPtrHi recordPtrLo rf
    halignRet
  have hcr :
      CodeReq.ofProg (RecordPtrB : Word) (widxRecordPtrProg recordPtrHi recordPtrLo) =
      CodeReq.ofProg (RecordPtrB : Word) widxRecordPtr_prog := by
    rw [widxRecordPtr_prog_eq_param]
  have h0' :
      cpsTripleWithin 7 (RecordPtrB : Word) ret
        (CodeReq.ofProg (RecordPtrB : Word) widxRecordPtr_prog)
        (regAtoms rf exposedRegs ** ((.x1 : Reg) ↦ᵣ ret))
        (regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf)
          exposedRegs ** ((.x1 : Reg) ↦ᵣ ret)) := by
    rw [← hcr]; exact h0
  exact cpsTripleWithin_extend_code record_ptr_in_fullCode h0'

/-! la of `widx_records` from AUIPC PC = RecordPtrB+12 resolves to WidxRecordsBase. -/
set_option maxRecDepth 8000 in
theorem record_ptr_la_eq_base :
    ((RecordPtrB : Word) + 12) +
        ((recordPtrHi.zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 recordPtrLo =
      WidxRecordsBase := by
  simp only [RecordPtrB, recordPtrHi, recordPtrLo, WidxRecordsBase,
    GuestAddrs.widx_record_ptr, GuestAddrs.widx_records, laHi, laLo]
  decide

/-- Index 0: after `widx_record_ptr`, a0 = WidxRecordsBase. -/
theorem widxRecordPtrResult_zero_a0 (rf : RegFile)
    (hidx : rf.get .x10 = (0 : Word)) :
    (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo rf).get .x10 =
      WidxRecordsBase := by
  -- get_set_ne rf r r' v (h : r' ≠ r); get_set_self rf r v (h : r ≠ x0)
  have n10_5 : (.x10 : Reg) ≠ .x5 := by decide
  have n5_6 : (.x5 : Reg) ≠ .x6 := by decide
  have n5_10 : (.x5 : Reg) ≠ .x10 := by decide
  have n5_0 : (.x5 : Reg) ≠ .x0 := by decide
  have n6_0 : (.x6 : Reg) ≠ .x0 := by decide
  have n10_0 : (.x10 : Reg) ≠ .x0 := by decide
  set auipc : Word :=
    (RecordPtrB : Word) + 4 + 4 + 4 +
      ((recordPtrHi.zeroExtend 32 <<< 12).signExtend 64)
  set laV : Word := auipc + signExtend12 recordPtrLo
  -- Named pipeline matching widxRecordPtrResult
  let s1 := rf.set .x5 (rf.get .x10 <<< 5)
  let s2 := s1.set .x6 (s1.get .x10 <<< 4)
  let s3 := s2.set .x5 (s2.get .x5 + s2.get .x6)
  let s4 := s3.set .x10 auipc
  let s5 := s4.set .x10 laV
  let s6 := s5.set .x10 (s5.get .x10 + s5.get .x5)
  -- Goal is s6.get x10 after unfold
  change s6.get .x10 = WidxRecordsBase
  have hs6 : s6.get .x10 = s5.get .x10 + s5.get .x5 :=
    RegFile.get_set_self s5 .x10 _ n10_0
  have hs5_10 : s5.get .x10 = laV := RegFile.get_set_self s4 .x10 laV n10_0
  have hs5_5 : s5.get .x5 = s4.get .x5 :=
    RegFile.get_set_ne s4 .x10 .x5 laV n5_10
  have hs4_5 : s4.get .x5 = s3.get .x5 :=
    RegFile.get_set_ne s3 .x10 .x5 auipc n5_10
  have hs3_5 : s3.get .x5 = s2.get .x5 + s2.get .x6 :=
    RegFile.get_set_self s2 .x5 _ n5_0
  have hs2_5 : s2.get .x5 = s1.get .x5 :=
    RegFile.get_set_ne s1 .x6 .x5 _ n5_6
  have hs2_6 : s2.get .x6 = s1.get .x10 <<< 4 :=
    RegFile.get_set_self s1 .x6 _ n6_0
  have hs1_5 : s1.get .x5 = rf.get .x10 <<< 5 :=
    RegFile.get_set_self rf .x5 _ n5_0
  have hs1_10 : s1.get .x10 = rf.get .x10 :=
    RegFile.get_set_ne rf .x5 .x10 _ n10_5
  have hsum : s5.get .x10 + s5.get .x5 = laV := by
    rw [hs5_10, hs5_5, hs4_5, hs3_5, hs2_5, hs2_6, hs1_5, hs1_10, hidx]
    simp [BitVec.zero_shiftLeft, BitVec.add_zero]
  have hla : laV = WidxRecordsBase := by
    -- Concrete linked layout: discharge by decide on the full la expression.
    simp only [laV, auipc, RecordPtrB, recordPtrHi, recordPtrLo, WidxRecordsBase,
      GuestAddrs.widx_record_ptr, GuestAddrs.widx_records, laHi, laLo]
    decide
  rw [hs6, hsum, hla]

/-! ## Zero-index regAtoms form (for callWithin from one-hit path) -/

/-- Build a RegFile with a0=0 and optional x5/x6 seeds; other regs zero. -/
def zeroIdxRf (v5 v6 : Word) : RegFile :=
  RegFile.set (RegFile.set (RegFile.set (fun _ : Reg => (0 : Word)) .x10 (0 : Word))
    .x5 v5) .x6 v6

theorem zeroIdxRf_x10 (v5 v6 : Word) : (zeroIdxRf v5 v6).get .x10 = (0 : Word) := by
  simp [zeroIdxRf, RegFile.get, RegFile.set]

/-- `widx_record_ptr` with a0=0 via guest regAtoms triple. Fuel 7. -/
theorem widx_record_ptr_zero_sep
    (ret v5 v6 : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7 (RecordPtrB : Word) ret fullCode
      (regAtoms (zeroIdxRf v5 v6) exposedRegs ** ((.x1 : Reg) ↦ᵣ ret))
      (regAtoms (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo
          (zeroIdxRf v5 v6))
        exposedRegs ** ((.x1 : Reg) ↦ᵣ ret)) :=
  widx_record_ptr_guest_spec ret (zeroIdxRf v5 v6) halignRet

/-- After zero-index call, a0 is WidxRecordsBase. -/
theorem widx_record_ptr_zero_a0_of_result (v5 v6 : Word) :
    (widxRecordPtrResult (RecordPtrB : Word) recordPtrHi recordPtrLo
      (zeroIdxRf v5 v6)).get .x10 = WidxRecordsBase :=
  widxRecordPtrResult_zero_a0 (zeroIdxRf v5 v6) (zeroIdxRf_x10 v5 v6)

end EvmAsm.Codegen.WitnessLookupByHashIndexedCallees
