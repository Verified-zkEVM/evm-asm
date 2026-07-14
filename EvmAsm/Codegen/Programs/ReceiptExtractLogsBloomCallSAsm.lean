/-
  Call-site contract for K152 `receipt_extract_logs_bloom`.

  The routine has one K20 NTH_ITEM call (receipt field 2).  This theorem
  exposes that call through the shared, strict K20 adapter; the remaining
  status/length branches and the 256-byte copy are composed by the caller
  proof.
-/

import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Rv64.SAsm.GlobalData

namespace EvmAsm.Codegen.ReceiptExtractLogsBloomCallSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

abbrev B : Word := (GuestAddrs.receipt_extract_logs_bloom : Word)
abbrev K20B : Word := (GuestAddrs.rlp_list_nth_item : Word)
abbrev offsetCell : Word := (GuestAddrs.relb_offset : Word)
abbrev lengthCell : Word := (GuestAddrs.relb_length : Word)

theorem program_length : receiptExtractLogsBloom_prog.length = 46 := by decide

#guard receiptExtractLogsBloom_prog.length = 46
#guard (CodeReq.ofProg 0 receiptExtractLogsBloom_prog 0).isSome

def wrapperCode : CodeReq := CodeReq.ofProg B receiptExtractLogsBloom_prog

def code : CodeReq :=
  wrapperCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem wrapper_list_disjoint :
    wrapperCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold wrapperCode EvmAsm.Codegen.RlpListNthItemSAsm.code B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]
    decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide
  · rw [program_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide

theorem receiptExtractLogsBloom_call_spec_within
    (sp0 listBase listLenW indexW oldOffset oldLen vOld : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9))
      (B + 60) (B + 64) code
      (((.x1 ↦ᵣ vOld) **
        callEntryRest sp0 listBase listLenW indexW offsetCell lengthCell
          oldOffset oldLen { saved with ra := B + 64 } bytes) ** F)
      (((.x1 ↦ᵣ (B + 64)) **
        callReturnResult sp0 listBase indexW offsetCell lengthCell
          oldOffset oldLen { saved with ra := B + 64 } bytes listLen index) ** F) := by
  have htarget :
      (B + 60) + signExtend21
        (jalOff GuestAddrs.rlp_list_nth_item
          (GuestAddrs.receipt_extract_logs_bloom + 60)) = K20B := by
    unfold B K20B
    decide
  have hmem : ∀ a i,
      CodeReq.singleton (B + 60)
          (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
            (GuestAddrs.receipt_extract_logs_bloom + 60))) a = some i →
        code a = some i := by
    intro a i hi
    unfold code
    apply CodeReq.union_mono_left
    exact CodeReq.ofProg_mem_at B (B + 60) receiptExtractLogsBloom_prog 15
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.receipt_extract_logs_bloom + 60))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide) a i hi
  have hcalleeMem : ∀ a i,
      EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → code a = some i := by
    intro a i hi
    unfold code
    exact CodeReq.mono_union_right wrapper_list_disjoint (fun _ _ h => h) a i hi
  have hret : ((B + 60) + 4) &&& ~~~(1 : Word) = (B + 60) + 4 := by
    decide
  have h := rlpListNthItem_call_spec_within (cr := code)
    (callerPC := B + 60) (calleeEntry := K20B) vOld sp0 listBase listLenW
    indexW offsetCell lengthCell oldOffset oldLen
    (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.receipt_extract_logs_bloom + 60)) F hF saved bytes listLen index
    hlistLenW hindexW hindex hsalign hslack hover hvalid hret htarget rfl hmem
    hcalleeMem
  simpa [B, K20B] using h

#print axioms receiptExtractLogsBloom_call_spec_within

end EvmAsm.Codegen.ReceiptExtractLogsBloomCallSAsm
