/-
  EvmAsm.Codegen.Programs.HeaderExtractLogsBloomSpec

  The whole-program caller contract `headerExtractLogsBloom_spec_within` for
  `headerExtractLogsBloom_prog` (`Bloom.lean`, 46 instrs).  The routine extracts
  the header's `logs_bloom` field (RLP field index 6, a 256-byte value) via one
  `rlp_list_nth_item` call, checks the parse status and the field length
  (`= 256`), and byte-copies the 256-byte content into a caller-supplied output
  region.

  This maps directly onto the `receipt_extract_logs_bloom` sibling (byte-identical
  program up to field index 6-vs-2 and header-vs-receipt addresses) and reuses:
    - `RlpListNthItemSAsm.rlpListNthItem_call_spec_within` for the nth-item call
      (via the header analog `headerExtractLogsBloom_call_spec_within`, mirroring
      `ReceiptExtractLogsBloomCallSAsm.receiptExtractLogsBloom_call_spec_within`);
    - the header-root extractors' `copyIntoRegion` content-tie machinery
      (`copyIntoRegion`/`copyIntoRegion_length` from `ReturnWindowLoopSpec`).

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Rv64.SAsm.GlobalData
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.LaResolve
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec

namespace EvmAsm.Codegen.HeaderExtractLogsBloomSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Guest entry of `header_extract_logs_bloom`. -/
abbrev helbBase : Word := (Codegen.GuestAddrs.header_extract_logs_bloom : Word)
/-- Guest entry of `rlp_list_nth_item`. -/
abbrev K20B : Word := (Codegen.GuestAddrs.rlp_list_nth_item : Word)
/-- The global scratch offset cell. -/
abbrev helbOffAddr : Word := (Codegen.GuestAddrs.helb_offset : Word)
/-- The global scratch length cell. -/
abbrev helbLenAddr : Word := (Codegen.GuestAddrs.helb_length : Word)

theorem program_length : Codegen.headerExtractLogsBloom_prog.length = 46 := by decide

/-- The `header_extract_logs_bloom` body at its linked guest address. -/
def wrapperCode : CodeReq := CodeReq.ofProg helbBase Codegen.headerExtractLogsBloom_prog

/-- The whole linked image: the wrapper body ∪ the `rlp_list_nth_item` callee. -/
def fullCode : CodeReq :=
  wrapperCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem wrapper_list_disjoint :
    wrapperCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold wrapperCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [program_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide

/-- Discharge one `CodeReq.singleton A ins` membership fact for the wrapper body
    via `ofProg_mem_at` composed into `fullCode`. -/
theorem helbMem (prog : List Instr) (hprog : prog = Codegen.headerExtractLogsBloom_prog)
    (A : Word) (k : Nat) (ins : Instr)
    (hk : k < prog.length)
    (hA : A = helbBase + BitVec.ofNat 64 (4 * k))
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  subst hprog
  intro a i hs
  unfold fullCode
  apply CodeReq.union_mono_left
  exact CodeReq.ofProg_mem_at helbBase A Codegen.headerExtractLogsBloom_prog k ins hA hk hins
    (by rw [program_length]; norm_num) a i hs

/-- The `rlp_list_nth_item` callee code is contained in `fullCode`. -/
theorem helbCalleeMem : ∀ a i,
    EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right wrapper_list_disjoint (fun _ _ h => h) a i hi

/-! ## The nth-item call ([15], `helbBase+60 → helbBase+64`)

    Header analog of `receiptExtractLogsBloom_call_spec_within`: the single K20
    `rlp_list_nth_item` call on field index 6, exposed through the strict K20 call
    adapter. -/
set_option maxRecDepth 8000 in
theorem headerExtractLogsBloom_call_spec_within
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
      (helbBase + 60) (helbBase + 64) fullCode
      (((.x1 ↦ᵣ vOld) **
        callEntryRest sp0 listBase listLenW indexW helbOffAddr helbLenAddr
          oldOffset oldLen { saved with ra := helbBase + 64 } bytes) ** F)
      (((.x1 ↦ᵣ (helbBase + 64)) **
        callReturnResult sp0 listBase indexW helbOffAddr helbLenAddr
          oldOffset oldLen { saved with ra := helbBase + 64 } bytes listLen index) ** F) := by
  have htarget :
      (helbBase + 60) + signExtend21
        (jalOff Codegen.GuestAddrs.rlp_list_nth_item
          (Codegen.GuestAddrs.header_extract_logs_bloom + 60)) = K20B := by
    decide
  have hmem : ∀ a i,
      CodeReq.singleton (helbBase + 60)
          (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_list_nth_item
            (Codegen.GuestAddrs.header_extract_logs_bloom + 60))) a = some i →
        fullCode a = some i :=
    helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 60) 15
      (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_list_nth_item
        (Codegen.GuestAddrs.header_extract_logs_bloom + 60)))
      (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hret : ((helbBase + 60) + 4) &&& ~~~(1 : Word) = (helbBase + 60) + 4 := by decide
  have h := rlpListNthItem_call_spec_within (cr := fullCode)
    (callerPC := helbBase + 60) (calleeEntry := K20B) vOld sp0 listBase listLenW
    indexW helbOffAddr helbLenAddr oldOffset oldLen
    (jalOff Codegen.GuestAddrs.rlp_list_nth_item
      (Codegen.GuestAddrs.header_extract_logs_bloom + 60)) F hF saved bytes listLen index
    hlistLenW hindexW hindex hsalign hslack hover hvalid hret htarget rfl hmem
    helbCalleeMem
  exact h

#print axioms headerExtractLogsBloom_call_spec_within

end EvmAsm.Codegen.HeaderExtractLogsBloomSpec
