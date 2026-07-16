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
import EvmAsm.Codegen.Programs.HeaderFieldsGenericInit
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

/-! ## `la` materialize helpers (address-specific AUIPC hi/lo) -/

/-- `la x13, helb_offset` at [11]-[12] (`helbBase+44 → helbBase+52`). -/
theorem helbLaOff44 (v : Word) :
    cpsTripleWithin 2 (helbBase + 44) (helbBase + 52) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ helbOffAddr) := by
  have hau := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 44) 11
    (.AUIPC .x13 (Codegen.laHi Codegen.GuestAddrs.helb_offset
      (Codegen.GuestAddrs.header_extract_logs_bloom + 44)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have had := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 48) 12
    (.ADDI .x13 .x13 (Codegen.laLo Codegen.GuestAddrs.helb_offset
      (Codegen.GuestAddrs.header_extract_logs_bloom + 44)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have h := la_materialize_within .x13 v (helbBase + 44) helbOffAddr
    (by decide) (by decide) hau had
  rw [show (helbBase + 44 : Word) + 8 = helbBase + 52 from by bv_omega] at h
  exact h

/-- `la x14, helb_length` at [13]-[14] (`helbBase+52 → helbBase+60`). -/
theorem helbLaLen52 (v : Word) :
    cpsTripleWithin 2 (helbBase + 52) (helbBase + 60) fullCode
      (.x14 ↦ᵣ v) (.x14 ↦ᵣ helbLenAddr) := by
  have hau := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 52) 13
    (.AUIPC .x14 (Codegen.laHi Codegen.GuestAddrs.helb_length
      (Codegen.GuestAddrs.header_extract_logs_bloom + 52)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have had := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 56) 14
    (.ADDI .x14 .x14 (Codegen.laLo Codegen.GuestAddrs.helb_length
      (Codegen.GuestAddrs.header_extract_logs_bloom + 52)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have h := la_materialize_within .x14 v (helbBase + 52) helbLenAddr
    (by decide) (by decide) hau had
  rw [show (helbBase + 52 : Word) + 8 = helbBase + 60 from by bv_omega] at h
  exact h

/-! ## Prologue [0]-[14] (`helbBase → helbBase+60`)

    Allocate the 32-byte frame, save `ra/s0/s1/s2`, marshal the ABI inputs into
    the K20 argument registers (`x10=rlp ptr`, `x11=len`, `x12=6`), and
    materialize the two scratch-cell addresses (`x13=helb_offset`,
    `x14=helb_length`).  The post is exactly the K20 call precondition
    (`callEntryRest`), plus the saved frame and the pass-through output region. -/
set_option maxRecDepth 8000 in
theorem helbPrologue
    (sp0 listBase listLenW outPtr : Word) (fsaved : HeaderFieldsSpec.Saved)
    (s3 s4 s5 v13 v14 oldOffset oldLen : Word)
    (headerBytes outBytes : List (BitVec 8)) (newSp : Word)
    (h_newSp : newSp = sp0 + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin 15 helbBase (helbBase + 60) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt HeaderFieldsSpec.hxFrame
          (HeaderFieldsSpec.savedVals fsaved) **
        frameSlotsOwn HeaderFieldsSpec.hxFrame newSp **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ outPtr) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
      (((.x1 ↦ᵣ fsaved.ra) **
        callEntryRest newSp listBase listLenW (6 : Word) helbOffAddr helbLenAddr
          oldOffset oldLen
          { ra := fsaved.ra, s0 := listBase, s1 := listLenW, s2 := outPtr,
            s3 := s3, s4 := s4, s5 := s5 } headerBytes) **
        HeaderFieldsSpec.savedFrame newSp fsaved ** bytesRegion outPtr outBytes) := by
  -- [0] addi sp, sp, -32
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) helbBase (by decide)
  rw [← h_newSp] at ha0
  have ha := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl helbBase 0
      (.ADDI .x2 .x2 (-32 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) ha0
  rw [show helbBase + 4 = helbBase + 4 from rfl] at ha
  have haF := cpsTripleWithin_frameR
    (regsAt HeaderFieldsSpec.hxFrame (HeaderFieldsSpec.savedVals fsaved) **
      frameSlotsOwn HeaderFieldsSpec.hxFrame newSp **
      (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ outPtr) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
      stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
    (by repeat' first
      | exact pcFree_regsAt _ _ | exact pcFree_frameSlotsOwn _ _
      | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | apply pcFree_sepConj) ha
  -- [1]-[4] store sequence
  have hstoreMono : ∀ a i,
      CodeReq.ofProg (helbBase + 4) (storeProg HeaderFieldsSpec.hxFrame) a = some i →
        fullCode a = some i := by
    intro a i h_mem
    unfold fullCode
    apply CodeReq.union_mono_left
    exact CodeReq.ofProg_mono_sub helbBase (helbBase + 4)
      Codegen.headerExtractLogsBloom_prog (storeProg HeaderFieldsSpec.hxFrame) 1
      (by bv_omega) rfl (by rw [program_length]; simp [HeaderFieldsSpec.hxFrame])
      (by rw [program_length]; norm_num) a i h_mem
  have hs0 := storeSeq_spec HeaderFieldsSpec.hxFrame newSp
    (HeaderFieldsSpec.savedVals fsaved) (helbBase + 4) (by decide)
  have hs := cpsTripleWithin_extend_code hstoreMono hs0
  rw [show helbBase + 4 + BitVec.ofNat 64 (4 * HeaderFieldsSpec.hxFrame.length) = helbBase + 20 from by
    simp [HeaderFieldsSpec.hxFrame]; bv_omega] at hs
  have hsF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ outPtr) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
      stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
    (by repeat' first
      | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | apply pcFree_sepConj) hs
  -- [5]-[9] register moves
  have hm := HeaderFieldsSpec.hfSetupMoves5 (code := fullCode) helbBase listBase listLenW outPtr
    fsaved.s0 fsaved.s1 fsaved.s2
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 20) 5 (.MV .x8 .x10)
      (by rw [program_length]; norm_num) (by bv_omega) rfl)
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 24) 6 (.MV .x9 .x11)
      (by rw [program_length]; norm_num) (by bv_omega) rfl)
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 28) 7 (.MV .x18 .x12)
      (by rw [program_length]; norm_num) (by bv_omega) rfl)
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 32) 8 (.MV .x10 .x8)
      (by rw [program_length]; norm_num) (by bv_omega) rfl)
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 36) 9 (.MV .x11 .x9)
      (by rw [program_length]; norm_num) (by bv_omega) rfl)
  have hmF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ fsaved.ra) ** HeaderFieldsSpec.savedFrame newSp fsaved **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
      stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first
        | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | apply pcFree_sepConj) hm
  -- [10] li x12, 6
  have hli := li_spec_gen_within .x12 outPtr (6 : Word) (helbBase + 40) (by decide)
  have hlie := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 40) 10 (.LI .x12 (6 : Word))
      (by rw [program_length]; norm_num) (by bv_omega) rfl) hli
  rw [show (helbBase + 40 : Word) + 4 = helbBase + 44 from by bv_omega] at hlie
  have hliF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ fsaved.ra) ** HeaderFieldsSpec.savedFrame newSp fsaved **
      (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) ** (.x18 ↦ᵣ outPtr) **
      (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
      stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first
        | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | apply pcFree_sepConj) hlie
  -- [11]-[12] la x13, helb_offset ; [13]-[14] la x14, helb_length
  have hla13 := helbLaOff44 v13
  have hla13F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ fsaved.ra) ** HeaderFieldsSpec.savedFrame newSp fsaved **
      (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) ** (.x18 ↦ᵣ outPtr) **
      (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (6 : Word)) **
      (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
      stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first
        | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | apply pcFree_sepConj) hla13
  have hla14 := helbLaLen52 v14
  have hla14F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ fsaved.ra) ** HeaderFieldsSpec.savedFrame newSp fsaved **
      (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) ** (.x18 ↦ᵣ outPtr) **
      (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (6 : Word)) **
      (.x13 ↦ᵣ helbOffAddr) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
      stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first
        | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | apply pcFree_sepConj) hla14
  -- compose
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) haF hsF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [HeaderFieldsSpec.regsAt_hxFrame, HeaderFieldsSpec.frameSlotsSaved_hxFrame] at hp
    xperm_chunked hp) c01 hmF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c012 hliF
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0123 hla13F
  have call := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01234 hla14F
  refine cpsTripleWithin_mono_nSteps (by simp only [HeaderFieldsSpec.hxFrame_length]; omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by
      unfold callEntryRest entryRest savedRegTail
      xperm_chunked hq) call)

#print axioms helbPrologue

end EvmAsm.Codegen.HeaderExtractLogsBloomSpec
