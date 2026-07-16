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


/-! ## The shared return postcondition

    A 3-way disjunction pinning the a0 status and the output region content:
    on success (a0=0, len=256) the output holds the 256 field-6 content bytes
    (`copyIntoRegion`); on a0=2 the field-6 length was ≠256 (output unchanged);
    on a0=1 the RLP parse failed. -/
def helbRetPost (newSp listBase outPtr : Word) (fsaved : HeaderFieldsSpec.Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)) (fo len : Word) (junk : Assertion),
    ((((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x1 ↦ᵣ fsaved.ra) **
       (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) **
       HeaderFieldsSpec.savedFrame newSp fsaved) **
      bytesRegion listBase headerBytes ** bytesRegion outPtr finalOut ** junk) **
     ⌜(a0v = (0 : Word) ∧ Success headerBytes listBase listLen 6 fo len ∧
          len = (256 : Word) ∧
          finalOut = copyIntoRegion outBytes headerBytes 0 fo.toNat 256) ∨
       (a0v = (2 : Word) ∧ Success headerBytes listBase listLen 6 fo len ∧
          len ≠ (256 : Word) ∧ finalOut = outBytes) ∨
       (a0v = (1 : Word) ∧ Failure headerBytes listBase listLen 6)⌝) h

/-! ## Epilogue [40]-[45] (`helbBase+160 → return`)

    Restore `ra/s0/s1/s2`, deallocate the 32-byte frame, `ret`.  The status `a0`
    and the framed rest `Fr` are carried untouched. -/
set_option maxRecDepth 8000 in
theorem helbEpilogue (newSp a0v v1 v8 v9 v18 : Word) (fsaved : HeaderFieldsSpec.Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin 6 (helbBase + 160) (fsaved.ra &&& ~~~(1 : Word)) fullCode
      (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
      (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x1 ↦ᵣ fsaved.ra) **
        (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) **
        HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr) := by
  unfold HeaderFieldsSpec.savedFrame
  have hc0 := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 160) 40
    (.LD .x1 .x2 (0 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hc1 := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 164) 41
    (.LD .x8 .x2 (8 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hc2 := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 168) 42
    (.LD .x9 .x2 (16 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hc3 := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 172) 43
    (.LD .x18 .x2 (24 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hc4 := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 176) 44
    (.ADDI .x2 .x2 (32 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hc5 := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 180) 45
    (.JALR .x0 .x1 (0 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  -- [ld ra, 0(sp)]
  have hl0 := ld_spec_gen_within .x1 .x2 newSp v1 fsaved.ra (0 : BitVec 12) (helbBase + 160) (by decide)
  rw [signExtend12_0, show (newSp + 0 : Word) = newSp from by bv_omega] at hl0
  have el0 := cpsTripleWithin_extend_code hc0 hl0
  have el0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
     ((newSp + 8) ↦ₘ fsaved.s0) ** ((newSp + 16) ↦ₘ fsaved.s1) **
     ((newSp + 24) ↦ₘ fsaved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el0
  -- [ld s0, 8(sp)]
  have hl1 := ld_spec_gen_within .x8 .x2 newSp v8 fsaved.s0 (8 : BitVec 12) (helbBase + 164) (by decide)
  rw [show newSp + signExtend12 (8 : BitVec 12) = newSp + 8 from by
        rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide],
      show (helbBase + 164 : Word) + 4 = helbBase + 168 from by bv_omega] at hl1
  have el1 := cpsTripleWithin_extend_code hc1 hl1
  have el1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ fsaved.ra) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
     (newSp ↦ₘ fsaved.ra) ** ((newSp + 16) ↦ₘ fsaved.s1) ** ((newSp + 24) ↦ₘ fsaved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el1
  -- [ld s1, 16(sp)]
  have hl2 := ld_spec_gen_within .x9 .x2 newSp v9 fsaved.s1 (16 : BitVec 12) (helbBase + 168) (by decide)
  rw [show newSp + signExtend12 (16 : BitVec 12) = newSp + 16 from by
        rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide],
      show (helbBase + 168 : Word) + 4 = helbBase + 172 from by bv_omega] at hl2
  have el2 := cpsTripleWithin_extend_code hc2 hl2
  have el2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ fsaved.ra) ** (.x8 ↦ᵣ fsaved.s0) ** (.x18 ↦ᵣ v18) **
     (newSp ↦ₘ fsaved.ra) ** ((newSp + 8) ↦ₘ fsaved.s0) ** ((newSp + 24) ↦ₘ fsaved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el2
  -- [ld s2, 24(sp)]
  have hl3 := ld_spec_gen_within .x18 .x2 newSp v18 fsaved.s2 (24 : BitVec 12) (helbBase + 172) (by decide)
  rw [show newSp + signExtend12 (24 : BitVec 12) = newSp + 24 from by
        rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide],
      show (helbBase + 172 : Word) + 4 = helbBase + 176 from by bv_omega] at hl3
  have el3 := cpsTripleWithin_extend_code hc3 hl3
  have el3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ fsaved.ra) ** (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) **
     (newSp ↦ₘ fsaved.ra) ** ((newSp + 8) ↦ₘ fsaved.s0) ** ((newSp + 16) ↦ₘ fsaved.s1) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el3
  have hr01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) el0F el1F
  have hr012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hr01 el2F
  have hldF := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hr012 el3F
  -- [addi sp, sp, 32]
  have haddi := addi_spec_gen_same_within .x2 newSp (32 : BitVec 12) (helbBase + 176) (by decide)
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
      rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide],
    show (helbBase + 176 : Word) + 4 = helbBase + 180 from by bv_omega] at haddi
  have haddiE := cpsTripleWithin_extend_code hc4 haddi
  have haddiF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ fsaved.ra) ** (.x8 ↦ᵣ fsaved.s0) **
      (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) ** (newSp ↦ₘ fsaved.ra) **
      ((newSp + 8) ↦ₘ fsaved.s0) ** ((newSp + 16) ↦ₘ fsaved.s1) ** ((newSp + 24) ↦ₘ fsaved.s2)) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) haddiE
  -- [jalr x0, 0(x1)]
  have hjalr := jalr_x0_spec_gen_within .x1 fsaved.ra (0 : BitVec 12) (helbBase + 180)
  simp only [signExtend12_0] at hjalr
  rw [show (fsaved.ra + 0 : Word) = fsaved.ra from by bv_omega] at hjalr
  have hjalrE := cpsTripleWithin_extend_code hc5 hjalr
  have hjalrF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x8 ↦ᵣ fsaved.s0) **
      (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) ** (newSp ↦ₘ fsaved.ra) **
      ((newSp + 8) ↦ₘ fsaved.s0) ** ((newSp + 16) ↦ₘ fsaved.s1) ** ((newSp + 24) ↦ₘ fsaved.s2)) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hjalrE
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hldF haddiF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hjalrF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)


/-! ## Copy-loop helpers -/

private theorem helb_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem helb_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

private theorem helb_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

set_option maxRecDepth 8000 in
/-- One copy-loop body ([29]-[33], `helbBase+116 → helbBase+136`): copy one byte
    from `srcBase[srcOff+i]` to `dstBase[dstOff+i]` and decrement the counter. -/
private theorem helbCopyBody5 (srcBase dstBase x31old : Word)
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
    cpsTripleWithin 5 (helbBase + 116) (helbBase + 136) fullCode
      (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x31 : Reg) ↦ᵣ x31old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x31 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
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
  -- [29] lbu x31, 0(x28)
  have hlbu := bytesRegion_lbu_within .x31 .x28 srcBase x31old (helbBase + 116)
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [show (helbBase + 116 : Word) + 4 = helbBase + 120 from by bv_omega, ← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 116) 29
      (.LBU .x31 .x28 (0 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) hlbu
  have hlbuf := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hlbue
  -- [30] sb x31, 0(x29)
  have hsb := bytesRegion_sb_within .x29 .x31 dstBase (bval.zeroExtend 64) (helbBase + 120)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (helbBase + 120 : Word) + 4 = helbBase + 124 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 120) 30
      (.SB .x29 .x31 (0 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) hsb
  have hsbf := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hsbe
  -- [31] addi x28, x28, 1
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (helbBase + 124) (by decide)
  rw [helb_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (helbBase + 124 : Word) + 4 = helbBase + 128 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 124) 31
      (.ADDI .x28 .x28 (1 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) h3
  have h3f := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x31 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h3e
  -- [32] addi x29, x29, 1
  have h4 := addi_spec_gen_same_within .x29
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (helbBase + 128) (by decide)
  rw [helb_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (helbBase + 128 : Word) + 4 = helbBase + 132 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 128) 32
      (.ADDI .x29 .x29 (1 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) h4
  have h4f := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x31 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h4e
  -- [33] addi x30, x30, -1
  have h5 := addi_spec_gen_same_within .x30 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (helbBase + 132) (by decide)
  rw [helb_succ_dec m, show (helbBase + 132 : Word) + 4 = helbBase + 136 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 132) 33
      (.ADDI .x30 .x30 (-1 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) h5
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x31 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) h5e
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345

set_option maxRecDepth 8000 in
/-- The while-copy loop closure ([28]-[34], `helbBase+112 → helbBase+140`):
    the top `beq x30, x0` exits when the counter hits `0`; each iteration copies
    one byte and re-enters via the unconditional `jal` at [34]. Copies `n` bytes. -/
private theorem helbCopyLoop (srcBase dstBase x31old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff n i : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + i + n ≤ srcBytes.length)
    (h_dst_bound : dstOff + i + n ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_n : n < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * n + 1) (helbBase + 112) (helbBase + 140) fullCode
      (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x31 : Reg) ↦ᵣ x31old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x30 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + n)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + n)))) **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + n))) := by
  have ha_taken : (helbBase + 112 : Word) + signExtend13 (28 : BitVec 13) = helbBase + 140 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_fall : (helbBase + 112 : Word) + 4 = helbBase + 116 := by bv_omega
  have hbeqMem : ∀ a i', CodeReq.singleton (helbBase + 112) (.BEQ .x30 .x0 (28 : BitVec 13)) a = some i'
      → fullCode a = some i' :=
    helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 112) 28
      (.BEQ .x30 .x0 (28 : BitVec 13)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  induction n generalizing i x31old with
  | zero =>
    have hbeq := beq_spec_gen_within .x30 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (helbBase + 112)
    rw [ha_taken] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hbeqMem hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x31 : Reg) ↦ᵣ x31old) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) htaken
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [Nat.add_zero]
        rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
        have hq2 := sepConj_mono_left (regIs_implies_regOwn .x31) _
          (show (((.x31 : Reg) ↦ᵣ x31old) **
            ((.x30 : Reg) ↦ᵣ (0 : Word)) **
            ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
            ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes **
            bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i)) _ from by
            xperm_chunked hq)
        xperm_chunked hq2) htf
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x30 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (helbBase + 112)
    rw [ha_taken, ha_fall] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hbeqMem hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact helb_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x31 : Reg) ↦ᵣ x31old) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hnt
    have hbody := helbCopyBody5 srcBase dstBase x31old srcBytes dstBytes srcOff dstOff i k
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (helbBase + 136)
    rw [show (helbBase + 136 : Word) + signExtend21 (-24 : BitVec 21) = helbBase + 112 from by
      decide] at hjal
    have hjale := cpsTripleWithin_extend_code
      (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 136) 34
        (.JAL .x0 (-24 : BitVec 21)) (by rw [program_length]; norm_num) (by bv_omega) rfl) hjal
    have hjalf := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x31 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | apply pcFree_sepConj) hjale
    rw [sepConj_emp_left'] at hjalf
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega) (by omega)
    -- compose: beq_ntaken ;; body5 ;; jal ;; ih
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hbody
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hjalf
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 hih
    refine cpsTripleWithin_mono_nSteps (nSteps := 7 + (7 * k + 1)) (by omega) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [show i + 1 + k = i + (k + 1) from by omega] at hq
        xperm_chunked hq) s3

/-! ## `la` materialize helpers for the post-call length/offset loads -/

/-- `la x5, helb_length` at [17]-[18] (`helbBase+68 → helbBase+76`). -/
theorem helbLaLen68 (v : Word) :
    cpsTripleWithin 2 (helbBase + 68) (helbBase + 76) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ helbLenAddr) := by
  have hau := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 68) 17
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.helb_length
      (Codegen.GuestAddrs.header_extract_logs_bloom + 68)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have had := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 72) 18
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.helb_length
      (Codegen.GuestAddrs.header_extract_logs_bloom + 68)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have h := la_materialize_within .x5 v (helbBase + 68) helbLenAddr
    (by decide) (by decide) hau had
  rw [show (helbBase + 68 : Word) + 8 = helbBase + 76 from by bv_omega] at h
  exact h

/-- `la x5, helb_offset` at [22]-[23] (`helbBase+88 → helbBase+96`). -/
theorem helbLaOff88 (v : Word) :
    cpsTripleWithin 2 (helbBase + 88) (helbBase + 96) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ helbOffAddr) := by
  have hau := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 88) 22
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.helb_offset
      (Codegen.GuestAddrs.header_extract_logs_bloom + 88)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have had := helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 92) 23
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.helb_offset
      (Codegen.GuestAddrs.header_extract_logs_bloom + 88)))
    (by rw [program_length]; norm_num) (by bv_omega) rfl
  have h := la_materialize_within .x5 v (helbBase + 88) helbOffAddr
    (by decide) (by decide) hau had
  rw [show (helbBase + 88 : Word) + 8 = helbBase + 96 from by bv_omega] at h
  exact h

private theorem helb_ofNat_toNat (fo : Word) : (BitVec.ofNat 64 fo.toNat : Word) = fo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt fo.isLt

/-! ## Terminal tails: set `a0`, jump to the epilogue, return -/

set_option maxRecDepth 8000 in
/-- Success tail ([35]-[36] + epilogue): `li a0, 0 ; jal →+160 ; ret`. -/
private theorem helbTail0 (v10old newSp v1 v8 v9 v18 : Word) (fsaved : HeaderFieldsSpec.Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin (2 + 6) (helbBase + 140) (fsaved.ra &&& ~~~(1 : Word)) fullCode
      (((.x10 ↦ᵣ v10old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x1 ↦ᵣ fsaved.ra) **
        (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) **
        HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr) := by
  have hli := li_spec_gen_within .x10 v10old (0 : Word) (helbBase + 140) (by decide)
  have hlie := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 140) 35 (.LI .x10 (0 : Word))
      (by rw [program_length]; norm_num) (by bv_omega) rfl) hli
  rw [show (helbBase + 140 : Word) + 4 = helbBase + 144 from by bv_omega] at hlie
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have hjal := jal_x0_spec_gen_within (16 : BitVec 21) (helbBase + 144)
  rw [show (helbBase + 144 : Word) + signExtend21 (16 : BitVec 21) = helbBase + 160 from by decide] at hjal
  have hjale := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 144) 36 (.JAL .x0 (16 : BitVec 21))
      (by rw [program_length]; norm_num) (by bv_omega) rfl) hjal
  have hjalf := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hjale
  rw [sepConj_emp_left'] at hjalf
  have hepi := helbEpilogue newSp (0 : Word) v1 v8 v9 v18 fsaved Fr hFr
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjalf
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hepi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)

set_option maxRecDepth 8000 in
/-- Parse-fail tail ([37]-[38] + epilogue): `li a0, 1 ; jal →+160 ; ret`. -/
private theorem helbTail1 (v10old newSp v1 v8 v9 v18 : Word) (fsaved : HeaderFieldsSpec.Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin (2 + 6) (helbBase + 148) (fsaved.ra &&& ~~~(1 : Word)) fullCode
      (((.x10 ↦ᵣ v10old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
      (((.x10 ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x1 ↦ᵣ fsaved.ra) **
        (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) **
        HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr) := by
  have hli := li_spec_gen_within .x10 v10old (1 : Word) (helbBase + 148) (by decide)
  have hlie := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 148) 37 (.LI .x10 (1 : Word))
      (by rw [program_length]; norm_num) (by bv_omega) rfl) hli
  rw [show (helbBase + 148 : Word) + 4 = helbBase + 152 from by bv_omega] at hlie
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (helbBase + 152)
  rw [show (helbBase + 152 : Word) + signExtend21 (8 : BitVec 21) = helbBase + 160 from by decide] at hjal
  have hjale := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 152) 38 (.JAL .x0 (8 : BitVec 21))
      (by rw [program_length]; norm_num) (by bv_omega) rfl) hjal
  have hjalf := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hjale
  rw [sepConj_emp_left'] at hjalf
  have hepi := helbEpilogue newSp (1 : Word) v1 v8 v9 v18 fsaved Fr hFr
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjalf
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hepi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)

set_option maxRecDepth 8000 in
/-- Length-mismatch tail ([39] + epilogue): `li a0, 2 ; ret`. -/
private theorem helbTail2 (v10old newSp v1 v8 v9 v18 : Word) (fsaved : HeaderFieldsSpec.Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin (1 + 6) (helbBase + 156) (fsaved.ra &&& ~~~(1 : Word)) fullCode
      (((.x10 ↦ᵣ v10old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
      (((.x10 ↦ᵣ (2 : Word)) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x1 ↦ᵣ fsaved.ra) **
        (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) **
        HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr) := by
  have hli := li_spec_gen_within .x10 v10old (2 : Word) (helbBase + 156) (by decide)
  have hlie := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 156) 39 (.LI .x10 (2 : Word))
      (by rw [program_length]; norm_num) (by bv_omega) rfl) hli
  rw [show (helbBase + 156 : Word) + 4 = helbBase + 160 from by bv_omega] at hlie
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      HeaderFieldsSpec.savedFrame newSp fsaved) ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame
        repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have hepi := helbEpilogue newSp (2 : Word) v1 v8 v9 v18 fsaved Fr hFr
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hepi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)

/-! ## Post-call: peel the K20 `callReturnResult` into the explicit outcome -/

/-- Peel the `∃ status offset len v11 v12` and the `⌜Result⌝` pure fact from a
    `callReturnResult` precondition, reducing to a per-outcome obligation. -/
private theorem cpsTripleWithin_callReturn_pre
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (h : ∀ status offset len v11 v12,
        Result bytes listBase listLen index oldOffset oldLen status offset len →
        cpsTripleWithin N (helbBase + 64) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q) :
    cpsTripleWithin N (helbBase + 64) ret fullCode
      (((.x1 ↦ᵣ X) **
        callReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen csaved
          bytes listLen index) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold callReturnResult at hcRR
  obtain ⟨status, offset, len, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status offset len v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

/-! ## Post-call: length load ([17]-[20], `helbBase+68 → helbBase+84`)

    `la x5, helb_length ; ld x6, 0(x5) ; li x7, 256`. -/
private theorem helbLenBlock (len v5old v6old v7old : Word) :
    cpsTripleWithin 4 (helbBase + 68) (helbBase + 84) fullCode
      ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (helbLenAddr ↦ₘ len))
      ((.x5 ↦ᵣ helbLenAddr) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (256 : Word)) ** (helbLenAddr ↦ₘ len)) := by
  have f0 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (helbLenAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (helbLaLen68 v5old)
  have h1 := ld_spec_gen_within .x6 .x5 helbLenAddr v6old len (0 : BitVec 12)
    (helbBase + 76) (by decide)
  rw [signExtend12_0, show (helbLenAddr + 0 : Word) = helbLenAddr from by bv_omega,
      show (helbBase + 76 : Word) + 4 = helbBase + 80 from by bv_omega] at h1
  have e1 := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 76) 19
      (.LD .x6 .x5 (0 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) h1
  have f1 := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7old))
    pcFree_regIs e1
  have h2 := li_spec_gen_within .x7 v7old (256 : Word) (helbBase + 80) (by decide)
  rw [show (helbBase + 80 : Word) + 4 = helbBase + 84 from by bv_omega] at h2
  have e2 := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 80) 20
      (.LI .x7 (256 : Word)) (by rw [program_length]; norm_num) (by bv_omega) rfl) h2
  have f2 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ helbLenAddr) ** (.x6 ↦ᵣ len) ** (helbLenAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) e2
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-! ## Post-call: offset load + content-pointer setup ([22]-[27],
    `helbBase+88 → helbBase+112`)

    `la x5, helb_offset ; ld x6, 0(x5) ; add x28, x8, x6 ; mv x29, x18 ;
     li x30, 256`. -/
private theorem helbOffsetSetup (offset listBase outPtr v5old v6old v28old v29old v30old : Word) :
    cpsTripleWithin 6 (helbBase + 88) (helbBase + 112) fullCode
      ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
       (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) ** (helbOffAddr ↦ₘ offset))
      ((.x5 ↦ᵣ helbOffAddr) ** (.x6 ↦ᵣ offset) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
       (.x28 ↦ᵣ (listBase + offset)) ** (.x29 ↦ᵣ outPtr) ** (.x30 ↦ᵣ (256 : Word)) **
       (helbOffAddr ↦ₘ offset)) := by
  have f0 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) **
     (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) ** (helbOffAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (helbLaOff88 v5old)
  have h1 := ld_spec_gen_within .x6 .x5 helbOffAddr v6old offset (0 : BitVec 12)
    (helbBase + 96) (by decide)
  rw [signExtend12_0, show (helbOffAddr + 0 : Word) = helbOffAddr from by bv_omega,
      show (helbBase + 96 : Word) + 4 = helbBase + 100 from by bv_omega] at h1
  have e1 := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 96) 24
      (.LD .x6 .x5 (0 : BitVec 12)) (by rw [program_length]; norm_num) (by bv_omega) rfl) h1
  have f1 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ v29old) **
     (.x30 ↦ᵣ v30old))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj) e1
  have h2 := add_spec_gen_within .x28 .x8 .x6 listBase offset v28old (helbBase + 100) (by decide)
  rw [show (helbBase + 100 : Word) + 4 = helbBase + 104 from by bv_omega] at h2
  have e2 := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 100) 25
      (.ADD .x28 .x8 .x6) (by rw [program_length]; norm_num) (by bv_omega) rfl) h2
  have f2 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ helbOffAddr) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) **
     (helbOffAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) e2
  have h3 := mv_spec_gen_within .x29 .x18 outPtr v29old (helbBase + 104) (by decide)
  rw [show (helbBase + 104 : Word) + 4 = helbBase + 108 from by bv_omega] at h3
  have e3 := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 104) 26
      (.MV .x29 .x18) (by rw [program_length]; norm_num) (by bv_omega) rfl) h3
  have f3 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ helbOffAddr) ** (.x6 ↦ᵣ offset) ** (.x8 ↦ᵣ listBase) **
     (.x28 ↦ᵣ (listBase + offset)) ** (.x30 ↦ᵣ v30old) ** (helbOffAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) e3
  have h4 := li_spec_gen_within .x30 v30old (256 : Word) (helbBase + 108) (by decide)
  rw [show (helbBase + 108 : Word) + 4 = helbBase + 112 from by bv_omega] at h4
  have e4 := cpsTripleWithin_extend_code
    (helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 108) 27
      (.LI .x30 (256 : Word)) (by rw [program_length]; norm_num) (by bv_omega) rfl) h4
  have f4 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ helbOffAddr) ** (.x6 ↦ᵣ offset) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
     (.x28 ↦ᵣ (listBase + offset)) ** (.x29 ↦ᵣ outPtr) ** (helbOffAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) e4
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f0 f1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f2
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f3
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f4
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => by xperm_chunked hp) s4

/-! ## Post-call: copy 256 content bytes then the success tail ([28]-[36]+epilogue,
    `helbBase+112 → return`) -/
set_option maxRecDepth 8000 in
private theorem helbCopyThenTail0
    (offset listBase outPtr newSp x31old v8 v9 a0old v1 : Word) (fsaved : HeaderFieldsSpec.Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : offset.toNat + 256 ≤ headerBytes.length)
    (h_dst_bound : 256 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin ((7 * 256 + 1) + (2 + 6)) (helbBase + 112) (fsaved.ra &&& ~~~(1 : Word)) fullCode
      (((.x30 ↦ᵣ (256 : Word)) ** (.x28 ↦ᵣ (listBase + offset)) ** (.x29 ↦ᵣ outPtr) **
        (.x31 ↦ᵣ x31old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes) **
       ((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ outPtr) ** HeaderFieldsSpec.savedFrame newSp fsaved ** Fr))
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x1 ↦ᵣ fsaved.ra) **
        (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) **
        HeaderFieldsSpec.savedFrame newSp fsaved) **
       ((.x30 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset.toNat + 256))) **
        (.x29 ↦ᵣ (outPtr + (256 : Word))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase headerBytes **
        bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 offset.toNat 256) ** Fr)) := by
  have hcopy := helbCopyLoop listBase outPtr x31old headerBytes outBytes offset.toNat 0 256 0
    h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over (by decide)
    h_src_valid h_dst_valid
  simp only [Nat.add_zero, Nat.zero_add] at hcopy
  rw [show (outPtr + BitVec.ofNat 64 0 : Word) = outPtr from by bv_omega,
      show copyIntoRegion outBytes headerBytes 0 offset.toNat 0 = outBytes from rfl,
      helb_ofNat_toNat offset,
      show (BitVec.ofNat 64 256 : Word) = (256 : Word) from by decide] at hcopy
  have hcopyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
     (.x18 ↦ᵣ outPtr) ** HeaderFieldsSpec.savedFrame newSp fsaved ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hcopy
  have htail := helbTail0 a0old newSp v1 v8 v9 outPtr fsaved
    ((.x30 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset.toNat + 256))) **
     (.x29 ↦ᵣ (outPtr + (256 : Word))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase headerBytes **
     bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 offset.toNat 256) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hcopyF htail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-! ## Post-call: the a0=0 success continuation ([22]-[36]+epilogue,
    `helbBase+88 → return`) -/
set_option maxRecDepth 8000 in
private theorem helbSuccessContinue
    (offset listBase outPtr newSp v5old v6old v28old v29old v30old x31old v9 a0old v1 : Word)
    (fsaved : HeaderFieldsSpec.Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : offset.toNat + 256 ≤ headerBytes.length)
    (h_dst_bound : 256 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 + ((7 * 256 + 1) + (2 + 6))) (helbBase + 88) (fsaved.ra &&& ~~~(1 : Word))
      fullCode
      ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
       (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) ** (.x31 ↦ᵣ x31old) **
       (.x0 ↦ᵣ (0 : Word)) ** (helbOffAddr ↦ₘ offset) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) **
       HeaderFieldsSpec.savedFrame newSp fsaved ** Fr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 32)) ** (.x1 ↦ᵣ fsaved.ra) **
        (.x8 ↦ᵣ fsaved.s0) ** (.x9 ↦ᵣ fsaved.s1) ** (.x18 ↦ᵣ fsaved.s2) **
        HeaderFieldsSpec.savedFrame newSp fsaved) **
       ((.x30 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset.toNat + 256))) **
        (.x29 ↦ᵣ (outPtr + (256 : Word))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase headerBytes **
        bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 offset.toNat 256) **
        ((.x5 ↦ᵣ helbOffAddr) ** (.x6 ↦ᵣ offset) ** (helbOffAddr ↦ₘ offset) ** Fr))) := by
  have hsetup := helbOffsetSetup offset listBase outPtr v5old v6old v28old v29old v30old
  have hsetupF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ x31old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
     bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) **
     (.x9 ↦ᵣ v9) ** HeaderFieldsSpec.savedFrame newSp fsaved ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hsetup
  have hctf := helbCopyThenTail0 offset listBase outPtr newSp x31old listBase v9 a0old v1 fsaved
    headerBytes outBytes ((.x5 ↦ᵣ helbOffAddr) ** (.x6 ↦ᵣ offset) ** (helbOffAddr ↦ₘ offset) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hsetupF hctf
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-! ## Post-call: length-check dispatch ([21]→ret, `helbBase+84`)

    `bne x6, x7, +72`: on `len = 256` fall through to the offset-load / copy /
    success tail (a0=0); on `len ≠ 256` branch to the length-mismatch tail
    (a0=2).  Both arms carry the abstract `Success` fact into `helbRetPost`. -/
set_option maxRecDepth 8000 in
private theorem helbLenDispatch
    (offset len listBase outPtr newSp v5old v28old v29old v30old x31old a0old v1 v9 : Word)
    (fsaved : HeaderFieldsSpec.Saved) (headerBytes outBytes : List (BitVec 8)) (listLen : Nat)
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : offset.toNat + 256 ≤ headerBytes.length)
    (h_dst_bound : 256 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hSucc : Success headerBytes listBase listLen 6 offset len) :
    cpsTripleWithin (1 + (6 + ((7 * 256 + 1) + (2 + 6)))) (helbBase + 84)
      (fsaved.ra &&& ~~~(1 : Word)) fullCode
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x8 ↦ᵣ listBase) **
       (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) **
       (.x31 ↦ᵣ x31old) ** (.x0 ↦ᵣ (0 : Word)) ** (helbOffAddr ↦ₘ offset) **
       (helbLenAddr ↦ₘ len) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) **
       HeaderFieldsSpec.savedFrame newSp fsaved ** Fr)
      (helbRetPost newSp listBase outPtr fsaved headerBytes outBytes listLen) := by
  have ha_t : (helbBase + 84 : Word) + signExtend13 (72 : BitVec 13) = helbBase + 156 := by
    rw [show signExtend13 (72 : BitVec 13) = (72 : Word) from by decide]; bv_omega
  have ha_f : (helbBase + 84 : Word) + 4 = helbBase + 88 := by bv_omega
  have hmono : ∀ a i', CodeReq.singleton (helbBase + 84) (.BNE .x6 .x7 (72 : BitVec 13)) a = some i'
      → fullCode a = some i' :=
    helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 84) 21
      (.BNE .x6 .x7 (72 : BitVec 13)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hbne := bne_spec_gen_within .x6 .x7 (72 : BitVec 13) len (256 : Word) (helbBase + 84)
  rw [ha_t, ha_f] at hbne
  have hbnee := cpsBranchWithin_extend_code hmono hbne
  by_cases hlen : len = (256 : Word)
  · -- fall through: success path (a0=0)
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 hlen)
    have hntF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) **
       (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) ** (.x31 ↦ᵣ x31old) ** (.x0 ↦ᵣ (0 : Word)) **
       (helbOffAddr ↦ₘ offset) ** (helbLenAddr ↦ₘ len) ** bytesRegion listBase headerBytes **
       bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) **
       (.x9 ↦ᵣ v9) ** HeaderFieldsSpec.savedFrame newSp fsaved ** Fr)
      (by unfold HeaderFieldsSpec.savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hnt
    have hsucc := helbSuccessContinue offset listBase outPtr newSp v5old len v28old v29old v30old
      x31old v9 a0old v1 fsaved headerBytes outBytes
      ((.x7 ↦ᵣ (256 : Word)) ** (helbLenAddr ↦ₘ len) ** Fr)
      (by repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
      h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
    have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntF hsucc
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun h hq => ?_) s)
    refine ⟨(0 : Word), copyIntoRegion outBytes headerBytes 0 offset.toNat 256, offset, len,
      (.x30 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset.toNat + 256))) **
      (.x29 ↦ᵣ (outPtr + (256 : Word))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ helbOffAddr) ** (.x6 ↦ᵣ offset) ** (helbOffAddr ↦ₘ offset) **
      (.x7 ↦ᵣ (256 : Word)) ** (helbLenAddr ↦ₘ len) ** Fr, ?_⟩
    exact (sepConj_pure_right _).2 ⟨by xperm_chunked hq, Or.inl ⟨rfl, hSucc, hlen, rfl⟩⟩
  · -- branch taken: length-mismatch tail (a0=2)
    have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hlen ((sepConj_pure_right _).1 hQ).2)
    have htkF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) **
       (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) ** (.x31 ↦ᵣ x31old) ** (.x0 ↦ᵣ (0 : Word)) **
       (helbOffAddr ↦ₘ offset) ** (helbLenAddr ↦ₘ len) ** bytesRegion listBase headerBytes **
       bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) **
       (.x9 ↦ᵣ v9) ** HeaderFieldsSpec.savedFrame newSp fsaved ** Fr)
      (by unfold HeaderFieldsSpec.savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) htk
    have htail := helbTail2 a0old newSp v1 listBase v9 outPtr fsaved
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
       (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) ** (.x31 ↦ᵣ x31old) ** (.x0 ↦ᵣ (0 : Word)) **
       (helbOffAddr ↦ₘ offset) ** (helbLenAddr ↦ₘ len) ** bytesRegion listBase headerBytes **
       bytesRegion outPtr outBytes ** Fr)
      (by repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj)
    have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) htkF htail
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun h hq => ?_) s)
    refine ⟨(2 : Word), outBytes, offset, len,
      (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
      (.x29 ↦ᵣ v29old) ** (.x30 ↦ᵣ v30old) ** (.x31 ↦ᵣ x31old) ** (.x0 ↦ᵣ (0 : Word)) **
      (helbOffAddr ↦ₘ offset) ** (helbLenAddr ↦ₘ len) ** Fr, ?_⟩
    exact (sepConj_pure_right _).2 ⟨by xperm_chunked hq, Or.inr (Or.inl ⟨rfl, hSucc, hlen, rfl⟩)⟩

/-! ## Post-call: the success (status=0) arm ([16]→ret, `helbBase+64`)

    `bne x10, x0, +84` falls through (status is 0), then the length load
    ([17]-[20]) and the length-check dispatch. -/
set_option maxRecDepth 8000 in
private theorem helbOkArm
    (offset len listBase outPtr newSp v5 v6 v7 v28 v29 v30 v31 v1 v9 : Word)
    (fsaved : HeaderFieldsSpec.Saved) (headerBytes outBytes : List (BitVec 8)) (listLen : Nat)
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : offset.toNat + 256 ≤ headerBytes.length)
    (h_dst_bound : 256 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hSucc : Success headerBytes listBase listLen 6 offset len) :
    cpsTripleWithin (1 + (4 + (1 + (6 + ((7 * 256 + 1) + (2 + 6)))))) (helbBase + 64)
      (fsaved.ra &&& ~~~(1 : Word)) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (helbOffAddr ↦ₘ offset) **
       (helbLenAddr ↦ₘ len) ** bytesRegion listBase headerBytes ** (.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** HeaderFieldsSpec.savedFrame newSp fsaved **
       bytesRegion outPtr outBytes ** Fr)
      (helbRetPost newSp listBase outPtr fsaved headerBytes outBytes listLen) := by
  -- [16] bne x10, x0, +84 : not taken (x10 = 0)
  have ha_t : (helbBase + 64 : Word) + signExtend13 (84 : BitVec 13) = helbBase + 148 := by
    rw [show signExtend13 (84 : BitVec 13) = (84 : Word) from by decide]; bv_omega
  have ha_f : (helbBase + 64 : Word) + 4 = helbBase + 68 := by bv_omega
  have hmono : ∀ a i', CodeReq.singleton (helbBase + 64) (.BNE .x10 .x0 (84 : BitVec 13)) a = some i'
      → fullCode a = some i' :=
    helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 64) 16
      (.BNE .x10 .x0 (84 : BitVec 13)) (by rw [program_length]; norm_num) (by bv_omega) rfl
  have hbne := bne_spec_gen_within .x10 .x0 (84 : BitVec 13) (0 : Word) (0 : Word) (helbBase + 64)
  rw [ha_t, ha_f] at hbne
  have hbnee := cpsBranchWithin_extend_code hmono hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have hntF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
     (helbOffAddr ↦ₘ offset) ** (helbLenAddr ↦ₘ len) ** bytesRegion listBase headerBytes **
     (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** HeaderFieldsSpec.savedFrame newSp fsaved **
     bytesRegion outPtr outBytes ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hnt
  -- [17]-[20] length load
  have hlb := helbLenBlock len v5 v6 v7
  have hlbF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
     (helbOffAddr ↦ₘ offset) ** bytesRegion listBase headerBytes **
     (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** HeaderFieldsSpec.savedFrame newSp fsaved **
     bytesRegion outPtr outBytes ** Fr)
    (by unfold HeaderFieldsSpec.savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hlb
  -- [21]→ret length-check dispatch
  have hdisp := helbLenDispatch offset len listBase outPtr newSp helbLenAddr v28 v29 v30 v31
    (0 : Word) v1 v9 fsaved headerBytes outBytes listLen Fr hFr
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
    hSucc
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntF hlbF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hdisp
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => hp) s2)

/-! ## Post-call outcome ([16]→ret, `helbBase+64`)

    Peel the K20 `callReturnResult` (`∃ status offset len` + the `Result`
    relation), then split on the parse `Result`:
      * `ok` (status 0): the `bne x10, x0` falls through into the success arm;
      * `fail` (status 1): the `bne` is taken, jumping to the parse-fail tail
        (a0=1). -/
set_option maxRecDepth 8000 in
private theorem helbPostCallOutcome
    (listBase outPtr newSp indexW oldOffset oldLen : Word)
    (csaved : Saved) (fsaved : HeaderFieldsSpec.Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLen : Nat)
    (hcs0 : csaved.s0 = listBase) (hcs2 : csaved.s2 = outPtr)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_dst_bound : 256 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hbound : ∀ fo ln, Success headerBytes listBase listLen 6 fo ln →
      fo.toNat + 256 ≤ headerBytes.length) :
    cpsTripleWithin (1 + (4 + (1 + (6 + ((7 * 256 + 1) + (2 + 6)))))) (helbBase + 64)
      (fsaved.ra &&& ~~~(1 : Word)) fullCode
      (((.x1 ↦ᵣ (helbBase + 64)) **
        callReturnResult newSp listBase indexW helbOffAddr helbLenAddr oldOffset oldLen csaved
          headerBytes listLen 6) **
       (HeaderFieldsSpec.savedFrame newSp fsaved ** bytesRegion outPtr outBytes))
      (helbRetPost newSp listBase outPtr fsaved headerBytes outBytes listLen) := by
  apply cpsTripleWithin_callReturn_pre newSp listBase indexW helbOffAddr helbLenAddr
    oldOffset oldLen csaved headerBytes listLen 6
  intro status offset len v11 v12 hResult
  cases hResult with
  | ok _ _ hSucc =>
    have hbnd := hbound offset len hSucc
    refine cpsTripleWithin_weaken (fun h hp => by
        simp only [savedRegTail, hcs0, hcs2] at hp; xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn7
        (P := (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ listBase) **
          (.x18 ↦ᵣ outPtr) ** (helbOffAddr ↦ₘ offset) ** (helbLenAddr ↦ₘ len) **
          bytesRegion listBase headerBytes ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (helbBase + 64)) **
          (.x9 ↦ᵣ csaved.s1) ** HeaderFieldsSpec.savedFrame newSp fsaved **
          bytesRegion outPtr outBytes **
          ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
           (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
           stackFree newSp 8))
        (r1 := .x5) (r2 := .x6) (r3 := .x7) (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
        (fun v5 v6 v7 v28 v29 v30 v31 =>
          cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ hq => hq)
            (helbOkArm offset len listBase outPtr newSp v5 v6 v7 v28 v29 v30 v31 (helbBase + 64)
              csaved.s1 fsaved headerBytes outBytes listLen
              ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
               (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
               stackFree newSp 8)
              (by repeat' first
                | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_stackFree _ _
                | apply pcFree_sepConj)
              h_src_align h_dst_align hbnd h_dst_bound h_src_over h_dst_over h_src_valid
              h_dst_valid hSucc)))
  | fail hFail =>
    -- [16] bne x10, x0, +84 : taken (status = 1)
    have ha_t : (helbBase + 64 : Word) + signExtend13 (84 : BitVec 13) = helbBase + 148 := by
      rw [show signExtend13 (84 : BitVec 13) = (84 : Word) from by decide]; bv_omega
    have ha_f : (helbBase + 64 : Word) + 4 = helbBase + 68 := by bv_omega
    have hmono : ∀ a i',
        CodeReq.singleton (helbBase + 64) (.BNE .x10 .x0 (84 : BitVec 13)) a = some i'
        → fullCode a = some i' :=
      helbMem Codegen.headerExtractLogsBloom_prog rfl (helbBase + 64) 16
        (.BNE .x10 .x0 (84 : BitVec 13)) (by rw [program_length]; norm_num) (by bv_omega) rfl
    have hbne := bne_spec_gen_within .x10 .x0 (84 : BitVec 13) (1 : Word) (0 : Word) (helbBase + 64)
    rw [ha_t, ha_f] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono hbne
    have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htkF := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (helbBase + 64)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** (.x8 ↦ᵣ listBase) **
       (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ outPtr) ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
       (.x21 ↦ᵣ csaved.s5) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** bytesRegion listBase headerBytes ** (helbOffAddr ↦ₘ oldOffset) **
       (helbLenAddr ↦ₘ oldLen) ** HeaderFieldsSpec.savedFrame newSp fsaved **
       bytesRegion outPtr outBytes)
      (by unfold HeaderFieldsSpec.savedFrame; repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_stackFree _ _
        | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) htk
    have htail := helbTail1 (1 : Word) newSp (helbBase + 64) listBase csaved.s1 outPtr fsaved
      ((.x0 ↦ᵣ (0 : Word)) ** stackFree newSp 8 ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
       (.x21 ↦ᵣ csaved.s5) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** bytesRegion listBase headerBytes ** (helbOffAddr ↦ₘ oldOffset) **
       (helbLenAddr ↦ₘ oldLen) ** bytesRegion outPtr outBytes)
      (by repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_stackFree _ _
        | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) htkF htail
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by
        simp only [savedRegTail, hcs0, hcs2] at hp; xperm_chunked hp) (fun h hq => ?_) s)
    refine ⟨(1 : Word), outBytes, oldOffset, oldLen,
      (.x0 ↦ᵣ (0 : Word)) ** stackFree newSp 8 ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
      (.x21 ↦ᵣ csaved.s5) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen), ?_⟩
    exact (sepConj_pure_right _).2 ⟨by xperm_chunked hq, Or.inr (Or.inr ⟨rfl, hFail⟩)⟩

/-! ## Whole-program caller contract

    `helbPrologue [0]-[14] ;; the K20 nth-item call [15] ;; the post-call outcome
    [16]→ret`, composed into one raw-pinned `cpsTripleWithin` from `helbBase` to
    the function return (`fsaved.ra &&& ~~~1`).  On the a0=0 success path the
    output region holds the genuine 256-byte field-6 content
    (`copyIntoRegion outBytes headerBytes 0 offset.toNat 256`), tied to the K20
    `Success … 6 offset 256` fact; a0=2 means the field length was ≠256; a0=1
    means the RLP parse failed. -/
set_option maxRecDepth 8000 in
theorem headerExtractLogsBloom_spec_within
    (sp0 newSp listBase outPtr : Word) (fsaved : HeaderFieldsSpec.Saved)
    (s3 s4 s5 v13 v14 oldOffset oldLen : Word)
    (headerBytes outBytes : List (BitVec 8)) (listLen : Nat)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_dst_bound : 256 ≤ outBytes.length)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hbound : ∀ fo ln, Success headerBytes listBase listLen 6 fo ln →
      fo.toNat + 256 ≤ headerBytes.length)
    (h_newSp : newSp = sp0 + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin
      ((15 + (1 + ((12 + ((85 + 93 * (6 + 2)) + 6)) + 9))) +
        (1 + (4 + (1 + (6 + ((7 * 256 + 1) + (2 + 6)))))))
      helbBase (fsaved.ra &&& ~~~(1 : Word)) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt HeaderFieldsSpec.hxFrame
          (HeaderFieldsSpec.savedVals fsaved) **
        frameSlotsOwn HeaderFieldsSpec.hxFrame newSp **
        (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ outPtr) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
        stackFree newSp 8 ** (helbOffAddr ↦ₘ oldOffset) ** (helbLenAddr ↦ₘ oldLen))
      (helbRetPost newSp listBase outPtr fsaved headerBytes outBytes listLen) := by
  have hpro := helbPrologue sp0 listBase (BitVec.ofNat 64 listLen) outPtr fsaved s3 s4 s5 v13 v14
    oldOffset oldLen headerBytes outBytes newSp h_newSp
  have hcall := headerExtractLogsBloom_call_spec_within newSp listBase (BitVec.ofNat 64 listLen)
    (6 : Word) oldOffset oldLen fsaved.ra
    { ra := fsaved.ra, s0 := listBase, s1 := BitVec.ofNat 64 listLen, s2 := outPtr,
      s3 := s3, s4 := s4, s5 := s5 } headerBytes listLen 6
    (HeaderFieldsSpec.savedFrame newSp fsaved ** bytesRegion outPtr outBytes)
    (by repeat' first
      | exact pcFree_memIs | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    rfl (by decide) (by decide) h_src_align h_slack h_src_over h_src_valid
  have hpost := helbPostCallOutcome listBase outPtr newSp (6 : Word) oldOffset oldLen
    { ra := helbBase + 64, s0 := listBase, s1 := BitVec.ofNat 64 listLen, s2 := outPtr,
      s3 := s3, s4 := s4, s5 := s5 } fsaved headerBytes outBytes listLen
    rfl rfl h_src_align h_dst_align h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
    hbound
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold callEntryRest savedRegTail at hp ⊢; xperm_chunked hp) hpro hcall
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 hpost
  exact c2


end EvmAsm.Codegen.HeaderExtractLogsBloomSpec
