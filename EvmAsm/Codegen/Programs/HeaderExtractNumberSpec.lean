/-
  Caller contract for the 8-instruction `header_extract_number` wrapper.

  `headerExtractNumber_prog` allocates a 16-byte frame, saves `ra`, shuffles
  its arguments (`a3 := a2` output pointer, `a2 := 8` field index), tail-calls
  the verified lenient `rlp_field_to_u64` selector, then restores `ra`,
  deallocates, and returns.  Its whole-program contract is therefore

      prologue  ;;  rlpFieldToU64_flat_spec_within  ;;  epilogue

  and its success post pins the caller's output cell to the
  big-endian decode of the real field-8 content (via K34's `Result`).
-/

import EvmAsm.Codegen.Programs.RlpFieldToU64FlatSAsm
import EvmAsm.Codegen.Programs.HeaderU64

namespace EvmAsm.Codegen.HeaderExtractNumberSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64SAsm

/-! ## Base addresses and linked code

    Header field 8 (`number`) is `Uint` in the reference model, so this
    wrapper intentionally uses the lenient K34 path.  The machine-side width
    assumption remains explicit in the bridge below. -/

abbrev H : Word := (GuestAddrs.header_extract_number : Word)

theorem hdr_length : headerExtractNumber_prog.length = 8 := by decide

/-- The wrapper's own re-emitted instructions at `header_extract_number`. -/
def hdrCode : CodeReq := CodeReq.ofProg H headerExtractNumber_prog

/-- The full linked closure: this wrapper plus the lenient K34 selector and its
    transitive callees. -/
def fullCode : CodeReq := hdrCode.union EvmAsm.Codegen.RlpFieldToU64SAsm.code

theorem hdr_disjoint :
    hdrCode.Disjoint EvmAsm.Codegen.RlpFieldToU64SAsm.code := by
  unfold hdrCode EvmAsm.Codegen.RlpFieldToU64SAsm.code
  refine CodeReq.Disjoint.union_right ?_
    (CodeReq.Disjoint.union_right ?_ ?_)
  · unfold EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode
      EvmAsm.Codegen.RlpFieldToU64SAsm.B H
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [hdr_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
    · rw [hdr_length, EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
  · unfold EvmAsm.Codegen.RlpListNthItemSAsm.code
      EvmAsm.Codegen.RlpListNthItemSAsm.B H
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [hdr_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · rw [hdr_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode
      rlp_content_to_u64_code EvmAsm.Codegen.RlpFieldToU64SAsm.C64B H
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [hdr_length]; decide
    · rw [rlp_content_to_u64_prog_length]; decide
    · rw [hdr_length, rlp_content_to_u64_prog_length]; decide


/-- K34's linked code is subsumed by the wrapper's full closure. -/
theorem k34_mono :
    ∀ a i, EvmAsm.Codegen.RlpFieldToU64SAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right hdr_disjoint (fun _ _ h => h) a i hi

theorem hdr_mono : ∀ a i, hdrCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-! ## Caller-facing pre/post -/

/-- Pre-prologue caller footprint.  `a0/a1/a2 = listBase/listLenW/outputPtr`,
    `x8/x9 = s0In/s1In` (callee-saved, threaded), the K34 stack region
    (`frameSlotsOwn frame newSp ** stackFree newSp 8`) and the wrapper's own
    return slot (`spH ↦ₘ oldRaSlot`). -/
def hdrPre
    (sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13 old14
      oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (spH ↦ₘ oldRaSlot) **
  (.x8 ↦ᵣ s0In) ** (.x9 ↦ᵣ s1In) ** frameSlotsOwn frame newSp **
  stackFree newSp 8 **
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ outputPtr) **
  (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (outputPtr ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) **
  (lengthCell ↦ₘ oldLen)

/-- Success return: `a0 = 0` (or the empty join encoded in K34's `Result`),
    and the output cell `saved.s1 = outputPtr` holds the big-endian decode of
    the field-8 content (pinned inside `successPayload`'s
    `Result`). -/
def hdrSuccess
    (sp0 spH newSp raIn listBase : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ offset len v12 x5 scalarStatus wrapperStatus outputValue,
    ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) **
      ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
       successPayload newSp listBase offset len v12 x5 scalarStatus
         wrapperStatus outputValue saved bytes listLen 8)) h

/-- Failure return: `a0 = 1` and the output cell is zeroed. -/
def hdrFailure
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) **
      ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
       failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
         listLen 8)) h

def hdrPost
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h =>
    hdrSuccess sp0 spH newSp raIn listBase outer saved bytes listLen h ∨
    hdrFailure sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
      listLen h

/-! ## Prologue (instructions 0--3) -/

set_option maxRecDepth 8000 in
/-- Allocate the 16-byte frame, save `ra`, and shuffle arguments so the pre
    is exactly K34's `flatPre` (framed by the wrapper's own saved-`ra`). -/
theorem hdrPrologue
    (sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13 old14
      oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 : Word)
    (outer : Saved) (bytes : List (BitVec 8))
    (houter : outer = { ra := H + 20, s0 := s0In, s1 := s1In })
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12)) :
    cpsTripleWithin 4 H (H + 16) fullCode
      (hdrPre sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13
        old14 oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 bytes)
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
       flatPre spH newSp listBase listLenW (8 : Word) outputPtr oldOut
         oldOffset oldLen old14 outer s2 s3 s4 s5 bytes) := by
  -- [0] ADDI x2 x2 -16 : sp0 → spH
  have h0 := addi_spec_gen_same_within .x2 sp0 (-16 : BitVec 12) H (by decide)
  rw [← hspH] at h0
  have h0' := cpsTripleWithin_extend_code (cr' := hdrCode)
    (CodeReq.ofProg_mem_at H H headerExtractNumber_prog 0
      (.ADDI .x2 .x2 (-16 : BitVec 12)) (by decide) (by rw [hdr_length]; decide)
      rfl (by rw [hdr_length]; decide)) h0
  -- [1] SD x2 x1 0 : store raIn at [spH]
  have h1 := sd_spec_gen_within .x2 .x1 spH raIn oldRaSlot (0 : BitVec 12) (H + 4)
  rw [show spH + signExtend12 (0 : BitVec 12) = spH from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := hdrCode)
    (CodeReq.ofProg_mem_at H (H + 4) headerExtractNumber_prog 1
      (.SD .x2 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [hdr_length]; decide)
      rfl (by rw [hdr_length]; decide)) h1
  -- [2] MV x13 x12 : x13 := outputPtr
  have h2 := mv_spec_gen_within .x13 .x12 outputPtr old13 (H + 8) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := hdrCode)
    (CodeReq.ofProg_mem_at H (H + 8) headerExtractNumber_prog 2 (.MV .x13 .x12)
      (by bv_omega) (by rw [hdr_length]; decide) rfl
      (by rw [hdr_length]; decide)) h2
  -- [3] LI x12 8 : x12 := 8
  have h3 := li_spec_gen_within .x12 outputPtr (8 : Word) (H + 12) (by decide)
  have h3' := cpsTripleWithin_extend_code (cr' := hdrCode)
    (CodeReq.ofProg_mem_at H (H + 12) headerExtractNumber_prog 3
      (.LI .x12 (8 : Word)) (by bv_omega) (by rw [hdr_length]; decide) rfl
      (by rw [hdr_length]; decide)) h3
  -- Frame everything each instruction does not touch.
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ oldRaSlot) ** (.x12 ↦ᵣ outputPtr) **
      (.x13 ↦ᵣ old13)) (by pcf) h0'
  have h1F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ outputPtr) ** (.x13 ↦ᵣ old13)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn))
    (by pcf) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x13 ↦ᵣ outputPtr))
    (by pcf) h3'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 h3F
  -- The active four registers/cell, established.
  have hlocal : cpsTripleWithin 4 H (H + 16) hdrCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ oldRaSlot) **
        (.x12 ↦ᵣ outputPtr) ** (.x13 ↦ᵣ old13))
      ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
        (.x12 ↦ᵣ (8 : Word)) ** (.x13 ↦ᵣ outputPtr)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0123
  -- Frame the untouched remainder (inlined so `xperm` sees concrete atoms).
  have hframed := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ s0In) ** (.x9 ↦ᵣ s1In) ** frameSlotsOwn frame newSp **
      stackFree newSp 8 **
      (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x14 ↦ᵣ old14) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
      (outputPtr ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) **
      (lengthCell ↦ₘ oldLen)) (by pcf) hlocal
  have hall := cpsTripleWithin_extend_code hdr_mono hframed
  subst houter
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold hdrPre at hp
      xperm_hyp hp) (fun h hq => by
      unfold flatPre wholeRest
      xperm_hyp hq) hall


/-! ## Epilogue core (instructions 5--7) -/

set_option maxRecDepth 8000 in
/-- Restore `ra`, deallocate the wrapper's 16-byte frame, and return, generic
    over the callee's result footprint `G`. -/
theorem epiCore (sp0 spH raIn : Word) (G : Assertion) (hG : G.pcFree)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 3 (H + 20) raIn fullCode
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ spH) ** G)
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) ** G) := by
  -- [5] LD x1 x2 0 : restore ra
  have h5 := ld_spec_gen_within .x1 .x2 spH (H + 20) raIn (0 : BitVec 12) (H + 20)
    (by decide)
  rw [show spH + signExtend12 (0 : BitVec 12) = spH from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h5
  have h5' := cpsTripleWithin_extend_code hdr_mono
    (cpsTripleWithin_extend_code (cr' := hdrCode)
      (CodeReq.ofProg_mem_at H (H + 20) headerExtractNumber_prog 5
        (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega) (by rw [hdr_length]; decide)
        rfl (by rw [hdr_length]; decide)) h5)
  -- [6] ADDI x2 x2 16 : deallocate
  have h6 := addi_spec_gen_same_within .x2 spH (16 : BitVec 12) (H + 24) (by decide)
  rw [show spH + signExtend12 (16 : BitVec 12) = sp0 from by
    rw [hspH]; exact sext_frameRestore sp0 (-16 : BitVec 12) (16 : BitVec 12)
      (by decide)] at h6
  have h6' := cpsTripleWithin_extend_code hdr_mono
    (cpsTripleWithin_extend_code (cr' := hdrCode)
      (CodeReq.ofProg_mem_at H (H + 24) headerExtractNumber_prog 6
        (.ADDI .x2 .x2 (16 : BitVec 12)) (by bv_omega) (by rw [hdr_length]; decide)
        rfl (by rw [hdr_length]; decide)) h6)
  -- [7] JALR x0 x1 0 : return
  have h7 := EvmAsm.Evm64.ret_spec_within' (H + 28) raIn
  rw [hret] at h7
  have h7' := cpsTripleWithin_extend_code hdr_mono
    (cpsTripleWithin_extend_code (cr' := hdrCode)
      (CodeReq.ofProg_mem_at H (H + 28) headerExtractNumber_prog 7
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [hdr_length]; decide)
        rfl (by rw [hdr_length]; decide)) h7)
  have h6F := cpsTripleWithin_frameR ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn)) (by pcf) h6'
  have h7F := cpsTripleWithin_frameR ((.x2 ↦ᵣ sp0) ** (spH ↦ₘ raIn)) (by pcf) h7'
  have h56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h5' h6F
  have h567 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h56 h7F
  have hcore : cpsTripleWithin 3 (H + 20) raIn fullCode
      ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (spH ↦ₘ raIn)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h567
  have hframed := cpsTripleWithin_frameR G hG hcore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hframed


/-! ## Epilogue over K34's result post (instructions 5--7) -/

set_option maxRecDepth 8000 in
/-- Case-split K34's `flatPost` and route each arm through `epiCore`, yielding
    the wrapper's own `hdrPost` (output cell pinned in each `Payload`). -/
theorem hdrEpilogue
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 3 (H + 20) raIn fullCode
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
       flatPost spH newSp listBase oldOffset oldLen outer saved bytes listLen 8)
      (hdrPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
        listLen) := by
  -- Success arm: pull the payload existentials out first, route through epiCore.
  have tripleS' : cpsTripleWithin 3 (H + 20) raIn fullCode
      (fun h => ∃ offset len v12 x5 ss ws ov,
        ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
          (((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
            savedFrame newSp outer) **
           successPayload newSp listBase offset len v12 x5 ss ws ov saved bytes
             listLen 8)) h)
      (hdrPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
        listLen) := by
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun offset => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun len => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun x5 => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun ss => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun ws => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun ov => ?_)
    have hcoreS := epiCore sp0 spH raIn
        ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
          successPayload newSp listBase offset len v12 x5 ss ws ov saved bytes
            listLen 8)
        (by unfold savedFrame successPayload; pcf) hspH hret
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
      hcoreS
    exact Or.inl ⟨offset, len, v12, x5, ss, ws, ov, by xperm_hyp hq⟩
  have tripleS : cpsTripleWithin 3 (H + 20) raIn fullCode
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
       flatSuccessReturned spH newSp listBase outer saved bytes listLen 8)
      (hdrPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
        listLen) :=
    cpsTripleWithin_weaken (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp,
        ⟨offset, len, v12, x5, ss, ws, ov, hinner⟩⟩ := hp
      exact ⟨offset, len, v12, x5, ss, ws, ov,
        h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp, hinner⟩)
      (fun _ hq => hq) tripleS'
  -- Failure arm.
  have tripleF' : cpsTripleWithin 3 (H + 20) raIn fullCode
      (fun h => ∃ v11 v12,
        ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
          (((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
            savedFrame newSp outer) **
           failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
             listLen 8)) h)
      (hdrPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
        listLen) := by
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v11 => ?_)
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
    have hcoreF := epiCore sp0 spH raIn
        ((.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) ** savedFrame newSp outer **
          failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
            listLen 8)
        (by unfold savedFrame failurePayload; pcf) hspH hret
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
      hcoreF
    exact Or.inr ⟨v11, v12, by xperm_hyp hq⟩
  have tripleF : cpsTripleWithin 3 (H + 20) raIn fullCode
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
       flatFailureReturned spH newSp listBase oldOffset oldLen outer saved bytes
         listLen 8)
      (hdrPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
        listLen) :=
    cpsTripleWithin_weaken (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp,
        ⟨v11, v12, hinner⟩⟩ := hp
      exact ⟨v11, v12, h1, h2, hd, hu, hx1, h3, h4, hd2, hu2, hsp, hinner⟩)
      (fun _ hq => hq) tripleF'
  -- Combine the arms.
  have hor := cpsTripleWithin_pre_or tripleS tripleF
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) hor
  unfold flatPost at hp
  have hinner := sepConj_mono_right
    (fun h' (hh : ((spH ↦ₘ raIn) **
        (fun h'' => flatSuccessReturned spH newSp listBase outer saved bytes
            listLen 8 h'' ∨
          flatFailureReturned spH newSp listBase oldOffset oldLen outer saved
            bytes listLen 8 h'')) h') => sepConj_or_split h' hh) h hp
  exact sepConj_or_split h hinner


/-! ## Whole-program caller contract -/

set_option maxRecDepth 8000 in
/-- **`header_extract_number` caller contract.**  The 8-instruction wrapper =
    prologue ;; `rlpFieldToU64_flat_spec_within` (field index 8) ;; epilogue.
    On `a0 = 0` the caller's output cell holds the big-endian decode
    of the real field-8 content (pinned inside `successPayload`'s `Result`);
    `a0 = 1` is an RLP parse failure and `a0 = 2` a field wider than 8 bytes,
    both with a zeroed output cell. -/
theorem header_extract_number_spec_within
    (sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13 old14
      oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hnewSp : newSp = spH + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    let outer : Saved := { ra := H + 20, s0 := s0In, s1 := s1In }
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (8 + 2)) + 6)) + 9)
    -- The tail bound follows the caller-owned input byte region, as in the
    -- callee's data-derived `rlpFieldToU64_flat_spec_within` bound.
    let tailSteps := (7 + (1 + (7 * bytes.length + 11))) + 5
    let n34 := (7 + 4 + callSteps) + ((1 + tailSteps) + 5)
    cpsTripleWithin (4 + (1 + n34) + 3) H raIn fullCode
      (hdrPre sp0 raIn oldRaSlot spH newSp listBase listLenW outputPtr old13
        old14 oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 bytes)
      (hdrPost sp0 spH newSp raIn listBase oldOffset oldLen outer saved bytes
        listLen) := by
  intro outer saved callSteps tailSteps n34
  -- Prologue: instructions 0--3.
  have hpro := hdrPrologue sp0 raIn oldRaSlot spH newSp listBase listLenW
    outputPtr old13 old14 oldOut oldOffset oldLen s0In s1In s2 s3 s4 s5 outer
    bytes rfl hspH
  -- Call: instruction 4 (jal) + lenient K34.
  have hflat := rlpFieldToU64_flat_spec_within spH newSp listBase listLenW
    (8 : Word) outputPtr oldOut oldOffset oldLen old14 outer s2 s3 s4 s5 bytes
    listLen 8 hnewSp hlistLenW (by decide) (by decide) hsalign hslack hover
    hvalid (by show (H + 20) &&& ~~~(1 : Word) = H + 20; decide)
  have hflatC := cpsTripleWithin_extend_code k34_mono hflat
  have hflatF := cpsTripleWithin_frameR (spH ↦ₘ raIn) (by pcf) hflatC
  have hcallee : cpsTripleWithin n34 B (H + 20) fullCode
      ((.x1 ↦ᵣ (H + 20)) **
        (flatPre spH newSp listBase listLenW (8 : Word) outputPtr oldOut
          oldOffset oldLen old14 outer s2 s3 s4 s5 bytes ** (spH ↦ₘ raIn)))
      ((.x1 ↦ᵣ (H + 20)) **
        (flatPost spH newSp listBase oldOffset oldLen outer saved bytes listLen 8
          ** (spH ↦ₘ raIn))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall := callWithin_spec (H + 16) B raIn
    (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.header_extract_number + 16))
    n34 (by show (H + 16) + signExtend21 _ = B; decide)
    (fun a i hi => hdr_mono a i
      (CodeReq.ofProg_mem_at H (H + 16) headerExtractNumber_prog 4
        (.JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64
          (GuestAddrs.header_extract_number + 16))) (by bv_omega)
        (by rw [hdr_length]; decide) rfl (by rw [hdr_length]; decide) a i hi))
    (by unfold flatPre wholeRest; pcf) hcallee
  rw [show (H + 16 + 4 : Word) = H + 20 from by bv_omega] at hcall
  have hcall' : cpsTripleWithin (1 + n34) (H + 16) (H + 20) fullCode
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
        flatPre spH newSp listBase listLenW (8 : Word) outputPtr oldOut oldOffset
          oldLen old14 outer s2 s3 s4 s5 bytes)
      ((.x1 ↦ᵣ (H + 20)) ** (spH ↦ₘ raIn) **
        flatPost spH newSp listBase oldOffset oldLen outer saved bytes listLen 8) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcall
  -- Epilogue: instructions 5--7.
  have hepi := hdrEpilogue sp0 spH newSp raIn listBase oldOffset oldLen outer
    saved bytes listLen hspH hret
  -- Compose the three phases.
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hpro hcall'
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) h01 hepi


end EvmAsm.Codegen.HeaderExtractNumberSpec
