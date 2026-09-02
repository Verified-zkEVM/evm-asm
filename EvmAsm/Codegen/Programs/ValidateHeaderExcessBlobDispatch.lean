/-
  EvmAsm.Codegen.Programs.ValidateHeaderExcessBlobDispatch

  The excess-blob dispatch composition (item three of the #12346
  decomposition): `ldNumber` → `numberZeroBeq` (not taken) → the three
  argument `LD`s → `addiParentStructPtr96` → the `excess_blob` JAL
  (under-target arm as hcallee) → `excessStatusBne` (not taken), over
  `fullCode = callerCode ∪ k70Cr`.

  Reuses the single-instruction arms and `H` / `prog` from
  `ValidateHeaderInlineArms`; do not invent a second entry contract.
-/

import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasArms
import EvmAsm.Codegen.Programs.ValidateHeaderCheckGasLimit
import EvmAsm.Codegen.Programs.CheckGasLimitSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.ValidateHeaderInlineArms

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.ValidateHeaderInlineArms

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderGasCorrespondence
  (excessFrame excessSavedFrame excessEntryRest excessCalleePost excessFrameVals
    ExcessRet ExcessK k70Cr k70Target
    validate_header_excess_blob_gas_call_spec_within
    header_validate_excess_blob_gas_under_target_spec_within
    baseFrame baseSavedFrame baseFrameVals baseEntryRest baseCalleePost
    BaseRet BaseK validate_header_base_fee_call_spec_within)
open EvmAsm.Codegen.ValidateHeaderCheckGasLimit
  (callerFrame checkGasLimitStatus4Post checkGasLimitFallPost
    validate_header_check_gas_limit_routes_spec_within)
open EvmAsm.Codegen.CheckGasLimitSAsm (cglStatus)

/-! ## Excess-blob dispatch composition (`H+56 → H+88`, first increment)

    `ldNumber` → `numberZeroBeq` (not taken) → the three argument `LD`s →
    `addiParentStructPtr96` → the `excess_blob` JAL (under-target arm as
    hcallee) → `excessStatusBne` (not taken).  Because the K70 callee occupies
    a disjoint address range, the whole composition lives over
    `fullCode = callerCode ∪ k70Cr`; the single-instruction arms are lifted
    from `callerCode` by left-union monotonicity.  The claimed-region gate is
    the callee frame (`frameSlotsOwn` + `regsAt` + `regOwns` + `x0`), which the
    core `validateHeaderCorePre` does not carry, so this pre extends it. -/

abbrev fullCode : CodeReq := callerCode.union k70Cr

theorem fullCode_caller_mono :
    ∀ a i, callerCode a = some i → fullCode a = some i := by
  intro a i h
  unfold fullCode
  exact CodeReq.union_mono_left a i h

theorem caller_disjoint_k70 :
    callerCode.Disjoint k70Cr := by
  unfold callerCode k70Cr
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [validateHeader_length]; decide
  · decide
  · rw [validateHeader_length]; decide

abbrev excessBlobDispatchPre
    (spC thisStruct parentStructPtr : Word) (vals : Reg → Word)
    (o5 o10 o11 o12 o13 number thisExcess parentBlob parentExcess oldRa : Word)
    (G : Assertion) : Assertion :=
  ((.x18 ↦ᵣ thisStruct) ** (.x5 ↦ᵣ o5) ** ((thisStruct + 64) ↦ₘ number) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ parentStructPtr) **
    (.x10 ↦ᵣ o10) ** ((thisStruct + 136) ↦ₘ thisExcess) **
    (.x11 ↦ᵣ o11) ** ((parentStructPtr + 128) ↦ₘ parentBlob) **
    (.x12 ↦ᵣ o12) ** ((parentStructPtr + 136) ↦ₘ parentExcess) **
    (.x13 ↦ᵣ o13) **
    (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
    (.x20 ↦ᵣ vals .x20) ** (.x21 ↦ᵣ vals .x21) **
    (.x2 ↦ᵣ spC) **
    frameSlotsOwn excessFrame (spC + signExtend12 (-64 : BitVec 12)) **
    regOwns [.x6, .x28, .x29, .x30, .x31] **
    (.x1 ↦ᵣ oldRa) ** G)

abbrev excessBlobDispatchPost
    (spC : Word) (vals : Reg → Word)
    (thisStruct parentStructPtr number thisExcess parentBlob parentExcess : Word)
    (G : Assertion) : Assertion :=
  (excessCalleePost spC vals (0 : Word) ExcessRet empAssertion **
    ((thisStruct + 64) ↦ₘ number) ** ((thisStruct + 136) ↦ₘ thisExcess) **
    ((parentStructPtr + 128) ↦ₘ parentBlob) **
    ((parentStructPtr + 136) ↦ₘ parentExcess) ** G)

/-! The pre-call route `H+56 → H+80`: `ldNumber` → `numberZeroBeq` (not taken)
    → the three argument `LD`s → `addiParentStructPtr96`.  The post is the
    standalone pre-call state `S6` (the same `excessBlobDispatchPre` shape with
    the loaded values). -/
set_option maxRecDepth 8000 in
theorem excessBlobDispatch_preCall
    (spC thisStruct parentStructPtr : Word) (vals : Reg → Word)
    (o5 o10 o11 o12 o13 number thisExcess parentBlob parentExcess oldRa : Word)
    (G : Assertion) (hG : G.pcFree) (hnum : number ≠ 0) :
    cpsTripleWithin (1+1+1+1+1+1) (H + 56) (H + 80) fullCode
      (excessBlobDispatchPre spC thisStruct parentStructPtr vals
        o5 o10 o11 o12 o13 number thisExcess parentBlob parentExcess oldRa G)
      (excessBlobDispatchPre spC thisStruct parentStructPtr vals
        (o5 := number) (o10 := thisExcess) (o11 := parentBlob) (o12 := parentExcess)
        (o13 := parentStructPtr + 96) (number := number) (thisExcess := thisExcess)
        (parentBlob := parentBlob) (parentExcess := parentExcess) (oldRa := oldRa) G) := by
  let frameAmb : Assertion :=
    (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
    (.x20 ↦ᵣ vals .x20) ** (.x21 ↦ᵣ vals .x21) **
    (.x2 ↦ᵣ spC) **
    frameSlotsOwn excessFrame (spC + signExtend12 (-64 : BitVec 12)) **
    regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x1 ↦ᵣ oldRa)
  have h1 := ldNumber thisStruct o5 number
  have h1C := cpsTripleWithin_extend_code fullCode_caller_mono h1
  have h1F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ parentStructPtr) **
      (.x10 ↦ᵣ o10) ** ((thisStruct + 136) ↦ₘ thisExcess) **
      (.x11 ↦ᵣ o11) ** ((parentStructPtr + 128) ↦ₘ parentBlob) **
      (.x12 ↦ᵣ o12) ** ((parentStructPtr + 136) ↦ₘ parentExcess) **
      (.x13 ↦ᵣ o13) ** frameAmb ** G)
    (by dsimp [frameAmb]; pcf; exact hG) h1C
  have h2 := numberZeroBeq_ntaken number hnum
  have h2C := cpsTripleWithin_extend_code fullCode_caller_mono h2
  have h2F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisStruct) ** ((thisStruct + 64) ↦ₘ number) **
      (.x19 ↦ᵣ parentStructPtr) **
      (.x10 ↦ᵣ o10) ** ((thisStruct + 136) ↦ₘ thisExcess) **
      (.x11 ↦ᵣ o11) ** ((parentStructPtr + 128) ↦ₘ parentBlob) **
      (.x12 ↦ᵣ o12) ** ((parentStructPtr + 136) ↦ₘ parentExcess) **
      (.x13 ↦ᵣ o13) ** frameAmb ** G)
    (by dsimp [frameAmb]; pcf; exact hG) h2C
  have h3 := ldThisExcessBlobGas thisStruct o10 thisExcess
  have h3C := cpsTripleWithin_extend_code fullCode_caller_mono h3
  have h3F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ parentStructPtr) **
      (.x11 ↦ᵣ o11) ** ((parentStructPtr + 128) ↦ₘ parentBlob) **
      (.x12 ↦ᵣ o12) ** ((parentStructPtr + 136) ↦ₘ parentExcess) **
      (.x13 ↦ᵣ o13) **
      ((thisStruct + 64) ↦ₘ number) ** frameAmb ** G)
    (by dsimp [frameAmb]; pcf; exact hG) h3C
  have h4 := ldParentBlobGasUsed parentStructPtr o11 parentBlob
  have h4C := cpsTripleWithin_extend_code fullCode_caller_mono h4
  have h4F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x18 ↦ᵣ thisStruct) ** (.x10 ↦ᵣ thisExcess) **
      ((thisStruct + 64) ↦ₘ number) ** ((thisStruct + 136) ↦ₘ thisExcess) **
      (.x12 ↦ᵣ o12) ** ((parentStructPtr + 136) ↦ₘ parentExcess) **
      (.x13 ↦ᵣ o13) ** frameAmb ** G)
    (by dsimp [frameAmb]; pcf; exact hG) h4C
  have h5 := ldParentExcessBlobGas parentStructPtr o12 parentExcess
  have h5C := cpsTripleWithin_extend_code fullCode_caller_mono h5
  have h5F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x18 ↦ᵣ thisStruct) ** (.x10 ↦ᵣ thisExcess) **
      ((thisStruct + 64) ↦ₘ number) ** ((thisStruct + 136) ↦ₘ thisExcess) **
      (.x11 ↦ᵣ parentBlob) ** ((parentStructPtr + 128) ↦ₘ parentBlob) **
      (.x13 ↦ᵣ o13) ** frameAmb ** G)
    (by dsimp [frameAmb]; pcf; exact hG) h5C
  have h6 := addiParentStructPtr96 parentStructPtr o13
  have h6C := cpsTripleWithin_extend_code fullCode_caller_mono h6
  have h6F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x18 ↦ᵣ thisStruct) ** (.x10 ↦ᵣ thisExcess) **
      (.x11 ↦ᵣ parentBlob) ** (.x12 ↦ᵣ parentExcess) **
      ((thisStruct + 64) ↦ₘ number) ** ((thisStruct + 136) ↦ₘ thisExcess) **
      ((parentStructPtr + 128) ↦ₘ parentBlob) **
      ((parentStructPtr + 136) ↦ₘ parentExcess) ** frameAmb ** G)
    (by dsimp [frameAmb]; pcf; exact hG) h6C
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1F h2F
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s12 h3F
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s123 h4F
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1234 h5F
  have s123456 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s12345 h6F
  exact cpsTripleWithin_weaken (fun _ hp => by dsimp [excessBlobDispatchPre, frameAmb] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by dsimp [excessBlobDispatchPre, frameAmb] at hq ⊢; xperm_hyp hq) s123456

set_option maxRecDepth 8000 in
theorem excessBlobDispatch_spec
    (spC thisStruct parentStructPtr : Word) (vals : Reg → Word)
    (o5 o10 o11 o12 o13 number thisExcess parentBlob parentExcess oldRa : Word)
    (G : Assertion) (hG : G.pcFree)
    (hx18 : vals .x18 = thisStruct) (hx19 : vals .x19 = parentStructPtr)
    (hnum : number ≠ 0) (ha0 : thisExcess = 0)
    (hnowrap : ¬ BitVec.ult (parentExcess + parentBlob) parentExcess = true)
    (hunder : BitVec.ult (parentExcess + parentBlob) k70Target = true) :
    cpsTripleWithin (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 29) (H + 56) (H + 88) fullCode
      (excessBlobDispatchPre spC thisStruct parentStructPtr vals
        o5 o10 o11 o12 o13 number thisExcess parentBlob parentExcess oldRa G)
      (excessBlobDispatchPost spC vals thisStruct parentStructPtr number
        thisExcess parentBlob parentExcess G) := by
  let memAtoms : Assertion :=
    ((thisStruct + 64) ↦ₘ number) ** ((thisStruct + 136) ↦ₘ thisExcess) **
    ((parentStructPtr + 128) ↦ₘ parentBlob) **
    ((parentStructPtr + 136) ↦ₘ parentExcess)
  let status : Word := if thisExcess = 0 then (0 : Word) else 2
  let S6 : Assertion :=
    excessBlobDispatchPre spC thisStruct parentStructPtr vals
      (o5 := number) (o10 := thisExcess) (o11 := parentBlob) (o12 := parentExcess)
      (o13 := parentStructPtr + 96) (number := number) (thisExcess := thisExcess)
      (parentBlob := parentBlob) (parentExcess := parentExcess) (oldRa := oldRa) G
  have hmemAtoms : memAtoms.pcFree := by dsimp [memAtoms]; pcf
  have hFcall : (memAtoms ** G).pcFree := pcFree_sepConj hmemAtoms hG
  have hpre := excessBlobDispatch_preCall spC thisStruct parentStructPtr vals
    o5 o10 o11 o12 o13 number thisExcess parentBlob parentExcess oldRa G hG hnum
  have hcallee := EvmAsm.Codegen.ValidateHeaderGasCorrespondence.header_validate_excess_blob_gas_under_target_spec_within
    spC ExcessRet thisExcess parentBlob parentExcess (parentStructPtr + 96) vals
    (by decide) hnowrap hunder
  have hcall := EvmAsm.Codegen.ValidateHeaderGasCorrespondence.validate_header_excess_blob_gas_call_spec_within
    (cr := fullCode) (calleeCode := k70Cr) (n := 29)
    spC vals thisExcess parentBlob parentExcess (parentStructPtr + 96) status oldRa
    empAssertion empAssertion (memAtoms ** G)
    (by unfold empAssertion; exact pcFree_emp) hFcall
    caller_disjoint_k70 (fun _ _ h => h) hcallee
  -- weaken the call triple's pre from the folded C to the standalone S6
  have hcallS6 : cpsTripleWithin (1 + 29) (H + 80) (H + 84) fullCode
      S6
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ ExcessRet) ** (.x2 ↦ᵣ spC) **
        frameSlotsSaved excessFrame (spC + signExtend12 (-64 : BitVec 12))
          (excessFrameVals ExcessRet vals) **
        regsAt excessSavedFrame vals **
        regOwns [.x5, .x6, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
        memAtoms ** G) := by
    exact cpsTripleWithin_weaken (fun h hp => by
      -- S6 → C : fold x8..x21 into regsAt, convert x5 to regOwn, package memAtoms/G into F
      dsimp [status, memAtoms, S6, excessBlobDispatchPre] at hp ⊢
      simp [excessEntryRest, excessSavedFrame, regsAt, regOwns,
        sepConj_emp_right'] at hp ⊢
      rw [hx18, hx19] at ⊢
      have hx5 : ∀ h, (.x5 ↦ᵣ number) h → regOwn .x5 h :=
        regIs_implies_regOwn (r := .x5)
      let R : Assertion :=
        (.x1 ↦ᵣ oldRa) ** (.x2 ↦ᵣ spC) **
        frameSlotsOwn excessFrame (spC + signExtend12 4032#12) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
        (.x18 ↦ᵣ thisStruct) ** (.x19 ↦ᵣ parentStructPtr) **
        (.x20 ↦ᵣ vals .x20) ** (.x21 ↦ᵣ vals .x21) **
        (.x10 ↦ᵣ thisExcess) ** (.x11 ↦ᵣ parentBlob) ** (.x12 ↦ᵣ parentExcess) **
        (.x13 ↦ᵣ (parentStructPtr + 96)) **
        regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        memAtoms ** G
      have hpFront : ((.x5 ↦ᵣ number) ** R) h := by
        dsimp [R, memAtoms]
        xperm_hyp hp
      have hpOwn : (regOwn .x5 ** R) h := sepConj_mono_left hx5 _ hpFront
      dsimp [R, memAtoms] at hpOwn
      xperm_hyp hpOwn)
      (fun _ hq => by
        dsimp [memAtoms] at hq ⊢
        rw [show status = (0 : Word) from by
          dsimp [status]
          simp [ha0]] at hq
        simp [excessCalleePost, sepConj_emp_right'] at hq ⊢
        xperm_hyp hq) hcall
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by dsimp [S6]; exact hp) hpre hcallS6
  have h8 := excessStatusBne_ntaken (0 : Word) rfl
  have h8C := cpsTripleWithin_extend_code fullCode_caller_mono h8
  have h8F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ExcessRet) ** (.x2 ↦ᵣ spC) **
      frameSlotsSaved excessFrame (spC + signExtend12 (-64 : BitVec 12))
        (excessFrameVals ExcessRet vals) **
      regsAt excessSavedFrame vals **
      regOwns [.x5, .x6, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
      memAtoms ** G)
    (by dsimp [memAtoms, excessFrame, excessSavedFrame]; pcf; exact hG) h8C
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s7 h8F
  exact cpsTripleWithin_weaken (fun _ hp => by dsimp [excessBlobDispatchPre] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by
      dsimp [memAtoms, excessBlobDispatchPost] at hq ⊢
      simp [excessCalleePost, sepConj_emp_right'] at hq ⊢
      xperm_hyp hq) s9




/-! ## Gas-check dispatch composition (`H+88 → H+116`, second increment)

    `ldGasUsed` → `ldGasLimit` → `gasUsedExceeds_ntaken` (gate:
    `¬ ult gasLimit gasUsed`) → `ldThisGasLimit` → `ldParentGasLimit`, then the
    `check_gas_limit` JAL via the PROVEN routes spec
    `validate_header_check_gas_limit_routes_spec_within` (a two-exit N-branch:
    the status-4 taken tail to `raIn`, and the fall-through to `H+116`).
    Unlike the K70 increment, `check_gas_limit` is `.proven`, so no `hcallee`
    hypothesis is needed; item three is here exercised on a proven callee's
    two-exit N-branch.  The caller frame keeps `x18`/`x19` and the header/parent
    memory atoms as standalone atoms (the five argument arms require them), the
    remaining caller state rides in `cglFrame` (the check-gas `callerFrame`
    minus `x18`/`x19`). -/

abbrev cglCode : CodeReq :=
  CodeReq.ofProg (GuestAddrs.check_gas_limit : Word) checkGasLimit_prog

abbrev cglFull : CodeReq := callerCode.union cglCode

theorem cglFull_caller_mono :
    ∀ a i, callerCode a = some i → cglFull a = some i := by
  intro a i h
  unfold cglFull
  exact CodeReq.union_mono_left a i h

theorem caller_disjoint_cgl :
    callerCode.Disjoint cglCode := by
  unfold callerCode cglCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [validateHeader_length]; decide
  · decide
  · rw [validateHeader_length]; decide

/-- The check-gas caller frame minus `x18`/`x19` (carried standalone by the
    five argument arms).  Reassembly into the routes-spec pre's full
    `callerFrame` happens in the final weaken. -/
abbrev cglFrame
    (spC raSlot o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
  (spC ↦ₘ raSlot) ** ((spC + BitVec.ofNat 64 8) ↦ₘ cs0) **
  ((spC + BitVec.ofNat 64 16) ↦ₘ cs1) **
  ((spC + BitVec.ofNat 64 24) ↦ₘ cs2) **
  ((spC + BitVec.ofNat 64 32) ↦ₘ cs3) **
  ((spC + BitVec.ofNat 64 40) ↦ₘ cs4) **
  ((spC + BitVec.ofNat 64 48) ↦ₘ cs5) ** F

abbrev gasCheckPre
    (spC headerBase parentStructPtr : Word)
    (o5 o6 o10 o11 gasUsed gasLimit parentGasLimit oldRa : Word)
    (raSlot o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (F : Assertion) : Assertion :=
  ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ o5) ** ((headerBase + 88) ↦ₘ gasUsed) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ o6) ** ((headerBase + 80) ↦ₘ gasLimit) **
    (.x19 ↦ᵣ parentStructPtr) ** ((parentStructPtr + 80) ↦ₘ parentGasLimit) **
    (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) **
    (.x1 ↦ᵣ oldRa) ** regOwn .x7 **
    cglFrame spC raSlot o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)

set_option maxRecDepth 8000 in
theorem gasCheckDispatch_preCall
    (spC headerBase parentStructPtr : Word)
    (o5 o6 o10 o11 gasUsed gasLimit parentGasLimit oldRa : Word)
    (raSlot o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_ok : ¬ BitVec.ult gasLimit gasUsed = true) :
    cpsTripleWithin (1 + 1 + 1 + 1 + 1) (H + 88) (H + 108) cglFull
      (gasCheckPre spC headerBase parentStructPtr
        o5 o6 o10 o11 gasUsed gasLimit parentGasLimit oldRa
        raSlot o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)
      (gasCheckPre spC headerBase parentStructPtr
        (o5 := gasUsed) (o6 := gasLimit) (o10 := gasLimit) (o11 := parentGasLimit)
        (gasUsed := gasUsed) (gasLimit := gasLimit) (parentGasLimit := parentGasLimit)
        (oldRa := oldRa) raSlot o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) := by
  let frameRes : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) ** regOwn .x7 **
    cglFrame spC raSlot o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F
  have h1 := ldGasUsed headerBase o5 gasUsed
  have h1C := cpsTripleWithin_extend_code cglFull_caller_mono h1
  have h1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ o6) ** ((headerBase + 80) ↦ₘ gasLimit) **
      (.x19 ↦ᵣ parentStructPtr) ** ((parentStructPtr + 80) ↦ₘ parentGasLimit) **
      (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** frameRes)
    (by dsimp [frameRes]; pcf; exact hF) h1C
  have h2 := ldGasLimit headerBase o6 gasLimit
  have h2C := cpsTripleWithin_extend_code cglFull_caller_mono h2
  have h2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ gasUsed) ** ((headerBase + 88) ↦ₘ gasUsed) **
      (.x19 ↦ᵣ parentStructPtr) ** ((parentStructPtr + 80) ↦ₘ parentGasLimit) **
      (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** frameRes)
    (by dsimp [frameRes]; pcf; exact hF) h2C
  have h3 := gasUsedExceeds_ntaken gasLimit gasUsed h_ok
  have h3C := cpsTripleWithin_extend_code cglFull_caller_mono h3
  have h3F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** ((headerBase + 88) ↦ₘ gasUsed) **
      ((headerBase + 80) ↦ₘ gasLimit) **
      (.x19 ↦ᵣ parentStructPtr) ** ((parentStructPtr + 80) ↦ₘ parentGasLimit) **
      (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** frameRes)
    (by dsimp [frameRes]; pcf; exact hF) h3C
  have h4 := ldThisGasLimit headerBase o10 gasLimit
  have h4C := cpsTripleWithin_extend_code cglFull_caller_mono h4
  have h4F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ gasUsed) ** (.x6 ↦ᵣ gasLimit) **
      ((headerBase + 88) ↦ₘ gasUsed) **
      (.x19 ↦ᵣ parentStructPtr) ** ((parentStructPtr + 80) ↦ₘ parentGasLimit) **
      (.x11 ↦ᵣ o11) ** frameRes)
    (by dsimp [frameRes]; pcf; exact hF) h4C
  have h5 := ldParentGasLimit parentStructPtr o11 parentGasLimit
  have h5C := cpsTripleWithin_extend_code cglFull_caller_mono h5
  have h5F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ gasUsed) ** (.x6 ↦ᵣ gasLimit) **
      (.x10 ↦ᵣ gasLimit) ** ((headerBase + 88) ↦ₘ gasUsed) **
      ((headerBase + 80) ↦ₘ gasLimit) ** frameRes)
    (by dsimp [frameRes]; pcf; exact hF) h5C
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1F h2F
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s12 h3F
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s123 h4F
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1234 h5F
  exact cpsTripleWithin_weaken (fun _ hp => by dsimp [gasCheckPre, frameRes] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by dsimp [gasCheckPre, frameRes] at hq ⊢; xperm_hyp hq) s12345


set_option maxRecDepth 8000 in
theorem gasCheckDispatch_spec
    (sp0 spC headerBase parentStructPtr : Word)
    (o5 o6 o10 o11 gasUsed gasLimit parentGasLimit oldRa : Word)
    (raIn o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (h_ok : ¬ BitVec.ult gasLimit gasUsed = true) :
    cpsNBranchWithin (5 + 23) (H + 88) cglFull
      (gasCheckPre spC headerBase parentStructPtr
        o5 o6 o10 o11 gasUsed gasLimit parentGasLimit oldRa
        raIn o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F)
      [(raIn, checkGasLimitStatus4Post sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
          parentGasLimit gasLimit
          (((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
            ((parentStructPtr + 80) ↦ₘ parentGasLimit) ** F)),
       (H + 116, checkGasLimitFallPost spC raIn o8 o9 headerBase parentStructPtr o20 o21
          cs0 cs1 cs2 cs3 cs4 cs5 gasLimit parentGasLimit
          (((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
            ((parentStructPtr + 80) ↦ₘ parentGasLimit) ** F))] := by
  have hpre := gasCheckDispatch_preCall spC headerBase parentStructPtr
    o5 o6 o10 o11 gasUsed gasLimit parentGasLimit oldRa
    raIn o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F hF h_ok
  have hcalleeCode : ∀ a i,
      CodeReq.ofProg (GuestAddrs.check_gas_limit : Word) checkGasLimit_prog a = some i →
      cglCode a = some i := by
    intro a i hi
    unfold cglCode
    exact hi
  have hFmem : (((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
      ((parentStructPtr + 80) ↦ₘ parentGasLimit) ** F).pcFree := by
    pcf
    exact hF
  have hroutes := validate_header_check_gas_limit_routes_spec_within
    (cr := cglFull) (calleeCode := cglCode)
    sp0 spC raIn o8 o9 headerBase parentStructPtr o20 o21 cs0 cs1 cs2 cs3 cs4 cs5
    gasLimit parentGasLimit oldRa
    (((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
      ((parentStructPtr + 80) ↦ₘ parentGasLimit) ** F)
    hFmem caller_disjoint_cgl hcalleeCode (fun _ _ h => h) hspC hret
  have hperm : ∀ h,
      (gasCheckPre spC headerBase parentStructPtr
        (o5 := gasUsed) (o6 := gasLimit) (o10 := gasLimit) (o11 := parentGasLimit)
        (gasUsed := gasUsed) (gasLimit := gasLimit) (parentGasLimit := parentGasLimit)
        (oldRa := oldRa) raIn o8 o9 o20 o21 cs0 cs1 cs2 cs3 cs4 cs5 F) h →
      ((.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ parentGasLimit) ** (.x1 ↦ᵣ oldRa) **
        regOwns [.x5, .x6, .x7] ** (.x0 ↦ᵣ (0 : Word)) **
        callerFrame spC raIn o8 o9 headerBase parentStructPtr o20 o21
          cs0 cs1 cs2 cs3 cs4 cs5
          (((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
            ((parentStructPtr + 80) ↦ₘ parentGasLimit) ** F)) h := by
    intro h hp
    have hx5 : ∀ h, (.x5 ↦ᵣ gasUsed) h → regOwn .x5 h :=
      regIs_implies_regOwn (r := .x5)
    have hx6 : ∀ h, (.x6 ↦ᵣ gasLimit) h → regOwn .x6 h :=
      regIs_implies_regOwn (r := .x6)
    unfold gasCheckPre cglFrame at hp
    unfold callerFrame at ⊢
    simp only [regOwns, sepConj_emp_right'] at hp ⊢
    have hp56 : (((.x5 ↦ᵣ gasUsed) ** (.x6 ↦ᵣ gasLimit)) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ parentStructPtr) **
          (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ parentGasLimit) ** (.x1 ↦ᵣ oldRa) **
          regOwn .x7 ** (.x18 ↦ᵣ headerBase) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) **
          (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) ** (spC ↦ₘ raIn) **
          ((spC + BitVec.ofNat 64 8) ↦ₘ cs0) ** ((spC + BitVec.ofNat 64 16) ↦ₘ cs1) **
          ((spC + BitVec.ofNat 64 24) ↦ₘ cs2) ** ((spC + BitVec.ofNat 64 32) ↦ₘ cs3) **
          ((spC + BitVec.ofNat 64 40) ↦ₘ cs4) ** ((spC + BitVec.ofNat 64 48) ↦ₘ cs5) **
          ((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
          ((parentStructPtr + 80) ↦ₘ parentGasLimit) ** F)) h := by
      xperm_hyp hp
    have hpB := sepConj_mono_left (sepConj_mono hx5 hx6) _ hp56
    xperm_hyp hpB
  exact cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr hperm hpre hroutes


/-! ## Base-fee dispatch composition (`H+116 → H+140`, third increment)

    `addiThisStructPtr96` → `ldParentGasLimitRe` → `ldParentGasUsed` →
    `addiParentStructPtr96Re`, then the `base_fee` JAL at `H+132` via
    `validate_header_base_fee_call_spec_within` with the callee triple supplied
    as the `hcallee` HYPOTHESIS (the base-fee callee coverage is #13231, whose
    producer is separate), then `baseFeeBne_ntaken` (gate `status = 0`).
    Item three is here exercised at a third dispatch site with the blocked
    callee carried as a premise, per the claimed-region hcore plan.

    The base-fee callee frame (`baseFrame` at `spC-16`) rides in the caller pre
    (`baseFeeFrameRes`); the four argument arms need `x18`/`x19` and the two
    parent-struct memory atoms as STANDALONE atoms (they read them), while
    `x18`/`x19` and those memory atoms must survive the callee (the core reads
    `x18` again at `H+140`), so they are threaded through the JAL in the
    caller residual `F`. -/

abbrev bfFull (calleeCode : CodeReq) : CodeReq := callerCode.union calleeCode

theorem bfFull_caller_mono (calleeCode : CodeReq) :
    ∀ a i, callerCode a = some i → bfFull calleeCode a = some i := by
  intro a i hi
  exact CodeReq.union_mono_left a i hi

abbrev baseFeeFrameRes (spC : Word) (vals : Reg → Word) (oldRa : Word)
    (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spC) **
  frameSlotsOwn baseFrame (spC + signExtend12 (-16 : BitVec 12)) **
  regsAt baseSavedFrame vals **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) ** F

abbrev baseFeeDispatchPre (spC thisPtr parentPtr : Word) (vals : Reg → Word)
    (o10 o11 o12 o13 gasLimit gasUsed oldRa : Word) (F : Assertion) : Assertion :=
  (.x18 ↦ᵣ thisPtr) ** (.x10 ↦ᵣ o10) **
  (.x19 ↦ᵣ parentPtr) ** (.x11 ↦ᵣ o11) ** ((parentPtr + 80) ↦ₘ gasLimit) **
  (.x12 ↦ᵣ o12) ** ((parentPtr + 88) ↦ₘ gasUsed) **
  (.x13 ↦ᵣ o13) **
  baseFeeFrameRes spC vals oldRa F

theorem baseFeeDispatch_preCall
    {calleeCode : CodeReq}
    (spC thisPtr parentPtr : Word) (vals : Reg → Word)
    (o10 o11 o12 o13 gasLimit gasUsed oldRa : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (1 + 1 + 1 + 1) (H + 116) (H + 132) (bfFull calleeCode)
      (baseFeeDispatchPre spC thisPtr parentPtr vals
        o10 o11 o12 o13 gasLimit gasUsed oldRa F)
      (baseFeeDispatchPre spC thisPtr parentPtr vals
        (o10 := thisPtr + 96) (o11 := gasLimit) (o12 := gasUsed)
        (o13 := parentPtr + 96) (gasLimit := gasLimit) (gasUsed := gasUsed)
        (oldRa := oldRa) F) := by
  let frameRes : Assertion := baseFeeFrameRes spC vals oldRa F
  have h1 := addiThisStructPtr96 thisPtr o10
  have h1C := cpsTripleWithin_extend_code
    (bfFull_caller_mono calleeCode) h1
  have h1F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ parentPtr) ** (.x11 ↦ᵣ o11) ** ((parentPtr + 80) ↦ₘ gasLimit) **
      (.x12 ↦ᵣ o12) ** ((parentPtr + 88) ↦ₘ gasUsed) **
      (.x13 ↦ᵣ o13) ** frameRes)
    (by dsimp [frameRes, baseFeeFrameRes]; pcf; exact hF) h1C
  have h2 := ldParentGasLimitRe parentPtr o11 gasLimit
  have h2C := cpsTripleWithin_extend_code
    (bfFull_caller_mono calleeCode) h2
  have h2F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisPtr) ** (.x10 ↦ᵣ (thisPtr + 96)) **
      (.x12 ↦ᵣ o12) ** ((parentPtr + 88) ↦ₘ gasUsed) **
      (.x13 ↦ᵣ o13) ** frameRes)
    (by dsimp [frameRes, baseFeeFrameRes]; pcf; exact hF) h2C
  have h3 := ldParentGasUsed parentPtr o12 gasUsed
  have h3C := cpsTripleWithin_extend_code
    (bfFull_caller_mono calleeCode) h3
  have h3F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisPtr) ** (.x10 ↦ᵣ (thisPtr + 96)) **
      (.x11 ↦ᵣ gasLimit) **
      ((parentPtr + 80) ↦ₘ gasLimit) **
      (.x13 ↦ᵣ o13) ** frameRes)
    (by dsimp [frameRes, baseFeeFrameRes]; pcf; exact hF) h3C
  have h4 := addiParentStructPtr96Re parentPtr o13
  have h4C := cpsTripleWithin_extend_code
    (bfFull_caller_mono calleeCode) h4
  have h4F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisPtr) ** (.x10 ↦ᵣ (thisPtr + 96)) **
      (.x11 ↦ᵣ gasLimit) **
      ((parentPtr + 80) ↦ₘ gasLimit) **
      (.x12 ↦ᵣ gasUsed) ** ((parentPtr + 88) ↦ₘ gasUsed) ** frameRes)
    (by dsimp [frameRes, baseFeeFrameRes]; pcf; exact hF) h4C
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1F h2F
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s12 h3F
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s123 h4F
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [baseFeeDispatchPre, frameRes, baseFeeFrameRes] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by dsimp [baseFeeDispatchPre, frameRes, baseFeeFrameRes] at hq ⊢; xperm_hyp hq)
    s1234

set_option maxRecDepth 8000 in
theorem baseFeeDispatch_spec
    {calleeCode : CodeReq} {n : Nat}
    (spC thisPtr parentPtr : Word) (vals : Reg → Word)
    (o10 o11 o12 o13 gasLimit gasUsed status oldRa : Word)
    (F : Assertion) (hF : F.pcFree)
    (hcallerDisj : callerCode.Disjoint calleeCode)
    (hstatus0 : status = 0)
    (hcallee : cpsTripleWithin n BaseK BaseRet calleeCode
      ((.x1 ↦ᵣ BaseRet) **
        baseEntryRest spC vals (thisPtr + 96) gasLimit gasUsed (parentPtr + 96)
          empAssertion)
      (baseCalleePost spC vals status BaseRet empAssertion)) :
    cpsTripleWithin (1 + 1 + 1 + 1 + (1 + n) + 1) (H + 116) (H + 140)
      (bfFull calleeCode)
      (baseFeeDispatchPre spC thisPtr parentPtr vals
        o10 o11 o12 o13 gasLimit gasUsed oldRa F)
      (baseCalleePost spC vals status BaseRet empAssertion **
        ((.x18 ↦ᵣ thisPtr) ** (.x19 ↦ᵣ parentPtr) **
          ((parentPtr + 80) ↦ₘ gasLimit) ** ((parentPtr + 88) ↦ₘ gasUsed) ** F)) := by
  let Fcall : Assertion :=
    (.x18 ↦ᵣ thisPtr) ** (.x19 ↦ᵣ parentPtr) **
      ((parentPtr + 80) ↦ₘ gasLimit) ** ((parentPtr + 88) ↦ₘ gasUsed) ** F
  have hFcall : Fcall.pcFree := by
    dsimp [Fcall]
    pcf
    exact hF
  have hpre := baseFeeDispatch_preCall (calleeCode := calleeCode)
    spC thisPtr parentPtr vals
    o10 o11 o12 o13 gasLimit gasUsed oldRa F hF
  have hcall := validate_header_base_fee_call_spec_within
    (cr := bfFull calleeCode) (calleeCode := calleeCode) (n := n)
    spC vals (thisPtr + 96) gasLimit gasUsed (parentPtr + 96) status oldRa
    empAssertion empAssertion Fcall
    (by unfold empAssertion; exact pcFree_emp) hFcall
    hcallerDisj (fun _ _ h => h) hcallee
  have hcallS6 : cpsTripleWithin (1 + n) (H + 132) (H + 136) (bfFull calleeCode)
      (baseFeeDispatchPre spC thisPtr parentPtr vals
        (o10 := thisPtr + 96) (o11 := gasLimit) (o12 := gasUsed)
        (o13 := parentPtr + 96) (gasLimit := gasLimit) (gasUsed := gasUsed)
        (oldRa := oldRa) F)
      ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ BaseRet) ** (.x2 ↦ᵣ spC) **
        frameSlotsSaved baseFrame (spC + signExtend12 (-16 : BitVec 12))
          (baseFrameVals BaseRet vals) **
        regsAt baseSavedFrame vals **
        regOwns [.x5, .x6, .x7, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
        Fcall) := by
    exact cpsTripleWithin_weaken (fun h hp => by
      dsimp [Fcall, baseFeeDispatchPre, baseFeeFrameRes] at hp ⊢
      simp [baseEntryRest, baseSavedFrame, regsAt, regOwns,
        sepConj_emp_right'] at hp ⊢
      xperm_hyp hp)
      (fun _ hq => by
        dsimp [Fcall] at hq ⊢
        simp [baseCalleePost, sepConj_emp_right'] at hq ⊢
        xperm_hyp hq) hcall
  have s7 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [Fcall, baseFeeDispatchPre] at hp ⊢; xperm_hyp hp) hpre hcallS6
  have h8 := baseFeeBne_ntaken status hstatus0
  have h8C := cpsTripleWithin_extend_code (bfFull_caller_mono calleeCode) h8
  have h8F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ BaseRet) ** (.x2 ↦ᵣ spC) **
      frameSlotsSaved baseFrame (spC + signExtend12 (-16 : BitVec 12))
        (baseFrameVals BaseRet vals) **
      regsAt baseSavedFrame vals **
      regOwns [.x5, .x6, .x7, .x11, .x12, .x13, .x28, .x29, .x30, .x31] ** Fcall)
    (by dsimp [Fcall, baseFrame, baseSavedFrame]; pcf; exact hF) h8C
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s7 h8F
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [baseFeeDispatchPre, Fcall] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by
      dsimp [Fcall] at hq ⊢
      simp [baseCalleePost, sepConj_emp_right'] at hq ⊢
      xperm_hyp hq) s9

/-!
## Timestamp and number-succ checks (H + 140 → H + 168)

The fourth dispatch increment (callee-free): after the base-fee JAL returns
status 0 at H + 140, the core checks that the header timestamp is strictly
after the parent's (BGEU ntaken at H + 148) and that the header number is
exactly parent + 1 (BNE ntaken at H + 164).  All seven arms are single
instructions over `callerCode`, so this composition is pure framing — no code
union needed.

Registers on entry (from the base-fee dispatch post): `x18 ↦ thisStruct`,
`x19 ↦ parentStructPtr`, `x10 ↦ 0` (status), the four struct dwords
`(thisStruct+64/72)` and `(parentStructPtr+64/72)` read by the loads, and the
caller frame residual `tsNumFrameRes`.

Establishes (post): `x5 ↦ this.number`, `x6 ↦ parent.number + 1`, all four
struct dwords intact, `x10 ↦ 0`.  Gates (static, caller-supplied):
`h_lt : BitVec.ult parentTs headerTs` (timestamp strictly increasing),
`heq : headerNum = parentNum + 1` (number successor).
-/

abbrev tsNumFrameRes (spC : Word) (vals : Reg → Word) (oldRa : Word)
    (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ oldRa) ** (.x10 ↦ᵣ (0 : Word)) **
  (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
  (.x20 ↦ᵣ vals .x20) ** (.x21 ↦ᵣ vals .x21) **
  regOwns [.x7, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word)) ** F

abbrev tsNumDispatchPre (spC thisStruct parentStructPtr : Word) (vals : Reg → Word)
    (o5 o6 headerTs parentTs headerNum parentNum oldRa : Word) (F : Assertion) : Assertion :=
  (.x18 ↦ᵣ thisStruct) ** (.x5 ↦ᵣ o5) ** ((thisStruct + 72) ↦ₘ headerTs) **
  (.x19 ↦ᵣ parentStructPtr) ** (.x6 ↦ᵣ o6) ** ((parentStructPtr + 72) ↦ₘ parentTs) **
  ((thisStruct + 64) ↦ₘ headerNum) ** ((parentStructPtr + 64) ↦ₘ parentNum) **
  tsNumFrameRes spC vals oldRa F

abbrev tsNumDispatchPost (spC thisStruct parentStructPtr : Word) (vals : Reg → Word)
    (headerTs parentTs headerNum parentNum oldRa : Word) (F : Assertion) : Assertion :=
  (.x18 ↦ᵣ thisStruct) ** (.x5 ↦ᵣ headerNum) ** ((thisStruct + 72) ↦ₘ headerTs) **
  (.x19 ↦ᵣ parentStructPtr) ** (.x6 ↦ᵣ (parentNum + 1)) ** ((parentStructPtr + 72) ↦ₘ parentTs) **
  ((thisStruct + 64) ↦ₘ headerNum) ** ((parentStructPtr + 64) ↦ₘ parentNum) **
  tsNumFrameRes spC vals oldRa F

set_option maxRecDepth 8000 in
theorem tsNumDispatch_spec
    (spC thisStruct parentStructPtr : Word) (vals : Reg → Word)
    (o5 o6 headerTs parentTs headerNum parentNum oldRa : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_lt : BitVec.ult parentTs headerTs)
    (heq : headerNum = parentNum + 1) :
    cpsTripleWithin (1 + 1 + 1 + 1 + 1 + 1 + 1) (H + 140) (H + 168) callerCode
      (tsNumDispatchPre spC thisStruct parentStructPtr vals
        o5 o6 headerTs parentTs headerNum parentNum oldRa F)
      (tsNumDispatchPost spC thisStruct parentStructPtr vals
        headerTs parentTs headerNum parentNum oldRa F) := by
  let frameRes : Assertion := tsNumFrameRes spC vals oldRa F
  have h1 := ldHeaderTimestamp thisStruct o5 headerTs
  have h1F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ parentStructPtr) ** (.x6 ↦ᵣ o6) ** ((parentStructPtr + 72) ↦ₘ parentTs) **
      ((thisStruct + 64) ↦ₘ headerNum) ** ((parentStructPtr + 64) ↦ₘ parentNum) ** frameRes)
    (by dsimp [frameRes, tsNumFrameRes]; pcf; exact hF) h1
  have h2 := ldParentTimestamp parentStructPtr o6 parentTs
  have h2F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisStruct) ** (.x5 ↦ᵣ headerTs) ** ((thisStruct + 72) ↦ₘ headerTs) **
      ((thisStruct + 64) ↦ₘ headerNum) ** ((parentStructPtr + 64) ↦ₘ parentNum) ** frameRes)
    (by dsimp [frameRes, tsNumFrameRes]; pcf; exact hF) h2
  have h3 := timestampNotIncreasing_ntaken parentTs headerTs h_lt
  have h3F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisStruct) ** ((thisStruct + 72) ↦ₘ headerTs) **
      (.x19 ↦ᵣ parentStructPtr) ** ((parentStructPtr + 72) ↦ₘ parentTs) **
      ((thisStruct + 64) ↦ₘ headerNum) ** ((parentStructPtr + 64) ↦ₘ parentNum) ** frameRes)
    (by dsimp [frameRes, tsNumFrameRes]; pcf; exact hF) h3
  have h4 := ldHeaderNumber6 thisStruct headerTs headerNum
  have h4F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ parentStructPtr) ** (.x6 ↦ᵣ parentTs) ** ((parentStructPtr + 72) ↦ₘ parentTs) **
      ((thisStruct + 72) ↦ₘ headerTs) ** ((parentStructPtr + 64) ↦ₘ parentNum) ** frameRes)
    (by dsimp [frameRes, tsNumFrameRes]; pcf; exact hF) h4
  have h5 := ldParentNumber6 parentStructPtr parentTs parentNum
  have h5F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisStruct) ** (.x5 ↦ᵣ headerNum) ** ((thisStruct + 64) ↦ₘ headerNum) **
      ((thisStruct + 72) ↦ₘ headerTs) ** ((parentStructPtr + 72) ↦ₘ parentTs) ** frameRes)
    (by dsimp [frameRes, tsNumFrameRes]; pcf; exact hF) h5
  have h6 := addiParentSucc parentNum
  have h6F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisStruct) ** (.x5 ↦ᵣ headerNum) ** ((thisStruct + 64) ↦ₘ headerNum) **
      ((thisStruct + 72) ↦ₘ headerTs) ** (.x19 ↦ᵣ parentStructPtr) **
      ((parentStructPtr + 72) ↦ₘ parentTs) ** ((parentStructPtr + 64) ↦ₘ parentNum) ** frameRes)
    (by dsimp [frameRes, tsNumFrameRes]; pcf; exact hF) h6
  have h7 := numberNotSucc_ntaken headerNum (parentNum + 1) heq
  have h7F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ thisStruct) ** ((thisStruct + 64) ↦ₘ headerNum) **
      ((thisStruct + 72) ↦ₘ headerTs) ** (.x19 ↦ᵣ parentStructPtr) **
      ((parentStructPtr + 72) ↦ₘ parentTs) ** ((parentStructPtr + 64) ↦ₘ parentNum) ** frameRes)
    (by dsimp [frameRes, tsNumFrameRes]; pcf; exact hF) h7
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1F h2F
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s12 h3F
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s123 h4F
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1234 h5F
  have s123456 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s12345 h6F
  have s1234567 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s123456 h7F
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [tsNumDispatchPre, frameRes, tsNumFrameRes] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by dsimp [tsNumDispatchPost, frameRes, tsNumFrameRes] at hq ⊢; xperm_hyp hq)
    s1234567

end EvmAsm.Codegen.ValidateHeaderInlineArms
