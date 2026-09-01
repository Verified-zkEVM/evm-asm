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
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.ValidateHeaderInlineArms

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.ValidateHeaderInlineArms

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderGasCorrespondence
  (excessFrame excessSavedFrame excessEntryRest excessCalleePost excessFrameVals
    ExcessRet ExcessK k70Cr k70Target
    validate_header_excess_blob_gas_call_spec_within
    header_validate_excess_blob_gas_under_target_spec_within)

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



end EvmAsm.Codegen.ValidateHeaderInlineArms
