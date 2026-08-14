/-
  EvmAsm.Codegen.Programs.TxSigningHashSpec

  **K145 `tx_signing_hash` — whole-routine Spec (#12038), multi-rate segments.**

  Umbrella module: scaffold/callWithins live in `TxSigningHashSpecCore`,
  body phases in `TxSigningHashSpecBodyEarly` / `TxSigningHashSpecBodyLate`,
  success-path glue in `TxSigningHashSpecSuccess`, call-return peel/fail in
  `TxSigningHashSpecJoin`.
  Same namespace; proofs compose toward `abiFrame` + `tx_signing_hash_spec_within`.

  ## DOMAIN

  Prefix path is total on `Word` via `tsh_prefix_any_callWithin` (short through
  long8). Keccak gather is ungated (`zkvm_keccak256_segments_spec_within`).
  No residual `< 2^56` input-domain gate.

  ## Consumer

  Live residual: `Eip7702AuthSigningHashSpec.txSigningHashContract`.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecJoin
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Stateless.SpecRef.Transactions

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.TxSigningHashResidual
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Codegen.MptSpliceSlotSpec
open EvmAsm.Stateless.SpecRef

/-! ## Caller-facing footprint (residual vocabulary)

    Matches `TxSigningHashResidual.signingHashCallEntry` /
    `signingHashCallReturn`. Prefix cover is total; residual notes are
    historical for consumers still citing the old gate. -/

/-- Entry footprint at the ABI boundary (`stackFree` for the 64-byte frame). -/
abbrev tshCallerPre := signingHashCallEntry

/-- Success/failure return with operational keccak (interim) — SpecRef lift is
    `signingHashOperationalReturn_to_spec` once `keccakBodyDigestBridge` holds,
    which multi-rate segments supplies via `kssDigest_eq_specref_any`. -/
abbrev tshCallerPostOperational := signingHashOperationalCallReturn

abbrev tshCallerPost := signingHashCallReturn

/-! ## Obligation note (in-module) -/

def tshDomainNote : String :=
  "PROVEN cover: tsh_prefix_any_callWithin is total on Word (short..long8). \
Keccak path uses ungated zkvm_keccak256_segments_spec_within. \
No residual payloadLen < 2^56 gate."

/-! ## Whole-routine: empty-length fail (conditional domain) -/

theorem tsh_ofProg_sub_fullCode :
    ∀ a i, CodeReq.ofProg H (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12)
        tshFrame tshBody) a = some i → fullCode a = some i := by
  intro a i hi
  have : tshCode a = some i := by
    simpa [tshCode, txSigningHash_prog_eq_abiFrame] using hi
  exact CodeReq.union_hit this

/-- **`tx_signing_hash` on the empty-input-length domain.**

    When `a1 = 0`, the body stores the type-prefix byte then takes the
    empty-length fail branch and returns `a0 = 1`. Frame restore is via
    `abiFrame_spec_own`. This is a **conditional** slice — not the short
    keccak success path. -/
theorem tx_signing_hash_spec_within_empty_len
    (sp0 ret : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 v5 wordOld : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalid : isValidByteAccess TshBuf = true)
    (hlen : a1 = 0) :
    cpsTripleWithin (1 + tshFrame.length + (5 + 3 + 2) + tshFrame.length + 1 + 1)
      H ret fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt tshFrame vals **
        frameSlotsOwn tshFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        tshEmptyFailCallerPre a0 a1 a2 a3 a4 v5 wordOld)
      ((.x2 ↦ᵣ sp0) ** regsAt tshFrame vals **
        frameSlotsSaved tshFrame (sp0 + signExtend12 (-64 : BitVec 12)) vals **
        tshEmptyFailCallerPost a1 a2 a3 a4 wordOld) := by
  have h := abiFrame_spec_own H sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    tshFrame (0 : BitVec 12) tshSregs vals tshBody (5 + 3 + 2)
    (tshEmptyFailCallerPre a0 a1 a2 a3 a4 v5 wordOld)
    (tshEmptyFailCallerPost a1 a2 a3 a4 wordOld)
    fullCode tshFrame_cons tshFrame_ne_zero
    (by rw [tshFrame_length]; decide)
    (by
      rw [txSigningHash_prog_eq_abiFrame, tsh_prog_length]
      decide)
    hret halign (tshFrame_restore sp0)
    (tshEmptyFailCallerPre_pcFree _ _ _ _ _ _ _)
    (tshEmptyFailCallerPost_pcFree _ _ _ _ _)
    tsh_ofProg_sub_fullCode
    (tshEmptyLenFailBody _ vals a0 a1 a2 a3 a4 v5 wordOld
      halignBuf hvalid hlen)
  rw [tshFrame_length] at h
  exact h

/-! ## Typed success: body under frame + abiFrame wrap -/

/-- Flattened `regsAt tshFrame` (same proof as BodyLate's private helper). -/
private theorem tsh_regsAt_frame' (vals : Reg → Word) :
    regsAt tshFrame vals =
      ((.x1 ↦ᵣ vals .x1) ** (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
        (.x18 ↦ᵣ vals .x18) ** (.x19 ↦ᵣ vals .x19) ** (.x20 ↦ᵣ vals .x20) **
        (.x21 ↦ᵣ vals .x21) ** (.x22 ↦ᵣ vals .x22)) := by
  simp [tshFrame, regsAt_cons, regsAt_nil, sepConj_emp_right']

private theorem tsh_regsOwnAt_frame' :
    regsOwnAt tshFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x21 ** regOwn .x22) := by
  simp [tshFrame, regsOwnAt_cons, regsOwnAt_nil, sepConj_emp_right']

/-- Body-level caller pre for the typed success path (no frame regs / SP). -/
def tshTypedSuccessCallerPre
    (a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31 oldOff oldLen wordOld cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion) : Assertion :=
  let saved := tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4
  (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
    (.x14 ↦ᵣ a4) **
    (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
    (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input **
    stackFree sp0 8 **
    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
    (.x31 ↦ᵣ v31) **
    (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen) **
    tshPostNthGatherAmbRest cellOld saved old0 old1 old2 old3 old4 old5
      outBytes payloadBs os sp0 A F

theorem tshTypedSuccessCallerPre_pcFree
    (a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31 oldOff oldLen wordOld cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree) :
    (tshTypedSuccessCallerPre a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
      oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
      input outBytes payloadBs os sp0 A F).pcFree := by
  unfold tshTypedSuccessCallerPre
  repeat first
    | exact tshPostNthGatherAmbRest_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hF
    | exact hA
    | exact hF
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_stackFree _ _
    | exact bytesRegion_pcFree _ _
    | exact (by pcf)

/-- Body under frame ownership for the typed success path.

    Frames `frameSlotsSaved` through `tshSetupThroughNthThenBodyExit_typed_spec`.
    Post still carries frame `regIs` inside the outcome disjunction; a follow-on
    lemma lifts those to `regsOwnAt` for `abiFrame_spec_own`.
    Requires `vals .x22 = 0` (setup enters with `x22 := 0`). -/
theorem tshTypedSuccessBody
    (newSp : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31 oldOff oldLen wordOld cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8))
    (listLen index : Nat)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (hnzFields : a2 ≠ 0)
    (hnzType : a3 ≠ 0)
    (h22 : vals .x22 = 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hindexW : tshNthIndexW a2 = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (hhi : wordOld &&& ~~~(0xFF#64) = 0)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ∀ offVal lenVal,
      ((offVal + lenVal) - (1 : Word)) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs [a3.truncate 8]
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs a0 (1 : Word),
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      tshTypedSuccessFuel (tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4)
        [a3.truncate 8] payloadBs offVal lenVal ≤ N)
    (hNfail : 1 + 1 ≤ N) :
    let setupFuel := 5 + 3 + 1 + 7 + (1 + 1 + 1 + 3 + 6)
    let callFuel := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let saved := tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4
    let typeBs : List (BitVec 8) := [a3.truncate 8]
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let Amb := tshPostNthGatherAmb (0 : Word) cellOld saved old0 old1 old2 old3 old4 old5
      outBytes typeBs payloadBs os newSp A F
    let callerPre := tshTypedSuccessCallerPre a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
      oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
      input outBytes payloadBs os newSp A F
    cpsTripleWithin (setupFuel + callFuel + N)
      (H + BitVec.ofNat 64 (4 * (1 + tshFrame.length)))
      (H + BitVec.ofNat 64 (4 * (1 + tshFrame.length + tshBody.length)))
      fullCode
      ((.x2 ↦ᵣ newSp) ** regsAt tshFrame vals **
        frameSlotsSaved tshFrame newSp vals ** callerPre)
      (frameSlotsSaved tshFrame newSp vals **
        tshNthOutcomePost
          (fun h => ∃ offVal lenVal,
            ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
              tshKssCallPost newSp
                (newSp + signExtend12 ((-64 : BitVec 12)))
                (tshKssJalPC + 4) tshSegsBase saved.s4
                (tshTypedSegs typeBs
                  (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
                  payloadBs saved.s0 (1 : Word))
                saved.s0 saved.s1 saved.s2 saved.s3 saved.s4 (1 : Word)
                ((offVal + lenVal) - (1 : Word)) A **
              ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
                (.x30 ↦ᵣ tshSegsBase) **
                (.x31 ↦ᵣ (saved.s0 + (1 : Word))) **
                (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
                  (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
                (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
                (stackFree newSp 8 ** bytesRegion a0 input **
                  regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
                  (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F)))) h)
          (fun h => ∃ v11 v12,
            (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
              (((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** savedRegTail saved) **
               ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
                (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
                regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
                (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) ** Amb) h)) := by
  intro setupFuel callFuel saved typeBs outBytes Amb callerPre
  rw [tshFrame_length, tshBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl,
    show 4 * (1 + 8 + 74) = 332 from rfl]
  have hcore := tshSetupThroughNthThenBodyExit_typed_spec
    a0 a1 a2 a3 a4 v5 v6 (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
    (vals .x21) wordOld newSp (vals .x1) v7 v28 v29 v30 v31 oldOff oldLen
    input listLen index cellOld old0 old1 old2 old3 old4 old5
    payloadBs os A F hA hF
    halignBuf hvalidBuf hlen hnzFields hnzType h0
    halignIn hoverIn hvalidIn hge hult hlistLenW hindexW hindex hslack hover
    hvalidBytes hhi h_out_align h_out_valid hpayW hos
    hsegsOk N hNok hNfail
  have hSlots : (frameSlotsSaved tshFrame newSp vals).pcFree :=
    pcFree_frameSlotsSaved _ _ _
  have hframed := cpsTripleWithin_frameR
    (frameSlotsSaved tshFrame newSp vals) hSlots hcore
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hframed
  · simp only [callerPre, tshTypedSuccessCallerPre, tshNthSaved, h22,
      tsh_regsAt_frame'] at hp ⊢
    xperm_hyp hp
  · -- `frameR` leaves `outcome ** slots`; goal wants `slots ** outcome`.
    xperm_hyp hq

/-! ## Body post → `regsOwnAt` (abiFrame shape) -/

private theorem tsh_pcFree_exists2 {α β : Sort _} {F : α → β → Assertion}
    (h : ∀ a b, (F a b).pcFree) :
    Assertion.pcFree (fun hp => ∃ a b, F a b hp) := by
  rintro hp ⟨a, b, hF⟩
  exact h a b hp hF

private theorem tsh_pcFree_or {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    Assertion.pcFree (fun hp => P hp ∨ Q hp) := by
  rintro hp (h | h)
  · exact hP hp h
  · exact hQ hp h

/-- Ok arm with TSH frame `regIs`/`x2` stripped into `regsOwnAt`. -/
def tshTypedSuccessCallerPostOk
    (newSp a0 a3 : Word) (saved : Saved)
    (input _outBytes payloadBs : List (BitVec 8))
    (offVal lenVal : Word) (A F : Assertion) : Assertion :=
  let typeBs : List (BitVec 8) := [a3.truncate 8]
  let kssSp := newSp + signExtend12 ((-64 : BitVec 12))
  let payloadLen := (offVal + lenVal) - (1 : Word)
  let segs := tshTypedSegs typeBs
    (rlpListPrefix payloadLen.toNat)
    payloadBs saved.s0 (1 : Word)
  frameSlotsSaved kssFrame kssSp
      (kssEntryVals (tshKssJalPC + 4) saved.s0 saved.s1 saved.s2 saved.s3 saved.s4
        (1 : Word) payloadLen) **
    kssCallerPost_multi tshSegsBase saved.s4 segs A **
    ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
      (.x30 ↦ᵣ tshSegsBase) **
      (.x31 ↦ᵣ (saved.s0 + (1 : Word))) **
      (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
        (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
      (stackFree newSp 8 ** bytesRegion a0 input **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
        (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F)))

/-- Fail arm with TSH frame `regIs`/`x2` stripped into `regsOwnAt`. -/
def tshTypedSuccessCallerPostFail
    (newSp a0 : Word) (saved : Saved)
    (oldOff oldLen cellOld a3 : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (v11 v12 : Word) (A F : Assertion) : Assertion :=
  let typeBs : List (BitVec 8) := [a3.truncate 8]
  ((stackFree newSp 8 **
    ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
      (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen))) **
   bytesRegion TshBuf typeBs **
   tshPostNthGatherAmbRest cellOld saved old0 old1 old2 old3 old4 old5
     outBytes payloadBs os newSp A F)

/-- Disjunctive body caller-post after stripping TSH frame regs. -/
def tshTypedSuccessCallerPost
    (newSp a0 a3 oldOff oldLen cellOld : Word) (saved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (A F : Assertion) : Assertion :=
  tshNthOutcomePost
    (fun h => ∃ offVal lenVal,
      tshTypedSuccessCallerPostOk newSp a0 a3 saved input outBytes payloadBs
        offVal lenVal A F h)
    (fun h => ∃ v11 v12,
      tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
        old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
        v11 v12 A F h)

theorem tshTypedSuccessCallerPostOk_pcFree
    (newSp a0 a3 : Word) (saved : Saved)
    (input outBytes payloadBs : List (BitVec 8))
    (offVal lenVal : Word) (A F : Assertion)
    (hA : A.pcFree) (hF : F.pcFree) :
    (tshTypedSuccessCallerPostOk newSp a0 a3 saved input outBytes payloadBs
      offVal lenVal A F).pcFree := by
  unfold tshTypedSuccessCallerPostOk
  repeat first
    | exact kssCallerPost_multi_pcFree _ _ _ _ hA
    | exact tshPrefixBssTail_pcFree _
    | exact hA
    | exact hF
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_stackFree _ _
    | exact pcFree_frameSlotsSaved _ _ _
    | exact bytesRegion_pcFree _ _
    | exact (by pcf)

theorem tshTypedSuccessCallerPostFail_pcFree
    (newSp a0 : Word) (saved : Saved)
    (oldOff oldLen cellOld a3 : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (v11 v12 : Word) (A F : Assertion)
    (hA : A.pcFree) (hF : F.pcFree) :
    (tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
      old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
      v11 v12 A F).pcFree := by
  unfold tshTypedSuccessCallerPostFail
  repeat first
    | exact tshPostNthGatherAmbRest_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hF
    | exact hA
    | exact hF
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_stackFree _ _
    | exact bytesRegion_pcFree _ _
    | exact (by pcf)

theorem tshTypedSuccessCallerPost_pcFree
    (newSp a0 a3 oldOff oldLen cellOld : Word) (saved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree) :
    (tshTypedSuccessCallerPost newSp a0 a3 oldOff oldLen cellOld saved
      old0 old1 old2 old3 old4 old5 input outBytes payloadBs os A F).pcFree := by
  unfold tshTypedSuccessCallerPost tshNthOutcomePost
  exact tsh_pcFree_or
    (tsh_pcFree_exists2 (fun offVal lenVal =>
      tshTypedSuccessCallerPostOk_pcFree newSp a0 a3 saved input outBytes
        payloadBs offVal lenVal A F hA hF))
    (tsh_pcFree_exists2 (fun v11 v12 =>
      tshTypedSuccessCallerPostFail_pcFree newSp a0 saved oldOff oldLen cellOld a3
        old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
        v11 v12 A F hA hF))

/-- Reassemble gather Amb as `x22` + type byte + rest. -/
theorem tshPostNthGatherAmb_eq_x22_type_rest
    (v22 cellOld : Word) (csaved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (outBytes typeBs payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion) :
    tshPostNthGatherAmb v22 cellOld csaved old0 old1 old2 old3 old4 old5
        outBytes typeBs payloadBs os sp0 A F =
      ((.x22 ↦ᵣ v22) ** bytesRegion TshBuf typeBs **
        tshPostNthGatherAmbRest cellOld csaved old0 old1 old2 old3 old4 old5
          outBytes payloadBs os sp0 A F) := by
  simp only [tshPostNthGatherAmb, tshPostNthGatherAmbRest]
  ac_rfl

/-- Lift one fail-arm full post (+ TSH frame slots) to `regsOwnAt` shape. -/
theorem tsh_fail_full_slots_to_own
    (newSp : Word) (saved : Saved)
    (a0 a3 oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (v11 v12 : Word) (A F : Assertion)
    (slots : Assertion) (h : PartialState)
    (hq : (slots **
        (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
          (((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** savedRegTail saved) **
           ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
            (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) **
         tshPostNthGatherAmb (0 : Word) cellOld saved old0 old1 old2 old3 old4 old5
           outBytes [a3.truncate 8] payloadBs os newSp A F)) h) :
    ((.x2 ↦ᵣ newSp) ** regsOwnAt tshFrame ** slots **
      tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
        old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
        v11 v12 A F) h := by
  let vals' : Reg → Word := fun
    | .x1 => tshNthJalPC + 4
    | .x8 => saved.s0
    | .x9 => saved.s1
    | .x18 => saved.s2
    | .x19 => saved.s3
    | .x20 => saved.s4
    | .x21 => saved.s5
    | .x22 => (0 : Word)
    | _ => (0 : Word)
  have hq2 : (regsAt tshFrame vals' **
      ((.x2 ↦ᵣ newSp) ** slots **
        tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
          old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
          v11 v12 A F)) h := by
    rw [tsh_regsAt_frame']
    simp only [vals', savedRegTail, tshTypedSuccessCallerPostFail,
      tshPostNthGatherAmb_eq_x22_type_rest] at hq ⊢
    xperm_hyp hq
  have hq3 :=
    sepConj_mono (regsAt_implies_regsOwnAt tshFrame vals') (fun _ hx => hx) h hq2
  rw [tsh_regsOwnAt_frame'] at hq3 ⊢
  xperm_hyp hq3

/-- Lift one ok-arm full post (+ TSH frame slots) to `regsOwnAt` shape. -/
theorem tsh_ok_full_slots_to_own
    (newSp a0 a3 : Word) (saved : Saved)
    (input outBytes payloadBs : List (BitVec 8))
    (offVal lenVal : Word) (A F : Assertion)
    (slots : Assertion) (h : PartialState)
    (hq : (slots **
        ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
          tshKssCallPost newSp
            (newSp + signExtend12 ((-64 : BitVec 12)))
            (tshKssJalPC + 4) tshSegsBase saved.s4
            (tshTypedSegs [a3.truncate 8]
              (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
              payloadBs saved.s0 (1 : Word))
            saved.s0 saved.s1 saved.s2 saved.s3 saved.s4 (1 : Word)
            ((offVal + lenVal) - (1 : Word)) A **
          ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
            (.x30 ↦ᵣ tshSegsBase) **
            (.x31 ↦ᵣ (saved.s0 + (1 : Word))) **
            (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
              (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
            (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
            (stackFree newSp 8 ** bytesRegion a0 input **
              regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
              (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F))))) h) :
    ((.x2 ↦ᵣ newSp) ** regsOwnAt tshFrame ** slots **
      tshTypedSuccessCallerPostOk newSp a0 a3 saved input outBytes payloadBs
        offVal lenVal A F) h := by
  let payloadLen := (offVal + lenVal) - (1 : Word)
  let vals' : Reg → Word := fun
    | .x1 => tshKssJalPC + 4
    | .x8 => saved.s0
    | .x9 => saved.s1
    | .x18 => saved.s2
    | .x19 => saved.s3
    | .x20 => saved.s4
    | .x21 => (1 : Word)
    | .x22 => payloadLen
    | _ => (0 : Word)
  have hq2 : (regsAt tshFrame vals' **
      ((.x2 ↦ᵣ newSp) ** slots **
        tshTypedSuccessCallerPostOk newSp a0 a3 saved input outBytes payloadBs
          offVal lenVal A F)) h := by
    rw [tsh_regsAt_frame']
    simp only [vals', payloadLen, tshKssCallPost, tshKssSregs,
      tshTypedSuccessCallerPostOk] at hq ⊢
    xperm_hyp hq
  have hq3 :=
    sepConj_mono (regsAt_implies_regsOwnAt tshFrame vals') (fun _ hx => hx) h hq2
  rw [tsh_regsOwnAt_frame'] at hq3 ⊢
  xperm_hyp hq3

/-- Body under frame with `regsOwnAt` — ready for `abiFrame_spec_own`. -/
theorem tshTypedSuccessBody_own
    (newSp : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31 oldOff oldLen wordOld cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8))
    (listLen index : Nat)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (hnzFields : a2 ≠ 0)
    (hnzType : a3 ≠ 0)
    (h22 : vals .x22 = 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hindexW : tshNthIndexW a2 = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (hhi : wordOld &&& ~~~(0xFF#64) = 0)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ∀ offVal lenVal,
      ((offVal + lenVal) - (1 : Word)) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs [a3.truncate 8]
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs a0 (1 : Word),
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      tshTypedSuccessFuel (tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4)
        [a3.truncate 8] payloadBs offVal lenVal ≤ N)
    (hNfail : 1 + 1 ≤ N) :
    let setupFuel := 5 + 3 + 1 + 7 + (1 + 1 + 1 + 3 + 6)
    let callFuel := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let saved := tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let callerPre := tshTypedSuccessCallerPre a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
      oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
      input outBytes payloadBs os newSp A F
    let callerPost := tshTypedSuccessCallerPost newSp a0 a3 oldOff oldLen cellOld saved
      old0 old1 old2 old3 old4 old5 input outBytes payloadBs os A F
    cpsTripleWithin (setupFuel + callFuel + N)
      (H + BitVec.ofNat 64 (4 * (1 + tshFrame.length)))
      (H + BitVec.ofNat 64 (4 * (1 + tshFrame.length + tshBody.length)))
      fullCode
      ((.x2 ↦ᵣ newSp) ** regsAt tshFrame vals **
        frameSlotsSaved tshFrame newSp vals ** callerPre)
      ((.x2 ↦ᵣ newSp) ** regsOwnAt tshFrame **
        frameSlotsSaved tshFrame newSp vals ** callerPost) := by
  intro setupFuel callFuel saved outBytes callerPre callerPost
  have hbody := tshTypedSuccessBody newSp vals a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
    oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
    input payloadBs os listLen index A F hA hF
    halignBuf hvalidBuf hlen hnzFields hnzType h22 h0
    halignIn hoverIn hvalidIn hge hult hlistLenW hindexW hindex hslack hover
    hvalidBytes hhi h_out_align h_out_valid hpayW hos
    hsegsOk N hNok hNfail
  refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [callerPre] at hp ⊢
      exact hp) (fun h hq => ?_) hbody
  -- hq : (slots ** outcome_full) h
  -- goal : (x2 ** regsOwnAt ** slots ** callerPost) h
  simp only [callerPost, tshTypedSuccessCallerPost]
  obtain ⟨h1, h2, hd, hu, hs, ho⟩ :=
    show (frameSlotsSaved tshFrame newSp vals **
        tshNthOutcomePost
          (fun hp => ∃ offVal lenVal,
            ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
              tshKssCallPost newSp
                (newSp + signExtend12 ((-64 : BitVec 12)))
                (tshKssJalPC + 4) tshSegsBase saved.s4
                (tshTypedSegs [a3.truncate 8]
                  (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
                  payloadBs saved.s0 (1 : Word))
                saved.s0 saved.s1 saved.s2 saved.s3 saved.s4 (1 : Word)
                ((offVal + lenVal) - (1 : Word)) A **
              ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
                (.x30 ↦ᵣ tshSegsBase) **
                (.x31 ↦ᵣ (saved.s0 + (1 : Word))) **
                (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
                  (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
                (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
                (stackFree newSp 8 ** bytesRegion a0 input **
                  regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
                  (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F)))) hp)
          (fun hp => ∃ v11 v12,
            (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
              (((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** savedRegTail saved) **
               ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
                (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
                regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
                (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) **
             tshPostNthGatherAmb (0 : Word) cellOld saved old0 old1 old2 old3 old4 old5
               outBytes [a3.truncate 8] payloadBs os newSp A F) hp)) h from hq
  cases ho with
  | inl hok =>
    obtain ⟨offVal, lenVal, hf⟩ := hok
    have hfull : ((frameSlotsSaved tshFrame newSp vals) **
        ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
          tshKssCallPost newSp
            (newSp + signExtend12 ((-64 : BitVec 12)))
            (tshKssJalPC + 4) tshSegsBase saved.s4
            (tshTypedSegs [a3.truncate 8]
              (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
              payloadBs saved.s0 (1 : Word))
            saved.s0 saved.s1 saved.s2 saved.s3 saved.s4 (1 : Word)
            ((offVal + lenVal) - (1 : Word)) A **
          ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
            (.x30 ↦ᵣ tshSegsBase) **
            (.x31 ↦ᵣ (saved.s0 + (1 : Word))) **
            (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
              (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
            (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
            (stackFree newSp 8 ** bytesRegion a0 input **
              regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
              (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F))))) h :=
      ⟨h1, h2, hd, hu, hs, hf⟩
    have hown := tsh_ok_full_slots_to_own newSp a0 a3 saved input outBytes payloadBs
      offVal lenVal A F (frameSlotsSaved tshFrame newSp vals) h hfull
    have himpl :
        ∀ h',
          tshTypedSuccessCallerPostOk newSp a0 a3 saved input outBytes payloadBs
              offVal lenVal A F h' →
          tshNthOutcomePost
            (fun hp => ∃ o l,
              tshTypedSuccessCallerPostOk newSp a0 a3 saved input outBytes payloadBs
                o l A F hp)
            (fun hp => ∃ v11 v12,
              tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
                old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
                v11 v12 A F hp) h' :=
      fun _ hx => tshNthOutcomePost_inl ⟨offVal, lenVal, hx⟩
    -- `**` is right-assoc: weaken the post atom three mono_right deep.
    exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right himpl))) h hown
  | inr hfail =>
    obtain ⟨v11, v12, hf⟩ := hfail
    have hfull : ((frameSlotsSaved tshFrame newSp vals) **
        (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
          (((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** savedRegTail saved) **
           ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
            (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) **
         tshPostNthGatherAmb (0 : Word) cellOld saved old0 old1 old2 old3 old4 old5
           outBytes [a3.truncate 8] payloadBs os newSp A F)) h :=
      ⟨h1, h2, hd, hu, hs, hf⟩
    have hown := tsh_fail_full_slots_to_own newSp saved a0 a3 oldOff oldLen cellOld
      old0 old1 old2 old3 old4 old5 input outBytes payloadBs os v11 v12 A F
      (frameSlotsSaved tshFrame newSp vals) h hfull
    have himpl :
        ∀ h',
          tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
              old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
              v11 v12 A F h' →
          tshNthOutcomePost
            (fun hp => ∃ o l,
              tshTypedSuccessCallerPostOk newSp a0 a3 saved input outBytes payloadBs
                o l A F hp)
            (fun hp => ∃ w11 w12,
              tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
                old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
                w11 w12 A F hp) h' :=
      fun _ hx => tshNthOutcomePost_inr ⟨v11, v12, hx⟩
    exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right himpl))) h hown

/-! ## Whole-routine typed success (`abiFrame_spec_own`) -/

/-- Typed success: whole `tx_signing_hash` under `abiFrame`.

    Preconditions are static (buffers, alignment, header-shape, index/list
    lengths). Outcomes (nth ok vs fail) live in the postcondition disjunction
    `tshTypedSuccessCallerPost`. Requires `vals .x22 = 0` (setup enters with
    `x22 := 0`).

    Distinct from `tx_signing_hash_spec_within_empty_len` (`a1 = 0` fail slice). -/
theorem tx_signing_hash_spec_within
    (sp0 ret : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31 oldOff oldLen wordOld cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8))
    (listLen index : Nat)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (hnzFields : a2 ≠ 0)
    (hnzType : a3 ≠ 0)
    (h22 : vals .x22 = 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hindexW : tshNthIndexW a2 = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (hhi : wordOld &&& ~~~(0xFF#64) = 0)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ∀ offVal lenVal,
      ((offVal + lenVal) - (1 : Word)) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs [a3.truncate 8]
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs a0 (1 : Word),
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      tshTypedSuccessFuel (tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4)
        [a3.truncate 8] payloadBs offVal lenVal ≤ N)
    (hNfail : 1 + 1 ≤ N) :
    let newSp := sp0 + signExtend12 (-64 : BitVec 12)
    let setupFuel := 5 + 3 + 1 + 7 + (1 + 1 + 1 + 3 + 6)
    let callFuel := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let bodySteps := setupFuel + callFuel + N
    let saved := tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let callerPre := tshTypedSuccessCallerPre a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
      oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
      input outBytes payloadBs os newSp A F
    let callerPost := tshTypedSuccessCallerPost newSp a0 a3 oldOff oldLen cellOld saved
      old0 old1 old2 old3 old4 old5 input outBytes payloadBs os A F
    cpsTripleWithin (1 + tshFrame.length + bodySteps + tshFrame.length + 1 + 1)
      H ret fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt tshFrame vals **
        frameSlotsOwn tshFrame newSp ** callerPre)
      ((.x2 ↦ᵣ sp0) ** regsAt tshFrame vals **
        frameSlotsSaved tshFrame newSp vals ** callerPost) := by
  intro newSp setupFuel callFuel bodySteps saved outBytes callerPre callerPost
  have h := abiFrame_spec_own H sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    tshFrame (0 : BitVec 12) tshSregs vals tshBody bodySteps
    callerPre callerPost
    fullCode tshFrame_cons tshFrame_ne_zero
    (by rw [tshFrame_length]; decide)
    (by
      rw [txSigningHash_prog_eq_abiFrame, tsh_prog_length]
      decide)
    hret halign (tshFrame_restore sp0)
    (tshTypedSuccessCallerPre_pcFree a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
      oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
      input outBytes payloadBs os newSp A F hA hF)
    (tshTypedSuccessCallerPost_pcFree newSp a0 a3 oldOff oldLen cellOld saved
      old0 old1 old2 old3 old4 old5 input outBytes payloadBs os A F hA hF)
    tsh_ofProg_sub_fullCode
    (by
      simpa only [newSp, setupFuel, callFuel, bodySteps, saved, outBytes, callerPre, callerPost]
        using tshTypedSuccessBody_own newSp vals a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
          oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
          input payloadBs os listLen index A F hA hF
          halignBuf hvalidBuf hlen hnzFields hnzType h22 h0
          halignIn hoverIn hvalidIn hge hult hlistLenW hindexW hindex hslack hover
          hvalidBytes hhi h_out_align h_out_valid hpayW hos
          hsegsOk N hNok hNfail)
  rw [tshFrame_length] at h
  exact h

/-! ## SpecRef correspondence shape (K145 / #12038)

    The machine proof above already composes every `rlp_encode_list_prefix`
    width through `tsh_prefix_any_callWithin`.  This bridge therefore carries
    the actual truncated-list payload, rather than a guessed width band, and
    leaves the eventual proof to identify that payload with the corresponding
    SpecRef transaction case.
-/

/-- The K145 transaction cases supported by `tx_signing_hash` itself.

    Legacy EIP-155 is deliberately absent: it appends `(chain_id, 0, 0)` and
    is handled by `tx_signing_hash_legacy_eip155` in the later K146 rung. -/
def txSigningHashSpecRefTarget
    (tx : EvmAsm.Stateless.SpecRef.Transaction)
    (nFields typePrefix : Word) : Option EvmAsm.Stateless.SpecRef.Hash32 :=
  open EvmAsm.Stateless.SpecRef in
  match tx with
  | .legacy t =>
      if nFields = 6 ∧ typePrefix = 0 then some (signing_hash_pre155 t) else none
  | .accessList t =>
      if nFields = 8 ∧ typePrefix = 1 then some (signing_hash_2930 t) else none
  | .feeMarket t =>
      if nFields = 9 ∧ typePrefix = 2 then some (signing_hash_1559 t) else none
  | .blob t =>
      if nFields = 11 ∧ typePrefix = 3 then some (signing_hash_4844 t) else none
  | .setCode t =>
      if nFields = 10 ∧ typePrefix = 4 then some (signing_hash_7702 t) else none

def txSigningHashSpecRefItems
    (tx : EvmAsm.Stateless.SpecRef.Transaction) :
    List EvmAsm.EL.RLP.RLPItem :=
  match EvmAsm.Stateless.SpecRef.txToRlpItem tx with
  | .list items => items
  | _ => []

/-- KSS post with the digest rewritten to the selected SpecRef hash. -/
def txSigningHashSpecRefKssPost
    (segsBase outputBase : Word) (segs : List KssSeg)
    (expected : EvmAsm.Stateless.SpecRef.Hash32) (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (regOwn .x11) ** (regOwn .x12) **
    ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
    (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
    regOwns kssFreeTemps **
    bytesRegion KssZk3
      (kssFinalState
        (kssAbsorbed (kssMsg segs) (kssMsg segs).length)
        (kssFill (kssMsg segs).length)) **
    bytesRegion outputBase expected **
    kssSegsIs segsBase segs ** A

/-- Success arm of the K145 post, with only the digest changed to SpecRef. -/
def txSigningHashSpecRefPostOk
    (newSp a0 a3 : Word) (saved : Saved)
    (input _outBytes payloadBs : List (BitVec 8))
    (offVal lenVal : Word) (expected : EvmAsm.Stateless.SpecRef.Hash32)
    (A F : Assertion) : Assertion :=
  let typeBs : List (BitVec 8) := [a3.truncate 8]
  let kssSp := newSp + signExtend12 ((-64 : BitVec 12))
  let payloadLen := (offVal + lenVal) - (1 : Word)
  let segs := tshTypedSegs typeBs
    (rlpListPrefix payloadLen.toNat) payloadBs saved.s0 (1 : Word)
  frameSlotsSaved kssFrame kssSp
      (kssEntryVals (tshKssJalPC + 4) saved.s0 saved.s1 saved.s2 saved.s3 saved.s4
        (1 : Word) payloadLen) **
    txSigningHashSpecRefKssPost tshSegsBase saved.s4 segs expected A **
    ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) **
      (.x30 ↦ᵣ tshSegsBase) **
      (.x31 ↦ᵣ (saved.s0 + (1 : Word))) **
      (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
      (stackFree newSp 8 ** bytesRegion a0 input **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
        (tshPrefixBssTail payloadLen ** F)))

/-- Full K145 post: preserve the machine failure arm verbatim, while the
    success arm exposes the selected SpecRef digest. -/
def txSigningHashSpecRefPost
    (newSp a0 a3 oldOff oldLen cellOld : Word) (saved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input outBytes payloadBs os : List (BitVec 8))
    (expected : EvmAsm.Stateless.SpecRef.Hash32) (A F : Assertion) : Assertion :=
  tshNthOutcomePost
    (fun h => ∃ offVal lenVal,
      txSigningHashSpecRefPostOk newSp a0 a3 saved input outBytes payloadBs
        offVal lenVal expected A F h)
    (fun h => ∃ v11 v12,
      tshTypedSuccessCallerPostFail newSp a0 saved oldOff oldLen cellOld a3
        old0 old1 old2 old3 old4 old5 input outBytes payloadBs os
        v11 v12 A F h)

/-- Correspondence statement for the already-proven K145 machine triple.

    The conclusion is a full triple: the failure arm remains unchanged and
    only the success arm rewrites the KSS output to the selected SpecRef hash.
    `h_decoder_payload` is the one named decoder-bridge residual: it relates
    the caller input and the actual gathered payload to the SpecRef RLP
    preimage.  No RLP width-band premise appears because the total prefix
    composition discharges all nine bands. -/
theorem tx_signing_hash_specRef_correspondence
    (tx : EvmAsm.Stateless.SpecRef.Transaction)
    (sp0 ret : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31 oldOff oldLen wordOld cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8))
    (listLen index : Nat) (expected : EvmAsm.Stateless.SpecRef.Hash32)
    (nFields typePrefix : Word)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (hnzFields : a2 ≠ 0)
    (hnzType : a3 ≠ 0)
    (h22 : vals .x22 = 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hindexW : tshNthIndexW a2 = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (hhi : wordOld &&& ~~~(0xFF#64) = 0)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ∀ offVal lenVal,
      ((offVal + lenVal) - (1 : Word)) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs [a3.truncate 8]
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs a0 (1 : Word),
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      tshTypedSuccessFuel (tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4)
        [a3.truncate 8] payloadBs offVal lenVal ≤ N)
    (hNfail : 1 + 1 ≤ N)
    (h_nFields : nFields = BitVec.ofNat 64 listLen)
    (h_typePrefix : typePrefix = a3)
    (h_decoder_payload :
      EvmAsm.EL.RLP.decodeFully input =
          some (EvmAsm.Stateless.SpecRef.txToRlpItem tx) ∧
      EvmAsm.EL.RLP.encode
          (.list ((txSigningHashSpecRefItems tx).take nFields.toNat)) =
        rlpListPrefix payloadBs.length ++ payloadBs)
    (h_target : txSigningHashSpecRefTarget tx nFields typePrefix = some expected) :
    let newSp := sp0 + signExtend12 (-64 : BitVec 12)
    let setupFuel := 5 + 3 + 1 + 7 + (1 + 1 + 1 + 3 + 6)
    let callFuel := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let bodySteps := setupFuel + callFuel + N
    let saved := tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let callerPre := tshTypedSuccessCallerPre a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31
      oldOff oldLen wordOld cellOld old0 old1 old2 old3 old4 old5
      input outBytes payloadBs os newSp A F
    let callerPost := txSigningHashSpecRefPost newSp a0 a3 oldOff oldLen cellOld saved
      old0 old1 old2 old3 old4 old5 input outBytes payloadBs os expected A F
    cpsTripleWithin (1 + tshFrame.length + bodySteps + tshFrame.length + 1 + 1)
      H ret fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt tshFrame vals **
        frameSlotsOwn tshFrame newSp ** callerPre)
      ((.x2 ↦ᵣ sp0) ** regsAt tshFrame vals **
        frameSlotsSaved tshFrame newSp vals ** callerPost) := by
  intro newSp setupFuel callFuel bodySteps saved outBytes callerPre callerPost
  have h := tx_signing_hash_spec_within
    sp0 ret vals a0 a1 a2 a3 a4 v5 v6 v7 v28 v29 v30 v31 oldOff oldLen wordOld cellOld
    old0 old1 old2 old3 old4 old5 input payloadBs os listLen index
    A F hA hF hret halign halignBuf hvalidBuf hlen hnzFields hnzType h22 h0
    halignIn hoverIn hvalidIn hge hult hlistLenW hindexW hindex hslack hover
    hvalidBytes hhi h_out_align h_out_valid hpayW hos hsegsOk N hNok hNfail
  rw [tshFrame_length] at h
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h
  intro hq hpost
  rcases h_decoder_payload with ⟨h_decode, h_payload⟩
  have hhash : ∀ offVal lenVal,
      EvmAsm.Stateless.SpecRef.keccak256
          (kssMsg (tshTypedSegs [a3.truncate 8]
            (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
            payloadBs saved.s0 (1 : Word))) = expected := by
    have hlen : ∀ offVal lenVal,
        ((offVal + lenVal) - (1 : Word)).toNat = payloadBs.length := by
      intro offVal lenVal
      have hseg := hsegsOk offVal lenVal
        (a0 + (1 : Word), payloadBs) (by simp [tshTypedSegs])
      rw [hpayW offVal lenVal]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hseg.2.1]
    intro offVal lenVal
    rw [hlen offVal lenVal]
    simp only [kssMsg, tshTypedSegs, List.flatMap_cons, List.flatMap_nil]
    have hinputLen : input.length < 2 ^ 64 := by omega
    have hlistLenLt : listLen < 2 ^ 64 := by omega
    have hnFieldsToNat : nFields.toNat = listLen := by
      rw [h_nFields, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlistLenLt]
    cases tx with
    | legacy t =>
      simp [txSigningHashSpecRefTarget, txSigningHashSpecRefItems,
        EvmAsm.Stateless.SpecRef.txToRlpItem, hnFieldsToNat,
        h_typePrefix] at h_target h_payload ⊢
      rcases h_target with ⟨⟨hn, ha⟩, he⟩
      exact False.elim (hnzType ha)
    | accessList t =>
      simp [txSigningHashSpecRefTarget, txSigningHashSpecRefItems,
        EvmAsm.Stateless.SpecRef.txToRlpItem, hnFieldsToNat,
        h_typePrefix] at h_target h_payload ⊢
      rcases h_target with ⟨⟨hn, ha⟩, he⟩
      have hnNat : nFields.toNat = 8 := by simp [hn]
      have hlist : listLen = 8 := by omega
      simp [hlist] at h_payload
      rw [← he]
      simp [ha, signing_hash_2930]
      rw [← h_payload]
      rfl
    | feeMarket t =>
      simp [txSigningHashSpecRefTarget, txSigningHashSpecRefItems,
        EvmAsm.Stateless.SpecRef.txToRlpItem, hnFieldsToNat,
        h_typePrefix] at h_target h_payload ⊢
      rcases h_target with ⟨⟨hn, ha⟩, he⟩
      have hnNat : nFields.toNat = 9 := by simp [hn]
      have hlist : listLen = 9 := by omega
      simp [hlist] at h_payload
      rw [← he]
      simp [ha, signing_hash_1559]
      rw [← h_payload]
      rfl
    | blob t =>
      simp [txSigningHashSpecRefTarget, txSigningHashSpecRefItems,
        EvmAsm.Stateless.SpecRef.txToRlpItem, hnFieldsToNat,
        h_typePrefix] at h_target h_payload ⊢
      rcases h_target with ⟨⟨hn, ha⟩, he⟩
      have hnNat : nFields.toNat = 11 := by simp [hn]
      have hlist : listLen = 11 := by omega
      simp [hlist] at h_payload
      rw [← he]
      simp [ha, signing_hash_4844]
      rw [← h_payload]
      rfl
    | setCode t =>
      simp [txSigningHashSpecRefTarget, txSigningHashSpecRefItems,
        EvmAsm.Stateless.SpecRef.txToRlpItem, hnFieldsToNat,
        h_typePrefix] at h_target h_payload ⊢
      rcases h_target with ⟨⟨hn, ha⟩, he⟩
      have hnNat : nFields.toNat = 10 := by simp [hn]
      have hlist : listLen = 10 := by omega
      simp [hlist] at h_payload
      rw [← he]
      simp [ha, signing_hash_7702]
      rw [← h_payload]
      rfl
  have himpl :
      ∀ h',
        tshTypedSuccessCallerPost newSp a0 a3 oldOff oldLen cellOld saved
            old0 old1 old2 old3 old4 old5 input outBytes payloadBs os A F h' →
        txSigningHashSpecRefPost newSp a0 a3 oldOff oldLen cellOld saved
            old0 old1 old2 old3 old4 old5 input outBytes payloadBs os expected A F h' := by
    intro h' ho
    simp only [tshTypedSuccessCallerPost, txSigningHashSpecRefPost,
      tshNthOutcomePost] at ho ⊢
    cases ho with
    | inl hok =>
        rcases hok with ⟨offVal, lenVal, hok⟩
        left
        refine ⟨offVal, lenVal, ?_⟩
        simp only [txSigningHashSpecRefPostOk, tshTypedSuccessCallerPostOk,
          txSigningHashSpecRefKssPost, kssCallerPost_multi] at hok ⊢
        rw [hhash offVal lenVal] at hok
        exact hok
    | inr hfail =>
        rcases hfail with ⟨v11, v12, hfail⟩
        exact Or.inr ⟨v11, v12, hfail⟩
  exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right himpl))) hq hpost

end EvmAsm.Codegen.TxSigningHashSpec
