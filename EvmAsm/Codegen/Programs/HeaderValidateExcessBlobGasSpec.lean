/-
  K70 `header_validate_excess_blob_gas`.

  This file owns the whole-routine contract for the linked K70 wrapper.  The
  Amsterdam price routine is not yet rowed, so its whole-routine contract is
  an explicit premise of the K70 composition.  The premise is stated at the
  price routine's actual ABI rather than at a proof-convenient projection:
  x10 carries the excess value, x11 carries the 32-byte BE output pointer, and
  the callee owns a 208-byte frame plus its three 48-byte working regions.
  `priceEntryRest_inhabited` keeps that gate honest by exhibiting the concrete
  non-degenerate entry layout already checked for Amsterdam.
-/

import EvmAsm.Codegen.Programs.Arm2Probe
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceU256Sat
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ValidateHeaderGasCorrespondence
open EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat

abbrev K : Word := ExcessK
abbrev Ret : Word := ExcessRet
abbrev PriceK : Word := (GuestAddrs.amsterdam_blob_gas_price_u256 : Word)

def priceFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]

def priceSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48),
   (.x22, 56)]

def priceFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

def priceOutputOwn (outPtr : Word) : Assertion :=
  memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) **
    memOwn (outPtr + 24)

def priceOutputPost (status outPtr : Word)
    (outBytes : List (BitVec 8)) : Assertion :=
  if status = (0 : Word) then bytesRegion outPtr outBytes
  else priceOutputOwn outPtr

def priceEntryRest
    (sp0 ret : Word) (vals : Reg → Word)
    (excess outPtr : Word) (scratch : Assertion) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsOwn priceFrame (sp0 + signExtend12 (-208 : BitVec 12)) **
  regsAt priceSavedFrame vals ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] ** scratch

def priceCalleePost
    (sp0 ret : Word) (vals : Reg → Word)
    (status outPtr : Word) (outBytes : List (BitVec 8))
    (scratchPost : Assertion) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved priceFrame (sp0 + signExtend12 (-208 : BitVec 12))
    (priceFrameVals ret vals) ** regsAt priceSavedFrame vals **
  (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ outPtr) **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
  priceOutputPost status outPtr outBytes ** scratchPost

def priceCode : CodeReq := CodeReq.ofProg PriceK amsterdamBlobGasPriceU256_prog

/-- The explicit missing-seam hypothesis consumed by the K70 route.  The
    result is an N-branch because status 0 preserves the exact output bytes,
    while status 1 leaves the output unspecified and therefore returns only
    ownership of its four dwords.  Both branches return to the K70 instruction
    immediately after the call. -/
def priceContract
    (n : Nat) (sp0 ret : Word) (vals : Reg → Word)
    (excess outPtr : Word) (outBytes : List (BitVec 8))
    (scratch scratchPost : Assertion) : Prop :=
  cpsNBranchWithin n PriceK priceCode
    (priceEntryRest sp0 ret vals excess outPtr scratch)
    [ (ret, priceCalleePost sp0 ret vals 0 outPtr outBytes scratchPost),
      (ret, priceCalleePost sp0 ret vals 1 outPtr outBytes scratchPost) ]

def priceScratch : Assertion :=
  bytesRegion sampleStackA zero48 ** bytesRegion sampleStackB zero48 **
  bytesRegion sampleStackC zero48 ** bytesRegion sampleOutPtr zero32

theorem priceEntryRest_sample_eq :
    priceEntryRest sampleSp0 sampleRet sampleSaved
      (0 : Word) sampleOutPtr priceScratch = entryPre := by
  funext h
  simp [priceEntryRest, priceScratch, entryPre, priceFrame, priceSavedFrame,
    sampleFrame, sampleSaved, sampleSp0, sampleNewSp,
    sampleStackA, sampleStackB, sampleStackC, sampleOutPtr,
    frameSlotsOwn, regsAt, regOwns, sepConj_emp_right']
  simp only [sepConj_assoc']
  constructor <;> intro hq <;> xperm_hyp hq

/-- The price premise is not an uninhabited symbolic shape: it has the
    concrete non-overlapping layout used by the existing Amsterdam witness.
    The witness is intentionally retained here rather than relying on the
    existence of the separate `entryState_exists` theorem. -/
theorem priceEntryRest_inhabited :
    (priceEntryRest sampleSp0 sampleRet sampleSaved
      (0 : Word) sampleOutPtr priceScratch).holdsFor sampleState := by
  rw [priceEntryRest_sample_eq]
  exact entryState_exists.2.2

/-! ## ABI shell

The wrapper's prologue and epilogue are already an ordinary `abiFrame_spec`
instance.  Keeping this shell separate makes the remaining route obligation
visible: the body theorem below is a continuation from `K + 32` to `K + 248`,
not a renamed copy of the final whole-routine statement. -/

def k70Body : Program := headerValidateExcessBlobGas_prog.drop 8 |>.take 54

def k70BodyPre
    (spC : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 : Word) (scratch : Assertion) : Assertion :=
  ((.x2 ↦ᵣ spC) ** regsAt excessFrame vals **
    frameSlotsSaved excessFrame spC vals **
    (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
    regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
    (.x0 ↦ᵣ (0 : Word)) ** scratch)

def k70BodyPost
    (spC : Word) (vals bodyVals : Reg → Word)
    (status : Word) (scratchPost : Assertion) : Assertion :=
  ((.x2 ↦ᵣ spC) ** regsAt excessFrame bodyVals **
    frameSlotsSaved excessFrame spC vals ** (.x10 ↦ᵣ status) **
    regOwns [.x5, .x6, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
    (.x0 ↦ᵣ (0 : Word)) ** scratchPost)

theorem k70_abi_from_body
    {cr : CodeReq} {bodySteps : Nat}
    (sp0 ret : Word) (vals bodyVals : Reg → Word)
    (a0 a1 a2 a3 status : Word)
    (scratch scratchPost F : Assertion)
    (hret : vals .x1 = ret)
    (hretAlign : (ret &&& ~~~(1 : Word)) = ret)
    (hscratch : scratch.pcFree) (hscratchPost : scratchPost.pcFree)
    (hF : F.pcFree)
    (hsub : ∀ a i,
      CodeReq.ofProg K (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12)
        excessFrame k70Body) a = some i → cr a = some i)
    (hbody : cpsTripleWithin bodySteps (K + 32) (K + 248) cr
      (k70BodyPre (sp0 + signExtend12 (-64 : BitVec 12)) vals
        a0 a1 a2 a3 scratch)
      (k70BodyPost (sp0 + signExtend12 (-64 : BitVec 12)) vals bodyVals
        status scratchPost)) :
    cpsTripleWithin (1 + excessFrame.length + bodySteps + excessFrame.length + 1 + 1)
      K ret cr
      (((.x1 ↦ᵣ ret) ** excessEntryRest sp0 vals a0 a1 a2 a3 scratch) ** F)
      (excessCalleePost sp0 vals status ret scratchPost ** F) := by
  have hframe : excessFrame = (.x1, (0 : BitVec 12)) :: excessSavedFrame := by
    rfl
  have habi := abiFrame_spec
    (base := K) (sp0 := sp0) (ret := ret)
    (negImm := (-64 : BitVec 12)) (posImm := (64 : BitVec 12))
    (frame := excessFrame) (raOfs := (0 : BitVec 12))
    (sregs := excessSavedFrame) (vals := vals) (vals' := bodyVals)
    (body := k70Body) (bodySteps := bodySteps)
    (callerPre :=
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
      (.x0 ↦ᵣ (0 : Word)) ** scratch)
    (callerPost :=
      (.x10 ↦ᵣ status) **
      regOwns [.x5, .x6, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
      (.x0 ↦ᵣ (0 : Word)) ** scratchPost)
    (cr := cr) hframe (by decide) (by decide) (by decide)
    hret hretAlign
    (by
      rw [BitVec.add_assoc,
        show signExtend12 (-64 : BitVec 12) + signExtend12 (64 : BitVec 12) =
          (0 : Word) from by decide]
      exact BitVec.add_zero sp0)
    (by pcf; exact hscratch) (by pcf; exact hscratchPost) hsub (by
      have hentry : K + BitVec.ofNat 64 (4 * (1 + excessFrame.length)) = K + 32 := by
        decide
      have hexit : K + BitVec.ofNat 64
          (4 * (1 + excessFrame.length + k70Body.length)) = K + 248 := by
        decide
      rw [hentry, hexit]
      simpa [k70BodyPre, k70BodyPost] using hbody)
  have habiF := cpsTripleWithin_frameR F hF habi
  refine cpsTripleWithin_weaken (P := _) (Q := _) ?_ ?_ habiF
  · intro h hp
    rw [← hret] at hp
    simp [excessEntryRest, excessFrame, excessSavedFrame,
      frameSlotsOwn, regsAt, regOwns, sepConj_emp_right'] at hp ⊢
    xperm_hyp hp
  · intro h hq
    simp [excessCalleePost, excessFrame, excessSavedFrame,
      excessFrameVals, frameSlotsSaved, regsAt, regOwns,
      sepConj_emp_right'] at hq ⊢
    rw [← hret]
    xperm_hyp hq

end EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
