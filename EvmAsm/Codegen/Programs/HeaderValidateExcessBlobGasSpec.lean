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

theorem k70_body_mem
    {cr : CodeReq}
    (hsub : ∀ a i,
      CodeReq.ofProg K (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12)
        excessFrame k70Body) a = some i → cr a = some i) :
    ∀ a i, CodeReq.ofProg (K + 32) k70Body a = some i → cr a = some i := by
  intro a i hi
  let pre : Program :=
    [.ADDI .x2 .x2 (-64 : BitVec 12)] ++ storeProg excessFrame
  let suf : Program :=
    loadProg excessFrame ++ [.ADDI .x2 .x2 (64 : BitVec 12), .JALR .x0 .x1 0]
  have hfull : abiFrameProg (-64 : BitVec 12) (64 : BitVec 12)
      excessFrame k70Body = pre ++ k70Body ++ suf := by
    rfl
  have hpre : pre.length = 8 := by
    simp [pre, excessFrame]
  have hmid : CodeReq.ofProg (K + BitVec.ofNat 64 (4 * pre.length)) k70Body a = some i := by
    simpa [hpre] using hi
  have hbound :
      4 * (pre ++ k70Body ++ suf).length < 2 ^ 64 := by
    simp [pre, suf, storeProg_length, loadProg_length]
    decide
  have hmem := CodeReq.ofProg_mono_subrange K
    pre k70Body suf
    hbound a i hmid
  have hmem' : CodeReq.ofProg K
      (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) excessFrame k70Body) a = some i := by
    rw [hfull]
    simpa [List.append_assoc] using hmem
  exact hsub a i hmem'

def k70StatusTailRest
    (spC : Word) (vals : Reg → Word) (scratch : Assertion) : Assertion :=
  (.x2 ↦ᵣ spC) ** regsAt excessFrame vals **
  frameSlotsSaved excessFrame spC vals **
  regOwns [.x5, .x6, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word)) ** scratch

theorem k70_status1_tail_spec
    {cr : CodeReq}
    (spC : Word) (vals : Reg → Word) (old10 : Word)
    (scratch : Assertion) (hscratch : scratch.pcFree)
    (hsub : ∀ a i,
      CodeReq.ofProg K (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12)
        excessFrame k70Body) a = some i → cr a = some i) :
    cpsTripleWithin 2 (K + 236) (K + 248) cr
      (k70StatusTailRest spC vals scratch ** (.x10 ↦ᵣ old10))
      (k70StatusTailRest spC vals scratch ** (.x10 ↦ᵣ (1 : Word))) := by
  let rest := k70StatusTailRest spC vals scratch
  have hrest : rest.pcFree := by
    dsimp [rest, k70StatusTailRest]
    pcf
    exact hscratch
  have hliAny : ∀ v, cpsTripleWithin 1 (K + 236) (K + 240) cr
      (rest ** (.x10 ↦ᵣ v)) (rest ** (.x10 ↦ᵣ (1 : Word))) := by
    intro v
    have hli := li_spec_gen_within .x10 v (1 : Word) (K + 236) (by decide)
    have hliMem := CodeReq.ofProg_mem_at K (K + 236)
      (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) excessFrame k70Body) 59
      (.LI .x10 (1 : Word)) (by decide) (by decide) rfl (by decide)
    have hliC := cpsTripleWithin_extend_code
      (fun a i hi => hsub a i (hliMem a i hi)) hli
    have hliF := cpsTripleWithin_frameR rest hrest hliC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hliOwn := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x10) (P := rest) (Q := rest ** (.x10 ↦ᵣ (1 : Word))) hliAny
  have hj := jal_x0_spec_gen_within (8 : BitVec 21) (K + 240)
  rw [show (K + 240) + signExtend21 (8 : BitVec 21) = K + 248 from by decide] at hj
  have hjMem := CodeReq.ofProg_mem_at K (K + 240)
    (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) excessFrame k70Body) 60
    (.JAL .x0 (8 : BitVec 21)) (by decide) (by decide) rfl (by decide)
  have hjC := cpsTripleWithin_extend_code
    (fun a i hi => hsub a i (hjMem a i hi)) hj
  have hjF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (1 : Word)) ** rest)
    (by
      dsimp [rest, k70StatusTailRest]
      pcf
      exact hscratch) hjC
  have hjump : cpsTripleWithin 1 (K + 240) (K + 248) cr
      (rest ** (.x10 ↦ᵣ (1 : Word)))
      (rest ** (.x10 ↦ᵣ (1 : Word))) := by
    simpa [rest, sepConj_assoc', sepConj_comm', sepConj_left_comm',
      sepConj_emp_left', sepConj_emp_right'] using hjF
  have hseq := cpsTripleWithin_seq_same_cr hliOwn hjump
  have hseqOld := cpsTripleWithin_weaken
    (P := rest ** regOwn .x10) (P' := rest ** (.x10 ↦ᵣ old10))
    (Q := rest ** (.x10 ↦ᵣ (1 : Word)))
    (Q' := rest ** (.x10 ↦ᵣ (1 : Word)))
    (fun _ hp => sepConj_mono_right (regIs_to_regOwn .x10 old10) _ hp)
    (fun _ hq => hq) hseq
  simpa [rest, k70StatusTailRest, sepConj_assoc', sepConj_comm',
    sepConj_left_comm'] using hseqOld

/-- K70's ABI composition around the body route.

This theorem discharges only the frame/prologue/epilogue part and consumes
`hbody` as the remaining body obligation.  In particular, the Amsterdam
`priceContract` above is still undischarged item 7 of the K70 seam inventory;
it is deliberately not hidden inside this theorem or presented as an existing
machine triple. -/
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
