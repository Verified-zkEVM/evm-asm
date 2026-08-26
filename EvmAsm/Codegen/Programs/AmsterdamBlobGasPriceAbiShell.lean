/-
Copyright (c) 2026 EvmAsm contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EvmAsm contributors
-/
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec

/-!
# Machine-side ABI-frame shell for `amsterdam_blob_gas_price_u256` (#12851)

This file discharges the *frame* half of the `taylorPriceContract` seam left
open by #12850: the 252-instruction linked routine
`amsterdam_blob_gas_price_u256` (symbol `0x8000b33c`, inlining the Taylor
recurrence — there is no separate taylor symbol) is
`prologue (9) · body (233) · epilogue (10)`, and its prologue/epilogue are
exactly `abiFrameProg (-208) 208 priceFrame body` for the K70 frame
descriptor `priceFrame`.  `amsterdam_blob_gas_price_abi_from_body` below
lifts any single-exit body contract to the whole-routine
`priceEntryRest → priceCalleePost` triple, mirroring the K70 pattern
`k70_abi_from_body`.

What remains open (recorded as `priceBodyContract`, the seam statement):
the functional body triple itself — 6-limb bignum multiply, restoring
division, and the Taylor recurrence invariant across the loop nest.  The
body-level contract pins `x11 ↦ᵣ outPtr` because the audited body reads
`x11` once (copy to `x21`) and never writes it; the frame rule restores the
saved registers from the slots regardless of `bodyVals`.

The 3-reference-functions-vs-2-guest-routines asymmetry (SpecRef
`taylor_exponential` / `calculate_blob_gas_price` / `calculate_excess_blob_gas`
vs the two linked routines) is recorded on the registry row.

Envelope (from the routine's own docstring, reuse per #12851): u64 input;
loop cap `i < 496` covering the measured 495 transitions at the acceptance
boundary; 306-bit in-envelope peak; 377-bit max pre-division product over
the full u64 domain; `2073394370` succeeds / `2073394371` overflows.
-/

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec

/-- The functional body: instructions 9..241 of the 252-instruction routine,
    i.e. everything between the `abiFrameProg` prologue and epilogue. -/
def priceBody : Program :=
  amsterdamBlobGasPriceU256_prog.drop (1 + priceFrame.length)
    |>.take (amsterdamBlobGasPriceU256_prog.length
      - (1 + priceFrame.length) - (priceFrame.length + 2))

#guard priceBody.length = 233

-- The emitted program is exactly the ABI-frame wrapping of the body.
set_option maxRecDepth 8000 in
theorem amsterdam_blob_gas_price_prog_eq_abiFrameProg :
    amsterdamBlobGasPriceU256_prog
      = abiFrameProg (-208 : BitVec 12) (208 : BitVec 12) priceFrame priceBody := by
  decide

/-- Body-entry precondition: frame slots saved (holding the entry values),
    frame registers exposed, caller ABI atoms (`x10` = excess, `x11` =
    outPtr, temporaries owned), the explicit setup workspace, plus the
    caller's `scratch`.  The output buffer is *not* pinned here — callers
    supply it through `scratch`, matching how `priceContract` accounts for it;
    the eighteen dwords written by setup are exposed separately by
    `priceWorkspaceOwn`. -/
def priceBodyPre
    (newSp : Word) (vals : Reg → Word)
    (excess outPtr : Word) (scratch : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** regsAt priceFrame vals **
    frameSlotsSaved priceFrame newSp vals **
    ((.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      priceWorkspaceOwn newSp **
      regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] ** scratch)

/-- Body-exit postcondition: `x10` = status, `x11` still exactly `outPtr`
    (audited: the body never writes `x11`), temporaries owned, frame
    registers at their body-exit values `bodyVals` (the epilogue restores
    from the slots, so these may differ from `vals`). -/
def priceBodyPost
    (newSp : Word) (vals bodyVals : Reg → Word)
    (status outPtr : Word) (outBytes : List (BitVec 8))
    (scratchPost : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** regsAt priceFrame bodyVals **
    frameSlotsSaved priceFrame newSp vals **
    ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ outPtr) **
      regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
      priceWorkspaceOwn newSp **
      priceOutputPost status outPtr outBytes ** scratchPost)

/-! The body does not preserve the ABI-frame registers at their entry values.
    Setup establishes the six fixed frame values below, while the outer loop
    exchanges x19 and x20 once per successful iteration.  Keep that relation
    explicit at the seam instead of hiding it in an unconstrained bodyVals. -/

def priceBodyFrameRel
    (newSp excess outPtr finalIndex : Word) (vals bodyVals : Reg → Word)
    (swapCount : Nat) : Prop :=
  bodyVals .x1 = vals .x1 ∧
  bodyVals .x8 = excess ∧
  bodyVals .x9 = EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat.taylorConstant ∧
  bodyVals .x18 = finalIndex ∧
  bodyVals .x21 = outPtr ∧
  bodyVals .x22 = newSp + signExtend12 (160 : BitVec 12) ∧
  ((swapCount % 2 = 0 ∧
      bodyVals .x19 = newSp + signExtend12 (64 : BitVec 12) ∧
      bodyVals .x20 = newSp + signExtend12 (112 : BitVec 12)) ∨
    (swapCount % 2 = 1 ∧
      bodyVals .x19 = newSp + signExtend12 (112 : BitVec 12) ∧
      bodyVals .x20 = newSp + signExtend12 (64 : BitVec 12)))

/-- The outer-loop counters are not independent witnesses.  `swapCount` counts
    exchanges of the two six-limb buffers.  A terminal path before (or after)
    the exchange has `x18 = swapCount + 1`; the swap/division overflow path
    has already exchanged once in the current round and therefore has
    `x18 = swapCount`.  The latter path cannot occur before its first swap.
    The 495 bound is the emitted `i < 496` horizon, not an assumed status. -/
def priceBodyRouteRel (status finalIndex : Word) (swapCount : Nat) : Prop :=
  swapCount ≤ 495 ∧
    ((status = (0 : Word) ∧
        finalIndex = BitVec.ofNat 64 (swapCount + 1)) ∨
      (status = (1 : Word) ∧
        ((finalIndex = BitVec.ofNat 64 (swapCount + 1)) ∨
          (swapCount > 0 ∧ finalIndex = BitVec.ofNat 64 swapCount))))

/-- Outcome relation for the body seam.  The body contract is parameterised by
    an outcome function so that status and exact output bytes are tied to the
    excess input; they are not fixed constants hidden in a supposedly
    unconditional triple. -/
def priceBodyOutcomeRel
    (outcome : Word → Word × List (BitVec 8))
    (excess status : Word) (outBytes : List (BitVec 8)) : Prop :=
  outcome excess = (status, outBytes)

/-- The frame valuation established by `price_setup_spec` at the loop head.
    Registers outside the ABI frame are intentionally inherited from `vals`.
    The body relation only observes the eight frame registers. -/
def priceBodySetupVals
    (newSp excess outPtr : Word) (vals : Reg → Word) : Reg → Word
  | .x1 => vals .x1
  | .x8 => excess
  | .x9 => EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat.taylorConstant
  | .x18 => 1
  | .x19 => newSp + signExtend12 (64 : BitVec 12)
  | .x20 => newSp + signExtend12 (112 : BitVec 12)
  | .x21 => outPtr
  | .x22 => newSp + signExtend12 (160 : BitVec 12)
  | r => vals r

theorem priceBodyFrameRel_setup
    (newSp excess outPtr : Word) (vals : Reg → Word) :
    priceBodyFrameRel newSp excess outPtr 1 vals
      (priceBodySetupVals newSp excess outPtr vals) 0 := by
  simp [priceBodyFrameRel, priceBodySetupVals]

/-! The body post is determined by the model outcome and the number of
    completed buffer exchanges.  In particular, do not existentially hide
    `bodyVals`: that would let `regsAt` choose an arbitrary post-state rather
    than describe the registers produced by the loop. -/

def priceBodyPostVals
    (newSp excess outPtr finalIndex : Word)
    (vals : Reg → Word) (swapCount : Nat) : Reg → Word
  | .x1 => vals .x1
  | .x8 => excess
  | .x9 => EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat.taylorConstant
  | .x18 => finalIndex
  | .x19 =>
      if swapCount % 2 = 0 then
        newSp + signExtend12 (64 : BitVec 12)
      else
        newSp + signExtend12 (112 : BitVec 12)
  | .x20 =>
      if swapCount % 2 = 0 then
        newSp + signExtend12 (112 : BitVec 12)
      else
        newSp + signExtend12 (64 : BitVec 12)
  | .x21 => outPtr
  | .x22 => newSp + signExtend12 (160 : BitVec 12)
  | r => vals r

theorem priceBodyFrameRel_postVals
    (newSp excess outPtr finalIndex : Word)
    (vals : Reg → Word) (swapCount : Nat) :
    priceBodyFrameRel newSp excess outPtr finalIndex vals
      (priceBodyPostVals newSp excess outPtr finalIndex vals swapCount) swapCount := by
  by_cases hparity : swapCount % 2 = 0
  · simp [priceBodyFrameRel, priceBodyPostVals, hparity]
  · have hmod : swapCount % 2 = 1 := by omega
    simp [priceBodyFrameRel, priceBodyPostVals, hmod]

def priceBodyOutcomePost
    (outcome : Word → Word × List (BitVec 8))
    (newSp : Word) (vals : Reg → Word) (excess outPtr status : Word)
    (scratchPost : Assertion) : Assertion :=
  fun h => ∃ (finalIndex : Word) (swapCount : Nat),
    priceBodyFrameRel newSp excess outPtr finalIndex vals
        (priceBodyPostVals newSp excess outPtr finalIndex vals swapCount) swapCount ∧
    priceBodyRouteRel status finalIndex swapCount ∧
    priceBodyOutcomeRel outcome excess status (outcome excess).2 ∧
    priceBodyPost newSp vals
      (priceBodyPostVals newSp excess outPtr finalIndex vals swapCount)
      status outPtr (outcome excess).2 scratchPost h

/-! The open seam statement (#12851 / K70 item 7): a model-indexed two-exit
    triple for the functional body between the frame entry (`PriceK + 36`)
    and the epilogue (`PriceK + 968`).  The status-0 arm carries exact output
    bytes; the status-1 arm carries only output ownership through
    `priceOutputPost`.  Discharging this over the emitted body — including the
    6-limb bignum arithmetic and the Taylor recurrence invariant — is the
    remaining machine work. -/
def priceBodyContract
    (bodySteps : Nat) (sp0 : Word) (vals : Reg → Word)
    (excess outPtr : Word)
    (outcome : Word → Word × List (BitVec 8))
    (scratch scratchPost : Assertion) : Prop :=
  cpsNBranchWithin bodySteps
    (PriceK + 36) priceCode
    (priceBodyPre (sp0 + signExtend12 (-208 : BitVec 12)) vals excess outPtr scratch)
    [(PriceK + 968,
        priceBodyOutcomePost outcome
          (sp0 + signExtend12 (-208 : BitVec 12)) vals excess outPtr 0 scratchPost),
      (PriceK + 968,
        priceBodyOutcomePost outcome
          (sp0 + signExtend12 (-208 : BitVec 12)) vals excess outPtr 1 scratchPost)]

theorem priceOutputPost_pcFree (status outPtr : Word) (outBytes : List (BitVec 8)) :
    (priceOutputPost status outPtr outBytes).pcFree := by
  unfold priceOutputPost
  split
  · exact bytesRegion_pcFree outPtr outBytes
  · exact pcFree_sepConj pcFree_memOwn (pcFree_sepConj pcFree_memOwn
      (pcFree_sepConj pcFree_memOwn pcFree_memOwn))

/-- `hsub` for the canonical code request: the whole program is the frame
    wrapping, so `priceCode` agrees with the `abiFrameProg` rendering. -/
theorem priceCode_sub_abiFrameProg
    (a : Word) (i : Instr)
    (h : CodeReq.ofProg PriceK
        (abiFrameProg (-208 : BitVec 12) (208 : BitVec 12) priceFrame priceBody) a
        = some i) :
    priceCode a = some i := by
  show CodeReq.ofProg PriceK amsterdamBlobGasPriceU256_prog a = some i
  rw [amsterdam_blob_gas_price_prog_eq_abiFrameProg]
  exact h

/-- **The ABI-frame shell** (mirror of `k70_abi_from_body`): lift a body
    contract to the whole-routine triple `priceEntryRest → priceCalleePost`.
    The step count is `bodySteps + 18` (1 alloc + 8 saves + body + 8 restores
    + 1 dealloc + 1 return-jump). -/
theorem amsterdam_blob_gas_price_abi_from_body
    {cr : CodeReq} {bodySteps : Nat}
    (sp0 ret : Word) (vals bodyVals : Reg → Word)
    (excess outPtr status : Word) (outBytes : List (BitVec 8))
    (scratch scratchPost F : Assertion)
    (hret : vals .x1 = ret)
    (hretAlign : (ret &&& ~~~(1 : Word)) = ret)
    (hscratch : scratch.pcFree) (hscratchPost : scratchPost.pcFree)
    (hF : F.pcFree)
    (hsub : ∀ a i,
      CodeReq.ofProg PriceK
        (abiFrameProg (-208 : BitVec 12) (208 : BitVec 12) priceFrame priceBody) a
          = some i → cr a = some i)
    (hbody : cpsTripleWithin bodySteps (PriceK + 36) (PriceK + 968) cr
      (priceBodyPre (sp0 + signExtend12 (-208 : BitVec 12)) vals excess outPtr scratch)
      (priceBodyPost (sp0 + signExtend12 (-208 : BitVec 12)) vals bodyVals status outPtr
        outBytes scratchPost)) :
    cpsTripleWithin (1 + priceFrame.length + bodySteps + priceFrame.length + 1 + 1)
      PriceK ret cr
      (priceEntryRest sp0 ret vals excess outPtr scratch ** F)
      (priceCalleePost sp0 ret vals status outPtr outBytes scratchPost ** F) := by
  have hframe : priceFrame = (.x1, (0 : BitVec 12)) :: priceSavedFrame := by
    rfl
  have hworkspace :
      (priceWorkspaceOwn (sp0 + signExtend12 (-208 : BitVec 12))).pcFree := by
    pcf
  have hcallerPre :
      ((.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        priceWorkspaceOwn (sp0 + signExtend12 (-208 : BitVec 12)) **
        regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] ** scratch).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj hworkspace
          (pcFree_sepConj (pcFree_regOwns _) hscratch)))
  have hcallerPost :
      ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ outPtr) **
        regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
        priceWorkspaceOwn (sp0 + signExtend12 (-208 : BitVec 12)) **
        priceOutputPost status outPtr outBytes ** scratchPost).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj hworkspace
            (pcFree_sepConj (priceOutputPost_pcFree status outPtr outBytes)
              hscratchPost))))
  have habi := abiFrame_spec
    (base := PriceK) (sp0 := sp0) (ret := ret)
    (negImm := (-208 : BitVec 12)) (posImm := (208 : BitVec 12))
    (frame := priceFrame) (raOfs := (0 : BitVec 12))
    (sregs := priceSavedFrame) (vals := vals) (vals' := bodyVals)
    (body := priceBody) (bodySteps := bodySteps)
    (callerPre :=
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      priceWorkspaceOwn (sp0 + signExtend12 (-208 : BitVec 12)) **
      regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] ** scratch)
    (callerPost :=
      (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ outPtr) **
      regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
      priceWorkspaceOwn (sp0 + signExtend12 (-208 : BitVec 12)) **
      priceOutputPost status outPtr outBytes ** scratchPost)
    (cr := cr) hframe (by decide) (by decide) (by decide)
    hret hretAlign
    (by
      rw [BitVec.add_assoc,
        show signExtend12 (-208 : BitVec 12) + signExtend12 (208 : BitVec 12) =
          (0 : Word) from by decide]
      exact BitVec.add_zero sp0)
    hcallerPre hcallerPost hsub (by
      have hentry : PriceK + BitVec.ofNat 64 (4 * (1 + priceFrame.length))
          = PriceK + 36 := by decide
      have hexit : PriceK + BitVec.ofNat 64
          (4 * (1 + priceFrame.length + priceBody.length)) = PriceK + 968 := by
        decide
      rw [hentry, hexit]
      simpa [priceBodyPre, priceBodyPost] using hbody)
  have habiF := cpsTripleWithin_frameR F hF habi
  refine cpsTripleWithin_weaken (P := _) (Q := _) ?_ ?_ habiF
  · intro h hp
    rw [← hret] at hp
    simp [priceEntryRest, priceFrame, priceSavedFrame,
      frameSlotsOwn, regsAt, regOwns, sepConj_emp_right'] at hp ⊢
    xperm_hyp hp
  · intro h hq
    simp [priceCalleePost, priceFrame, priceSavedFrame,
      priceFrameVals, frameSlotsSaved, regsAt, regOwns,
      sepConj_emp_right'] at hq ⊢
    rw [← hret]
    xperm_hyp hq

#print axioms amsterdam_blob_gas_price_prog_eq_abiFrameProg
#print axioms priceCode_sub_abiFrameProg
#print axioms amsterdam_blob_gas_price_abi_from_body

end EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell
