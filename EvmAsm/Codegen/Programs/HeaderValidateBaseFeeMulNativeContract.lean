/-
Native-shaped multiply callee contract at the K73 callsite (#12346 residual 2b,
coord ruling option ii, 2026-08-27).

DEFECT BEING REPAIRED (class (b) of #12851 family: ownership conflated with
value).  The seam family around here (`k73_decrease_mul_call_spec_within`,
`k73_decrease_entry_mul_status_spec_within`, their increase twins) carries the
multiply callee obligation as ONE symmetric pair of list parameters, so its
premise pins the initial accumulator/output windows and its conclusion pins the
same lists again as final content.  Bound against the deployed
`mulWhole_spec`, that forces `initOut = copyState M initOut 32` - false for
symbolic callers because `bytesRegion` pins content.  The existing mechanism
only ever worked at concrete witnesses (see WholeRoutes :1085, discharging by
definitional reduction of literal lists, and WholeSpec :396, which merely
respells the symmetric statement without discharging it).

THE FIX: pre OWNS the initial windows (content = whatever caller-supplied
scratch lists say); post PINS the computed images (`mulState` accumulator,
`copyState` output).  This REMOVES the hidden initial-content-equals-final-image
precondition rather than adding any, satisfying the standing rule that callee
instantiation adds no new preconditions.
-/
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore

namespace EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec

/-- Generic native-shaped multiply call frame: the callee obligation arrives
with SEPARATE initial-window lists (`accWin` / `outWin`, owned by the caller
through the premise) and final-image lists (`accImg` / `outImg`, pinned by the
callee's honest conclusion).  Everything else mirrors
`k73_mul_call_spec_within` (WholeSpec :294) positionally; the post conversion
reuses `k73_mul_body_post_factor`, which is name-blind, at the image lists. -/
theorem k73_mul_call_native_spec_within
    {cr : CodeReq} {n : Nat}
    (callerPC calleeEntry oldRa spOld spNew v8 v9 v18 v19 v20 aPtr b outPtr v13 : Word)
    (offset : BitVec 21) (F : Assertion) (hF : F.pcFree)
    (f0 f1 f2 f3 f4 f5 : Word)
    (aBytes accWin outWin accImg outImg : List (BitVec 8))
    (hcallee : cpsTripleWithin n calleeEntry (callerPC + 4) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre F spOld (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr v13 f0 f1 f2 f3 f4 f5
        aBytes accWin outWin)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost spNew (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr aBytes accImg outImg ** F))
    (htarget : callerPC + signExtend21 offset = calleeEntry)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      cr a = some i)
    (hcalleeMem : ∀ a i, mulCode a = some i → cr a = some i) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ oldRa) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accWin outWin F))
      (((.x1 ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accImg outImg ** F))) := by
  have hcalleeC := cpsTripleWithin_extend_code hcalleeMem hcallee
  have hcallee' : cpsTripleWithin n calleeEntry (callerPC + 4) cr
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accWin outWin F)
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accImg outImg ** F)) := by
    refine cpsTripleWithin_weaken (nSteps := n) (entry := calleeEntry)
      (exit_ := callerPC + 4) (cr := cr)
      (P := EvmAsm.Codegen.U256MulU64Be.mulWholePre F spOld (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr v13 f0 f1 f2 f3 f4 f5
        aBytes accWin outWin)
      (P' := ((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        k73MulPreNoRa spOld v8 v9 v18 v19 v20 aPtr b outPtr v13
          f0 f1 f2 f3 f4 f5 aBytes accWin outWin F)
      (Q := EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost spNew (callerPC + 4)
        v8 v9 v18 v19 v20 aPtr b outPtr aBytes accImg outImg ** F)
      (Q' := ((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        (k73MulBodyPostNoRa spNew (callerPC + 4) v8 v9 v18 v19 v20
          aPtr b outPtr aBytes accImg outImg ** F))
      ?_ ?_ hcalleeC
    · intro h hp
      dsimp [EvmAsm.Codegen.U256MulU64Be.mulWholePre, k73MulPreNoRa] at hp ⊢
      xperm_hyp hp
    · intro s hq
      exact k73_mul_body_post_factor spNew (callerPC + 4) v8 v9 v18 v19 v20
        aPtr b outPtr aBytes accImg outImg F s hq
  have hP : (k73MulPreNoRa spOld v8 v9 v18 v19 v20
      aPtr b outPtr v13 f0 f1 f2 f3 f4 f5 aBytes accWin outWin F).pcFree := by
    dsimp [k73MulPreNoRa]
    pcf
    exact hF
  exact callWithin_spec callerPC calleeEntry oldRa offset n
    htarget hmem hP hcallee'

end EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract
