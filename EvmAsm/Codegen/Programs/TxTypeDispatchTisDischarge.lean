/-
  Success-domain facts for intrinsic `TypeDispatchAssumed`.

  `TypeDispatchAssumed.success_flat` claims a0=0 for **all** `txBytes`
  (empty/unknown return a0=1) — not honest to discharge. This module records
  the success-domain core triple and the residual.

  Residual: redefine `TypeDispatchAssumed.success_flat` with
  `(teerTxTypeDispatch txBytes).1 = 0` hyp, then package via memOwn/regOwn
  peels (Type.lean call sites must supply hsuccess or stay on success path).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchTop
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxTypeDispatchSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

/-- Pure: success status implies non-empty (empty → status 1). -/
theorem teer_success_implies_nonempty (txBytes : List (BitVec 8))
    (h : (teerTxTypeDispatch txBytes).1 = (0 : Word)) :
    0 < txBytes.length := by
  match txBytes with
  | [] =>
    simp only [teerTxTypeDispatch] at h
    exact absurd h (by decide)
  | _ :: _ => simp

set_option maxRecDepth 8000 in
/-- Under classification success, the proven top has a0=0 and model type/inner.
    classical-3. Footprint is the leaf ABI (not yet intrinsic memOwn/scratch). -/
theorem typeDispatch_success_top
    (ret txBase typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin nTxTypeDispatchSteps D ret typeCode
      (typeFlatPre ret txBase (BitVec.ofNat 64 txBytes.length) typePtr innerPtr
        t0Old t1Old typeOld innerOld txBytes)
      (typeFlatPostOf ret txBase typePtr innerPtr txBytes) := by
  have _ := hsuccess  -- domain pin: status=0 in post model
  exact txTypeDispatch_spec_within ret txBase typePtr innerPtr t0Old t1Old
    typeOld innerOld txBytes hret halign hover (Or.inr hvalid0)

/-- Corollary: status word is 0 in the success post. -/
theorem typeDispatch_success_status_zero (txBytes : List (BitVec 8))
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word)) :
    (teerTxTypeDispatch txBytes).1 = (0 : Word) := hsuccess

#print axioms typeDispatch_success_top
#print axioms teer_success_implies_nonempty

end EvmAsm.Codegen.TxTypeDispatchSpec
