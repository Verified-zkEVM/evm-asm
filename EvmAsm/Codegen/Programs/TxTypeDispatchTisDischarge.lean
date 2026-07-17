/-
  Success-domain core for intrinsic `TypeDispatchAssumed` discharge.

  `TypeDispatchAssumed` is now honest (hsuccess + static LBU hyps).
  Full packaging (memOwn/regOwn peels + type_mono → fullCode) is residual;
  this file records the leaf success triple under the Assumed domain.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
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
/-- Under classification success, proven top has model post with a0=0.
    classical-3. Residual: reshape to intrinsic memOwn/scratch Assumed
    footprint + type_mono into fullCode. -/
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
  have _ := hsuccess
  exact txTypeDispatch_spec_within ret txBase typePtr innerPtr t0Old t1Old
    typeOld innerOld txBytes hret halign hover (Or.inr hvalid0)

#print axioms typeDispatch_success_top
#print axioms teer_success_implies_nonempty

end EvmAsm.Codegen.TxTypeDispatchSpec
