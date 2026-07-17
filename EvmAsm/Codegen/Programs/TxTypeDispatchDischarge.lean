/-
  Discharge of prover1 `TxTypeDispatchAssumed` from `txTypeDispatch_spec_within`.

  Teer residual 11→10: entry = GuestAddrs.tx_type_dispatch, nSteps = 256,
  pure model `teerTxTypeDispatch`, post with regOwn x5/x6/x11/x12/x13,
  strict hover `< 2^64` (matches prover1 pass-6 re-push).
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

/-- prover1 `TxTypeDispatchAssumed` shape (strict hover + regOwn a1–a3).
    Local until `TeerBodyAssumptions` lands on main. -/
structure TxTypeDispatchAssumed (cr : CodeReq) where
  entry : Word
  flat :
    ∀ (ret txBase txLen typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
      (txBytes : List (BitVec 8))
      (_hret : ret &&& ~~~(1 : Word) = ret)
      (_hlen : txLen = BitVec.ofNat 64 txBytes.length)
      (_halign : txBase.toNat % 8 = 0)
      (_hover : txBase.toNat + txBytes.length < 2 ^ 64)
      (_hvalid : ∀ k, k < txBytes.length →
        isValidByteAccess (txBase + BitVec.ofNat 64 k) = true),
      cpsTripleWithin nTxTypeDispatchSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLen) **
          (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes ** (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes) **
         ((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
           (typePtr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
           (innerPtr ↦ₘ (teerTxTypeDispatch txBytes).2.2)))

/-- Core discharge under `typeCode` (no CodeReq lift). -/
theorem txTypeDispatch_flat_under_typeCode
    (ret txBase txLen typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hlen : txLen = BitVec.ofNat 64 txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < txBytes.length →
      isValidByteAccess (txBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin nTxTypeDispatchSteps D ret typeCode
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLen) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes ** (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes) **
       ((.x10 ↦ᵣ (teerTxTypeDispatch txBytes).1) **
         (typePtr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
         (innerPtr ↦ₘ (teerTxTypeDispatch txBytes).2.2))) := by
  have hvalid0 : txBytes.length = 0 ∨
      isValidByteAccess (txBase + BitVec.ofNat 64 0) = true := by
    by_cases hlen0 : txBytes.length = 0
    · exact Or.inl hlen0
    · exact Or.inr (hvalid 0 (Nat.pos_of_ne_zero hlen0))
  have h :=
    txTypeDispatch_spec_within ret txBase typePtr innerPtr t0Old t1Old typeOld innerOld
      txBytes hret halign hover hvalid0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [typeFlatPre, hlen] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [typeFlatPostOf] at hq
    -- typeFlatPostOf flat → teer two-block post
    xperm_hyp hq) h

/-- Construct `TxTypeDispatchAssumed` for any CodeReq that extends `typeCode`. -/
def txTypeDispatchAssumed_of_spec (cr : CodeReq)
    (hmono : ∀ a i, typeCode a = some i → cr a = some i) :
    TxTypeDispatchAssumed cr where
  entry := D
  flat := fun ret txBase txLen typePtr innerPtr t0Old t1Old typeOld innerOld txBytes
      hret hlen halign hover hvalid => by
    have h0 :=
      txTypeDispatch_flat_under_typeCode ret txBase txLen typePtr innerPtr
        t0Old t1Old typeOld innerOld txBytes hret hlen halign hover hvalid
    exact cpsTripleWithin_extend_code hmono h0

/-- Specialization: assumed under the leaf's own `typeCode`. -/
def txTypeDispatchAssumed_typeCode : TxTypeDispatchAssumed typeCode :=
  txTypeDispatchAssumed_of_spec typeCode (fun _ _ h => h)

theorem txTypeDispatchAssumed_entry :
    txTypeDispatchAssumed_typeCode.entry = D := rfl

theorem txTypeDispatchAssumed_entry_guest :
    txTypeDispatchAssumed_typeCode.entry =
      BitVec.ofNat 64 GuestAddrs.tx_type_dispatch := rfl

#print axioms txTypeDispatch_flat_under_typeCode
#print axioms txTypeDispatchAssumed_typeCode

end EvmAsm.Codegen.TxTypeDispatchSpec
