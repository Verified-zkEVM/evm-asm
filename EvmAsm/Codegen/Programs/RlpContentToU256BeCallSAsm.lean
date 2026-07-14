import EvmAsm.Codegen.Programs.RlpFieldToU256BeSAsm
import EvmAsm.Rv64.RLP.ContentToU256Be

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

namespace RlpContentToU256BeCallSAsm

abbrev B : Word := (GuestAddrs.rlp_content_to_u256_be : Word)

/-! Flat caller-facing framing for the already-proven strict content leaf.
The semantic disjunction is copied unchanged from the Rv64 theorem; only the
link register and ambient assertion are made explicit for `callWithin_spec`.
-/

def flatPre
    (srcBase outPtr : Word) (len : Nat) (srcOff : Nat)
    (x5Old x6Old x7Old x28Old x29Old : Word)
    (srcBytes : List (BitVec 8)) : Assertion :=
  ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
   (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
   (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
   (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) **
   bytesRegion srcBase srcBytes ** memOwnU256 outPtr)

def flatPost
    (srcBase outPtr : Word) (len : Nat) (srcOff : Nat)
    (srcBytes : List (BitVec 8)) : Assertion :=
  (((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** regOwn .x5 **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion srcBase srcBytes) **
   (fun h =>
     (((.x10 ↦ᵣ (2 : Word)) ** memOwnU256 outPtr ** ⌜32 < len⌝) h) ∨
     (((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
        ⌜len = 0⌝) h) ∨
     (((.x10 ↦ᵣ (3 : Word)) ** memOwnU256 outPtr **
        ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
     (((.x10 ↦ᵣ (0 : Word)) **
        bytesRegion outPtr
          (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h)))

#guard EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog.length = 26

theorem rlpContentToU256Be_call_spec_within
    (base srcBase outPtr raVal : Word)
    (x5Old x6Old x7Old x28Old x29Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (A : Assertion) (hA : A.pcFree)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hdvalid : ∀ k, k < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * len + 16) base (raVal &&& ~~~1)
      (rlp_content_to_u256_be_code base)
      ((.x1 ↦ᵣ raVal) ** flatPre srcBase outPtr len srcOff
        x5Old x6Old x7Old x28Old x29Old srcBytes ** A)
      ((.x1 ↦ᵣ raVal) ** flatPost srcBase outPtr len srcOff srcBytes ** A) := by
  have hc := rlp_content_to_u256_be_spec_within base srcBase outPtr raVal
    x5Old x6Old x7Old x28Old x29Old srcBytes srcOff len hlen64 hsalign hoalign
    hslen hsover hoover hsvalid hdvalid
  have hcf := cpsTripleWithin_frameR A hA hc
  refine cpsTripleWithin_weaken (P' := ((.x1 ↦ᵣ raVal) **
      flatPre srcBase outPtr len srcOff x5Old x6Old x7Old x28Old x29Old srcBytes ** A))
    (Q' := ((.x1 ↦ᵣ raVal) **
      flatPost srcBase outPtr len srcOff srcBytes ** A))
    (fun h hp => ?_) (fun h hp => ?_) hcf
  · unfold flatPre at hp
    xperm_hyp hp
  · unfold flatPost
    xperm_hyp hp

#print axioms rlpContentToU256Be_call_spec_within

end RlpContentToU256BeCallSAsm
end EvmAsm.Codegen
