import EvmAsm.Codegen.Programs.RlpFieldToU64SAsm
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

namespace RlpContentToU64CallSAsm

abbrev B : Word := (GuestAddrs.rlp_content_to_u64 : Word)

/-! Flat caller framing for the strict content-to-u64 leaf.  The four-way
postcondition is copied from the unified Rv64 theorem unchanged. -/

def flatPre
    (srcBase : Word) (srcOff len : Nat)
    (t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) : Assertion :=
  ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
   (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x5 ↦ᵣ t0Old) **
   (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
   (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)

def flatPost
    (srcBase : Word) (srcOff len : Nat)
    (srcBytes : List (BitVec 8)) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion srcBase srcBytes) **
   (fun h =>
     (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
     (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
     (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
        ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
     (((.x10 ↦ᵣ (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0⌝) h)))

#guard EvmAsm.Rv64.RLP.rlp_content_to_u64_prog.length = 22

theorem rlpContentToU64_call_spec_within
    (base srcBase raVal : Word) (t0Old x6Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (A : Assertion) (hA : A.pcFree)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (7 * len + 11) base (raVal &&& ~~~1)
      (rlp_content_to_u64_code base)
      ((.x1 ↦ᵣ raVal) ** flatPre srcBase srcOff len t0Old x6Old t2Old t3Old srcBytes ** A)
      ((.x1 ↦ᵣ raVal) ** flatPost srcBase srcOff len srcBytes ** A) := by
  have hc := rlp_content_to_u64_spec_within base srcBase raVal t0Old x6Old t2Old t3Old
    srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  have hcf := cpsTripleWithin_frameR A hA hc
  refine cpsTripleWithin_weaken
    (P' := ((.x1 ↦ᵣ raVal) **
      flatPre srcBase srcOff len t0Old x6Old t2Old t3Old srcBytes ** A))
    (Q' := ((.x1 ↦ᵣ raVal) ** flatPost srcBase srcOff len srcBytes ** A))
    (fun h hp => ?_) (fun h hp => ?_) hcf
  · unfold flatPre at hp
    xperm_hyp hp
  · unfold flatPost
    xperm_hyp hp


end RlpContentToU64CallSAsm
end EvmAsm.Codegen
