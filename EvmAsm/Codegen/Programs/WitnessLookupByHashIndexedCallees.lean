/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedCallees

  Lift existing `widx_cmp32` machine triple onto the guest-linked PC and into
  `WitnessLookupByHashIndexedSpec.fullCode`, so the indexed binary-search body
  can `callWithin` it.

  `widx_record_ptr` lift (guest la hi/lo) follows in a later commit once the
  parameterized `widx_record_ptr_spec` is tied to `GuestAddrs.widx_records`.

  **Depends on PR #12169.** NEW file only — does not edit any #12169 path.
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec
import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedCallees

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
open EvmAsm.Crypto

/-- Guest-linked `widx_cmp32` triple, CodeReq widened to the indexed full image. -/
theorem widx_cmp32_guest_spec
    (ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64)
    (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 293 (Cmp32B : Word) ret fullCode
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
      (widxCmp32Post ptrA ptrB ret as bs) := by
  have h0 := widx_cmp32_spec (Cmp32B : Word) ret ptrA ptrB as bs
    hlenA hlenB halignA halignB hovA hovB hvalidA hvalidB halignRet
  -- Spec list and guest Program are definitionally the same instruction list.
  have hcr :
      CodeReq.ofProg (Cmp32B : Word) widxCmp32Prog =
      CodeReq.ofProg (Cmp32B : Word) widxCmp32_prog := by
    rw [widxCmp32Prog_eq_guest]
  have h0' :
      cpsTripleWithin 293 (Cmp32B : Word) ret
        (CodeReq.ofProg (Cmp32B : Word) widxCmp32_prog)
        (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
        (widxCmp32Post ptrA ptrB ret as bs) := by
    rw [← hcr]; exact h0
  exact cpsTripleWithin_extend_code cmp32_in_fullCode h0'

end EvmAsm.Codegen.WitnessLookupByHashIndexedCallees
