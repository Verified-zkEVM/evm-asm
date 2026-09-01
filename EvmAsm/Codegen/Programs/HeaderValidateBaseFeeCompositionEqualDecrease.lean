/-
  K74 arm composition for the equal and decreasing K73 routes (#12346 item 10).

  The machine-layer K74 proof is parameterized over the K73 caller seam.  This
  module discharges that seam for the two routes whose adapters are complete:
  the equal route preserves one flat-frame ambient, while the decreasing route
  changes its arithmetic scratch into the explicit Route-B exit junk.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpec
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionEqualRoute
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseRouteB
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseZero

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualDecrease

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualRoute
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256SubBeSAsm

/-! The exact bound emitted by the completed nonzero-decrease adapter.  Keep
    it as a named value so the K74 composition and its caller-facing theorem
    refer to the same route budget rather than duplicating an unlabelled
    arithmetic expression. -/

def k73_decr_route_steps (gasLimit gasUsed parentPtr : Word)
    (parentBytes expectedBytes : List (BitVec 8)) : Nat :=
  (20 + 3852 + 9) +
    (((((10 +
          (u256DivU64BeInPlaceFn Expected (gasLimit >>> 1)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).body.steps +
        (u256DivU64BeInPlaceFn Expected 8
          (u256DivU64BeQuotBytes
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (gasLimit >>> 1))).body.steps +
      1) +
      (1 +
        (5 +
          (u256SubBeInPlaceFn parentPtr Expected parentBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))
              8)).body.steps))) +
    1) + 9) + 10)

/-! The equal route has no route-local scratch transition.  Its caller-owned
    ambient can therefore be the same on both sides of K73; the only flat
    frame conversion needed by the K74 equality call is made explicit here. -/

theorem header_validate_base_fee_equal_route_spec_within
    {cr : CodeReq}
    (sp0 spH spK old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (Ftail : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hret : ((H + 40 : Word) &&& ~~~(1 : Word)) = H + 40)
    (hFtail : Ftail.pcFree)
    (hHeaderWf : (Region.mk headerPtr headerBytes).wf)
    (hExpectedWf : (Region.mk Expected expectedBytes).wf)
    (hHeaderLen : headerBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hDisj : headerPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ headerPtr.toNat)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i)
    (heqMono : ∀ a i, u256EqCode a = some i → cr a = some i)
    (heqWord : gasUsed = gasLimit >>> 1)
    (hsrc : parentBytes.length = 32)
    (hout : expectedBytes.length = 32) :
    cpsTripleWithin
      (27 + 29 +
        (U256EqSAsm.u256EqBody headerPtr Expected headerBytes
          (hvbfWrittenImage gasLimit gasUsed parentBytes)).steps) H (H + 40) cr
      (hvbfPre sp0 spH spK (H + 40) old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20 parentBytes expectedBytes headerBytes
        (k74FlatFrame Ftail))
      (hvbfFinalRouteB sp0 spH spK (H + 40) old8 headerPtr v9 old18
        (gasLimit >>> 1) v19 v20
        gasLimit gasUsed parentPtr parentBytes headerBytes
        (k74FlatFrame Ftail)) := by
  let F : Assertion := k74FlatFrame Ftail
  have hF : F.pcFree := by
    dsimp [F, k74FlatFrame]
    pcf
    exact hFtail
  have hk73 := k73_equal_route_adapter (cr := cr)
    spH spK old8 headerPtr gasLimit gasUsed parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes F
    hspK heqWord hsrc hout hret hF hk73Mono
  have hgen := header_validate_base_fee_spec_gen_within
    (cr := cr) (k73Code := cr) (n73 := 29)
    sp0 spH spK (H + 40) old8 headerPtr gasLimit gasUsed parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes F Ftail F
    hspH hspK hret hF hFtail hF (by rfl) hHeaderWf hExpectedWf
    hHeaderLen hExpectedLen hDisj hcode (fun _ _ h => h) hk73 heqMono
  simpa only [F] using hgen

/-! The nonzero-decrease route has a genuine scratch transition: the entry
    ambient contains the caller-supplied multiply frame and accumulator, while
    the post exposes the arithmetic scratch left by the subtract route.  The
    decrease adapter already proves that transition; this theorem discharges
    it at the K74 call site and normalizes its x14--x17 ownership through the
    same flat frame as the equality call. -/

theorem header_validate_base_fee_decrease_route_spec_within
    {cr : CodeReq}
    (sp0 spH spK old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (parentBytes expectedBytes headerBytes accWin : List (BitVec 8))
    (G : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hret : ((H + 40 : Word) &&& ~~~(1 : Word)) = H + 40)
    (hne : gasUsed ≠ gasLimit >>> 1)
    (hnotlt : ¬ (gasLimit >>> 1).toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : G.pcFree)
    (hHeaderWf : (Region.mk headerPtr headerBytes).wf)
    (hExpectedWf : (Region.mk Expected expectedBytes).wf)
    (hHeaderLen : headerBytes.length = 32)
    (hDisj : headerPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ headerPtr.toNat)
    (htargetPos : 0 < (gasLimit >>> 1).toNat)
    (hleTarget : (gasLimit >>> 1).toNat ≤ 2 ^ 56)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
      ((gasLimit >>> 1) - gasUsed).toNat < 2 ^ 256)
    (hlenP : parentBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (halignA : parentPtr.toNat % 8 = 0)
    (hoverA : parentPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (parentPtr + BitVec.ofNat 64 j) = true)
    (halignOut : Expected.toNat % 8 = 0)
    (hoverOut : Expected.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (Expected + BitVec.ofNat 64 j) = true)
    (hdisj : parentPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ parentPtr.toNat)
    (hrw : RwRegion.wf ⟨Expected, 32⟩)
    (hroBase : Region.wf ⟨parentPtr, parentBytes⟩)
    (hszDiv1 :
      4 * ((u256DivU64BeInPlaceFn Expected (gasLimit >>> 1)
        (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).body.size + 1)
        ≤ 2 ^ 64)
    (hszDiv2 :
      4 * ((u256DivU64BeInPlaceFn Expected 8
        (u256DivU64BeQuotBytes
          (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
          (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
          (gasLimit >>> 1))).body.size + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn parentPtr Expected parentBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (gasLimit >>> 1))
          (u256DivU64BeQuotBytes
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (gasLimit >>> 1))
          8)).body.size + 1)
        ≤ 2 ^ 64)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i)
    (heqMono : ∀ a i, u256EqCode a = some i → cr a = some i) :
    cpsTripleWithin
      (27 + k73_decr_route_steps gasLimit gasUsed parentPtr parentBytes expectedBytes +
        (U256EqSAsm.u256EqBody headerPtr Expected headerBytes
          (hvbfWrittenImage gasLimit gasUsed parentBytes)).steps) H (H + 40) cr
      (hvbfPre sp0 spH spK (H + 40) old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20 parentBytes expectedBytes headerBytes
        (k73_decr_env spK f0 f1 f2 f3 f4 f5 accWin G))
      (hvbfFinalRouteB sp0 spH spK (H + 40) old8 headerPtr v9 old18
        (gasLimit >>> 1) v19 v20 gasLimit gasUsed parentPtr parentBytes headerBytes
        (k73_decr_outj spK headerPtr parentPtr v9 old18 v19 v20 gasUsed
          (gasLimit >>> 1) parentBytes G)) := by
  let Fenv : Assertion := k73_decr_env spK f0 f1 f2 f3 f4 f5 accWin G
  let Ftail : Assertion :=
    k73_decr_outj_tail spK headerPtr parentPtr v9 old18 v19 v20 gasUsed
      (gasLimit >>> 1) parentBytes G
  let F : Assertion :=
    k73_decr_outj spK headerPtr parentPtr v9 old18 v19 v20 gasUsed
      (gasLimit >>> 1) parentBytes G
  have hFenv : Fenv.pcFree := by
    dsimp [Fenv, k73_decr_env]
    pcf
    exact hG
  have hFtail : Ftail.pcFree := by
    dsimp [Ftail, k73_decr_outj_tail]
    pcf
    exact hG
  have hF : F.pcFree := by
    dsimp [F, k73_decr_outj]
    pcf
    exact hG
  have hFflat : F = k74FlatFrame Ftail := by
    dsimp [F, Ftail]
    exact k73_decr_outj_out_eq spK headerPtr parentPtr v9 old18 v19 v20 gasUsed
      (gasLimit >>> 1) parentBytes G
  have hrouteRaw := k73_decr_route_adapter (cr := cr)
    spH spK old8 headerPtr gasLimit gasUsed parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes accWin
    f0 f1 f2 f3 f4 f5 G
    hspK hne hnotlt hnonzero hret hG htargetPos hleTarget hMulFit
    hlenP hExpectedLen hlenAcc halignA hoverA hvalidA halignOut hoverOut
    hvalidOut hdisj hrw hroBase hszDiv1 hszDiv2 hszSub hk73Mono
  have hk73 : cpsTripleWithin
      (k73_decr_route_steps gasLimit gasUsed parentPtr parentBytes expectedBytes)
      K73 (H + 40) cr
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes (H + 40) old8 Fenv)
      ((.x1 ↦ᵣ (H + 40)) **
        k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18
          (gasLimit >>> 1) v19 v20 gasUsed gasLimit parentPtr parentBytes
          headerBytes F) := by
    simpa [Fenv, F, k73_decr_route_steps] using hrouteRaw
  have hgen := header_validate_base_fee_spec_gen_within
    (cr := cr) (k73Code := cr)
    (n73 := k73_decr_route_steps gasLimit gasUsed parentPtr parentBytes expectedBytes)
    sp0 spH spK (H + 40) old8 headerPtr gasLimit gasUsed parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes Fenv Ftail F
    hspH hspK hret hFenv hFtail hF hFflat hHeaderWf hExpectedWf
    hHeaderLen hExpectedLen hDisj hcode (fun _ _ h => h) hk73 heqMono
  simpa only [Fenv, F] using hgen

/-! The zero-gas decrease route is the target-positive fall-through after the
    K73 target-zero guard.  Its adapter has no multiply ambient: the only
    route-local frame is the K74 flat-frame ownership carried by `Ftail`.
    `htargetPos` is deliberately an explicit caller fact here.  At the real
    `check_gas_limit` fall-through it is the pure fact produced from the
    machine's zero status; this theorem does not replace that producer with a
    fresh hypothesis hidden in a local proof. -/

theorem header_validate_base_fee_zero_decrease_route_spec_within
    {cr : CodeReq}
    (sp0 spH spK old8 headerPtr gasLimit parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (Ftail : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hret : ((H + 40 : Word) &&& ~~~(1 : Word)) = H + 40)
    (htargetPos : 0 < (gasLimit >>> 1).toNat)
    (hFtail : Ftail.pcFree)
    (hHeaderWf : (Region.mk headerPtr headerBytes).wf)
    (hExpectedWf : (Region.mk Expected expectedBytes).wf)
    (hHeaderLen : headerBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hsrc : parentBytes.length = 32)
    (hHeaderDisj : headerPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ headerPtr.toNat)
    (hParentDisj : parentPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ parentPtr.toNat)
    (hroBase : Region.wf ⟨parentPtr, parentBytes⟩)
    (hrw : RwRegion.wf ⟨Expected, 32⟩)
    (hovBase : parentPtr.toNat + 32 < 2 ^ 64)
    (hovExpected : Expected.toNat + 32 < 2 ^ 64)
    (hszDiv : 4 *
      ((u256DivU64BeFn parentPtr Expected 8 parentBytes expectedBytes).body.size + 1)
        ≤ 2 ^ 64)
    (hszSub : 4 *
      ((u256SubBeInPlaceFn parentPtr Expected parentBytes
        (u256DivU64BeQuotBytes parentBytes expectedBytes 8)).body.size + 1)
        ≤ 2 ^ 64)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i)
    (heqMono : ∀ a i, u256EqCode a = some i → cr a = some i) :
    cpsTripleWithin
      (27 +
        EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_route_steps
          parentPtr parentBytes expectedBytes +
        (U256EqSAsm.u256EqBody headerPtr Expected headerBytes
          (hvbfWrittenImage gasLimit 0 parentBytes)).steps) H (H + 40) cr
      (hvbfPre sp0 spH spK (H + 40) old8 headerPtr gasLimit 0 parentPtr
        v9 old18 v19 v20 parentBytes expectedBytes headerBytes
        (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_env
          Ftail))
      (hvbfFinalRouteB sp0 spH spK (H + 40) old8 headerPtr v9 old18
        (gasLimit >>> 1) v19 v20 gasLimit 0 parentPtr parentBytes headerBytes
        (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_outj
          Ftail)) := by
  let F : Assertion := Ftail
  have hF : F.pcFree := by
    simpa [F] using hFtail
  have hne : (0 : Word) ≠ gasLimit >>> 1 := by
    intro hzero
    have : (gasLimit >>> 1) = 0 := hzero.symm
    simp [this] at htargetPos
  have hnotlt : ¬ (gasLimit >>> 1).toNat < (0 : Word).toNat := by
    simp
  have hk73 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_route_adapter
    (cr := cr) spH spK old8 headerPtr gasLimit 0 (gasLimit >>> 1) parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes F
    hspK rfl hne hnotlt rfl htargetPos hret hF hrw hroBase hsrc hExpectedLen
    hovBase hovExpected hParentDisj hszDiv hszSub hk73Mono
  have hFenv :
      (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_env F).pcFree := by
    dsimp [EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_env]
    pcf
    exact hFtail
  have hFpost :
      (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_outj F).pcFree := by
    dsimp [EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_outj]
    pcf
    exact hFtail
  have hFflat :
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_outj F =
        k74FlatFrame F := by
    exact EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_outj_out_eq F
  have hgen := header_validate_base_fee_spec_gen_within
    (cr := cr) (k73Code := cr)
    (n73 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_route_steps
      parentPtr parentBytes expectedBytes)
    sp0 spH spK (H + 40) old8 headerPtr gasLimit 0 parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes
    (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_env F)
    F (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero.k73_zero_outj F)
    hspH hspK hret hFenv hF hFpost hFflat hHeaderWf hExpectedWf
    hHeaderLen hExpectedLen hHeaderDisj hcode (fun _ _ h => h) hk73 heqMono
  simpa only [F] using hgen

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualDecrease
