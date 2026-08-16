import EvmAsm.Codegen.Programs.HeaderExtendedDecodeWalkSpec

namespace EvmAsm.Codegen.HeaderExtendedDecodeWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-! Complete setup-frame plus converter call.  The x12 assertion is retained
    as the walker content length through the setup; the callee contract may
    rebind x12 at a u256 site, but that rebinding is explicit in hcallee. -/
set_option maxRecDepth 8000 in
theorem walk_next_status_to_converter_site
    {cr calleeCode : CodeReq} {F Q : Assertion} {n : Nat}
    (base failPC calleeEntry returnRa cursor status endPtr contentLen savedCursor : Word)
    (bneOff : BitVec 13) (offset : BitVec 21)
    (hF : F.pcFree)
    (hFail : base + signExtend13 bneOff = failPC)
    (hcodeBne : ∀ a i,
      CodeReq.singleton base (.BNE .x11 .x0 bneOff) a = some i → cr a = some i)
    (hcodeSub : ∀ a i,
      CodeReq.singleton (base + 4) (.SUB .x10 .x10 .x12) a = some i → cr a = some i)
    (hcodeMv : ∀ a i,
      CodeReq.singleton (base + 8) (.MV .x11 .x12) a = some i → cr a = some i)
    (hoffset : (base + 12) + signExtend21 offset = calleeEntry)
    (halign : ((base + 12) + 4) &&& ~~~(1 : Word) = (base + 12) + 4)
    (hdisj : (CodeReq.singleton (base + 12) (.JAL .x1 offset)).Disjoint calleeCode)
    (hcodeCall : ∀ a i,
      (CodeReq.singleton (base + 12) (.JAL .x1 offset)).union calleeCode a = some i →
        cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry (((base + 12) + 4) &&& ~~~(1 : Word))
      calleeCode
      ((.x1 ↦ᵣ ((base + 12) + 4)) **
        ((.x10 ↦ᵣ (cursor - contentLen)) ** (.x11 ↦ᵣ contentLen) **
          (.x12 ↦ᵣ contentLen) ** (.x9 ↦ᵣ endPtr) **
          (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) ** F)) Q) :
    cpsBranchWithin (4 + n) base cr
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F)
      ((base + 12) + 4) Q failPC
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F) := by
  have hsetup0 := walk_next_status_to_converter_setup base failPC bneOff
    cursor status endPtr contentLen savedCursor returnRa hF hFail
    hcodeBne hcodeSub hcodeMv
  have hframe :
      (((.x10 ↦ᵣ (cursor - contentLen)) ** (.x11 ↦ᵣ contentLen) **
        (.x12 ↦ᵣ contentLen) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) ** F).pcFree) := by
    repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact hF
  have hsetup : cpsBranchWithin 3 base cr
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F)
      (base + 12)
      ((.x1 ↦ᵣ returnRa) **
        ((.x10 ↦ᵣ (cursor - contentLen)) ** (.x11 ↦ᵣ contentLen) **
          (.x12 ↦ᵣ contentLen) ** (.x9 ↦ᵣ endPtr) **
          (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      failPC
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F) := by
    refine cpsBranchWithin_weaken
      (P := ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F))
      (P' := ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F))
      (Q_t := (((.x10 ↦ᵣ (cursor - contentLen)) ** (.x11 ↦ᵣ contentLen) **
        (.x12 ↦ᵣ contentLen) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ returnRa) ** F)))
      (Q_t' := ((.x1 ↦ᵣ returnRa) **
        ((.x10 ↦ᵣ (cursor - contentLen)) ** (.x11 ↦ᵣ contentLen) **
          (.x12 ↦ᵣ contentLen) ** (.x9 ↦ᵣ endPtr) **
          (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) ** F)))
      (Q_f := ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F))
      (Q_f' := ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ contentLen) **
        (.x9 ↦ᵣ endPtr) ** (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F))
      (by intro _ hp; exact hp) (by intro _ hp; xperm_chunked hp)
      (by intro _ hp; exact hp) hsetup0
  have hcall := converter_call_site (base + 12) calleeEntry returnRa offset hframe
    hoffset halign hdisj hcodeCall hcallee
  have h := walk_next_status_to_converter_call base (base + 12) ((base + 12) + 4)
    failPC returnRa hsetup hcall
  have hbound : 3 + (1 + n) = 4 + n := by omega
  rw [hbound] at h
  simpa [BitVec.add_assoc] using h


/-! Fixed linked sites for the seven converter arms.  The setup theorem above
    supplies S with x12 retained as content length; these declarations pin the
    status-branch and converter-JAL PCs so a moved arm cannot silently reuse a
    proof for a different field.  Site 532 is the u256 arm, whose S/hcall
    contract is where an explicit output-pointer rebind of x12 belongs. -/
theorem header_extended_decode_walk_converter_site_312
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (oldRa : Word)
    (hsetup : cpsBranchWithin 3 (decoderBase + 312) cr P (decoderBase + 324)
      ((.x1 ↦ᵣ oldRa) ** S) (decoderBase + 664) Sf)
    (hcall : cpsTripleWithin n (decoderBase + 324) (decoderBase + 328) cr
      ((.x1 ↦ᵣ oldRa) ** S) Q) :
    cpsBranchWithin (3 + n) (decoderBase + 312) cr P (decoderBase + 328)
      Q (decoderBase + 664) Sf := by
  exact walk_next_status_to_converter_call (decoderBase + 312) (decoderBase + 324)
    (decoderBase + 328) (decoderBase + 664) oldRa hsetup hcall

theorem header_extended_decode_walk_converter_site_352
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (oldRa : Word)
    (hsetup : cpsBranchWithin 3 (decoderBase + 352) cr P (decoderBase + 364)
      ((.x1 ↦ᵣ oldRa) ** S) (decoderBase + 664) Sf)
    (hcall : cpsTripleWithin n (decoderBase + 364) (decoderBase + 368) cr
      ((.x1 ↦ᵣ oldRa) ** S) Q) :
    cpsBranchWithin (3 + n) (decoderBase + 352) cr P (decoderBase + 368)
      Q (decoderBase + 664) Sf := by
  exact walk_next_status_to_converter_call (decoderBase + 352) (decoderBase + 364)
    (decoderBase + 368) (decoderBase + 664) oldRa hsetup hcall

theorem header_extended_decode_walk_converter_site_392
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (oldRa : Word)
    (hsetup : cpsBranchWithin 3 (decoderBase + 392) cr P (decoderBase + 404)
      ((.x1 ↦ᵣ oldRa) ** S) (decoderBase + 664) Sf)
    (hcall : cpsTripleWithin n (decoderBase + 404) (decoderBase + 408) cr
      ((.x1 ↦ᵣ oldRa) ** S) Q) :
    cpsBranchWithin (3 + n) (decoderBase + 392) cr P (decoderBase + 408)
      Q (decoderBase + 664) Sf := by
  exact walk_next_status_to_converter_call (decoderBase + 392) (decoderBase + 404)
    (decoderBase + 408) (decoderBase + 664) oldRa hsetup hcall

theorem header_extended_decode_walk_converter_site_432
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (oldRa : Word)
    (hsetup : cpsBranchWithin 3 (decoderBase + 432) cr P (decoderBase + 444)
      ((.x1 ↦ᵣ oldRa) ** S) (decoderBase + 664) Sf)
    (hcall : cpsTripleWithin n (decoderBase + 444) (decoderBase + 448) cr
      ((.x1 ↦ᵣ oldRa) ** S) Q) :
    cpsBranchWithin (3 + n) (decoderBase + 432) cr P (decoderBase + 448)
      Q (decoderBase + 664) Sf := by
  exact walk_next_status_to_converter_call (decoderBase + 432) (decoderBase + 444)
    (decoderBase + 448) (decoderBase + 664) oldRa hsetup hcall

theorem header_extended_decode_walk_converter_site_532
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (oldRa : Word)
    (hsetup : cpsBranchWithin 3 (decoderBase + 532) cr P (decoderBase + 544)
      ((.x1 ↦ᵣ oldRa) ** S) (decoderBase + 664) Sf)
    (hcall : cpsTripleWithin n (decoderBase + 544) (decoderBase + 548) cr
      ((.x1 ↦ᵣ oldRa) ** S) Q) :
    cpsBranchWithin (3 + n) (decoderBase + 532) cr P (decoderBase + 548)
      Q (decoderBase + 664) Sf := by
  exact walk_next_status_to_converter_call (decoderBase + 532) (decoderBase + 544)
    (decoderBase + 548) (decoderBase + 664) oldRa hsetup hcall

theorem header_extended_decode_walk_converter_site_592
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (oldRa : Word)
    (hsetup : cpsBranchWithin 3 (decoderBase + 592) cr P (decoderBase + 604)
      ((.x1 ↦ᵣ oldRa) ** S) (decoderBase + 664) Sf)
    (hcall : cpsTripleWithin n (decoderBase + 604) (decoderBase + 608) cr
      ((.x1 ↦ᵣ oldRa) ** S) Q) :
    cpsBranchWithin (3 + n) (decoderBase + 592) cr P (decoderBase + 608)
      Q (decoderBase + 664) Sf := by
  exact walk_next_status_to_converter_call (decoderBase + 592) (decoderBase + 604)
    (decoderBase + 608) (decoderBase + 664) oldRa hsetup hcall

theorem header_extended_decode_walk_converter_site_632
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (oldRa : Word)
    (hsetup : cpsBranchWithin 3 (decoderBase + 632) cr P (decoderBase + 644)
      ((.x1 ↦ᵣ oldRa) ** S) (decoderBase + 664) Sf)
    (hcall : cpsTripleWithin n (decoderBase + 644) (decoderBase + 648) cr
      ((.x1 ↦ᵣ oldRa) ** S) Q) :
    cpsBranchWithin (3 + n) (decoderBase + 632) cr P (decoderBase + 648)
      Q (decoderBase + 664) Sf := by
  exact walk_next_status_to_converter_call (decoderBase + 632) (decoderBase + 644)
    (decoderBase + 648) (decoderBase + 664) oldRa hsetup hcall

end EvmAsm.Codegen.HeaderExtendedDecodeWalkSpec
