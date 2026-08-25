/-
  K74 wrapper epilogue and complete triple.

  The shared K74/K73 station contracts and prefix/call composition live in
  HeaderValidateBaseFeeSpecCore.lean.  This module retains the original public
  declarations while keeping the wrapper proof below the file-size guard.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec

/-! The shared epilogue is kept separate so the two status paths can use it
    with their different link values (`H+40` and `H+60`). -/

theorem hvbfEpilogue
    {cr : CodeReq}
    (sp0 spH raIn old8 headerPtr raBefore status out11 gasUsed : Word)
    (spK v9 old18 target v19 v20 parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hF : F.pcFree) :
    cpsTripleWithin 4 (H + 84) raIn cr
      ((.x1 ↦ᵣ raBefore) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F)
      (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        status out11 parentBytes expectedBytes headerBytes F) := by
  have h1 := ld_spec_gen_within .x1 .x2 spH raBefore raIn
    (0 : BitVec 12) (H + 84) (by decide)
  have h1' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 84) hvbfProg 21
        (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h1)
  have h2 := ld_spec_gen_within .x8 .x2 spH headerPtr old8
    (8 : BitVec 12) (H + 88) (by decide)
  have h2' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 88) hvbfProg 22
        (.LD .x8 .x2 (8 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h2)
  have h3 := addi_spec_gen_same_within .x2 spH (16 : BitVec 12) (H + 92) (by decide)
  rw [show spH + signExtend12 (16 : BitVec 12) = sp0 from by
    rw [hspH]
    exact sext_frameRestore sp0 (-16 : BitVec 12) (16 : BitVec 12) (by decide)] at h3
  have h3' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 92) hvbfProg 23
        (.ADDI .x2 .x2 (16 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h3)
  have h4 := EvmAsm.Evm64.ret_spec_within' (H + 96) raIn
  rw [hret] at h4
  have h4' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 96) hvbfProg 24
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h4)
  have hSaved :
      frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) =
        (((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
          ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8)) := by
    change (((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      (((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) ** empAssertion)) = _
    rw [sepConj_emp_right']
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) **
      (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) **
      tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) **
      (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ old8) ** (.x10 ↦ᵣ status) **
      (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) **
      tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h3'
  have h4F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) ** (.x10 ↦ᵣ status) **
      (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) **
      tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h4'
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1F h2F
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 h3F
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h123 h4F
  refine cpsTripleWithin_weaken (fun _ hp => by
      rw [hSaved] at hp
      xperm_hyp hp)
    (fun _ hq => by
      unfold hvbfFinal tailRest
      rw [hSaved]
      xperm_hyp hq) h1234

/-! The K73 failure path owns `x11` rather than preserving the caller's
    gas-used value.  Lift the concrete epilogue over that owned register so
    the status-2 wrapper post does not reintroduce the old false pin. -/
theorem hvbfEpilogueScratchOwn
    {cr : CodeReq}
    (sp0 spH raIn old8 headerPtr raBefore status out11 gasUsed : Word)
    (spK v9 old18 target v19 v20 parentPtr : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hF : F.pcFree) :
    cpsTripleWithin 4 (H + 84) raIn cr
      ((.x1 ↦ᵣ raBefore) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        (.x10 ↦ᵣ status) ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
          parentBytes scratchBytes headerBytes F)
      (hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        status out11 parentBytes scratchBytes headerBytes F) := by
  let P : Assertion :=
    (.x1 ↦ᵣ raBefore) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
      tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        parentBytes scratchBytes headerBytes F
  have hP : P.pcFree := by
    dsimp [P]
    pcf
    exact hF
  have hforall : ∀ old11, cpsTripleWithin 4 (H + 84) raIn cr
      (P ** (.x11 ↦ᵣ old11))
      (hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        status out11 parentBytes scratchBytes headerBytes F) := by
    intro old11
    have h := hvbfEpilogue (cr := cr)
      sp0 spH raIn old8 headerPtr raBefore status old11 gasUsed
      spK v9 old18 target v19 v20 parentPtr parentBytes scratchBytes headerBytes F
      hspH hret hcode hF
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h_state hq => ?_) h
    dsimp [P] at hp ⊢
    xperm_hyp hp
    let OutRest : Assertion :=
      (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) **
        (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
          parentBytes scratchBytes headerBytes F
    have hq1 :
        ((.x11 ↦ᵣ old11) ** OutRest) h_state := by
      dsimp [OutRest, hvbfFinal, tailRest] at hq ⊢
      xperm_hyp hq
    have hq2 : (regOwn .x11 ** OutRest) h_state :=
      sepConj_mono_left
        (P := (.x11 ↦ᵣ old11)) (P' := regOwn .x11) (Q := OutRest)
        (regIs_implies_regOwn (r := .x11) (v := old11)) _ hq1
    dsimp [OutRest, hvbfFinalScratch, tailRestScratch] at hq2 ⊢
    rw [show BitVec.ofNat 64 0 = (0 : Word) by rfl] at hq2
    rw [← (show (0 : Word) = BitVec.ofNat 64 0 by rfl)]
    xperm_chunked hq2
  have hown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
    (P := P)
    (Q := hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
      status out11 parentBytes scratchBytes headerBytes F)
    hforall
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => hq) hown
  dsimp [P] at hp ⊢
  xperm_hyp hp

/-! A same-`CodeReq` branch may have different continuations on its two exits.
    The library's union-based rules are deliberately more general, but the
    wrapper's dispatch reuses one linked image for both paths. -/

theorem cpsBranchWithin_seq_two_triples_same_cr
    {nBranch nTaken nFall : Nat} {entry target fall exit_ : Word}
    {cr : CodeReq} {P Qt Qf Q : Assertion}
    (hBranch : cpsBranchWithin nBranch entry cr P target Qt fall Qf)
    (hTaken : cpsTripleWithin nTaken target exit_ cr Qt Q)
    (hFall : cpsTripleWithin nFall fall exit_ cr Qf Q) :
    cpsBranchWithin (nBranch + nTaken + nFall) entry cr P exit_ Q exit_ Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hcase⟩ := hBranch R hR s hcr hPR hpc
  rcases hcase with ⟨hpc_t, hQtR⟩ | ⟨hpc_f, hQfR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hTaken R hR s1 hcr' hQtR hpc_t
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2,
      Or.inl ⟨hpc2, hQR⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hFall R hR s1 hcr' hQfR hpc_f
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2,
      Or.inr ⟨hpc2, hQR⟩⟩

theorem cpsBranchWithin_merge_two_bounds_same_cr
    {nBranch nTaken nFall : Nat} {entry target fall exit_ : Word}
    {cr : CodeReq} {P Qt Qf Q : Assertion}
    (hBranch : cpsBranchWithin nBranch entry cr P target Qt fall Qf)
    (hTaken : cpsTripleWithin nTaken target exit_ cr Qt Q)
    (hFall : cpsTripleWithin nFall fall exit_ cr Qf Q) :
    cpsTripleWithin (nBranch + nTaken + nFall) entry exit_ cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hcase⟩ := hBranch R hR s hcr hPR hpc
  rcases hcase with ⟨hpc_t, hQtR⟩ | ⟨hpc_f, hQfR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hTaken R hR s1 hcr' hQtR hpc_t
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2, hpc2, hQR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hFall R hR s1 hcr' hQfR hpc_f
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2, hpc2, hQR⟩

/-! ## Complete K74 wrapper

The two callee triples remain explicit premises.  The K73 premise is the
wrapper's only production seam; the equality helper is treated the same way
until its linked routine receives a corresponding whole-routine proof. -/

theorem header_validate_base_fee_spec_within
    {cr k73Code eqCode : CodeReq} {n73 nEq : Nat}
    (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (G : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hG : G.pcFree)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hk73Mono : ∀ a i, k73Code a = some i → cr a = some i)
    (hk73 : cpsTripleWithin n73 K73 (H + 40) k73Code
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes raIn old8 (k74FlatFrame G))
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20
          gasUsed parentPtr parentBytes expectedBytes headerBytes (k74FlatFrame G)))
    (heqMono : ∀ a i, eqCode a = some i → cr a = some i)
    (heq : cpsTripleWithin nEq EqK (H + 60) eqCode
      ((.x1 ↦ᵣ (H + 60)) **
        eqPre spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes (k74FlatFrame G))
      ((.x1 ↦ᵣ (H + 60)) **
        eqPostOwn spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes (k74FlatFrame G))) :
    cpsTripleWithin (27 + n73 + nEq) H raIn cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20 parentBytes expectedBytes headerBytes (k74FlatFrame G))
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes (k74FlatFrame G)) := by
  let F : Assertion := k74FlatFrame G
  have hF : G.pcFree := hG
  let v18 : Word := gasLimit >>> 1
  have hk73' := header_validate_base_fee_k73_call_spec_within
    (cr := cr) (calleeCode := k73Code) (n := n73)
    sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes F hspH hspK
    (by dsimp [F, k74FlatFrame]; pcf; exact hF) hcode
    hk73Mono hk73
  have hcall : cpsTripleWithin (10 + n73) H (H + 40) cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
    simpa only [F] using hk73'

  have hmem10 : ∀ a i,
      CodeReq.singleton (H + 40) (.BNE .x10 .x0 (40 : BitVec 13)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 40) hvbfProg 10
      (.BNE .x10 .x0 (40 : BitVec 13)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hbne_values : ∀ status : Word, cpsBranchWithin 1 (H + 40) cr
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ status)) (H + 80)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 44)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) := by
    intro status
    have hb := bne_spec_gen_within .x10 .x0 (40 : BitVec 13) status
      (0 : Word) (H + 40)
    have hb' := cpsBranchWithin_extend_code hmem10 hb
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ status)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := status)) h hq'')
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ status)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := status)) h hq'') hb'
  have hbneOwn : cpsBranchWithin 1 (H + 40) cr
      ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 80)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 44)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) :=
    cpsBranchWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := H + 40) (r := .x10)
      (P := (.x0 ↦ᵣ (0 : Word)))
      (exit_t := H + 80) (exit_f := H + 44)
      (Q_t := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10)
      (Q_f := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) hbne_values
  have hbneFrame := cpsBranchWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      regOwn .x11 ** tailRest spH spK raIn old8 headerPtr
        v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) hbneOwn
  have hbne : cpsBranchWithin 1 (H + 40) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 80)
        (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 44)
        (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsBranchWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_)
      (fun _ hq => ?_) hbneFrame
    · unfold hvbfDispatchPost at hp
      xperm_hyp hp
    · unfold hvbfDispatchPost
      xperm_hyp hq
    · unfold hvbfDispatchPost
      xperm_hyp hq

  have hmem20 : ∀ a i,
      CodeReq.singleton (H + 80) (.LI .x10 2) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 80) hvbfProg 20
      (.LI .x10 2) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h20 := li_spec_gen_own_within .x10 (2 : Word) (H + 80) (by decide)
  have h20' := cpsTripleWithin_extend_code hmem20 h20
  have h20F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h20'
  have h20Epi : cpsTripleWithin 1 (H + 80) (H + 84) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPreScratch spH spK raIn old8 headerPtr (H + 40) (2 : Word) gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h20F
    · unfold hvbfDispatchPost at hp
      xperm_hyp hp
    · unfold tailRest at hq
      unfold hvbfEpiPreScratch at ⊢
      xperm_hyp hq
  have h20Full := hvbfEpilogueScratchOwn (cr := cr)
    sp0 spH raIn old8 headerPtr (H + 40) (2 : Word) gasUsed gasUsed
    spK v9 old18 v18 v19 v20 parentPtr parentBytes expectedBytes headerBytes F
    hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
  have hFailPin : cpsTripleWithin 5 (H + 80) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        (2 : Word) gasUsed parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPreScratch at hp
      xperm_hyp hp)
      h20Epi h20Full
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hFail : cpsTripleWithin 5 (H + 80) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hFailPin
    unfold hvbfFinalAny
    exact Or.inl ⟨expectedBytes, hq⟩

  have hFailScratch : ∀ (status : Word) (scratchBytes : List (BitVec 8)),
      status ≠ (0 : Word) →
      cpsTripleWithin 5 (H + 80) raIn cr
        ((.x1 ↦ᵣ (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          (2 : Word) gasUsed parentBytes scratchBytes headerBytes F) := by
    intro status scratchBytes _hstatus
    have h20ScratchF := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (H + 40)) ** (regIs .x2 spH) ** (regIs .x8 headerPtr) **
        regOwn .x11 ** (regIs .x0 (0 : Word)) **
        tailRestScratch spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes scratchBytes headerBytes F) (by pcf; exact hF) h20'
    have h20Scratch : cpsTripleWithin 1 (H + 80) (H + 84) cr
        ((.x1 ↦ᵣ (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfEpiPreScratch spH spK raIn old8 headerPtr (H + 40) (2 : Word) gasUsed parentPtr
          v9 old18 v18 v19 v20 parentBytes scratchBytes headerBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => ?_) h20ScratchF
      · have hp' := hp
        unfold k73FailurePost at hp'
        let failureRest : Assertion :=
          (regIs .x1 (H + 40)) ** (regIs .x2 spH) ** (regIs .x8 headerPtr) **
          regOwn .x11 ** (regIs .x0 (0 : Word)) **
          tailRestScratch spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            parentBytes scratchBytes headerBytes F
        have hreg : ((.x10 ↦ᵣ status) ** failureRest) h := by
          dsimp [failureRest]
          unfold tailRestScratch at hp' ⊢
          dsimp [H] at hp' ⊢
          xperm_hyp hp'
        have hown : (regOwn .x10 ** failureRest) h :=
          sepConj_mono_left (regIs_implies_regOwn (r := .x10) (v := status)) h hreg
        dsimp [failureRest] at hown
        unfold tailRestScratch at hown ⊢
        dsimp [H] at hown ⊢
        xperm_hyp hown
      · unfold hvbfEpiPreScratch
        unfold tailRestScratch at hq
        xperm_hyp hq
    have h20FullScratch := hvbfEpilogueScratchOwn (cr := cr)
      sp0 spH raIn old8 headerPtr (H + 40) (2 : Word) gasUsed gasUsed
      spK v9 old18 v18 v19 v20 parentPtr parentBytes scratchBytes headerBytes F
      hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPreScratch at hp
      xperm_hyp hp) h20Scratch h20FullScratch
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

  have hFailureBranch : ∀ (status : Word) (scratchBytes : List (BitVec 8)),
      status ≠ (0 : Word) →
      cpsTripleWithin 6 (H + 40) raIn cr
        ((.x1 ↦ᵣ (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
    intro status scratchBytes hstatus
    have hbneRaw := bne_spec_gen_within .x10 .x0 (40 : BitVec 13) status
      (0 : Word) (H + 40)
    have hbneCode := cpsBranchWithin_extend_code hmem10 hbneRaw
    have hbneFrame := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        regOwn .x11 **
        tailRestScratch spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes scratchBytes headerBytes F) (by pcf; exact hF) hbneCode
    have hbneFailure : cpsBranchWithin 1 (H + 40) cr
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (H + 80)
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F **
          ⌜status ≠ (0 : Word)⌝)
        (H + 44)
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F **
          ⌜status = (0 : Word)⌝) := by
      refine cpsBranchWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_)
        (fun _ hq => ?_) hbneFrame
      · unfold k73FailurePost at hp
        xperm_hyp hp
      · unfold k73FailurePost
        unfold tailRestScratch at hq ⊢
        dsimp [H] at hq ⊢
        xperm_hyp hq
      · unfold k73FailurePost
        unfold tailRestScratch at hq ⊢
        dsimp [H] at hq ⊢
        xperm_hyp hq
    have h_taken : cpsTripleWithin 1 (H + 40) (H + 80) cr
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F) := by
      apply cpsBranchWithin_takenStripPure2 hbneFailure
      intro h hq
      open EvmAsm.Rv64.Tactics in
        extract_pure_deep hq
      exact hstatus hq.1
    have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      h_taken (hFailScratch status scratchBytes hstatus)
    have hseq' : cpsTripleWithin 6 (H + 40) raIn cr
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hseq
      exact Or.inl ⟨scratchBytes, hq⟩
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hseq'

  have hmem11 : ∀ a i,
      CodeReq.singleton (H + 44) (.MV .x10 .x8) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 44) hvbfProg 11
      (.MV .x10 .x8) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h11_values : ∀ old10, cpsTripleWithin 1 (H + 44) (H + 48) cr
      ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ old10))
      ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ headerPtr)) := by
    intro old10
    have hm := mv_spec_gen_within .x10 .x8 headerPtr old10 (H + 44) (by decide)
    exact cpsTripleWithin_extend_code hmem11 hm
  have h11Own : cpsTripleWithin 1 (H + 44) (H + 48) cr
      ((.x8 ↦ᵣ headerPtr) ** regOwn .x10)
      ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ headerPtr)) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := H + 44) (r := .x10)
      (P := (.x8 ↦ᵣ headerPtr)) (exit_ := H + 48)
      (Q := (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ headerPtr)) h11_values
  have h11F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** regOwn .x11 **
      (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h11Own
  have h11Done : cpsTripleWithin 1 (H + 44) (H + 48) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEqPrefixPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h11F
    · unfold hvbfDispatchPost at hp
      xperm_hyp hp
    · unfold hvbfEqPrefixPost at ⊢
      xperm_hyp hq

  have hmem12 : ∀ a i,
      CodeReq.singleton (H + 48)
        (.AUIPC .x11 (laHi GuestAddrs.hvbf_expected
          (GuestAddrs.header_validate_base_fee + 48))) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 48) hvbfProg 12
      (.AUIPC .x11 (laHi GuestAddrs.hvbf_expected
        (GuestAddrs.header_validate_base_fee + 48))) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hmem13 : ∀ a i,
      CodeReq.singleton (H + 52)
        (.ADDI .x11 .x11 (laLo GuestAddrs.hvbf_expected
          (GuestAddrs.header_validate_base_fee + 48))) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 52) hvbfProg 13
      (.ADDI .x11 .x11 (laLo GuestAddrs.hvbf_expected
        (GuestAddrs.header_validate_base_fee + 48))) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hla := EvmAsm.Rv64.la_materialize_within .x11 gasUsed (H + 48) Expected
    (by decide) (by unfold H Expected; decide) hmem12 hmem13
  have hlaValues : ∀ old11, cpsTripleWithin 2 (H + 48) (H + 56) cr
      (.x11 ↦ᵣ old11) (.x11 ↦ᵣ Expected) := by
    intro old11
    have hlaOld := EvmAsm.Rv64.la_materialize_within .x11 old11 (H + 48) Expected
      (by decide) (by unfold H Expected; decide) hmem12 hmem13
    simpa only [show H + 48 + 8 = H + 56 by bv_omega] using hlaOld
  have hlaOwn0 := cpsTripleWithin_of_forall_regIs_to_regOwn_single (r := .x11)
    (Q := (.x11 ↦ᵣ Expected)) hlaValues
  have hlaOwn : cpsTripleWithin 2 (H + 48) (H + 56) cr
      (regOwn .x11) (.x11 ↦ᵣ Expected) := by
    simpa only [sepConj_emp_left'] using hlaOwn0
  have hlaF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x10 ↦ᵣ headerPtr) ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) hlaOwn
  have hprefixRaw := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold hvbfEqPrefixPost at hp
    xperm_hyp hp) h11Done hlaF
  have hprefix : cpsTripleWithin 3 (H + 44) (H + 56) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        eqPre spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hprefixRaw
    unfold eqPre
    xperm_hyp hq

  have hmem14 : ∀ a i,
      CodeReq.singleton (H + 56)
        (.JAL .x1 (jalOff GuestAddrs.u256_eq
          (GuestAddrs.header_validate_base_fee + 56))) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 56) hvbfProg 14
      (.JAL .x1 (jalOff GuestAddrs.u256_eq
        (GuestAddrs.header_validate_base_fee + 56))) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have heqCr := cpsTripleWithin_extend_code heqMono heq
  have heqFramedRaw := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr)) (by pcf) heqCr
  have heqFramed : cpsTripleWithin nEq EqK (H + 56 + 4) cr
      ((.x1 ↦ᵣ (H + 56 + 4)) **
        ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
          eqPre spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            parentBytes expectedBytes headerBytes F))
      ((.x1 ↦ᵣ (H + 56 + 4)) **
        ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
          eqPostOwn spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            parentBytes expectedBytes headerBytes F)) := by
    rw [show H + 60 = H + 56 + 4 by bv_omega] at heqFramedRaw
    refine cpsTripleWithin_weaken (fun _ hp => by
        unfold eqPre tailRest at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        unfold eqPostOwn tailRest at hq ⊢
        xperm_hyp hq) heqFramedRaw
  have heqCallRaw := callWithin_spec (cr := cr)
    (P := (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      eqPre spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F)
    (Q := (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      eqPostOwn spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F)
    (H + 56) EqK (H + 40)
      (jalOff GuestAddrs.u256_eq
        (GuestAddrs.header_validate_base_fee + 56)) nEq
    (by exact jalOff_correct_add GuestAddrs.u256_eq
          GuestAddrs.header_validate_base_fee 56 (by decide) (by decide)
          (by decide) (by decide)) hmem14
    (by pcf; exact hF) heqFramed
  have heqAtRaw := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_hyp hp) hprefix heqCallRaw
  have heqAt0 : cpsTripleWithin (4 + nEq) (H + 44) (H + 60) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 60)) **
        ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
          eqPostOwn spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
            parentBytes expectedBytes headerBytes F)) := by
    have hretEq : H + 56 + 4 = H + 60 := by bv_omega
    have hsteps : 3 + (1 + nEq) = 4 + nEq := by omega
    simpa only [Nat.add_assoc, hretEq, hsteps] using heqAtRaw
  have heqAt : cpsTripleWithin (4 + nEq) (H + 44) (H + 60) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) heqAt0
    unfold eqPostOwn tailRest at hq
    unfold hvbfEqDispatchPost tailRest at ⊢
    xperm_hyp hq

  have hmem15 : ∀ a i,
      CodeReq.singleton (H + 60) (.BEQ .x10 .x0 (12 : BitVec 13)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 60) hvbfProg 15
      (.BEQ .x10 .x0 (12 : BitVec 13)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hbeq_values : ∀ eqStatus : Word, cpsBranchWithin 1 (H + 60) cr
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ eqStatus)) (H + 72)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 64)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) := by
    intro eqStatus
    have hb := beq_spec_gen_within .x10 .x0 (12 : BitVec 13) eqStatus
      (0 : Word) (H + 60)
    have hb' := cpsBranchWithin_extend_code hmem15 hb
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ eqStatus)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := eqStatus)) h hq'')
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ eqStatus)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := eqStatus)) h hq'') hb'
  have hbeqOwn : cpsBranchWithin 1 (H + 60) cr
      ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 72)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 64)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) :=
    cpsBranchWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := H + 60) (r := .x10)
      (P := (.x0 ↦ᵣ (0 : Word)))
      (exit_t := H + 72) (exit_f := H + 64)
      (Q_t := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10)
      (Q_f := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) hbeq_values
  have hbeqFrame := cpsBranchWithin_frameR
    ((.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ Expected) **
      tailRest spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) hbeqOwn
  have hbeq : cpsBranchWithin 1 (H + 60) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 72)
        (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 64)
        (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsBranchWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_)
      (fun _ hq => ?_) hbeqFrame
    · simp only [hvbfEqDispatchPost, tailRest] at hp ⊢
      xperm_hyp hp
    · simp only [hvbfEqDispatchPost, tailRest] at hq ⊢
      xperm_hyp hq
    · simp only [hvbfEqDispatchPost, tailRest] at hq ⊢
      xperm_hyp hq

  have hmem18 : ∀ a i,
      CodeReq.singleton (H + 72) (.LI .x10 1) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 72) hvbfProg 18
      (.LI .x10 1) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h18 := li_spec_gen_own_within .x10 (1 : Word) (H + 72) (by decide)
  have h18' := cpsTripleWithin_extend_code hmem18 h18
  have h18F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h18'
  have h18Epi : cpsTripleWithin 1 (H + 72) (H + 76) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (1 : Word) Expected parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h18F
    · simp only [hvbfEqDispatchPost, tailRest] at hp ⊢
      xperm_hyp hp
    · simp only [hvbfEpiPre, tailRest] at hq ⊢
      xperm_hyp hq
  have hmem19 : ∀ a i,
      CodeReq.singleton (H + 76) (.JAL .x0 (8 : BitVec 21)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 76) hvbfProg 19
      (.JAL .x0 (8 : BitVec 21)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h19 := jal_x0_spec_gen_within (8 : BitVec 21) (H + 76)
  have h19' := cpsTripleWithin_extend_code hmem19 h19
  have h19F := cpsTripleWithin_frameR
    (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (1 : Word) Expected parentPtr
      v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h19'
  have hThenEpi : cpsTripleWithin 2 (H + 72) (H + 84) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (1 : Word) Expected parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simpa only [sepConj_emp_left'] using hp) h18Epi h19F
    have hpc : H + 76 + signExtend21 (8 : BitVec 21) = H + 84 := by
      have hs : signExtend21 (8 : BitVec 21) = (8 : Word) := by decide
      rw [hs]
      bv_omega
    rw [hpc] at h
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
    simpa only [sepConj_emp_left'] using hq
  have hEpi1 := hvbfEpilogue (cr := cr)
    sp0 spH raIn old8 headerPtr (H + 60) (1 : Word) Expected gasUsed
    spK v9 old18 v18 v19 v20 parentPtr parentBytes expectedBytes headerBytes F
    hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
  have hThenPin : cpsTripleWithin 6 (H + 72) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        (1 : Word) Expected parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPre at hp
      xperm_hyp hp) hThenEpi hEpi1
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hThen : cpsTripleWithin 6 (H + 72) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hThenPin
    unfold hvbfFinalAny
    exact Or.inr (Or.inr hq)

  have hmem16 : ∀ a i,
      CodeReq.singleton (H + 64) (.LI .x10 0) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 64) hvbfProg 16
      (.LI .x10 0) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h16 := li_spec_gen_own_within .x10 (0 : Word) (H + 64) (by decide)
  have h16' := cpsTripleWithin_extend_code hmem16 h16
  have h16F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h16'
  have h16Epi : cpsTripleWithin 1 (H + 64) (H + 68) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (0 : Word) Expected parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h16F
    · simp only [hvbfEqDispatchPost, tailRest] at hp ⊢
      xperm_hyp hp
    · simp only [hvbfEpiPre, tailRest] at hq ⊢
      xperm_hyp hq
  have hmem17 : ∀ a i,
      CodeReq.singleton (H + 68) (.JAL .x0 (16 : BitVec 21)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 68) hvbfProg 17
      (.JAL .x0 (16 : BitVec 21)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h17 := jal_x0_spec_gen_within (16 : BitVec 21) (H + 68)
  have h17' := cpsTripleWithin_extend_code hmem17 h17
  have h17F := cpsTripleWithin_frameR
    (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (0 : Word) Expected parentPtr
      v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h17'
  have hElseEpi : cpsTripleWithin 2 (H + 64) (H + 84) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (0 : Word) Expected parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simpa only [sepConj_emp_left'] using hp) h16Epi h17F
    have hpc : H + 68 + signExtend21 (16 : BitVec 21) = H + 84 := by
      have hs : signExtend21 (16 : BitVec 21) = (16 : Word) := by decide
      rw [hs]
      bv_omega
    rw [hpc] at h
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
    simpa only [sepConj_emp_left'] using hq
  have hEpi0 := hvbfEpilogue (cr := cr)
    sp0 spH raIn old8 headerPtr (H + 60) (0 : Word) Expected gasUsed
    spK v9 old18 v18 v19 v20 parentPtr parentBytes expectedBytes headerBytes F
    hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
  have hElsePin : cpsTripleWithin 6 (H + 64) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        (0 : Word) Expected parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPre at hp
      xperm_hyp hp) hElseEpi hEpi0
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hElse : cpsTripleWithin 6 (H + 64) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hElsePin
    unfold hvbfFinalAny
    exact Or.inr (Or.inl hq)

  have hEqFull : cpsTripleWithin 7 (H + 60) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    have h := cpsBranchWithin_merge_same_cr hbeq hThen hElse
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hEqFullAt : cpsTripleWithin (11 + nEq) (H + 44) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      heqAt hEqFull
    have hs : (4 + nEq) + 7 = 11 + nEq := by omega
    simpa only [hs] using h
  have hMerge : cpsTripleWithin (17 + nEq) (H + 40) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 old18 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    have h := cpsBranchWithin_merge_two_bounds_same_cr hbne hFail hEqFullAt
    have hs : 1 + 5 + (11 + nEq) = 17 + nEq := by omega
    simpa only [hs] using h
  have hSuccessMerge : cpsTripleWithin (17 + nEq) (H + 40) raIn cr
      ((regIs .x1 (H + 40)) **
        k73PostOwn spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes raIn old8 F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => hq) hMerge
    unfold hvbfDispatchPost at ⊢
    dsimp [k73PostOwn] at hp ⊢
    xperm_chunked hp
  have hMergeAny : cpsTripleWithin (17 + nEq) (H + 40) raIn cr
      ((regIs .x1 (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    intro R hR s hcr hPR hpc
    obtain ⟨h, hcompat, hP_R⟩ := hPR
    obtain ⟨h1, h2, hd, hunion, hP, hR_⟩ := hP_R
    obtain ⟨h1P, h2P, hdP, hunionP, hx1, hK⟩ := hP
    unfold k73CallPost at hK
    rcases hK with hsuccess | ⟨status, scratchBytes, hstatus, hfailure⟩
    · have hP' :
          ((regIs .x1 (H + 40)) **
            k73PostOwn spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
              parentBytes expectedBytes headerBytes raIn old8 F) h1 := by
        exact ⟨h1P, h2P, hdP, hunionP, hx1, hsuccess⟩
      have hpre :
          (((regIs .x1 (H + 40)) **
            k73PostOwn spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
              parentBytes expectedBytes headerBytes raIn old8 F) ** R) h := by
        exact ⟨h1, h2, hd, hunion, hP', hR_⟩
      have hpreS :
          (((regIs .x1 (H + 40)) **
            k73PostOwn spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
              parentBytes expectedBytes headerBytes raIn old8 F) ** R).holdsFor s := by
        exact ⟨h, hcompat, hpre⟩
      exact hSuccessMerge R hR s hcr hpreS hpc
    · have hP' :
          ((regIs .x1 (H + 40)) **
            k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
              status parentBytes scratchBytes headerBytes raIn old8 F) h1 := by
        exact ⟨h1P, h2P, hdP, hunionP, hx1, hfailure⟩
      have hpre :
          (((regIs .x1 (H + 40)) **
            k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
              status parentBytes scratchBytes headerBytes raIn old8 F) ** R) h := by
        exact ⟨h1, h2, hd, hunion, hP', hR_⟩
      have hpreS :
          (((regIs .x1 (H + 40)) **
            k73FailurePost spH spK headerPtr v9 old18 v18 v19 v20 gasUsed parentPtr
              status parentBytes scratchBytes headerBytes raIn old8 F) ** R).holdsFor s := by
        exact ⟨h, hcompat, hpre⟩
      obtain ⟨k, hk, s', hstep, hpc', hQR⟩ :=
        hFailureBranch status scratchBytes hstatus R hR s hcr hpreS hpc
      exact ⟨k, by omega, s', hstep, hpc', hQR⟩
  have hAll := cpsTripleWithin_seq_same_cr hcall hMergeAny
  have hs : (10 + n73) + (17 + nEq) = 27 + n73 + nEq := by omega
  simpa only [F, k74FlatFrame, hs] using hAll

end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
