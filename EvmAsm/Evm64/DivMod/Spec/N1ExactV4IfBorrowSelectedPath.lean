module

public import EvmAsm.Evm64.DivMod.Spec.N1ExactV4IfBorrowPathWord

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Build the selected-if-borrow semantic evidence package from selected N1
    path evidence for the canonical `getLimbN` inputs. This is the preferred
    boundary for new wrappers because it carries the selected branch-sensitive
    facts directly instead of exposing the legacy `Carry2NzAll` package. -/
theorem FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_selected_path_evidence_getLimbN
    (sp base : Word) (a b : EvmWord)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  exact FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_bltu_selected
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    hbltu3 hbltu2 hbltu1 hbltu0
    (N1SelectedIfBorrowPathEvidence.selectedCarryIfBorrowFacts hpath)
    hfacts

/-- Project the hdiv package from selected N1 path evidence for the canonical
    `getLimbN` inputs. -/
theorem FullDivN1CallMaxmaxmaxHdivs_of_selected_path_evidence_getLimbN
    (sp base : Word) (a b : EvmWord)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    FullDivN1CallMaxmaxmaxHdivs a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact FullDivN1CallMaxmaxmaxHdivs_of_selected_if_borrow_semantic_evidence
    sp base a b jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz
    (FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_selected_path_evidence_getLimbN
      sp base a b jOld v5Old v6Old v7Old v10Old v11Old v2Old
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts)

/-- Project the hdiv package from selected N1 path evidence for canonical
    `getLimbN` inputs, using the public EVM-word nonzero hypothesis. -/
theorem FullDivN1CallMaxmaxmaxHdivs_of_selected_path_evidence_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b ≠ 0)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    FullDivN1CallMaxmaxmaxHdivs a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  FullDivN1CallMaxmaxmaxHdivs_of_selected_path_evidence_getLimbN
    sp base a b jOld v5Old v6Old v7Old v10Old v11Old v2Old
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
    hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts

/-- N1 selected-if-borrow stack wrapper consuming selected path evidence
    directly, without exposing the older all-true `Carry2NzAll` package at
    this boundary. This is the `divCode_v4` counterpart to the no-NOP wrapper
    below. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_selected_path_semantic_facts_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  have hevidence :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_selected_path_evidence_getLimbN
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts
  have hselected :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_selectedInput
      sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence
  have hdivs :=
    FullDivN1CallMaxmaxmaxHdivs_of_selected_path_evidence_getLimbN
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_if_borrow_input_hdivs
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl rfl rfl rfl rfl
    ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z
    hshift_nz halign hselected hdivs

/-- No-NOP N1 selected-if-borrow stack wrapper consuming selected path
    evidence directly, without exposing the older all-true `Carry2NzAll`
    package at this boundary. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_noNop_of_selected_if_borrow_selected_path_semantic_facts_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  have hevidence :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_selected_path_evidence_getLimbN
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts
  have hselected :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_selectedInput
      sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence
  have hdivs :=
    FullDivN1CallMaxmaxmaxHdivs_of_selected_path_evidence_getLimbN
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_noNop_of_selected_if_borrow_input_hdivs
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl rfl rfl rfl rfl
    ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z
    hshift_nz halign hselected hdivs

/-- N1 selected-if-borrow stack wrapper for canonical `getLimbN` inputs that
    consumes the bundled selected-if-borrow semantic evidence directly. This
    keeps selected path/carry/hdiv projections behind one private evidence
    object at the stack-wrapper boundary. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_semantic_evidence_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  have hselected :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_selectedInput
      sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence
  have hdivs :=
    FullDivN1CallMaxmaxmaxHdivs_of_selected_if_borrow_semantic_evidence
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      rfl rfl rfl rfl rfl rfl rfl rfl
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hevidence
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_if_borrow_input_hdivs
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl rfl rfl rfl rfl
    ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z
    hshift_nz halign hselected hdivs

/-- No-NOP counterpart of
    `evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_semantic_evidence_ne_zero_getLimbN`. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_noNop_of_selected_if_borrow_semantic_evidence_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  have hselected :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_selectedInput
      sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence
  have hdivs :=
    FullDivN1CallMaxmaxmaxHdivs_of_selected_if_borrow_semantic_evidence
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      rfl rfl rfl rfl rfl rfl rfl rfl
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hevidence
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_noNop_of_selected_if_borrow_input_hdivs
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl rfl rfl rfl rfl
    ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z
    hshift_nz halign hselected hdivs

end EvmAsm.Evm64
