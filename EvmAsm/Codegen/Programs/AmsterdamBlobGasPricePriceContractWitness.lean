import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody11Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14TerminalSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Composition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundParityComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundQBackComposition
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceU256Sat
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceTaylorTie
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody8Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterFold
import EvmAsm.Rv64.MemSat

set_option maxRecDepth 8000

/-!
  Constructive satisfiability witness for `priceContract` (#12346, K70 seam):
  the `excess = 0` input.  This is a NON-VACUITY witness for one input value,
  not a discharge of the contract: it proves that the machine, from the
  concrete `excess = 0` entry state, runs `priceContract` to the status-0 exit
  in 8271 steps.  Inputs with `excess ≠ 0` are NOT covered here (they require
  the full 495-round fold).

  Route (measured, verified against the per-window specs):
    setup 27  (`price_setup_spec`, PriceK+36 → PriceK+144)
    round 4028 (`taylor_round` at j=0, acc=[D,0,0,0,0,0] with D = taylorDW;
                 the +804 round-zero exit and the 10 overflow exits are dead,
                 only the QBACK backedge fires)
    second loop-head pass 14 (loop_test_or_chainP 13 + loop_test_beqz_branch 1,
                 acc now [0×6] so beqz-taken fires at +804)
    exitdiv+tail 4183 (round_zero_exitdiv_tail_swapped, +804 → +968)
  body total 8252; whole routine 8271 = 1+8+8252+8+1+1 (ABI shell).
  Model: `taylor_price_outcome_zero` gives priceOutcome 0 = (0, natToBeBytes 32 1).
-/

namespace EvmAsm.Codegen.AmsterdamBlobGasPricePriceContractWitness

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec

/-- Drop an exit whose post is absurd (`∀ h, Q h → False`) from an N-branch's
    exit list.  Used to eliminate the dead overflow exits of `taylor_round` at
    `excess = 0`, where each carries a pure that reduces to false. -/
private theorem cpsNBranchWithin_drop_absurd_exit
    {nSteps : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {pre post : List (Word × Assertion)} {m : Word} {Q : Assertion}
    (hQ : ∀ h, Q h → False)
    (h : cpsNBranchWithin nSteps entry cr P (pre ++ [(m, Q)] ++ post)) :
    cpsNBranchWithin nSteps entry cr P (pre ++ post) := by
  intro R hRfree s hcr hP hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hRfree s hcr hP hpc
  refine ⟨k, hk, s', hstep, ex, ?_, hpc', hQR⟩
  have hne : ex ≠ (m, Q) := by
    intro heq
    subst heq
    have hQl := holdsFor_sepConj_elim_left hQR
    obtain ⟨hq, _, hqw⟩ := hQl
    exact hQ hq hqw
  have hmem' : ex ∈ pre ++ post := by
    rw [List.mem_append] at hmem
    rcases hmem with hpre | hrest
    · rw [List.mem_append] at hpre
      rcases hpre with hpre' | hm
      · exact List.mem_append.mpr (Or.inl hpre')
      · exfalso
        exact hne (List.mem_singleton.mp hm)
    · exact List.mem_append.mpr (Or.inr hrest)
  exact hmem'

end EvmAsm.Codegen.AmsterdamBlobGasPricePriceContractWitness