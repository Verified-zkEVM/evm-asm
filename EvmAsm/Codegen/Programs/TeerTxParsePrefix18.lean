/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix18

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **walk-boundary scratch-ownership adaptor**.

  At every walk boundary the previous `…_toglue` block returns the walk-callee
  scratch as `teerWalkScratch` (the seven `regOwn` cells `x5`/`x6`/`x7`/`x28..x31`
  plus `x0` and the single physical `bytesRegion`), but the next walk dispatch
  GROUP's precondition wants those seven scratch registers CONCRETE
  (`x5 ↦ t0Old … x31 ↦ t6Old`).  `teer_walk_scratch_regOwn_adaptor` bridges the
  gap once and for all: given a walk block that holds for EVERY concrete choice
  of the seven scratch values (which every group spec is, being universally
  quantified over `t0Old..t6Old`), it produces the variant whose precondition
  carries only `teerWalkScratch` — so the join is a pure permutation match
  (`teerWalkScratch` as a single atom) with the previous block's fall post.

  Built on `cpsBranchWithin_of_forall_regIs_to_regOwn7` (module 15): reshape the
  precondition to the trailing-`regIs` form the `∀`→`regOwn` lemma expects,
  abstract the seven scratch registers, then reshape back to `teerWalkScratch`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix17

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The walk-boundary scratch-ownership adaptor -/

set_option maxRecDepth 8000 in
/-- **Walk-boundary scratch adaptor.**  Turns a walk block that holds for every
    concrete scratch (`x5 ↦ t0 … x31 ↦ t6`, with `x0 ↦ 0` and the physical
    `bytesRegion` trailing) into the variant whose precondition carries only the
    bundled `teerWalkScratch srcBase srcBytes`, keeping the leading `x1`/`x10`/
    `x11`/`x12` register cells and the trailing frame `REST` unchanged. -/
theorem teer_walk_scratch_regOwn_adaptor
    {nSteps : Nat} {entry exit_t exit_f : Word} {Q_t Q_f : Assertion}
    (x1v x10v x11v x12v srcBase : Word) (srcBytes : List (BitVec 8))
    (REST : Assertion)
    (h : ∀ t0 t1 t2 t3 t4 t5 t6 : Word,
      cpsBranchWithin nSteps entry fullCode
        (((.x1 ↦ᵣ x1v) **
          ((.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x12 ↦ᵣ x12v) **
            (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) ** (.x28 ↦ᵣ t3) **
            (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes)) ** REST)
        exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry fullCode
      (((.x1 ↦ᵣ x1v) **
        ((.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x12 ↦ᵣ x12v) **
          teerWalkScratch srcBase srcBytes)) ** REST)
      exit_t Q_t exit_f Q_f := by
  -- Step 1: reshape into the trailing-regIs form `regOwn7` expects.
  have h' : ∀ v1 v2 v3 v4 v5 v6 v7 : Word,
      cpsBranchWithin nSteps entry fullCode
        ((((.x1 ↦ᵣ x1v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x12 ↦ᵣ x12v) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** REST) **
          (.x5 ↦ᵣ v1) ** (.x6 ↦ᵣ v2) ** (.x7 ↦ᵣ v3) ** (.x28 ↦ᵣ v4) **
          (.x29 ↦ᵣ v5) ** (.x30 ↦ᵣ v6) ** (.x31 ↦ᵣ v7)))
        exit_t Q_t exit_f Q_f := by
    intro v1 v2 v3 v4 v5 v6 v7
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) (h v1 v2 v3 v4 v5 v6 v7)
  -- Step 2: abstract the seven scratch registers to `regOwn`.
  have h'' := cpsBranchWithin_of_forall_regIs_to_regOwn7 .x5 .x6 .x7 .x28 .x29 .x30 .x31 h'
  -- Step 3: fold the `regOwn` block back into `teerWalkScratch`.
  exact cpsBranchWithin_weaken
    (fun _ hp => by simp only [teerWalkScratch] at hp; xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq) h''

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
