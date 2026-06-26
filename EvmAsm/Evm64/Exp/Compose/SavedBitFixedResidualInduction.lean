/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedResidualInduction

  The `ExpResidual`-threaded merged fixed-x19 EXP loop-body induction.

  STATUS: scaffold + validated plan (resumable WIP). The full induction proof is
  the single remaining atomic piece for `evm_exp_stack_spec_within`; every
  ingredient lemma it needs is already proven and committed (see below). This
  file is intentionally NOT yet imported into `EvmAsm/Evm64/Exp.lean`, so the
  umbrella build stays green while the proof is finished.

  Unlike `exp_merged_loop_from_iterpre_induction` (parametric in `c6`, hence
  needing the unprovable pure `MergedReloadReshuffle`), this induction threads
  the exponent residual through the body via the framed step and carries the
  control invariant as a pure side condition, making the reload boundary a pure
  re-partition.

  ── EXACT STATEMENT (validated to elaborate; copy this when filling the proof) ──

  theorem exp_merged_loop_from_iterpre_residual_induction
      (base sp evmSp a0 a1 a2 a3 : Word) (R : Assertion)
      (exponentWord : EvmWord) (lookahead : Word)
      (hbase : (base + 44 : Word) &&& 1 = 0)
      (hExitU :
        ∀ (e c6 iterCount ptr nextLimb r0 r1 r2 r3 : Word) (ps : PartialState),
          (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base **
            expTwoMulFixedExpResidual 3 ptr lookahead exponentWord) ps →
          R ps)
      (n : Nat) :
      ∀ (e c6 iterCount v10 v18 ptr nextLimb tOld vOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 : Word),
        iterCount.toNat = n + 1 →
        expTwoMulFixedControlInvariant exponentWord (255 - n) c6 ptr nextLimb evmSp →
        cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
            tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
           expTwoMulFixedExpResidual ((255 - n) / 64) ptr lookahead exponentWord)
          R

  ── PROOF PLAN (all cited lemmas proven & committed) ──

  induction n.
  • zero (n=0, k=255, b=3, ExpResidual 3 = emp): apply
    `exp_fixed_loop_body_final_succ_step_framed` with F := ExpResidual 3 ptr …
    (= emp; `expTwoMulFixedExpResidual_ge_three`), hF via `_pcFree`,
    hzero via `expTwoMulIterCountNew_eq_zero_of_toNat_one`, hExit := hExitU
    instantiated.
  • succ k (n=k+1, k_iter=255-(k+1)=254-k, b=(254-k)/64): apply
    `exp_fixed_loop_body_succ_step_framed (k+1)` with F := ExpResidual b ptr …,
    hExit = vacuous (count≠0) via the framed vacuous bridge, and hLoop built as:
      intro the cpsTriple; obtain the `MergedLoopPost ** F ** Rframe` holdsFor;
      rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost]; unfold CaseLoopPost
      into its 4 CountPost disjuncts (SkipCond/Skip[**PointerPost] ∨
      ReloadCond/ReloadSkip):
        - non-reload (SkipCond / Skip): apply
          `expTwoMulFixedIterSkip{Cond,}CountPost_residual_repartition`
          (input `(CountPost ** PointerPost) ** (ExpResidual b ptr ** Rframe)`,
          output next IterPre ** (ExpResidual b ptr ** Rframe)); derive the next
          control invariant via `expTwoMulFixedControlInvariant_succ_no_reload`
          (b, ptr unchanged); apply IH at n=k.
        - reload (ReloadCond / ReloadSkip): the disjunct pure gives
          c6+signExtend12(-1)=0; with the carried control invariant,
          `expTwoMulFixedControlInvariant_reload_mod` ⇒ k_iter%64=63, and
          k_iter<255 ⇒ `expTwoMulFixedReloadBlock_cases` ⇒ b∈{0,1,2}; apply the
          matching `expTwoMulFixedIterReload{Cond,Skip}CountPost_residual_repartition_{zero,one,two}`
          (output next IterPre ** ((ptr↦nextLimb) ** ExpResidual (b+1)(ptr-8) ** Rframe));
          the stale `(ptr↦nextLimb)` cell joins the ambient frame; derive next
          control invariant via `expTwoMulFixedControlInvariant_succ_reload`;
          apply IH at n=k (b+1, ptr-8). Use `xperm_hyp` for opaque-frame perms.

  ── REMAINING SUBTLETY (the one open design point) ──
  At exit (n=0, b=3) `ExpResidual 3 = emp`, so the exit-bridge disjuncts
  (`SavedBitFixedExitBridge.lean`) — which need the read-only exponent frame
  `evmWordIs (evmSp-32) exponentWord` — must source it from the *ambient*
  universal frame (the passed exponent cells, above x16), not from `F`. So
  `hExitU`'s eventual discharge (step C) reconciles the exit post against the
  ambient exponent; this affects only the `hExitU` *discharge*, not this
  induction's statement (which carries `ExpResidual 3 = emp` cleanly).

  ── CHAIN after this induction (proven ingredients) ──
  instantiate at n=255 (b=0; control invariant at k=0 is
  `expTwoMulFixedControlInvariant_zero`; entry residual = ExpResidual 0 plus the
  +24 look-ahead sourced from the ambient stack) → hBody; feed boundary
  `exp_two_mul_fixed_full_loop_boundary_of_entry_iterpre_body_general_spec_within`
  (`SavedBitBoundaryLoopFixedEntryExists.lean:1054`) + the proven semantic bridge
  `expTwoMulFixedAccumulatorInvariant_full` → `evm_exp_stack_spec_within`.
-/

import EvmAsm.Evm64.Exp.Compose.MergedLoopInd
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedMergedFramedStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadResidualRepartition

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

end EvmAsm.Evm64.Exp.Compose
