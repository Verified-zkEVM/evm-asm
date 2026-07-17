/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix6

  PASS 3 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  COMPOSES the tx-parse prefix call groups + BNEs (proven in
  `TeerTxParsePrefix`..`TeerTxParsePrefix5`) into a single `cpsBranchWithin`
  chain from the body-entry PC `teerB + 136` toward the per-auth loop head
  `teerB + 724`, under the `TeerBodyAssumptions` footing plus the per-walk
  parse-success hypotheses.

  The join recipe (from `teer_txtype_dispatch_spec`, module 5): every
  parse-failure `BNE` routes TAKEN → far epilogue `teerB + 2856` and NOT-TAKEN
  → the next PC.  Chaining two such branches uses
  `cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr`; appending a
  straight-line block uses `cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr`.
  Because THIS pass targets only the loop-entry witness (the ntaken exit), the
  shared TAKEN (failure) postcondition is the trivial `teerFail := fun _ => True`
  (each per-BNE failure state weakens into it); a later epilogue pass refines it.

  **Frame union** (hard piece 1): the entry precondition carries the UNION of
  all downstream-touched registers / `.bss` cells as an ambient frame
  (`teerPrefixExtra`); each small segment spec is framed with the complement it
  does not touch, and reconciled through each join by `xperm_hyp`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix5
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- The shared TAKEN (parse-failure) postcondition at the far epilogue
    `teerB + 2856`.  Every per-`BNE` failure state weakens into this trivial
    assertion; THIS pass proves only that a parse failure REACHES the epilogue,
    with the precise rolled-back state deferred to the epilogue pass. -/
def teerFail : Assertion := fun _ => True

/-- Any assertion weakens to `teerFail`. -/
theorem to_teerFail (Q : Assertion) : ∀ h, Q h → teerFail h := fun _ _ => trivial

/-! ## type==4 check as a `cpsBranchWithin` (`teerB + 168 →`)

    Composes the type load (`teer_type4_load_spec`, instrs 42..45, lifted from
    `teerCode`) with the type-mismatch `BNE` (`teer_type4_bne_spec`, instr 46).
    TAKEN (`type ≠ 4`) → far epilogue `teerB + 2856`; NOT-TAKEN (`type = 4`) →
    `teerB + 188`, the inner-payload cursor setup.  The scratch registers `x5`,
    `x6` arrive OWNED (clobbered by the `tx_type_dispatch` callee), so the
    precondition exposes `regOwn` for them (and `x7`, staged by the load). -/
set_option maxRecDepth 8000 in
theorem teer_type4_branch_spec (v7 tval : Word) :
    cpsBranchWithin 5 (teerB + 168) fullCode
      ((teerType ↦ₘ tval) ** (.x7 ↦ᵣ v7) ** regOwn .x5 ** regOwn .x6)
      (teerB + 2856) teerFail
      (teerB + 188)
      (((.x5 ↦ᵣ teerType) ** (.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) **
         (teerType ↦ₘ tval)) ** ⌜tval = (4 : Word)⌝) := by
  -- The scratch registers `x5`, `x6` arrive OWNED (clobbered by the callee);
  -- the load overwrites them, so their inbound values are irrelevant.
  have concrete : ∀ v5 v6, cpsBranchWithin 5 (teerB + 168) fullCode
      ((teerType ↦ₘ tval) ** (.x7 ↦ᵣ v7) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (teerB + 2856) teerFail
      (teerB + 188)
      (((.x5 ↦ᵣ teerType) ** (.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) **
         (teerType ↦ₘ tval)) ** ⌜tval = (4 : Word)⌝) := by
    intro v5 v6
    have hload := cpsTripleWithin_extend_code teer_mono (teer_type4_load_spec v5 v6 v7 tval)
    have hbneF := cpsBranchWithin_frameR ((.x5 ↦ᵣ teerType) ** (teerType ↦ₘ tval))
      (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
      (teer_type4_bne_spec tval)
    have hb := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by xperm_hyp hp) hload hbneF
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ _ => trivial) (fun h hq => by xperm_hyp hq) hb
  refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_exists_pre (fun v5 => cpsBranchWithin_exists_pre (fun v6 => concrete v5 v6)))
  obtain ⟨h1, h2, hd, hu, hT, h3, h4, hd2, hu2, h7, h5, h6, hd3, hu3, ⟨v5, hx5⟩, ⟨v6, hx6⟩⟩ := hp
  exact ⟨v5, v6, h1, h2, hd, hu, hT, h3, h4, hd2, hu2, h7, h5, h6, hd3, hu3, hx5, hx6⟩

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
