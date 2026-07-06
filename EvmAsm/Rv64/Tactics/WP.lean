/-
  EvmAsm.Rv64.Tactics.WP

  Thin tactic surface for WP/CFG certificates.  The proof search/calculation
  lives in the certificate constructors; this tactic consumes the resulting
  object and closes the corresponding CPS goal.
-/

import Lean
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.WPAttr
import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.Tactics

open Lean Meta Elab Tactic

/-- Close a `cpsTripleWithin` goal with a `WP.Triple`/`WP.CFG.Cert`.

    Example:
    ```
    wp_rv64 myCfg
    ```
    elaborates to `exact myCfg.sound`. -/
syntax (name := wpRv64Tac) "wp_rv64 " term : tactic

macro_rules
  | `(tactic| wp_rv64 $cfg:term) =>
      `(tactic| exact ($cfg).sound)

private def solveMVarWithLocalHyp (mvarId : MVarId) : TacticM Bool := do
  if ← mvarId.isAssigned then
    return true
  let target ← instantiateMVars (← mvarId.getType)
  let mvarDecl ← mvarId.getDecl
  unless mvarDecl.userName.isAnonymous do
    for localDecl in ← getLCtx do
      unless localDecl.isImplementationDetail do
        if localDecl.userName == mvarDecl.userName then
          let localType ← instantiateMVars localDecl.type
          if ← withoutModifyingState (isDefEq localType target) then
            mvarId.assign (mkFVar localDecl.fvarId)
            return true
  unless ← isProp target do
    return false
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let hyp := mkFVar localDecl.fvarId
      let hypType ← instantiateMVars localDecl.type
      if ← withoutModifyingState (isDefEq hypType target) then
        mvarId.assign hyp
        return true
  return false

private def localCandidatesForMVar (mvarId : MVarId) : TacticM (Array Expr) := do
  let target ← instantiateMVars (← mvarId.getType)
  let mvarDecl ← mvarId.getDecl
  let mut named : Array Expr := #[]
  let mut typed : Array Expr := #[]
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let localType ← instantiateMVars localDecl.type
      if ← withoutModifyingState (isDefEq localType target) then
        let localExpr := mkFVar localDecl.fvarId
        typed := typed.push localExpr
        if !mvarDecl.userName.isAnonymous && localDecl.userName == mvarDecl.userName then
          named := named.push localExpr
  if !named.isEmpty then
    return named
  return typed

private def solveMVarByWpParamTactics (mvarId : MVarId) : TacticM Bool := do
  if ← mvarId.isAssigned then
    return true
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    unless ← isProp target do
      return false
    let saved ← saveState
    let originalGoals ← getGoals
    try
      replaceMainGoal [mvarId]
      evalTactic (← `(tactic| first | assumption | omega | bv_omega))
      unless (← getGoals).isEmpty do
        throwError "wp parameter tactic left open goals"
      setGoals originalGoals
      return true
    catch _ =>
      restoreState saved
      return false

partial def solveParamMVarsWithLocals (params : Array Expr) (idx : Nat) : TacticM Bool := do
  if hidx : idx < params.size then
    let param ← instantiateMVars params[idx]
    if param.isMVar then
      let mvarId := param.mvarId!
      if ← mvarId.isAssigned then
        solveParamMVarsWithLocals params (idx + 1)
      else
        let candidates ← localCandidatesForMVar mvarId
        for candidate in candidates do
          let saved ← saveState
          mvarId.assign candidate
          if ← solveParamMVarsWithLocals params (idx + 1) then
            return true
          restoreState saved
        let saved ← saveState
        if ← solveMVarByWpParamTactics mvarId then
          if ← solveParamMVarsWithLocals params (idx + 1) then
            return true
        restoreState saved
        return false
    else
      solveParamMVarsWithLocals params (idx + 1)
  else
    return true

private def closeWithWpHint (goal : MVarId) (declName : Name) : TacticM Unit := do
  let goalType ← instantiateMVars (← goal.getType)
  let hintConst ← mkConstWithFreshMVarLevels declName
  let hintType ← inferType hintConst
  let (params, _, body) ← forallMetaTelescope hintType
  unless ← isDefEq body goalType do
    throwError "hint result does not match goal"
  unless ← solveParamMVarsWithLocals params 0 do
    throwError "hint parameters were not inferable from local context"
  let proof ← instantiateMVars (mkAppN hintConst params)
  if proof.hasExprMVar then
    throwError "hint left unresolved metavariables"
  goal.assign proof
  replaceMainGoal []

private def appendWpHintFailures (errMsg : MessageData)
    (errors : Array (Name × String)) : MessageData :=
  if errors.isEmpty then
    errMsg
  else
    errors.foldl
      (fun errMsg error => errMsg ++ m!"\n    {error.fst}: {error.snd}")
      (errMsg ++ m!"\n  Candidate failures:")

private def collectWpHintFailures (goal : MVarId) (entries : Array Name) :
    TacticM (Array (Name × String)) := do
  let mut errors : Array (Name × String) := #[]
  for declName in entries do
    let saved ← saveState
    try
      closeWithWpHint goal declName
      restoreState saved
    catch e =>
      restoreState saved
      let msg ← e.toMessageData.toString
      errors := errors.push (declName, msg)
  return errors

/-- Close a `WP.Entails` goal using declarations tagged with
    `@[rv64_wp_entails]`.  This is deliberately separate from the `rv64_wp` simp
    set: simp exposes the assertion shape, then this tactic applies named
    semantic bridge lemmas whose statements are not rewrite rules. -/
elab "wp_rv64_entails" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  unless goalType.isAppOfArity ``EvmAsm.Rv64.WP.Entails 2 do
    throwError "wp_rv64_entails: expected WP.Entails goal"
  let entries := rv64WpEntailsExt.getState (← getEnv)
  let mut errors : Array (Name × String) := #[]
  for declName in entries do
    let saved ← saveState
    try
      closeWithWpHint goal declName
      return
    catch e =>
      restoreState saved
      let msg ← e.toMessageData.toString
      errors := errors.push (declName, msg)
      continue
  let goalType ← instantiateMVars (← goal.getType)
  let errMsg := appendWpHintFailures m!"wp_rv64_entails: no @[rv64_wp_entails] theorem closed the goal.
  Tried {entries.size} registered theorem(s).
  Goal: {goalType}" errors
  throwError (errMsg ++ m!"
  Hint: add a small @[rv64_wp_entails] lemma, or expose the assertion shape
  with `simp only [rv64_wp]`.")

/-- Try declarations tagged with `@[rv64_wp_dead]` against the current
    unreachable-exit goal.  Tagged lemmas may have explicit proof arguments;
    generated side goals are discharged from local hypotheses. -/
elab "wp_rv64_dead_hint" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  unless ← isProp goalType do
    throwError "wp_rv64_dead_hint: expected proposition goal"
  let entries := rv64WpDeadExt.getState (← getEnv)
  let mut errors : Array (Name × String) := #[]
  for declName in entries do
    let saved ← saveState
    try
      closeWithWpHint goal declName
      return
    catch eHint =>
      restoreState saved
      let hintMsg ← eHint.toMessageData.toString
      let saved ← saveState
      try
        let hint := mkIdent declName
        evalTactic (← `(tactic| apply $hint:ident <;> assumption))
        unless (← getGoals).isEmpty do
          throwError "hint left open goals"
        return
      catch eApply =>
        restoreState saved
        let applyMsg ← eApply.toMessageData.toString
        errors := errors.push
          (declName, "closeWithWpHint: " ++ hintMsg ++
            "\n      fallback apply: " ++ applyMsg)
        continue
  let goalType ← instantiateMVars (← goal.getType)
  let errMsg := appendWpHintFailures m!"wp_rv64_dead_hint: no @[rv64_wp_dead] theorem closed the goal.
  Tried {entries.size} registered theorem(s).
  Goal: {goalType}" errors
  throwError (errMsg ++ m!"
  Hint: add a contradiction lemma tagged @[rv64_wp_dead], or pass the
  unreachable proof directly to WP.CFG.unreachable.")

/-- Close an unreachable-exit goal, after exposing small WP definitions if
    needed, using declarations tagged with `@[rv64_wp_dead]`. -/
syntax (name := wpRv64DeadTac) "wp_rv64_dead" : tactic

macro_rules
  | `(tactic| wp_rv64_dead) =>
      `(tactic| first
        | wp_rv64_dead_hint
        | simp only [rv64_wp]; wp_rv64_dead_hint
        | try dsimp; wp_rv64_dead_hint
        | try dsimp; simp only [rv64_wp]; wp_rv64_dead_hint)


private def isWpCertLikeGoal (goalType : Expr) : TacticM Bool := do
  let goalType ← whnfR goalType
  return goalType.isAppOfArity ``EvmAsm.Rv64.WP.Triple 4 ||
    goalType.isAppOfArity ``EvmAsm.Rv64.WP.Branch 2 ||
    goalType.isAppOfArity ``EvmAsm.Rv64.WP.NBranch 2

/-- Close a WP certificate goal using declarations tagged with `@[rv64_wp_cert]`.
    The target fixes the program/control-flow shape; remaining proof arguments
    are filled from local hypotheses by name or exact type. -/
elab "wp_rv64_cert" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  unless ← isWpCertLikeGoal goalType do
    throwError "wp_rv64_cert: expected WP.Triple/WP.CFG.Cert, WP.Branch, or WP.NBranch goal"
  let entries := rv64WpCertExt.getState (← getEnv)
  let mut errors : Array (Name × String) := #[]
  for declName in entries do
    let saved ← saveState
    try
      closeWithWpHint goal declName
      return
    catch e =>
      restoreState saved
      let msg ← e.toMessageData.toString
      errors := errors.push (declName, msg)
      continue
  let mut errMsg := m!"wp_rv64_cert: no @[rv64_wp_cert] declaration closed the goal.
  Tried {entries.size} registered declaration(s).
  Goal: {goalType}"
  errMsg := appendWpHintFailures errMsg errors
  errMsg := errMsg ++ m!"
  Hint: try the intended constructor directly once to expose missing static
  facts, or tag a reusable constructor with @[rv64_wp_cert]."
  throwError errMsg

attribute [rv64_wp]
  EvmAsm.Rv64.WP.Triple.refl_pre
  EvmAsm.Rv64.WP.Triple.unreachable_pre
  EvmAsm.Rv64.WP.Triple.ofSpec_pre
  EvmAsm.Rv64.WP.Triple.weakenPre_pre
  EvmAsm.Rv64.WP.Triple.weakenPost_pre
  EvmAsm.Rv64.WP.Triple.monoSteps_pre
  EvmAsm.Rv64.WP.Triple.extendCode_pre
  EvmAsm.Rv64.WP.Triple.frameR_pre
  EvmAsm.Rv64.WP.Triple.changeEntry_pre
  EvmAsm.Rv64.WP.Triple.changeExit_pre
  EvmAsm.Rv64.WP.Triple.seq_pre
  EvmAsm.Rv64.WP.Triple.seqDisjoint_pre
  EvmAsm.Rv64.WP.CFG.exitRefl_pre
  EvmAsm.Rv64.WP.CFG.block_pre
  EvmAsm.Rv64.WP.CFG.leaf_pre
  EvmAsm.Rv64.WP.CFG.frameR_pre
  EvmAsm.Rv64.WP.CFG.weakenPre_pre
  EvmAsm.Rv64.WP.CFG.weakenPost_pre
  EvmAsm.Rv64.WP.CFG.monoSteps_pre
  EvmAsm.Rv64.WP.CFG.extendCode_pre
  EvmAsm.Rv64.WP.CFG.changeEntry_pre
  EvmAsm.Rv64.WP.CFG.changeExit_pre
  EvmAsm.Rv64.WP.Branch.ofSpec_pre
  EvmAsm.Rv64.WP.Branch.ofSpec_exit_t
  EvmAsm.Rv64.WP.Branch.ofSpec_post_t
  EvmAsm.Rv64.WP.Branch.ofSpec_exit_f
  EvmAsm.Rv64.WP.Branch.ofSpec_post_f
  EvmAsm.Rv64.WP.Branch.frameR_pre
  EvmAsm.Rv64.WP.Branch.frameR_exit_t
  EvmAsm.Rv64.WP.Branch.frameR_post_t
  EvmAsm.Rv64.WP.Branch.frameR_exit_f
  EvmAsm.Rv64.WP.Branch.frameR_post_f
  EvmAsm.Rv64.WP.Branch.join_pre
  EvmAsm.Rv64.WP.Branch.seqTakenDisjoint_pre
  EvmAsm.Rv64.WP.Branch.seqNotTakenDisjoint_pre
  EvmAsm.Rv64.WP.Branch.seqTakenBranchConvergeDisjoint_pre

/-- Expose small WP certificate projections before using separation-logic
    permutation or pure-extraction tactics. -/
syntax (name := wpRv64NormTac) "wp_rv64_norm" : tactic
syntax (name := wpRv64NormAtTac) "wp_rv64_norm" " at " ident : tactic

macro_rules
  | `(tactic| wp_rv64_norm) =>
      `(tactic| try dsimp; try simp only [rv64_wp])
  | `(tactic| wp_rv64_norm at $h:ident) =>
      `(tactic| try dsimp at $h:ident; try simp only [rv64_wp] at $h:ident)

/-- Final diagnostic fallback for `wp_rv64_link`.  It runs only after the
    concrete link-closing alternatives have failed, so the message names the
    exact remaining entailment rather than asking the user to rediscover it by
    replaying constructors manually. -/
elab "wp_rv64_link_fail" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let goalTypeWhnf ← whnfR goalType
  unless goalTypeWhnf.isAppOfArity ``EvmAsm.Rv64.WP.Entails 2 do
    throwError m!"wp_rv64_link: expected WP.Entails goal.
  Goal: {goalType}"
  let lhs := goalTypeWhnf.getAppArgs[0]!
  let rhs := goalTypeWhnf.getAppArgs[1]!
  let entries := rv64WpEntailsExt.getState (← getEnv)
  let errors ← collectWpHintFailures goal entries
  let errMsg := appendWpHintFailures m!"wp_rv64_link: could not close the remaining WP.Entails goal.
  Tried reflexivity, local assumptions, Branch/CFG projection rewrites,
  rv64_wp normalization, xperm_pure, and {entries.size} registered
  @[rv64_wp_entails] theorem(s).
  Source: {lhs}
  Target: {rhs}" errors
  throwError (errMsg ++ m!"
  Hint: inspect whether the source and target differ by a missing projection
  rewrite such as WP.CFG.leaf_pre, by a frame permutation that xperm_pure
  cannot see, or by a reusable semantic bridge that should be tagged
  @[rv64_wp_entails].")

/-- Close the midpoint entailment between adjacent WP fragments.  The common
    case is definitional equality of the head postcondition and tail WP; semantic
    bridge lemmas tagged `@[rv64_wp_entails]` handle generated handoff shapes,
    and reordered separation frames fall through to `xperm`. -/
syntax (name := wpRv64LinkTac) "wp_rv64_link" : tactic

macro_rules
  | `(tactic| wp_rv64_link) =>
      `(tactic| solve
        | exact EvmAsm.Rv64.WP.Entails.refl _
        | assumption
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_t, EvmAsm.Rv64.WP.Branch.ofSpec_post_t] at hp; rw [EvmAsm.Rv64.WP.CFG.leaf_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_f, EvmAsm.Rv64.WP.Branch.ofSpec_post_f] at hp; rw [EvmAsm.Rv64.WP.CFG.leaf_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_t, EvmAsm.Rv64.WP.Branch.ofSpec_post_t] at hp; rw [EvmAsm.Rv64.WP.CFG.block_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_f, EvmAsm.Rv64.WP.Branch.ofSpec_post_f] at hp; rw [EvmAsm.Rv64.WP.CFG.block_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_t, EvmAsm.Rv64.WP.Branch.ofSpec_post_t] at hp; rw [EvmAsm.Rv64.WP.CFG.frameR_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_f, EvmAsm.Rv64.WP.Branch.ofSpec_post_f] at hp; rw [EvmAsm.Rv64.WP.CFG.frameR_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_t, EvmAsm.Rv64.WP.Branch.ofSpec_post_t] at hp; rw [EvmAsm.Rv64.WP.CFG.extendCode_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_f, EvmAsm.Rv64.WP.Branch.ofSpec_post_f] at hp; rw [EvmAsm.Rv64.WP.CFG.extendCode_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_t, EvmAsm.Rv64.WP.Branch.ofSpec_post_t] at hp; rw [EvmAsm.Rv64.WP.CFG.weakenPost_pre]; xperm_pure hp
        | intro h hp; rw [EvmAsm.Rv64.WP.Branch.frameR_post_f, EvmAsm.Rv64.WP.Branch.ofSpec_post_f] at hp; rw [EvmAsm.Rv64.WP.CFG.weakenPost_pre]; xperm_pure hp
        | intro h hp; dsimp at hp ⊢; simp only [rv64_wp] at hp ⊢; xperm_pure hp
        | intro h hp; wp_rv64_norm at hp; wp_rv64_norm; xperm_pure hp
        | intro h hp; try dsimp at hp ⊢; try simp only [rv64_wp] at hp ⊢; xperm_pure hp
        | intro h hp; simp only [rv64_wp] at hp ⊢; xperm_pure hp
        | intro h hp; try dsimp at hp ⊢; xperm_pure hp
        | intro h hp; xperm_pure hp
        | wp_rv64_entails
        | wp_rv64_norm; wp_rv64_entails
        | simp only [rv64_wp]; wp_rv64_entails
        | try dsimp; wp_rv64_entails
        | try dsimp; try simp only [rv64_wp]; wp_rv64_entails
        | wp_rv64_link_fail)


private def closeDisjointWithLocal (goal : MVarId) (goalType : Expr) : TacticM Bool := do
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let localType ← instantiateMVars localDecl.type
      if ← withoutModifyingState (isDefEq localType goalType) then
        goal.assign (mkFVar localDecl.fvarId)
        replaceMainGoal []
        return true
  return false

private def closeDisjointWithHint (goal : MVarId) : TacticM Unit := do
  let entries := rv64WpDisjointExt.getState (← getEnv)
  let mut errors : Array (Name × String) := #[]
  for declName in entries do
    let saved ← saveState
    try
      closeWithWpHint goal declName
      return
    catch e =>
      restoreState saved
      let msg ← e.toMessageData.toString
      errors := errors.push (declName, msg)
      continue
  let goalType ← instantiateMVars (← goal.getType)
  let errMsg := appendWpHintFailures m!"wp_rv64_disjoint: no @[rv64_wp_disjoint] theorem closed the goal.
  Tried {entries.size} registered theorem(s).
  Goal: {goalType}" errors
  throwError (errMsg ++ m!"
  Hint: add a local disjointness hypothesis or tag a semantic disjointness
  lemma with @[rv64_wp_disjoint].")

/-- Close a `CodeReq.Disjoint` goal using local hypotheses, declarations
    tagged with `@[rv64_wp_disjoint]`, or the structural prover shared with
    `seqFrame`. This keeps WP composition proofs from spelling out code-range
    side conditions for generated straight-line fragments and semantic code
    ranges. -/
elab "wp_rv64_disjoint" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let goalType ← whnfR goalType
  unless goalType.isAppOfArity ``EvmAsm.Rv64.CodeReq.Disjoint 2 do
    throwError "wp_rv64_disjoint: expected CodeReq.Disjoint goal"
  if ← closeDisjointWithLocal goal goalType then
    return
  let hintEntries := rv64WpDisjointExt.getState (← getEnv)
  let savedHint ← saveState
  try
    closeDisjointWithHint goal
  catch hintError =>
    restoreState savedHint
    let cr1 := goalType.getAppArgs[0]!
    let cr2 := goalType.getAppArgs[1]!
    try
      let proof ← withTransparency .all <| buildDisjointProof cr1 cr2
      (← getMainGoal).assign proof
      replaceMainGoal []
    catch e =>
      let mut errMsg := m!"wp_rv64_disjoint: no local hypothesis, registered hint, or
  structural proof closed the goal.
  Goal: {goalType}
  Hint: add a local disjointness hypothesis, or tag a semantic disjointness
  lemma with @[rv64_wp_disjoint]."
      unless hintEntries.isEmpty do
        let hintMsg ← hintError.toMessageData.toString
        errMsg := errMsg ++ m!"
  Registered hint prover error:
  {hintMsg}"
      errMsg := errMsg ++ m!"
  Structural prover error: {← e.toMessageData.toString}"
      throwError errMsg

/-- Lift a leaf CPS proof whose postcondition already matches the CFG
    postcondition. -/
syntax (name := wpRv64LeafTac) "wp_rv64_leaf " term : tactic

macro_rules
  | `(tactic| wp_rv64_leaf $h:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.leaf $h)

/-- Build a leaf CFG certificate by working backwards from the requested
    postcondition.  With no arguments, `runBlockFromPost` resolves registered
    `@[spec_gen_rv64]` specs from the goal's `CodeReq`; with arguments, a full
    explicit spec list is manual mode and a shorter single-instruction list is
    used as partial hints for otherwise automatic synthesis. -/
syntax (name := wpRv64LeafSynthTac) "wp_rv64_leaf_synth" ident* : tactic

macro_rules
  | `(tactic| wp_rv64_leaf_synth $specs:ident*) =>
      `(tactic| exact @EvmAsm.Rv64.WP.CFG.leaf ?_ _ _ _ ?_ _
        (by runBlockFromPost $specs*))

/-- Build an empty CFG at a join point with identical pre/post assertion. -/
syntax (name := wpRv64ExitReflTac)
  "wp_rv64_exit_refl " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_exit_refl $addr:term, $cr:term, $post:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.exitRefl $addr $cr $post)

/-- Build a CFG certificate from a head CPS proof and tail certificate when the
    head postcondition is definitionally the tail precondition. -/
syntax (name := wpRv64CfgSeqExactTac)
  "wp_rv64_cfg_seq_exact " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_seq_exact $head:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.seqExact $tail $head)

/-- Disjoint-code version of `wp_rv64_cfg_seq_exact`. -/
syntax (name := wpRv64CfgSeqDisjointExactTac)
  "wp_rv64_cfg_seq_disjoint_exact " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_seq_disjoint_exact $hd:term, $head:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.seqDisjointExact $hd $tail $head)

/-- Close a CPS goal from exact head/tail CFG sequencing. -/
syntax (name := wpRv64SeqExactTac) "wp_rv64_seq_exact " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_exact $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.CFG.seqExact $tail $head).sound)

/-- Disjoint-code version of `wp_rv64_seq_exact`. -/
syntax (name := wpRv64SeqDisjointExactTac)
  "wp_rv64_seq_disjoint_exact " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_disjoint_exact $hd:term, $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.CFG.seqDisjointExact $hd $tail $head).sound)

/-- Package a bounded natural-number loop certificate as a CFG certificate. -/
syntax (name := wpRv64LoopNatTac) "wp_rv64_loop_nat " term : tactic

macro_rules
  | `(tactic| wp_rv64_loop_nat $hcert:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.loopNat $hcert)

/-- Close a CPS goal from a bounded natural-number loop certificate. -/
syntax (name := wpRv64LoopNatSoundTac) "wp_rv64_loop_nat_sound " term : tactic

macro_rules
  | `(tactic| wp_rv64_loop_nat_sound $hcert:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.CFG.loopNat $hcert).sound)

/-- Close a CPS goal from two adjacent same-code CPS blocks with exact
    midpoint. -/
syntax (name := wpRv64SeqBlockExactTac)
  "wp_rv64_seq_block_exact " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_block_exact $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.CFG.seqBlockExact $head $tail).sound)

/-- Disjoint-code version of `wp_rv64_seq_block_exact`. -/
syntax (name := wpRv64SeqBlockDisjointExactTac)
  "wp_rv64_seq_block_disjoint_exact " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_block_disjoint_exact $hd:term, $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.CFG.seqBlockDisjointExact $hd $head $tail).sound)

/-- Frame a single-exit CFG certificate and return the framed certificate. -/
syntax (name := wpRv64FrameRTac) "wp_rv64_frame " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_frame $cfg:term, $F:term, $hF:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.frameR $cfg $F $hF)

/-- Weaken a single-exit CFG certificate's computed precondition. -/
syntax (name := wpRv64WeakenPreTac) "wp_rv64_weaken_pre " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_weaken_pre $cfg:term, $hpre:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.weakenPre $cfg $hpre)

/-- Weaken a single-exit CFG certificate to an explicitly supplied
    precondition, synthesizing the entailment with `wp_rv64_link`. -/
syntax (name := wpRv64SetPreTac) "wp_rv64_set_pre " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_set_pre $cfg:term, $pre:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.weakenPre $cfg
        (show EvmAsm.Rv64.WP.Entails $pre ($cfg).pre by wp_rv64_link))

/-- Weaken a single-exit CFG certificate's continuation postcondition. -/
syntax (name := wpRv64WeakenPostTac) "wp_rv64_weaken_post " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_weaken_post $cfg:term, $hpost:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.weakenPost $cfg $hpost)

/-- Weaken a single-exit CFG certificate to an explicitly supplied
    postcondition, synthesizing the entailment with `wp_rv64_link`. -/
syntax (name := wpRv64SetPostTac) "wp_rv64_set_post " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_set_post $cfg:term, $post:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.weakenPost $cfg
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link))

/-- Increase a single-exit CFG certificate's step budget. -/
syntax (name := wpRv64MonoStepsTac) "wp_rv64_mono_steps " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_mono_steps $cfg:term, $hle:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.monoSteps $cfg $hle)

/-- Extend a single-exit CFG certificate to a larger persistent code requirement. -/
syntax (name := wpRv64ExtendCodeTac) "wp_rv64_extend_code " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_extend_code $cfg:term, $hmono:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.extendCode $cfg $hmono)

/-- Extend a single-exit CFG certificate and set an explicit precondition in
    one generated step. -/
syntax (name := wpRv64ExtendSetPreTac)
  "wp_rv64_extend_set_pre " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_extend_set_pre $cfg:term, $hmono:term, $pre:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.weakenPre
        (EvmAsm.Rv64.WP.CFG.extendCode $cfg $hmono)
        (show EvmAsm.Rv64.WP.Entails $pre
          (EvmAsm.Rv64.WP.CFG.extendCode $cfg $hmono).pre by wp_rv64_link))

/-- Rewrite a single-exit CFG certificate's entry address. -/
syntax (name := wpRv64ChangeEntryTac) "wp_rv64_change_entry " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_change_entry $cfg:term, $hentry:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.changeEntry $cfg $hentry)

/-- Rewrite a single-exit CFG certificate's exit address. -/
syntax (name := wpRv64ChangeExitTac) "wp_rv64_change_exit " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_change_exit $cfg:term, $hexit:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.changeExit $cfg $hexit)

/-- Build a certificate for an unreachable precondition. -/
syntax (name := wpRv64UnreachableTac)
  "wp_rv64_unreachable " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_unreachable $entry:term, $exit:term, $cr:term, $hpre:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.unreachable $entry $exit $cr $hpre)

/-- Compose a head CPS triple with a WP/CFG tail and close the midpoint
    entailment with `wp_rv64_link`. -/
syntax (name := wpRv64SeqTac) "wp_rv64_seq " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.Triple.seq $head $tail
        (by wp_rv64_link)).sound)

/-- Disjoint-code version of `wp_rv64_seq`. -/
syntax (name := wpRv64SeqDisjointTac) "wp_rv64_seq_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_disjoint $hd:term, $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.Triple.seqDisjoint $hd $head $tail
        (by wp_rv64_link)).sound)

/-- Build a single-exit CFG certificate by composing a head CPS triple with a
    tail certificate over disjoint code, supplying the midpoint entailment. -/
syntax (name := wpRv64CfgSeqDisjointWithTac)
  "wp_rv64_cfg_seq_disjoint_with " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_seq_disjoint_with $hd:term, $head:term, $tail:term, $hlink:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.seqDisjoint $hd $head $tail $hlink)

/-- Build a single-exit CFG certificate by composing a head CPS triple with a
    tail certificate over disjoint code, synthesizing the midpoint entailment. -/
syntax (name := wpRv64CfgSeqDisjointWithAutoTac)
  "wp_rv64_cfg_seq_disjoint_with_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_seq_disjoint_with_auto $hd:term, $head:term, $tail:term) =>
      `(tactic| wp_rv64_cfg_seq_disjoint_with $hd, $head, $tail, (by wp_rv64_link))

/-- Build a single-exit CFG certificate by composing a head CPS triple with a
    tail certificate over disjoint code, synthesizing disjointness and the
    midpoint entailment. -/
syntax (name := wpRv64CfgSeqDisjointAutoTac)
  "wp_rv64_cfg_seq_disjoint_auto " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_seq_disjoint_auto $head:term, $tail:term) =>
      `(tactic| wp_rv64_cfg_seq_disjoint_with_auto (by wp_rv64_disjoint), $head, $tail)

/-- Build a single-exit CFG certificate by composing a head certificate with a
    tail certificate over disjoint code, supplying the midpoint entailment. -/
syntax (name := wpRv64CfgCertSeqDisjointWithTac)
  "wp_rv64_cfg_cert_seq_disjoint_with " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_cert_seq_disjoint_with $hd:term, $head:term, $tail:term, $hlink:term) =>
      `(tactic| wp_rv64_cfg_seq_disjoint_with $hd, ($head).sound, $tail, $hlink)

/-- Build a single-exit CFG certificate by composing a head certificate with a
    tail certificate over disjoint code, synthesizing the midpoint entailment. -/
syntax (name := wpRv64CfgCertSeqDisjointWithAutoTac)
  "wp_rv64_cfg_cert_seq_disjoint_with_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_cert_seq_disjoint_with_auto $hd:term, $head:term, $tail:term) =>
      `(tactic| wp_rv64_cfg_seq_disjoint_with_auto $hd, ($head).sound, $tail)

/-- Build a single-exit CFG certificate by composing a head certificate with a
    tail certificate over disjoint code, synthesizing disjointness and the
    midpoint entailment. -/
syntax (name := wpRv64CfgCertSeqDisjointAutoTac)
  "wp_rv64_cfg_cert_seq_disjoint_auto " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_cfg_cert_seq_disjoint_auto $head:term, $tail:term) =>
      `(tactic| wp_rv64_cfg_seq_disjoint_auto ($head).sound, $tail)

/-- Compose two adjacent CPS blocks over one shared persistent code requirement. -/
syntax (name := wpRv64SeqBlockTac) "wp_rv64_seq_block " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_block $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.CFG.seqBlock $head $tail
        (by wp_rv64_link)).sound)

/-- Disjoint-code version of `wp_rv64_seq_block`. -/
syntax (name := wpRv64SeqBlockDisjointTac)
  "wp_rv64_seq_block_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_block_disjoint $hd:term, $head:term, $tail:term) =>
      `(tactic| exact (EvmAsm.Rv64.WP.CFG.seqBlockDisjoint $hd $head $tail
        (by wp_rv64_link)).sound)

/-- Compose a CPS block with an N-way CFG over disjoint code. -/
syntax (name := wpRv64SeqBlockNBranchDisjointTac)
  "wp_rv64_seq_block_nbranch_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_block_nbranch_disjoint $hd:term, $head:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.seqBlockNBranchDisjoint $hd $head $tail
        (by wp_rv64_link))

/-- Frame a single-exit head block and an N-way tail, then compose them over
    disjoint code. This is the common WP handoff shape for generated assembly:
    caller resources are framed across the head block, callee-save resources are
    framed across every tail exit, and the midpoint entailment is solved by the
    WP link automation. -/
syntax (name := wpRv64SeqBlockNBranchFramedDisjointTac)
  "wp_rv64_seq_block_nbranch_framed_disjoint " term ", " term ", " term ", " term
    ", " term ", " term ", " term : tactic

/-- Explicit-link variant of `wp_rv64_seq_block_nbranch_framed_disjoint`.
    Use this when the generated tail precondition needs a local normalization
    step before `wp_rv64_link` can see the assertion atoms. -/
syntax (name := wpRv64SeqBlockNBranchFramedDisjointWithTac)
  "wp_rv64_seq_block_nbranch_framed_disjoint_with " term ", " term ", " term ", " term
    ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_block_nbranch_framed_disjoint_with $hd:term, $head:term,
        $headFrame:term, $hHeadFrame:term, $tail:term, $tailFrame:term,
        $hTailFrame:term, $hlink:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.seqBlockNBranchDisjoint $hd
        (EvmAsm.Rv64.WP.CFG.frameR $head $headFrame $hHeadFrame).sound
        (EvmAsm.Rv64.WP.CFG.nbranchFrameR $tail $tailFrame $hTailFrame)
        $hlink)

macro_rules
  | `(tactic| wp_rv64_seq_block_nbranch_framed_disjoint $hd:term, $head:term,
        $headFrame:term, $hHeadFrame:term, $tail:term, $tailFrame:term,
        $hTailFrame:term) =>
      `(tactic| wp_rv64_seq_block_nbranch_framed_disjoint_with $hd, $head,
        $headFrame, $hHeadFrame, $tail, $tailFrame, $hTailFrame,
        (by
          dsimp only [EvmAsm.Rv64.WP.CFG.frameR, EvmAsm.Rv64.WP.CFG.nbranchFrameR,
            EvmAsm.Rv64.WP.Triple.frameR, EvmAsm.Rv64.WP.NBranch.frameR]
          wp_rv64_link))

/-- Same as `wp_rv64_seq_block_nbranch_framed_disjoint`, with the code
    disjointness side condition discharged by `wp_rv64_disjoint`. -/
syntax (name := wpRv64SeqBlockNBranchFramedAutoTac)
  "wp_rv64_seq_block_nbranch_framed_auto " term ", " term ", " term ", " term
    ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_seq_block_nbranch_framed_auto $head:term, $headFrame:term,
        $hHeadFrame:term, $tail:term, $tailFrame:term, $hTailFrame:term) =>
      `(tactic| wp_rv64_seq_block_nbranch_framed_disjoint
        (by wp_rv64_disjoint), $head, $headFrame, $hHeadFrame, $tail, $tailFrame,
        $hTailFrame)

/-- Continue a branch's taken exit with a WP/CFG tail over disjoint code. -/
syntax (name := wpRv64BranchSeqTakenDisjointTac)
  "wp_rv64_branch_taken_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_branch_taken_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.branchSeqTakenDisjoint $hd $br $tail
        (by wp_rv64_link))

/-- Continue a branch's taken exit with a CPS leaf over disjoint code. -/
syntax (name := wpRv64BranchSeqTakenBlockDisjointTac)
  "wp_rv64_branch_taken_block_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_branch_taken_block_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.branchSeqTakenBlockDisjoint $hd $br $tail
        (by wp_rv64_link))

/-- Continue a branch taken exit with another branch, merging both failure exits
    into the explicit shared failure post. The exit equality is expected to be
    definitional. -/
syntax (name := wpRv64BranchSeqTakenBranchConvergeDisjointTac)
  "wp_rv64_branch_taken_branch_converge_disjoint " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_branch_taken_branch_converge_disjoint $hd:term, $br:term, $tail:term, $failPost:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.branchSeqTakenBranchConvergeDisjoint
        (failPost := $failPost) $hd $br $tail (by rfl)
        (by wp_rv64_link) (by wp_rv64_link) (by wp_rv64_link))

syntax (name := wpRv64BranchSeqNotTakenDisjointTac)
  "wp_rv64_branch_not_taken_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_branch_not_taken_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.branchSeqNotTakenDisjoint $hd $br $tail
        (by wp_rv64_link))

/-- Continue a branch's not-taken exit with a CPS leaf over disjoint code. -/
syntax (name := wpRv64BranchSeqNotTakenBlockDisjointTac)
  "wp_rv64_branch_not_taken_block_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_branch_not_taken_block_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.branchSeqNotTakenBlockDisjoint $hd $br $tail
        (by wp_rv64_link))

/-- Continue a branch's taken exit with a CPS leaf over disjoint code and expose
    the resulting branch as an N-way branch. -/
syntax (name := wpRv64BranchSeqTakenBlockNBranchDisjointTac)
  "wp_rv64_branch_taken_block_nbranch_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_branch_taken_block_nbranch_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.branchSeqTakenBlockNBranchDisjoint $hd $br $tail
        (by wp_rv64_link))

/-- Continue a branch's not-taken exit with an N-way branch over disjoint code. -/
syntax (name := wpRv64BranchSeqNotTakenNBranchDisjointTac)
  "wp_rv64_branch_not_taken_nbranch_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_branch_not_taken_nbranch_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.branchSeqNotTakenNBranchDisjoint $hd $br $tail
        (by wp_rv64_link))

/-- Continue the head exit of an N-way branch with a CPS leaf over disjoint code.
    The tactic expects the N-branch exits field to reduce to a cons. -/
syntax (name := wpRv64NBranchSeqHeadBlockDisjointTac)
  "wp_rv64_nbranch_head_block_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_head_block_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqHeadBlockDisjoint $hd $br (by rfl) $tail
        (by wp_rv64_link))

/-- Continue the head exit of an N-way branch with another N-way branch over
    disjoint code. The tactic expects the N-branch exits field to reduce to a cons. -/
syntax (name := wpRv64NBranchSeqHeadNBranchDisjointTac)
  "wp_rv64_nbranch_head_nbranch_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_head_nbranch_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqHeadNBranchDisjoint $hd $br (by rfl) $tail
        (by wp_rv64_link))

/-- Continue an arbitrary exit with another N-way branch over disjoint code.
    The preExits argument is the list of exits to preserve before the selected exit. -/
syntax (name := wpRv64NBranchSeqExitNBranchDisjointTac)
  "wp_rv64_nbranch_exit_nbranch_disjoint " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_exit_nbranch_disjoint $hd:term, $br:term, $preExits:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqExitNBranchDisjoint
        (preExits := $preExits) $hd $br (by rfl) $tail (by wp_rv64_link))

/-- Continue an arbitrary exit with a single-exit CFG certificate over disjoint
    code. The preExits argument is the list of exits to preserve before the
    selected exit, and the exits field is expected to reduce definitionally. -/
syntax (name := wpRv64NBranchSeqExitCertDisjointTac)
  "wp_rv64_nbranch_exit_cert_disjoint " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_exit_cert_disjoint $hd:term, $br:term, $preExits:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqExitCertDisjoint
        (preExits := $preExits) $hd $br (by rfl) $tail (by wp_rv64_link))

/-- Continue an arbitrary exit with a single-exit CFG certificate, supplying the
    generated exit-list proof and link entailment explicitly. This is the useful
    endpoint for proof-producing code that normalizes exits with a local lemma. -/
syntax (name := wpRv64NBranchSeqExitCertDisjointWithTac)
  "wp_rv64_nbranch_exit_cert_disjoint_with " term ", " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_exit_cert_disjoint_with $hd:term, $br:term, $preExits:term, $hexits:term, $tail:term, $hlink:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqExitCertDisjoint
        (preExits := $preExits) $hd $br $hexits $tail $hlink)

/-- Preserve the first exit and continue the second exit with another N-way branch
    over disjoint code. The tactic expects the exits field to reduce to a two-cons prefix. -/
syntax (name := wpRv64NBranchSeqSecondNBranchDisjointTac)
  "wp_rv64_nbranch_second_nbranch_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_second_nbranch_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqSecondNBranchDisjoint $hd $br (by rfl) $tail
        (by wp_rv64_link))

/-- Continue the third exit of a four-way N-branch with a single-exit CFG over
    disjoint tail code. The exit-list proof is expected to be definitional. -/
syntax (name := wpRv64NBranchSeqThirdCertDisjointTac)
  "wp_rv64_nbranch_third_cert_disjoint " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_third_cert_disjoint $hd:term, $br:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqThirdCertDisjoint $hd $br (by rfl) $tail
        (by wp_rv64_link))

/-- Continue the third exit of a four-way N-branch with a single-exit CFG,
    supplying the normalized exit-list proof and link entailment explicitly. -/
syntax (name := wpRv64NBranchSeqThirdCertDisjointWithTac)
  "wp_rv64_nbranch_third_cert_disjoint_with " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_third_cert_disjoint_with $hd:term, $br:term, $hexits:term, $tail:term, $hlink:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqThirdCertDisjoint $hd $br $hexits $tail $hlink)

/-- Continue the third exit of a four-way N-branch with a single-exit CFG,
    supplying the normalized exit-list proof and synthesizing the midpoint
    entailment with `wp_rv64_link`. -/
syntax (name := wpRv64NBranchSeqThirdCertDisjointWithAutoTac)
  "wp_rv64_nbranch_third_cert_disjoint_with_auto " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_third_cert_disjoint_with_auto $hd:term, $br:term, $hexits:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqThirdCertDisjoint $hd $br $hexits $tail
        (by wp_rv64_link))

/-- Continue the third exit of a four-way N-branch with a single-exit CFG,
    synthesizing both the code disjointness side condition and midpoint
    entailment. -/
syntax (name := wpRv64NBranchSeqThirdCertAutoTac)
  "wp_rv64_nbranch_third_cert_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_third_cert_auto $br:term, $hexits:term, $tail:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchSeqThirdCertDisjoint
        (by wp_rv64_disjoint) $br $hexits $tail (by wp_rv64_link))

/-- Frame every exit of an N-way branch with a PC-free assertion. -/
syntax (name := wpRv64NBranchFrameRTac)
  "wp_rv64_nbranch_frame " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_frame $br:term, $F:term, $hF:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchFrameR $br $F $hF)

/-- Extend an N-way branch to a larger persistent code requirement. -/
syntax (name := wpRv64NBranchExtendCodeTac)
  "wp_rv64_nbranch_extend_code " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_extend_code $br:term, $hmono:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.NBranch.extendCode $br $hmono)

/-- Weaken an N-way branch precondition, solving the entailment with `wp_rv64_link`. -/
syntax (name := wpRv64NBranchWeakenPreTac)
  "wp_rv64_nbranch_weaken_pre " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_pre $br:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.NBranch.weakenPre $br (by wp_rv64_link))

/-- Weaken an N-way branch precondition with an explicit entailment proof. -/
syntax (name := wpRv64NBranchWeakenPreWithTac)
  "wp_rv64_nbranch_weaken_pre_with " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_pre_with $br:term, $hpre:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.NBranch.weakenPre $br $hpre)

/-- Weaken an N-way branch to an explicitly supplied precondition, solving the
    entailment through the WP link automation.  Supplying the precondition is
    important because `WP.NBranch` stores `pre` as a field rather than an index,
    so the surrounding result type does not determine it. -/
syntax (name := wpRv64NBranchSetPreTac)
  "wp_rv64_nbranch_set_pre " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_set_pre $br:term, $pre:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.NBranch.weakenPre $br
        (show EvmAsm.Rv64.WP.Entails $pre ($br).pre by wp_rv64_link))

/-- Frame every exit of an N-way branch and set an explicit precondition in one
    generated step.  This is the common shape when a caller frame is preserved
    across every branch exit, but the source precondition is more structured
    than the raw framed WP precondition. -/
syntax (name := wpRv64NBranchFrameSetPreTac)
  "wp_rv64_nbranch_frame_set_pre " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_frame_set_pre $br:term, $frame:term, $hFrame:term, $pre:term) =>
      `(tactic|
        exact EvmAsm.Rv64.WP.NBranch.weakenPre
          (EvmAsm.Rv64.WP.CFG.nbranchFrameR $br $frame $hFrame)
          (show EvmAsm.Rv64.WP.Entails $pre
            (EvmAsm.Rv64.WP.CFG.nbranchFrameR $br $frame $hFrame).pre by
            dsimp only [EvmAsm.Rv64.WP.CFG.nbranchFrameR, EvmAsm.Rv64.WP.NBranch.frameR]
            wp_rv64_link))

/-- Extend an N-way branch to a larger code requirement and set an explicit
    precondition in one generated step. -/
syntax (name := wpRv64NBranchExtendSetPreTac)
  "wp_rv64_nbranch_extend_set_pre " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_extend_set_pre $br:term, $hmono:term, $pre:term) =>
      `(tactic|
        exact EvmAsm.Rv64.WP.NBranch.weakenPre
          (EvmAsm.Rv64.WP.NBranch.extendCode $br $hmono)
          (show EvmAsm.Rv64.WP.Entails $pre
            (EvmAsm.Rv64.WP.NBranch.extendCode $br $hmono).pre by wp_rv64_link))

/-- Weaken the exit postconditions of an N-way branch. -/
syntax (name := wpRv64NBranchWeakenPostsTac)
  "wp_rv64_nbranch_weaken_posts " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts $br:term, $exits:term, $hmap:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts $br $exits $hmap)

/-- Weaken the head exit of an N-way branch. The tactic expects the exits field
    to reduce to a cons. -/
syntax (name := wpRv64NBranchWeakenHeadPostTac)
  "wp_rv64_nbranch_weaken_head " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_head $br:term, $hpost:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenHeadPost $br (by rfl) $hpost)

/-- Weaken exactly two known exits of an N-way branch. The exits field is
    expected to reduce definitionally to the two-exit list. -/
syntax (name := wpRv64NBranchWeakenPosts2Tac)
  "wp_rv64_nbranch_weaken_posts2 " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts2 $br:term, $h1:term, $h2:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts2 $br (by rfl) $h1 $h2)

/-- Weaken exactly two known exits, synthesizing the per-exit entailments with
    `wp_rv64_link`.  The supplied terms are the replacement postconditions. -/
syntax (name := wpRv64NBranchWeakenPosts2AutoTac)
  "wp_rv64_nbranch_weaken_posts2_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts2_auto $br:term, $p1:term, $p2:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts2 $br (by rfl)
        (show EvmAsm.Rv64.WP.Entails _ $p1 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p2 by wp_rv64_link))

/-- Weaken exactly three known exits of an N-way branch. The exits field is
    expected to reduce definitionally to the three-exit list. -/
syntax (name := wpRv64NBranchWeakenPosts3Tac)
  "wp_rv64_nbranch_weaken_posts3 " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts3 $br:term, $h1:term, $h2:term, $h3:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts3 $br (by rfl) $h1 $h2 $h3)

/-- Weaken exactly three known exits, synthesizing the per-exit entailments with
    `wp_rv64_link`.  The supplied terms are the replacement postconditions. -/
syntax (name := wpRv64NBranchWeakenPosts3AutoTac)
  "wp_rv64_nbranch_weaken_posts3_auto " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts3_auto $br:term, $p1:term, $p2:term, $p3:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts3 $br (by rfl)
        (show EvmAsm.Rv64.WP.Entails _ $p1 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p2 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p3 by wp_rv64_link))

/-- Weaken exactly four known exits of an N-way branch. The exits field is
    expected to reduce definitionally to the four-exit list. -/
syntax (name := wpRv64NBranchWeakenPosts4Tac)
  "wp_rv64_nbranch_weaken_posts4 " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts4 $br:term, $h1:term, $h2:term, $h3:term, $h4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4 $br (by rfl) $h1 $h2 $h3 $h4)

/-- Weaken exactly four known exits, synthesizing the per-exit entailments with
    `wp_rv64_link`.  The supplied terms are the replacement postconditions. -/
syntax (name := wpRv64NBranchWeakenPosts4AutoTac)
  "wp_rv64_nbranch_weaken_posts4_auto " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts4_auto $br:term, $p1:term, $p2:term, $p3:term, $p4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4 $br (by rfl)
        (show EvmAsm.Rv64.WP.Entails _ $p1 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p2 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p3 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p4 by wp_rv64_link))

/-- Weaken exactly four known exits of an N-way branch, supplying the generated
    exit-list proof explicitly. -/
syntax (name := wpRv64NBranchWeakenPosts4WithTac)
  "wp_rv64_nbranch_weaken_posts4_with " term ", " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts4_with $br:term, $hexits:term, $h1:term, $h2:term, $h3:term, $h4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4 $br $hexits $h1 $h2 $h3 $h4)

/-- Weaken exactly four known exits with an explicit exit-list proof,
    synthesizing the per-exit entailments with `wp_rv64_link`. -/
syntax (name := wpRv64NBranchWeakenPosts4WithAutoTac)
  "wp_rv64_nbranch_weaken_posts4_with_auto " term ", " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts4_with_auto $br:term, $hexits:term, $p1:term, $p2:term, $p3:term, $p4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4 $br $hexits
        (show EvmAsm.Rv64.WP.Entails _ $p1 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p2 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p3 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p4 by wp_rv64_link))

/-- Weaken four known exits into three by merging the first two same-target
    exits, synthesizing the per-exit entailments with `wp_rv64_link`. -/
syntax (name := wpRv64NBranchWeakenPosts4MergeFirstTwoWithAutoTac)
  "wp_rv64_nbranch_weaken_posts4_merge_first_two_with_auto " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts4_merge_first_two_with_auto $br:term, $hexits:term, $p12:term, $p3:term, $p4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4MergeFirstTwo $br $hexits
        (show EvmAsm.Rv64.WP.Entails _ $p12 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p12 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p3 by wp_rv64_link)
        (show EvmAsm.Rv64.WP.Entails _ $p4 by wp_rv64_link))

/-- Join exactly two known exits when the first exit is the only reachable one. -/
syntax (name := wpRv64NBranchJoin2ResolveFirstTac)
  "wp_rv64_nbranch_join2_resolve_first " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join2_resolve_first $br:term, $hexits:term, $hlink1:term, $hdead2:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin2ResolveFirst $br $hexits $hlink1 $hdead2)

/-- Join exactly two known exits when the first exit is the only reachable one,
    synthesizing the reachable-exit entailment with `wp_rv64_link`. -/
syntax (name := wpRv64NBranchJoin2ResolveFirstAutoTac)
  "wp_rv64_nbranch_join2_resolve_first_auto " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join2_resolve_first_auto $br:term, $hexits:term, $post:term, $hdead2:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin2ResolveFirst $br $hexits
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link) $hdead2)

/-- Join two known exits when the first exit is reachable, synthesizing both
    the reachable-exit entailment and dead second exit. -/
syntax (name := wpRv64NBranchJoin2ResolveFirstDeadAutoTac)
  "wp_rv64_nbranch_join2_resolve_first_dead_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join2_resolve_first_dead_auto $br:term, $hexits:term, $post:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin2ResolveFirst $br $hexits
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link)
        (by wp_rv64_dead))

/-- Join exactly two known exits when the second exit is the only reachable one. -/
syntax (name := wpRv64NBranchJoin2ResolveSecondTac)
  "wp_rv64_nbranch_join2_resolve_second " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join2_resolve_second $br:term, $hexits:term, $hdead1:term, $hlink2:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin2ResolveSecond $br $hexits $hdead1 $hlink2)

/-- Join exactly two known exits when the second exit is the only reachable one,
    synthesizing the reachable-exit entailment with `wp_rv64_link`. -/
syntax (name := wpRv64NBranchJoin2ResolveSecondAutoTac)
  "wp_rv64_nbranch_join2_resolve_second_auto " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join2_resolve_second_auto $br:term, $hexits:term, $hdead1:term, $post:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin2ResolveSecond $br $hexits $hdead1
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link))

/-- Join two known exits when the second exit is reachable, synthesizing both
    the dead first exit and reachable-exit entailment. -/
syntax (name := wpRv64NBranchJoin2ResolveSecondDeadAutoTac)
  "wp_rv64_nbranch_join2_resolve_second_dead_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join2_resolve_second_dead_auto $br:term, $hexits:term, $post:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin2ResolveSecond $br $hexits
        (by wp_rv64_dead)
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link))

/-- Join exactly three known exits when the second exit is the only reachable one. -/
syntax (name := wpRv64NBranchJoin3ResolveSecondTac)
  "wp_rv64_nbranch_join3_resolve_second " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join3_resolve_second $br:term, $hexits:term, $hdead1:term, $hlink2:term, $hdead3:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin3ResolveSecond $br $hexits $hdead1 $hlink2 $hdead3)

/-- Join exactly three known exits when the second exit is the only reachable one,
    synthesizing the reachable-exit entailment with `wp_rv64_link`. -/
syntax (name := wpRv64NBranchJoin3ResolveSecondAutoTac)
  "wp_rv64_nbranch_join3_resolve_second_auto " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join3_resolve_second_auto $br:term, $hexits:term, $hdead1:term, $post:term, $hdead3:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin3ResolveSecond $br $hexits $hdead1
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link) $hdead3)

/-- Join three known exits when the second exit is reachable, synthesizing the
    dead outer exits and reachable-exit entailment. -/
syntax (name := wpRv64NBranchJoin3ResolveSecondDeadAutoTac)
  "wp_rv64_nbranch_join3_resolve_second_dead_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join3_resolve_second_dead_auto $br:term, $hexits:term, $post:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin3ResolveSecond $br $hexits
        (by wp_rv64_dead)
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link)
        (by wp_rv64_dead))

/-- Join exactly four known exits of an N-way branch, supplying the generated
    exit-list proof and one continuation per exit. -/
syntax (name := wpRv64NBranchJoin4WithTac)
  "wp_rv64_nbranch_join4_with " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join4_with $br:term, $hexits:term, $tailBound:term, $t1:term, $hlink1:term, $h1:term, $t2:term, $hlink2:term, $h2:term, $t3:term, $hlink3:term, $h3:term, $t4:term, $hlink4:term, $h4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin4 $br $hexits $tailBound
        $t1 $t2 $t3 $t4 $hlink1 $hlink2 $hlink3 $hlink4 $h1 $h2 $h3 $h4)

/-- Join exactly four known exits, computing the common continuation bound from
    the supplied certificates. -/
syntax (name := wpRv64NBranchJoin4MaxTac)
  "wp_rv64_nbranch_join4 " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join4 $br:term, $hexits:term, $t1:term, $hlink1:term, $t2:term, $hlink2:term, $t3:term, $hlink3:term, $t4:term, $hlink4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin4Max $br $hexits
        $t1 $t2 $t3 $t4 $hlink1 $hlink2 $hlink3 $hlink4)

/-- Join exactly four known exits when the third exit is the only reachable one.
    The other exits are discharged from contradiction proofs. -/
syntax (name := wpRv64NBranchJoin4ResolveThirdTac)
  "wp_rv64_nbranch_join4_resolve_third " term ", " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join4_resolve_third $br:term, $hexits:term, $hdead1:term, $hdead2:term, $hlink3:term, $hdead4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin4ResolveThird $br $hexits
        $hdead1 $hdead2 $hlink3 $hdead4)

/-- Join four known exits when the third exit is reachable, synthesizing the
    dead surrounding exits and reachable-exit entailment. -/
syntax (name := wpRv64NBranchJoin4ResolveThirdDeadAutoTac)
  "wp_rv64_nbranch_join4_resolve_third_dead_auto " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_join4_resolve_third_dead_auto $br:term, $hexits:term, $post:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchJoin4ResolveThird $br $hexits
        (by wp_rv64_dead) (by wp_rv64_dead)
        (show EvmAsm.Rv64.WP.Entails _ $post by wp_rv64_link)
        (by wp_rv64_dead))

/-- Display the computed precondition field of a WP/CFG certificate. -/
syntax (name := wpRv64Cmd) "#wp_rv64 " term : command

macro_rules
  | `(#wp_rv64 $cfg:term) =>
      `(#check ($cfg).pre)

end EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64.Tactics.WPTests

open EvmAsm.Rv64

example {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.Triple entry exit_ cr post) :
    cpsTripleWithin cfg.nSteps entry exit_ cr cfg.pre post := by
  wp_rv64 cfg

example {entry exit_ : Word} {cr : CodeReq} {post F : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post) (hF : F.pcFree) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr (post ** F) := by
  wp_rv64_frame cfg, F, hF

example {entry exit_ : Word} {cr : CodeReq} {pre post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post)
    (hpre : EvmAsm.Rv64.WP.Entails pre cfg.pre) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_weaken_pre cfg, hpre

example {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_set_pre cfg, cfg.pre

example {entry exit_ : Word} {cr : CodeReq} {post post' : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post)
    (hpost : EvmAsm.Rv64.WP.Entails post post') :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post' := by
  wp_rv64_weaken_post cfg, hpost

example {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_set_post cfg, post

example {entry exit_ : Word} {cr : CodeReq} {post : Assertion} {nSteps' : Nat}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post)
    (hle : cfg.nSteps ≤ nSteps') :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_mono_steps cfg, hle

example {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr' post := by
  wp_rv64_extend_code cfg, hmono

example {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr' post := by
  wp_rv64_extend_set_pre cfg, hmono, cfg.pre

example {entry entry' exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post)
    (hentry : entry' = entry) :
    EvmAsm.Rv64.WP.CFG.Cert entry' exit_ cr post := by
  wp_rv64_change_entry cfg, hentry

example {entry exit_ exit_' : Word} {cr : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post)
    (hexit : exit_ = exit_') :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_' cr post := by
  wp_rv64_change_exit cfg, hexit

example {entry exit_ : Word} {cr : CodeReq} {pre post : Assertion}
    (hpre : ∀ h, pre h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_unreachable entry, exit_, cr, hpre

example {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq} {pre post : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_leaf h

def wp_rv64_leaf_synth_li_cfg (base imm : Word) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.LI .x5 imm))
      (.x5 ↦ᵣ imm) := by
  wp_rv64_leaf_synth

example (base imm : Word) :
    (wp_rv64_leaf_synth_li_cfg base imm).pre = regOwn .x5 := rfl

/--
error: runBlockFromPost: no spec could be instantiated backwards for `EvmAsm.Rv64.Instr.LI` at base.
  Tried 2 candidate(s):
    EvmAsm.Rv64.li_spec_gen_within: runBlockFromPost: could not match postcondition atom while resolving EvmAsm.Rv64.li_spec_gen_within:
  EvmAsm.Rv64.Reg.x5 ↦ᵣ imm
    EvmAsm.Rv64.li_spec_gen_own_within: runBlockFromPost: could not match postcondition atom while resolving EvmAsm.Rv64.li_spec_gen_own_within:
  EvmAsm.Rv64.Reg.x5 ↦ᵣ imm
  Hint: strengthen the requested postcondition with the atoms produced by this instruction,
    use an ownership-style spec for overwritten resources, or pass explicit spec hypotheses.
  Progress: resolved 0 of 1 bounded instruction spec(s) backwards before failure.
---
error: unsolved goals
base imm : Word
⊢ WP.CFG.Cert base (base + 4) (CodeReq.singleton base (Instr.LI Reg.x5 imm)) (Reg.x6 ↦ᵣ imm)
-/
#guard_msgs in
example {base imm : Word} :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.LI .x5 imm))
      (.x6 ↦ᵣ imm) := by
  wp_rv64_leaf_synth

def wp_rv64_leaf_synth_addi_manual_cfg (base v : Word) (imm : BitVec 12) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.ADDI .x5 .x5 imm))
      (.x5 ↦ᵣ (v + signExtend12 imm)) := by
  let hAddi := addi_spec_same_within .x5 v imm base (by decide)
  wp_rv64_leaf_synth hAddi

example (base v : Word) (imm : BitVec 12) :
    (wp_rv64_leaf_synth_addi_manual_cfg base v imm).pre = (.x5 ↦ᵣ v) := rfl

def wp_rv64_leaf_synth_partial_hint_cfg (base v : Word) (imm : BitVec 12) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 8)
      (CodeReq.ofProg base [(.LI .x5 v), (.ADDI .x5 .x5 imm)])
      (.x5 ↦ᵣ (v + signExtend12 imm)) := by
  let hAddi := addi_spec_same_within .x5 v imm (base + 4) (by decide)
  wp_rv64_leaf_synth hAddi

example (base v : Word) (imm : BitVec 12) :
    (wp_rv64_leaf_synth_partial_hint_cfg base v imm).pre = regOwn .x5 := rfl

def wp_rv64_leaf_synth_addi_own_cfg (base v : Word) (imm : BitVec 12) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.ADDI .x6 .x5 imm))
      ((.x5 ↦ᵣ v) ** (.x6 ↦ᵣ (v + signExtend12 imm))) := by
  wp_rv64_leaf_synth

example (base v : Word) (imm : BitVec 12) :
    (wp_rv64_leaf_synth_addi_own_cfg base v imm).pre =
      ((.x5 ↦ᵣ v) ** regOwn .x6) := rfl

/--
trace: [runBlock.leafSynth] synthesized regOwn Reg.x6 for old-value parameter of type Word
[runBlock.leafSynth] matched EvmAsm.Rv64.addi_spec_gen_within for EvmAsm.Rv64.Instr.ADDI at base
[runBlock.leafSynth] synthesized predecessor assertion:
      (Reg.x5 ↦ᵣ v) ** regOwn Reg.x6
-/
#guard_msgs in
set_option trace.runBlock.leafSynth true in
example (base v : Word) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.ADDI .x6 .x5 (1 : BitVec 12)))
      ((.x5 ↦ᵣ v) ** (.x6 ↦ᵣ (v + signExtend12 (1 : BitVec 12)))) := by
  wp_rv64_leaf_synth

def wp_rv64_leaf_synth_add_own_cfg (base v1 v2 : Word) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.ADD .x7 .x5 .x6))
      ((.x5 ↦ᵣ v1) ** (.x6 ↦ᵣ v2) ** (.x7 ↦ᵣ (v1 + v2))) := by
  wp_rv64_leaf_synth

example (base v1 v2 : Word) :
    (wp_rv64_leaf_synth_add_own_cfg base v1 v2).pre =
      ((.x5 ↦ᵣ v1) ** (.x6 ↦ᵣ v2) ** regOwn .x7) := rfl

def wp_rv64_leaf_synth_sd_own_cfg (base addr data : Word) (offset : BitVec 12) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.SD .x5 .x6 offset))
      ((.x5 ↦ᵣ addr) ** (.x6 ↦ᵣ data) **
        ((addr + signExtend12 offset) ↦ₘ data)) := by
  wp_rv64_leaf_synth

example (base addr data : Word) (offset : BitVec 12) :
    (wp_rv64_leaf_synth_sd_own_cfg base addr data offset).pre =
      ((.x5 ↦ᵣ addr) ** (.x6 ↦ᵣ data) **
        memOwn (addr + signExtend12 offset)) := rfl

/-- `SLTIU rd, rs1, 1` is a zero classifier: the RISC-V unsigned-less-than result
against `1` agrees with a plain `v = 0` test on `Word`. -/
theorem sltiu_one_zero_classifier (v : Word) :
    (if BitVec.ult v (signExtend12 (1 : BitVec 12)) then (1 : Word) else (0 : Word)) =
      (if v = 0 then (1 : Word) else (0 : Word)) := by
  simp only [signExtend12_1]
  by_cases h : v = 0
  · simp [h]
  · have hne : v.toNat ≠ 0 := fun hc => h (BitVec.eq_of_toNat_eq (by simpa using hc))
    simpa [BitVec.ult_iff_toNat_lt, hne, Nat.lt_one_iff] using h

-- `SLTIU x6, x5, 1` is a zero classifier: `x6 := 1` iff `x5 <ᵘ 1`, i.e. iff `x5 = 0`.
def wp_rv64_leaf_synth_sltiu_zero_cfg (base v : Word) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 4)
      (CodeReq.singleton base (.SLTIU .x6 .x5 (1 : BitVec 12)))
      ((.x5 ↦ᵣ v) **
        (.x6 ↦ᵣ (if BitVec.ult v (signExtend12 (1 : BitVec 12)) then (1 : Word) else (0 : Word)))) := by
  wp_rv64_leaf_synth

example (base v : Word) :
    (wp_rv64_leaf_synth_sltiu_zero_cfg base v).pre =
      ((.x5 ↦ᵣ v) ** regOwn .x6) := rfl

-- `LI x5, imm; SLTIU x6, x5, 1` loads an arbitrary word into `x5`, then classifies
-- whether it is zero into `x6`, exercising post-driven synthesis across two instructions.
def wp_rv64_leaf_synth_li_sltiu_zero_cfg (base imm : Word) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 8)
      (CodeReq.ofProg base
        [ .LI .x5 imm,
          .SLTIU .x6 .x5 (1 : BitVec 12) ])
      ((.x5 ↦ᵣ imm) **
        (.x6 ↦ᵣ (if BitVec.ult imm (signExtend12 (1 : BitVec 12)) then (1 : Word) else (0 : Word)))) := by
  wp_rv64_leaf_synth

example (base imm : Word) :
    (wp_rv64_leaf_synth_li_sltiu_zero_cfg base imm).pre =
      (regOwn .x5 ** regOwn .x6) := rfl

-- Restated via `sltiu_one_zero_classifier`: `x6` ends up `1` iff the loaded word is `0`.
example (base imm : Word) :
    EvmAsm.Rv64.WP.CFG.Cert base (base + 8)
      (CodeReq.ofProg base
        [ .LI .x5 imm,
          .SLTIU .x6 .x5 (1 : BitVec 12) ])
      ((.x5 ↦ᵣ imm) ** (.x6 ↦ᵣ (if imm = 0 then (1 : Word) else (0 : Word)))) := by
  have h := wp_rv64_leaf_synth_li_sltiu_zero_cfg base imm
  rwa [sltiu_one_zero_classifier] at h

example {entry : Word} {cr : CodeReq} {post : Assertion} :
    EvmAsm.Rv64.WP.CFG.Cert entry entry cr post := by
  wp_rv64_exit_refl entry, cr, post

example {P : Assertion} {A : Prop} (hA : A) :
    EvmAsm.Rv64.WP.Entails P (P ** ⌜A⌝) := by
  wp_rv64_link

/--
error: wp_rv64_link: could not close the remaining WP.Entails goal.
  Tried reflexivity, local assumptions, Branch/CFG projection rewrites,
  rv64_wp normalization, xperm_pure, and 0 registered
  @[rv64_wp_entails] theorem(s).
  Source: P
  Target: Q
  Hint: inspect whether the source and target differ by a missing projection
  rewrite such as WP.CFG.leaf_pre, by a frame permutation that xperm_pure
  cannot see, or by a reusable semantic bridge that should be tagged
  @[rv64_wp_entails].
-/
#guard_msgs in
example {P Q : Assertion} : EvmAsm.Rv64.WP.Entails P Q := by
  wp_rv64_link

/--
error: wp_rv64_cert: no @[rv64_wp_cert] declaration closed the goal.
  Tried 0 registered declaration(s).
  Goal: WP.Triple entry exit_ cr post
  Hint: try the intended constructor directly once to expose missing static
  facts, or tag a reusable constructor with @[rv64_wp_cert].
-/
#guard_msgs in
example {entry exit_ : Word} {cr : CodeReq} {post : Assertion} :
    EvmAsm.Rv64.WP.Triple entry exit_ cr post := by
  wp_rv64_cert

theorem wp_rv64_dead_test_hint {P : Assertion} (hdead : ∀ h, P h → False) :
    ∀ h, P h → False :=
  hdead

attribute [rv64_wp_dead] wp_rv64_dead_test_hint

example {P : Assertion} (hdead : ∀ h, P h → False) :
    ∀ h, P h → False := by
  wp_rv64_dead

example {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (tail : EvmAsm.Rv64.WP.Triple mid exit_ cr post)
    (head : cpsTripleWithin nSteps entry mid cr pre tail.pre) :
    cpsTripleWithin (nSteps + tail.nSteps) entry exit_ cr pre post := by
  wp_rv64_seq head, tail

example {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (tail : EvmAsm.Rv64.WP.CFG.Cert mid exit_ cr post)
    (head : cpsTripleWithin nSteps entry mid cr pre tail.pre) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_cfg_seq_exact head, tail

example {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (tail : EvmAsm.Rv64.WP.CFG.Cert mid exit_ cr post)
    (head : cpsTripleWithin nSteps entry mid cr pre tail.pre) :
    cpsTripleWithin (nSteps + tail.nSteps) entry exit_ cr pre post := by
  wp_rv64_seq_exact head, tail

example {nSteps : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (tail : EvmAsm.Rv64.WP.CFG.Cert mid exit_ cr2 post)
    (head : cpsTripleWithin nSteps entry mid cr1 pre tail.pre) :
    cpsTripleWithin (nSteps + tail.nSteps) entry exit_ (cr1.union cr2) pre post := by
  wp_rv64_seq_disjoint_exact hd, head, tail

example {nHead nTail : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nHead entry mid cr pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr midPost post) :
    cpsTripleWithin (nHead + nTail) entry exit_ cr pre post := by
  wp_rv64_seq_block head, tail

example {nHead nTail : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nHead entry mid cr pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr midPost post) :
    cpsTripleWithin (nHead + nTail) entry exit_ cr pre post := by
  wp_rv64_seq_block_exact head, tail

example {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    {fuel : Nat}
    (hcert : EvmAsm.Rv64.WP.loopNatCert nHeader nBody nExit
      header bodyEntry exit_ cr inv bodyPre exitPost post 0 fuel) :
    EvmAsm.Rv64.WP.CFG.Cert header exit_ cr post := by
  wp_rv64_loop_nat hcert

example {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    {fuel : Nat}
    (hcert : EvmAsm.Rv64.WP.loopNatCert nHeader nBody nExit
      header bodyEntry exit_ cr inv bodyPre exitPost post 0 fuel) :
    cpsTripleWithin (EvmAsm.Rv64.WP.loopBound nHeader nBody nExit fuel)
      header exit_ cr (inv 0) post := by
  wp_rv64_loop_nat_sound hcert

example {nHead nTail : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr2 midPost post) :
    cpsTripleWithin (nHead + nTail) entry exit_ (cr1.union cr2) pre post := by
  wp_rv64_seq_block_disjoint hd, head, tail

example {nHead nTail : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr2 midPost post) :
    cpsTripleWithin (nHead + nTail) entry exit_ (cr1.union cr2) pre post := by
  wp_rv64_seq_block_disjoint_exact hd, head, tail

example {nHead : Nat} {entry mid : Word} {cr1 cr2 : CodeReq}
    {pre midPost : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost) :
    EvmAsm.Rv64.WP.CFG.Cert entry mid (cr1.union cr2) midPost := by
  let tail := EvmAsm.Rv64.WP.CFG.exit mid cr2 (EvmAsm.Rv64.WP.Entails.refl midPost)
  wp_rv64_cfg_seq_disjoint_auto head, tail

example {entry mid : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : EvmAsm.Rv64.WP.CFG.Cert entry mid cr1 post) :
    EvmAsm.Rv64.WP.CFG.Cert entry mid (cr1.union cr2) post := by
  let tail := EvmAsm.Rv64.WP.CFG.exit mid cr2 (EvmAsm.Rv64.WP.Entails.refl post)
  wp_rv64_cfg_cert_seq_disjoint_auto head, tail

example {nTail : Nat} {entry target : Word} {cr1 cr2 : CodeReq}
    {tailPre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_t target cr2 tailPre post)
    (hlink : EvmAsm.Rv64.WP.Entails br.post_t tailPre) :
    EvmAsm.Rv64.WP.Branch entry (cr1.union cr2) := by
  exact EvmAsm.Rv64.WP.CFG.branchSeqTakenBlockDisjoint hd br tail hlink

example {nTail : Nat} {entry target : Word} {cr1 cr2 : CodeReq}
    {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_t target cr2 br.post_t post) :
    EvmAsm.Rv64.WP.Branch entry (cr1.union cr2) := by
  wp_rv64_branch_taken_block_disjoint hd, br, tail

example {nTail : Nat} {entry target : Word} {cr1 cr2 : CodeReq}
    {tailPre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_f target cr2 tailPre post)
    (hlink : EvmAsm.Rv64.WP.Entails br.post_f tailPre) :
    EvmAsm.Rv64.WP.Branch entry (cr1.union cr2) := by
  exact EvmAsm.Rv64.WP.CFG.branchSeqNotTakenBlockDisjoint hd br tail hlink

example {nTail : Nat} {entry target : Word} {cr1 cr2 : CodeReq}
    {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_f target cr2 br.post_f post) :
    EvmAsm.Rv64.WP.Branch entry (cr1.union cr2) := by
  wp_rv64_branch_not_taken_block_disjoint hd, br, tail

example {nTail : Nat} {entry target : Word} {cr1 cr2 : CodeReq}
    {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_t target cr2 br.post_t post) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  wp_rv64_branch_taken_block_nbranch_disjoint hd, br, tail

example {nTail : Nat} {entry succ : Word} {cr1 cr2 : CodeReq}
    {succPost : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tailSound : cpsBranchWithin nTail br.exit_t cr2 br.post_t
      br.exit_f br.post_f succ succPost) :
    EvmAsm.Rv64.WP.Branch entry (cr1.union cr2) := by
  let tail := EvmAsm.Rv64.WP.Branch.ofSpec tailSound
  wp_rv64_branch_taken_branch_converge_disjoint hd, br, tail, br.post_f

example {entry : Word} {cr : CodeReq}
    (br : EvmAsm.Rv64.WP.Branch entry cr) :
    EvmAsm.Rv64.WP.NBranch entry cr :=
  EvmAsm.Rv64.WP.CFG.nbranchOfBranch br

example {entry : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tail : EvmAsm.Rv64.WP.NBranch br.exit_f cr2)
    (hlink : EvmAsm.Rv64.WP.Entails br.post_f tail.pre) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) :=
  EvmAsm.Rv64.WP.CFG.branchSeqNotTakenNBranchDisjoint hd br tail hlink

example {nTail : Nat} {entry : Word} {cr1 cr2 : CodeReq}
    {exits : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tailSound : cpsNBranchWithin nTail br.exit_f cr2 br.post_f exits) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  let tail := EvmAsm.Rv64.WP.NBranch.ofSpec tailSound
  wp_rv64_branch_not_taken_nbranch_disjoint hd, br, tail

example {nTail : Nat} {entry target : Word} {cr1 cr2 : CodeReq}
    {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_t target cr2 br.post_t post) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  let nb := EvmAsm.Rv64.WP.CFG.nbranchOfBranch br
  wp_rv64_nbranch_head_block_disjoint hd, nb, tail

example {nTail : Nat} {entry : Word} {cr1 cr2 : CodeReq}
    {exits : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.Branch entry cr1)
    (tailSound : cpsNBranchWithin nTail br.exit_t cr2 br.post_t exits) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  let nb := EvmAsm.Rv64.WP.CFG.nbranchOfBranch br
  let tail := EvmAsm.Rv64.WP.NBranch.ofSpec tailSound
  wp_rv64_nbranch_head_nbranch_disjoint hd, nb, tail

example {entry l1 l2 l3 l4 l3' : Word} {cr1 cr2 : CodeReq}
    {Q1 Q2 Q3 Q4 R : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.NBranch entry cr1)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (tail : EvmAsm.Rv64.WP.CFG.Cert l3 l3' cr2 R)
    (hlink : EvmAsm.Rv64.WP.Entails Q3 tail.pre) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  wp_rv64_nbranch_third_cert_disjoint_with hd, br, hexits, tail, hlink

example {entry l1 l2 l3 l4 : Word} {cr1 cr2 : CodeReq}
    {Q1 Q2 Q3 Q4 : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.NBranch entry cr1)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)]) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  let tail := EvmAsm.Rv64.WP.CFG.exit l3 cr2 (EvmAsm.Rv64.WP.Entails.refl Q3)
  wp_rv64_nbranch_third_cert_disjoint_with_auto hd, br, hexits, tail

example {entry l1 l2 l3 l4 : Word} {cr1 cr2 : CodeReq}
    {Q1 Q2 Q3 Q4 : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.NBranch entry cr1)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)]) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  let tail := EvmAsm.Rv64.WP.CFG.exit l3 cr2 (EvmAsm.Rv64.WP.Entails.refl Q3)
  wp_rv64_nbranch_third_cert_auto br, hexits, tail

example {entry : Word} {cr : CodeReq} {F : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr) (hF : F.pcFree) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_frame br, F, hF

example {entry : Word} {cr : CodeReq}
    (br : EvmAsm.Rv64.WP.NBranch entry cr) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_set_pre br, br.pre

example {entry : Word} {cr : CodeReq} {pre F : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr) (hF : F.pcFree)
    (hpre : EvmAsm.Rv64.WP.Entails pre (br.pre ** F)) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_frame_set_pre br, F, hF, pre

example {entry : Word} {cr : CodeReq} {exits' : List (Word × Assertion)}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hmap : ∀ ex ∈ br.exits, ∃ ex' ∈ exits',
      ex'.1 = ex.1 ∧ EvmAsm.Rv64.WP.Entails ex.2 ex'.2) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_weaken_posts br, exits', hmap

example {entry l : Word} {cr : CodeReq} {headPost headPost' : Assertion}
    {others : List (Word × Assertion)}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = (l, headPost) :: others)
    (hpost : EvmAsm.Rv64.WP.Entails headPost headPost') :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  exact EvmAsm.Rv64.WP.CFG.nbranchWeakenHeadPost br hexits hpost

example {entry l1 l2 l3 l4 : Word} {cr : CodeReq}
    {Q1 Q2 Q3 Q4 Q1' Q2' Q3' Q4' : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (h1 : EvmAsm.Rv64.WP.Entails Q1 Q1')
    (h2 : EvmAsm.Rv64.WP.Entails Q2 Q2')
    (h3 : EvmAsm.Rv64.WP.Entails Q3 Q3')
    (h4 : EvmAsm.Rv64.WP.Entails Q4 Q4') :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4 br hexits h1 h2 h3 h4

example {entry l1 l2 l3 l4 : Word} {cr : CodeReq}
    {Q1 Q2 Q3 Q4 Q1' Q2' Q3' Q4' : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (h1 : EvmAsm.Rv64.WP.Entails Q1 Q1')
    (h2 : EvmAsm.Rv64.WP.Entails Q2 Q2')
    (h3 : EvmAsm.Rv64.WP.Entails Q3 Q3')
    (h4 : EvmAsm.Rv64.WP.Entails Q4 Q4') :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_weaken_posts4_with br, hexits, h1, h2, h3, h4

example {entry l1 l2 l3 l4 : Word} {cr : CodeReq}
    {Q1 Q2 Q3 Q4 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)]) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_weaken_posts4_with_auto br, hexits, Q1, Q2, Q3, Q4

example {entry l l3 l4 : Word} {cr : CodeReq}
    {Q Q3 Q4 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l, Q), (l, Q), (l3, Q3), (l4, Q4)]) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_weaken_posts4_merge_first_two_with_auto br, hexits, Q, Q3, Q4

example {entry l1 l2 : Word} {cr : CodeReq} {post Q1 Q2 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hlink1 : EvmAsm.Rv64.WP.Entails Q1 post)
    (hdead2 : ∀ h, Q2 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l1 cr post := by
  wp_rv64_nbranch_join2_resolve_first br, hexits, hlink1, hdead2

example {entry l1 l2 : Word} {cr : CodeReq} {Q1 Q2 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hdead2 : ∀ h, Q2 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l1 cr Q1 := by
  wp_rv64_nbranch_join2_resolve_first_auto br, hexits, Q1, hdead2

example {entry l1 l2 : Word} {cr : CodeReq} {Q1 Q2 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hdead2 : ∀ h, Q2 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l1 cr Q1 := by
  wp_rv64_nbranch_join2_resolve_first_dead_auto br, hexits, Q1

example {entry l1 l2 : Word} {cr : CodeReq} {post Q1 Q2 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : EvmAsm.Rv64.WP.Entails Q2 post) :
    EvmAsm.Rv64.WP.CFG.Cert entry l2 cr post := by
  wp_rv64_nbranch_join2_resolve_second br, hexits, hdead1, hlink2

example {entry l1 l2 : Word} {cr : CodeReq} {Q1 Q2 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hdead1 : ∀ h, Q1 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l2 cr Q2 := by
  wp_rv64_nbranch_join2_resolve_second_auto br, hexits, hdead1, Q2

example {entry l1 l2 : Word} {cr : CodeReq} {Q1 Q2 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hdead1 : ∀ h, Q1 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l2 cr Q2 := by
  wp_rv64_nbranch_join2_resolve_second_dead_auto br, hexits, Q2

example {entry l1 l2 l3 : Word} {cr : CodeReq} {post Q1 Q2 Q3 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : EvmAsm.Rv64.WP.Entails Q2 post)
    (hdead3 : ∀ h, Q3 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l2 cr post := by
  wp_rv64_nbranch_join3_resolve_second br, hexits, hdead1, hlink2, hdead3

example {entry l1 l2 l3 : Word} {cr : CodeReq} {Q1 Q2 Q3 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (hdead1 : ∀ h, Q1 h → False)
    (hdead3 : ∀ h, Q3 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l2 cr Q2 := by
  wp_rv64_nbranch_join3_resolve_second_auto br, hexits, hdead1, Q2, hdead3

example {entry l1 l2 l3 : Word} {cr : CodeReq} {Q1 Q2 Q3 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (hdead1 : ∀ h, Q1 h → False)
    (hdead3 : ∀ h, Q3 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l2 cr Q2 := by
  wp_rv64_nbranch_join3_resolve_second_dead_auto br, hexits, Q2

example {entry exit_ l1 l2 l3 l4 : Word} {cr : CodeReq} {post Q1 Q2 Q3 Q4 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (t1 : EvmAsm.Rv64.WP.CFG.Cert l1 exit_ cr post)
    (t2 : EvmAsm.Rv64.WP.CFG.Cert l2 exit_ cr post)
    (t3 : EvmAsm.Rv64.WP.CFG.Cert l3 exit_ cr post)
    (t4 : EvmAsm.Rv64.WP.CFG.Cert l4 exit_ cr post)
    (hlink1 : EvmAsm.Rv64.WP.Entails Q1 t1.pre)
    (hlink2 : EvmAsm.Rv64.WP.Entails Q2 t2.pre)
    (hlink3 : EvmAsm.Rv64.WP.Entails Q3 t3.pre)
    (hlink4 : EvmAsm.Rv64.WP.Entails Q4 t4.pre) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_nbranch_join4_with br, hexits, Nat.max (Nat.max t1.nSteps t2.nSteps)
    (Nat.max t3.nSteps t4.nSteps),
    t1, hlink1, Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
    t2, hlink2, Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _),
    t3, hlink3, Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
    t4, hlink4, Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

example {entry exit_ l1 l2 l3 l4 : Word} {cr : CodeReq} {post Q1 Q2 Q3 Q4 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (t1 : EvmAsm.Rv64.WP.CFG.Cert l1 exit_ cr post)
    (t2 : EvmAsm.Rv64.WP.CFG.Cert l2 exit_ cr post)
    (t3 : EvmAsm.Rv64.WP.CFG.Cert l3 exit_ cr post)
    (t4 : EvmAsm.Rv64.WP.CFG.Cert l4 exit_ cr post)
    (hlink1 : EvmAsm.Rv64.WP.Entails Q1 t1.pre)
    (hlink2 : EvmAsm.Rv64.WP.Entails Q2 t2.pre)
    (hlink3 : EvmAsm.Rv64.WP.Entails Q3 t3.pre)
    (hlink4 : EvmAsm.Rv64.WP.Entails Q4 t4.pre) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_nbranch_join4 br, hexits, t1, hlink1, t2, hlink2, t3, hlink3, t4, hlink4

example {entry l1 l2 l3 l4 : Word} {cr : CodeReq} {post Q1 Q2 Q3 Q4 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (hdead1 : ∀ h, Q1 h → False)
    (hdead2 : ∀ h, Q2 h → False)
    (hlink3 : EvmAsm.Rv64.WP.Entails Q3 post)
    (hdead4 : ∀ h, Q4 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l3 cr post := by
  wp_rv64_nbranch_join4_resolve_third br, hexits, hdead1, hdead2, hlink3, hdead4

example {entry l1 l2 l3 l4 : Word} {cr : CodeReq} {Q1 Q2 Q3 Q4 : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (hdead1 : ∀ h, Q1 h → False)
    (hdead2 : ∀ h, Q2 h → False)
    (hdead4 : ∀ h, Q4 h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry l3 cr Q3 := by
  wp_rv64_nbranch_join4_resolve_third_dead_auto br, hexits, Q3

example {entry head l : Word} {cr1 cr2 : CodeReq}
    {headPost secondPost : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.NBranch entry cr1)
    (hexits : br.exits = (head, headPost) :: (l, secondPost) :: others)
    (tail : EvmAsm.Rv64.WP.NBranch l cr2)
    (hlink : EvmAsm.Rv64.WP.Entails secondPost tail.pre) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  exact EvmAsm.Rv64.WP.CFG.nbranchSeqSecondNBranchDisjoint hd br hexits tail hlink

example {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post) :
    EvmAsm.Rv64.WP.NBranch entry cr :=
  EvmAsm.Rv64.WP.NBranch.ofTriple cfg

example {entry l l' : Word} {cr1 cr2 : CodeReq}
    {exitPost post : Assertion} {preExits others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : EvmAsm.Rv64.WP.NBranch entry cr1)
    (hexits : br.exits = preExits ++ (l, exitPost) :: others)
    (tail : EvmAsm.Rv64.WP.CFG.Cert l l' cr2 post)
    (hlink : EvmAsm.Rv64.WP.Entails exitPost tail.pre) :
    EvmAsm.Rv64.WP.NBranch entry (cr1.union cr2) := by
  wp_rv64_nbranch_exit_cert_disjoint_with hd, br, preExits, hexits, tail, hlink

example :
    EvmAsm.Rv64.CodeReq.Disjoint
      (EvmAsm.Rv64.CodeReq.singleton (0 : Word) (.ADDI .x1 .x0 (0 : BitVec 12)))
      (EvmAsm.Rv64.CodeReq.singleton (4 : Word) (.ADDI .x2 .x0 (0 : BitVec 12))) := by
  wp_rv64_disjoint

end EvmAsm.Rv64.Tactics.WPTests
