/-
  EvmAsm.Rv64.Tactics.WP

  Thin tactic surface for WP/CFG certificates.  The proof search/calculation
  lives in the certificate constructors; this tactic consumes the resulting
  object and closes the corresponding CPS goal.
-/

import Lean
import EvmAsm.Rv64.Tactics.WPAttr
import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.WP.Call
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

private def closeWithWpEntailsHint (goal : MVarId) (declName : Name) : TacticM Unit := do
  let goalType ← instantiateMVars (← goal.getType)
  let hintConst ← mkConstWithFreshMVarLevels declName
  let hintType ← inferType hintConst
  let (params, _, body) ← forallMetaTelescope hintType
  unless ← isDefEq body goalType do
    throwError "hint result does not match goal"
  let proof ← instantiateMVars (mkAppN hintConst params)
  if proof.hasExprMVar then
    throwError "hint left unresolved metavariables"
  goal.assign proof
  replaceMainGoal []

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
  for declName in entries do
    let saved ← saveState
    try
      closeWithWpEntailsHint goal declName
      return
    catch _ =>
      restoreState saved
      continue
  throwError "wp_rv64_entails: no @[rv64_wp_entails] theorem closed the goal"

/-- Close the midpoint entailment between adjacent WP fragments.  The common
    case is definitional equality of the head postcondition and tail WP; semantic
    bridge lemmas tagged `@[rv64_wp_entails]` handle generated handoff shapes,
    and reordered separation frames fall through to `xperm`. -/
syntax (name := wpRv64LinkTac) "wp_rv64_link" : tactic

macro_rules
  | `(tactic| wp_rv64_link) =>
      `(tactic| first
        | exact EvmAsm.Rv64.WP.Entails.refl _
        | wp_rv64_entails
        | simp only [rv64_wp]; wp_rv64_entails
        | dsimp; wp_rv64_entails
        | dsimp; simp only [rv64_wp]; wp_rv64_entails
        | intro _ _hp; xperm_hyp _hp
        | intro _ _hp; xperm_pure _hp
        | intro _ _hp; simp only [rv64_wp] at _hp ⊢; xperm_hyp _hp
        | intro _ _hp; simp only [rv64_wp] at _hp ⊢; xperm_pure _hp
        | intro _ _hp; dsimp at _hp ⊢; xperm_hyp _hp
        | intro _ _hp; dsimp at _hp ⊢; xperm_pure _hp
        | intro _ _hp; dsimp at _hp ⊢; simp only [rv64_wp] at _hp ⊢; xperm_hyp _hp
        | intro _ _hp; dsimp at _hp ⊢; simp only [rv64_wp] at _hp ⊢; xperm_pure _hp)

/-- Close a `CodeReq.Disjoint` goal using the structural prover shared with
    `seqFrame`.  This keeps WP composition proofs from spelling out code-range
    side conditions for generated straight-line fragments. -/
elab "wp_rv64_disjoint" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  unless goalType.isAppOfArity ``EvmAsm.Rv64.CodeReq.Disjoint 2 do
    throwError "wp_rv64_disjoint: expected CodeReq.Disjoint goal"
  let cr1 := goalType.getAppArgs[0]!
  let cr2 := goalType.getAppArgs[1]!
  let proof ← withTransparency .all <| buildDisjointProof cr1 cr2
  goal.assign proof

/-- Frame a single-exit CFG certificate and return the framed certificate. -/
syntax (name := wpRv64FrameRTac) "wp_rv64_frame " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_frame $cfg:term, $F:term, $hF:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.frameR $cfg $F $hF)

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

/-- Extend an N-way branch to a larger code requirement and set an explicit
    precondition in one generated step. -/
syntax (name := wpRv64NBranchExtendSetPreTac)
  "wp_rv64_nbranch_extend_set_pre " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_extend_set_pre $br:term, $hmono:term, $pre:term) =>
      `(tactic|
        let br' := EvmAsm.Rv64.WP.NBranch.extendCode $br $hmono
        exact EvmAsm.Rv64.WP.NBranch.weakenPre br'
          (show EvmAsm.Rv64.WP.Entails $pre br'.pre by wp_rv64_link))

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

/-- Weaken exactly three known exits of an N-way branch. The exits field is
    expected to reduce definitionally to the three-exit list. -/
syntax (name := wpRv64NBranchWeakenPosts3Tac)
  "wp_rv64_nbranch_weaken_posts3 " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts3 $br:term, $h1:term, $h2:term, $h3:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts3 $br (by rfl) $h1 $h2 $h3)

/-- Weaken exactly four known exits of an N-way branch. The exits field is
    expected to reduce definitionally to the four-exit list. -/
syntax (name := wpRv64NBranchWeakenPosts4Tac)
  "wp_rv64_nbranch_weaken_posts4 " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts4 $br:term, $h1:term, $h2:term, $h3:term, $h4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4 $br (by rfl) $h1 $h2 $h3 $h4)

/-- Weaken exactly four known exits of an N-way branch, supplying the generated
    exit-list proof explicitly. -/
syntax (name := wpRv64NBranchWeakenPosts4WithTac)
  "wp_rv64_nbranch_weaken_posts4_with " term ", " term ", " term ", " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts4_with $br:term, $hexits:term, $h1:term, $h2:term, $h3:term, $h4:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts4 $br $hexits $h1 $h2 $h3 $h4)

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
    (hpre : ∀ h, pre h → False) :
    EvmAsm.Rv64.WP.CFG.Cert entry exit_ cr post := by
  wp_rv64_unreachable entry, exit_, cr, hpre

example {P : Assertion} {A : Prop} (hA : A) :
    EvmAsm.Rv64.WP.Entails P (P ** ⌜A⌝) := by
  wp_rv64_link

example {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (tail : EvmAsm.Rv64.WP.Triple mid exit_ cr post)
    (head : cpsTripleWithin nSteps entry mid cr pre tail.pre) :
    cpsTripleWithin (nSteps + tail.nSteps) entry exit_ cr pre post := by
  wp_rv64_seq head, tail

example {nHead nTail : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nHead entry mid cr pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr midPost post) :
    cpsTripleWithin (nHead + nTail) entry exit_ cr pre post := by
  wp_rv64_seq_block head, tail

example {nHead nTail : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr2 midPost post) :
    cpsTripleWithin (nHead + nTail) entry exit_ (cr1.union cr2) pre post := by
  wp_rv64_seq_block_disjoint hd, head, tail

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

example {entry : Word} {cr : CodeReq} {F : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr) (hF : F.pcFree) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_frame br, F, hF

example {entry : Word} {cr : CodeReq}
    (br : EvmAsm.Rv64.WP.NBranch entry cr) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_set_pre br, br.pre

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
