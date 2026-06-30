/-
  EvmAsm.Rv64.Tactics.WP

  Thin tactic surface for WP/CFG certificates.  The proof search/calculation
  lives in the certificate constructors; this tactic consumes the resulting
  object and closes the corresponding CPS goal.
-/

import Lean
import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.Tactics

open Lean Elab Tactic

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

/-- Close the midpoint entailment between adjacent WP fragments.  The common
    case is definitional equality of the head postcondition and tail WP; reordered
    separation frames fall through to `xperm`. -/
syntax (name := wpRv64LinkTac) "wp_rv64_link" : tactic

macro_rules
  | `(tactic| wp_rv64_link) =>
      `(tactic| first
        | exact EvmAsm.Rv64.WP.Entails.refl _
        | intro _ _hp; xperm_hyp _hp)

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

/-- Continue a branch's not-taken exit with a WP/CFG tail over disjoint code. -/
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

/-- Frame every exit of an N-way branch with a PC-free assertion. -/
syntax (name := wpRv64NBranchFrameRTac)
  "wp_rv64_nbranch_frame " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_frame $br:term, $F:term, $hF:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchFrameR $br $F $hF)

/-- Weaken the exit postconditions of an N-way branch. -/
syntax (name := wpRv64NBranchWeakenPostsTac)
  "wp_rv64_nbranch_weaken_posts " term ", " term ", " term : tactic

macro_rules
  | `(tactic| wp_rv64_nbranch_weaken_posts $br:term, $exits:term, $hmap:term) =>
      `(tactic| exact EvmAsm.Rv64.WP.CFG.nbranchWeakenPosts $br $exits $hmap)

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

example {entry : Word} {cr : CodeReq} {F : Assertion}
    (br : EvmAsm.Rv64.WP.NBranch entry cr) (hF : F.pcFree) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_frame br, F, hF

example {entry : Word} {cr : CodeReq} {exits' : List (Word × Assertion)}
    (br : EvmAsm.Rv64.WP.NBranch entry cr)
    (hmap : ∀ ex ∈ br.exits, ∃ ex' ∈ exits',
      ex'.1 = ex.1 ∧ EvmAsm.Rv64.WP.Entails ex.2 ex'.2) :
    EvmAsm.Rv64.WP.NBranch entry cr := by
  wp_rv64_nbranch_weaken_posts br, exits', hmap

end EvmAsm.Rv64.Tactics.WPTests
