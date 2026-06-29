/-
  EvmAsm.Rv64.WP.Core

  A small weakest-precondition style layer over the existing bounded CPS
  Hoare triples.  The layer is intentionally soundness-first: each calculator
  result exposes a precondition together with a proof that the existing
  `cpsTripleWithin`/`cpsNBranchWithin` contract follows.
-/

import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64
namespace WP

/-- Assertion entailment.  `Entails P Q` means every partial state satisfying
    `P` also satisfies `Q`. -/
def Entails (P Q : Assertion) : Prop :=
  ∀ h, P h → Q h

namespace Entails

theorem refl (P : Assertion) : Entails P P :=
  fun _ hp => hp

theorem trans {P Q R : Assertion} (hPQ : Entails P Q) (hQR : Entails Q R) :
    Entails P R :=
  fun h hp => hQR h (hPQ h hp)

end Entails

/-- A backward WP result for a single-exit region.

    The intended reading is: to establish `post` at `exit_`, it is sufficient
    to prove `pre` at `entry`; `sound` is the existing CPS triple that makes
    this kernel-checked. -/
structure Triple (entry exit_ : Word) (cr : CodeReq) (post : Assertion) where
  nSteps : Nat
  pre : Assertion
  sound : cpsTripleWithin nSteps entry exit_ cr pre post

namespace Triple

/-- The reduced precondition computed by the WP object. -/
def wp {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) : Assertion :=
  t.pre

/-- A same-address continuation: the WP of `post` at the current PC is `pre`
    when `pre` entails `post`. -/
def refl (addr : Word) (cr : CodeReq) {pre post : Assertion}
    (h : Entails pre post) : Triple addr addr cr post where
  nSteps := 0
  pre := pre
  sound := by
    intro R hR s _hcr hPR hpc
    exact ⟨0, Nat.le_refl 0, s, rfl, hpc, by
      obtain ⟨hp, hcompat, hpq⟩ := hPR
      exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

/-- Lift an already-proved CPS triple into a WP result, weakening its
    postcondition to the requested continuation post. -/
def ofSpec {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post post' : Assertion}
    (hpost : Entails post post')
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    Triple entry exit_ cr post' where
  nSteps := nSteps
  pre := pre
  sound := cpsTripleWithin_weaken (fun _ hp => hp) hpost h

/-- Weaken the computed precondition. -/
def weakenPre {entry exit_ : Word} {cr : CodeReq} {post pre' : Assertion}
    (t : Triple entry exit_ cr post) (hpre : Entails pre' t.pre) :
    Triple entry exit_ cr post where
  nSteps := t.nSteps
  pre := pre'
  sound := cpsTripleWithin_weaken hpre (fun _ hp => hp) t.sound

/-- Weaken the continuation postcondition. -/
def weakenPost {entry exit_ : Word} {cr : CodeReq} {post post' : Assertion}
    (t : Triple entry exit_ cr post) (hpost : Entails post post') :
    Triple entry exit_ cr post' where
  nSteps := t.nSteps
  pre := t.pre
  sound := cpsTripleWithin_weaken (fun _ hp => hp) hpost t.sound

/-- Increase the step budget of a WP result. -/
def monoSteps {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) {nSteps' : Nat} (hle : t.nSteps ≤ nSteps') :
    Triple entry exit_ cr post where
  nSteps := nSteps'
  pre := t.pre
  sound := cpsTripleWithin_mono_nSteps hle t.sound

/-- Extend a WP result to a larger persistent code requirement. -/
def extendCode {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    Triple entry exit_ cr' post where
  nSteps := t.nSteps
  pre := t.pre
  sound := cpsTripleWithin_extend_code hmono t.sound

/-- Rewrite the entry address of a WP result. -/
def changeEntry {entry entry' exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (hentry : entry' = entry) :
    Triple entry' exit_ cr post where
  nSteps := t.nSteps
  pre := t.pre
  sound := by
    intro R hR s hcr hPR hpc
    exact t.sound R hR s hcr hPR (by simpa [hentry] using hpc)

/-- Rewrite the exit address of a WP result. -/
def changeExit {entry exit_ exit_' : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (hexit : exit_ = exit_') :
    Triple entry exit_' cr post where
  nSteps := t.nSteps
  pre := t.pre
  sound := by
    intro R hR s hcr hPR hpc
    obtain ⟨k, hk, s', hstep, hpc', hpost⟩ := t.sound R hR s hcr hPR hpc
    exact ⟨k, hk, s', hstep, by simpa [hexit] using hpc', hpost⟩

/-- Backward sequencing when both regions share the same persistent code
    requirement.  The precondition of the tail becomes the requested
    postcondition for the head. -/
def seq {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nSteps entry mid cr pre midPost)
    (tail : Triple mid exit_ cr post)
    (hlink : Entails midPost tail.pre) :
    Triple entry exit_ cr post where
  nSteps := nSteps + tail.nSteps
  pre := pre
  sound := cpsTripleWithin_seq_perm_same_cr hlink head tail.sound

/-- Backward sequencing for disjoint code requirements. -/
def seqDisjoint {nSteps : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nSteps entry mid cr1 pre midPost)
    (tail : Triple mid exit_ cr2 post)
    (hlink : Entails midPost tail.pre) :
    Triple entry exit_ (cr1.union cr2) post where
  nSteps := nSteps + tail.nSteps
  pre := pre
  sound := cpsTripleWithin_seq_with_perm hd hlink head tail.sound

end Triple

/-- A two-exit branch summary consumable by the WP join rule. -/
structure Branch (entry : Word) (cr : CodeReq) where
  nSteps : Nat
  pre : Assertion
  exit_t : Word
  post_t : Assertion
  exit_f : Word
  post_f : Assertion
  sound : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f

namespace Branch

def ofSpec {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exit_t : Word} {post_t : Assertion}
    {exit_f : Word} {post_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f) :
    Branch entry cr where
  nSteps := nSteps
  pre := pre
  exit_t := exit_t
  post_t := post_t
  exit_f := exit_f
  post_f := post_f
  sound := h

/-- Frame both exits of a branch with a PC-free assertion. -/
def frameR {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) : Branch entry cr where
  nSteps := br.nSteps
  pre := br.pre ** F
  exit_t := br.exit_t
  post_t := br.post_t ** F
  exit_f := br.exit_f
  post_f := br.post_f ** F
  sound := cpsBranchWithin_frameR F hF br.sound

/-- Join a branch by providing a continuation for each exit.  The branch's
    posts only need to entail the corresponding continuation preconditions. -/
def join {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : Branch entry cr)
    (t : Triple br.exit_t exit_ cr post)
    (f : Triple br.exit_f exit_ cr post)
    (ht : Entails br.post_t t.pre)
    (hf : Entails br.post_f f.pre) :
    Triple entry exit_ cr post where
  nSteps := br.nSteps + Nat.max t.nSteps f.nSteps
  pre := br.pre
  sound := by
    exact cpsBranchWithin_merge_same_cr
      (cpsBranchWithin_weaken (fun _ hp => hp) ht hf br.sound)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_left t.nSteps f.nSteps) t.sound)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right t.nSteps f.nSteps) f.sound)

/-- Continue only the taken exit of a branch with disjoint code, leaving the
    not-taken exit open.  This is useful for early failure/success endpoints in
    generated CFGs. -/
def seqTakenDisjoint {entry target : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Triple br.exit_t target cr2 post)
    (hlink : Entails br.post_t tail.pre) :
    Branch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exit_t := target
  post_t := post
  exit_f := br.exit_f
  post_f := br.post_f
  sound := cpsBranchWithin_seq_cpsTripleWithin_taken hd br.sound (tail.weakenPre hlink).sound

end Branch

/-- A multi-exit branch summary. -/
structure NBranch (entry : Word) (cr : CodeReq) where
  nSteps : Nat
  pre : Assertion
  exits : List (Word × Assertion)
  sound : cpsNBranchWithin nSteps entry cr pre exits

namespace NBranch

def ofSpec {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry cr pre exits) :
    NBranch entry cr where
  nSteps := nSteps
  pre := pre
  exits := exits
  sound := h

/-- Join all exits with a uniform continuation bound. -/
def join {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : NBranch entry cr) (tailBound : Nat)
    (hall : ∀ ex ∈ br.exits, cpsTripleWithin tailBound ex.1 exit_ cr ex.2 post) :
    Triple entry exit_ cr post where
  nSteps := br.nSteps + tailBound
  pre := br.pre
  sound := cpsNBranchWithin_merge br.sound hall

end NBranch

end WP
end EvmAsm.Rv64
