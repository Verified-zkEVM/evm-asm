/-
  EvmAsm.Rv64.WP.Loop

  Bounded invariant/variant loop rule for the WP layer.  The rule does not
  infer control flow: callers provide the loop header branch, body triple,
  early-exit postcondition entailment, and final forced-exit triple.
-/

import EvmAsm.Rv64.WP.Core

namespace EvmAsm.Rv64
namespace WP

/-- Step budget for a loop with `fuel` possible body iterations. -/
def loopBound (nHeader nBody nExit : Nat) : Nat → Nat
  | 0 => nExit
  | fuel + 1 => nHeader + (nBody + loopBound nHeader nBody nExit fuel)

/-- Input obligations for a bounded natural-number loop.

    `start` is the current invariant index and `fuel` is the remaining variant.
    At each non-final iteration, the header branches either to the body or to
    the loop exit.  The body advances `inv start` to `inv (start + 1)`.
    At `fuel = 0`, callers provide a final triple that reaches the exit from
    `inv start`; this is where a caller proves the loop cannot continue. -/
def loopNatCert (nHeader nBody nExit : Nat)
    (header bodyEntry exit_ : Word) (cr : CodeReq)
    (inv bodyPre exitPost : Nat → Assertion) (post : Assertion)
    (start : Nat) : Nat → Prop
  | 0 =>
      cpsTripleWithin nExit header exit_ cr (inv start) post
  | fuel + 1 =>
      cpsBranchWithin nHeader header cr (inv start)
        bodyEntry (bodyPre start) exit_ (exitPost start) ∧
      cpsTripleWithin nBody bodyEntry header cr (bodyPre start) (inv (start + 1)) ∧
      Entails (exitPost start) post ∧
      loopNatCert nHeader nBody nExit header bodyEntry exit_ cr inv bodyPre exitPost post
        (start + 1) fuel

/-- Soundness of `loopNatCert`: the generated precondition is `inv start`. -/
theorem loopNatCert_sound {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    {start fuel : Nat}
    (hcert : loopNatCert nHeader nBody nExit header bodyEntry exit_ cr
      inv bodyPre exitPost post start fuel) :
    cpsTripleWithin (loopBound nHeader nBody nExit fuel)
      header exit_ cr (inv start) post := by
  induction fuel generalizing start with
  | zero =>
      simpa [loopNatCert, loopBound] using hcert
  | succ fuel ih =>
      obtain ⟨hHeader, hBody, hExitPost, hTailCert⟩ := hcert
      have hTail :
          cpsTripleWithin (loopBound nHeader nBody nExit fuel)
            header exit_ cr (inv (start + 1)) post :=
        ih hTailCert
      have hBodyTail :
          cpsTripleWithin (nBody + loopBound nHeader nBody nExit fuel)
            bodyEntry exit_ cr (bodyPre start) post :=
        cpsTripleWithin_seq_same_cr hBody hTail
      have hExit :
          cpsTripleWithin (nBody + loopBound nHeader nBody nExit fuel)
            exit_ exit_ cr (exitPost start) post := by
        exact cpsTripleWithin_mono_nSteps
          (Nat.zero_le (nBody + loopBound nHeader nBody nExit fuel))
          (Triple.refl exit_ cr hExitPost).sound
      simpa [loopBound] using
        (cpsBranchWithin_merge_same_cr hHeader hBodyTail hExit)

/-- Input obligations for a bounded natural-number loop **with a mid-body
    early exit** (`break`).

    Same skeleton as `loopNatCert`, but the body is a *branch* rather than a
    straight triple: from `bodyEntry` it either falls back to `header` with
    `inv (start + 1)` (continue) or jumps to `exit_` with `breakPost start`
    (break).  The break arm short-cuts straight to the loop's postcondition
    — that is the whole content of the construct: `breakPost` need only
    entail `post`.  Both the header exit (guard fails) and the break exit
    entail `post`. -/
def loopBreakNatCert (nHeader nBody nExit : Nat)
    (header bodyEntry exit_ : Word) (cr : CodeReq)
    (inv bodyPre exitPost breakPost : Nat → Assertion) (post : Assertion)
    (start : Nat) : Nat → Prop
  | 0 =>
      cpsTripleWithin nExit header exit_ cr (inv start) post
  | fuel + 1 =>
      cpsBranchWithin nHeader header cr (inv start)
        bodyEntry (bodyPre start) exit_ (exitPost start) ∧
      cpsBranchWithin nBody bodyEntry cr (bodyPre start)
        header (inv (start + 1)) exit_ (breakPost start) ∧
      Entails (exitPost start) post ∧
      Entails (breakPost start) post ∧
      loopBreakNatCert nHeader nBody nExit header bodyEntry exit_ cr
        inv bodyPre exitPost breakPost post (start + 1) fuel

/-- Soundness of `loopBreakNatCert`: the generated precondition is `inv start`,
    and the step budget is the same `loopBound` as an ordinary bounded loop
    (the break can only reach the exit *sooner*). -/
theorem loopBreakNatCert_sound {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost breakPost : Nat → Assertion} {post : Assertion}
    {start fuel : Nat}
    (hcert : loopBreakNatCert nHeader nBody nExit header bodyEntry exit_ cr
      inv bodyPre exitPost breakPost post start fuel) :
    cpsTripleWithin (loopBound nHeader nBody nExit fuel)
      header exit_ cr (inv start) post := by
  induction fuel generalizing start with
  | zero =>
      simpa [loopBreakNatCert, loopBound] using hcert
  | succ fuel ih =>
      obtain ⟨hHeader, hBody, hExitPost, hBreakPost, hTailCert⟩ := hcert
      have hTail :
          cpsTripleWithin (loopBound nHeader nBody nExit fuel)
            header exit_ cr (inv (start + 1)) post :=
        ih hTailCert
      have hBreakExit :
          cpsTripleWithin (loopBound nHeader nBody nExit fuel)
            exit_ exit_ cr (breakPost start) post :=
        cpsTripleWithin_mono_nSteps (Nat.zero_le _)
          (Triple.refl exit_ cr hBreakPost).sound
      -- The body branch, closed on both arms: continue folds into the tail
      -- certificate, break short-cuts to `post`.
      have hBodyMerged :
          cpsTripleWithin (nBody + loopBound nHeader nBody nExit fuel)
            bodyEntry exit_ cr (bodyPre start) post :=
        cpsBranchWithin_merge_same_cr hBody hTail hBreakExit
      have hHeaderExit :
          cpsTripleWithin (nBody + loopBound nHeader nBody nExit fuel)
            exit_ exit_ cr (exitPost start) post :=
        cpsTripleWithin_mono_nSteps (Nat.zero_le _)
          (Triple.refl exit_ cr hExitPost).sound
      simpa [loopBound] using
        (cpsBranchWithin_merge_same_cr hHeader hBodyMerged hHeaderExit)

/-- Package a bounded loop certificate as a WP triple. -/
def Triple.ofLoopNatCert {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    {fuel : Nat}
    (hcert : loopNatCert nHeader nBody nExit header bodyEntry exit_ cr
      inv bodyPre exitPost post 0 fuel) :
    Triple header exit_ cr post where
  nSteps := loopBound nHeader nBody nExit fuel
  pre := inv 0
  sound := loopNatCert_sound hcert

end WP
end EvmAsm.Rv64
