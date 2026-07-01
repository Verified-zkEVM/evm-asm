/-
  EvmAsm.Rv64.WP.Examples

  Small kernel-checked examples for the WP layer.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.Tactics.WP

namespace EvmAsm.Rv64
namespace WP
namespace Examples

/-- A concrete two-instruction backward WP certificate.

    The final postcondition is reduced to the precondition `.x5 ↦ᵣ v`; the
    code side-condition is the disjoint union of the two instruction fetches. -/
def addiTwiceCfg (base v : Word) (imm1 imm2 : BitVec 12) :
    CFG.Cert base ((base + 4) + 4)
      ((CodeReq.singleton base (.ADDI .x5 .x5 imm1)).union
        (CodeReq.singleton (base + 4) (.ADDI .x5 .x5 imm2)))
      (.x5 ↦ᵣ ((v + signExtend12 imm1) + signExtend12 imm2)) := by
  let head := addi_spec_same_within .x5 v imm1 base (by decide)
  let tailSpec := addi_spec_same_within .x5 (v + signExtend12 imm1) imm2 (base + 4) (by decide)
  exact CFG.seqDisjoint
    (CodeReq.Disjoint.singleton (by bv_omega))
    head
    (CFG.leaf tailSpec)
    (Entails.refl _)

example (base v : Word) (imm1 imm2 : BitVec 12) :
    (addiTwiceCfg base v imm1 imm2).pre = (.x5 ↦ᵣ v) := rfl

/-- Exact sequencing removes the midpoint entailment when the head postcondition
    is definitionally the generated tail precondition. -/
example {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (tail : CFG.Cert mid exit_ cr post)
    (head : cpsTripleWithin nSteps entry mid cr pre tail.pre) :
    CFG.Cert entry exit_ cr post :=
  CFG.seqExact tail head

example (base v : Word) (imm1 imm2 : BitVec 12) :
    cpsTripleWithin 2 base ((base + 4) + 4)
      ((CodeReq.singleton base (.ADDI .x5 .x5 imm1)).union
        (CodeReq.singleton (base + 4) (.ADDI .x5 .x5 imm2)))
      (.x5 ↦ᵣ v)
      (.x5 ↦ᵣ ((v + signExtend12 imm1) + signExtend12 imm2)) :=
  (addiTwiceCfg base v imm1 imm2).sound

/-- Branch/join shape: an LLM-supplied branch summary plus one continuation per
    exit reduces to the branch precondition. -/
example {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : Branch entry cr)
    (taken : CFG.Cert br.exit_t exit_ cr post)
    (notTaken : CFG.Cert br.exit_f exit_ cr post)
    (ht : Entails br.post_t taken.pre)
    (hf : Entails br.post_f notTaken.pre) :
    cpsTripleWithin (br.nSteps + Nat.max taken.nSteps notTaken.nSteps)
      entry exit_ cr br.pre post :=
  (CFG.branch br taken notTaken ht hf).sound

/-- Branch links may need to unfold certificate projections and permute framed
    resources. This models composing an independently-stated continuation whose
    precondition has the same atoms as the branch post in a different order. -/
example {nBranch nTaken nFail : Nat}
    {entry takenExit failExit exit_ : Word} {cr : CodeReq}
    {branchPre takenPost failPost finalPost frame : Assertion}
    (h_frame : frame.pcFree)
    (hBranch : cpsBranchWithin nBranch entry cr branchPre
      takenExit takenPost failExit failPost)
    (hTaken : cpsTripleWithin nTaken takenExit exit_ cr
      (frame ** takenPost) finalPost)
    (hFail : cpsTripleWithin nFail failExit exit_ cr
      (frame ** failPost) finalPost) :
    CFG.Cert entry exit_ cr finalPost := by
  let br0 := Branch.ofSpec hBranch
  let br := Branch.frameR br0 frame h_frame
  let takenCert : CFG.Cert br.exit_t exit_ cr finalPost := CFG.leaf hTaken
  let failCert : CFG.Cert br.exit_f exit_ cr finalPost := CFG.leaf hFail
  have h_taken_link : Entails br.post_t takenCert.pre := by
    wp_rv64_link
  have h_fail_link : Entails br.post_f failCert.pre := by
    wp_rv64_link
  exact CFG.branch br takenCert failCert h_taken_link h_fail_link

/-- Loop shape: a supplied indexed invariant and finite variant produce a
    regular CPS triple whose precondition is `inv 0`. -/
example {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    {fuel : Nat}
    (hcert : loopNatCert nHeader nBody nExit header bodyEntry exit_ cr
      inv bodyPre exitPost post 0 fuel) :
    cpsTripleWithin (loopBound nHeader nBody nExit fuel)
      header exit_ cr (inv 0) post :=
  (CFG.loopNat hcert).sound

/-- A one-iteration loop certificate shows the four obligations introduced by
    `loopNatCert`: header branch, body progress, early-exit handoff, and final
    forced-exit proof. -/
def oneIterationLoopCfg {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    (hHeader0 : cpsBranchWithin nHeader header cr (inv 0)
      bodyEntry (bodyPre 0) exit_ (exitPost 0))
    (hBody0 : cpsTripleWithin nBody bodyEntry header cr
      (bodyPre 0) (inv 1))
    (hExit0 : Entails (exitPost 0) post)
    (hFinal1 : cpsTripleWithin nExit header exit_ cr (inv 1) post) :
    CFG.Cert header exit_ cr post :=
  let hcert : loopNatCert nHeader nBody nExit header bodyEntry exit_ cr
      inv bodyPre exitPost post 0 1 := by
    change cpsBranchWithin nHeader header cr (inv 0)
        bodyEntry (bodyPre 0) exit_ (exitPost 0) ∧
      cpsTripleWithin nBody bodyEntry header cr (bodyPre 0) (inv 1) ∧
      Entails (exitPost 0) post ∧
      cpsTripleWithin nExit header exit_ cr (inv 1) post
    exact ⟨hHeader0, hBody0, hExit0, hFinal1⟩
  CFG.loopNat hcert

example {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    (hHeader0 : cpsBranchWithin nHeader header cr (inv 0)
      bodyEntry (bodyPre 0) exit_ (exitPost 0))
    (hBody0 : cpsTripleWithin nBody bodyEntry header cr
      (bodyPre 0) (inv 1))
    (hExit0 : Entails (exitPost 0) post)
    (hFinal1 : cpsTripleWithin nExit header exit_ cr (inv 1) post) :
    (oneIterationLoopCfg hHeader0 hBody0 hExit0 hFinal1).pre = inv 0 :=
  rfl

/-- A two-iteration loop certificate demonstrates how the recursive tail is
    just the same four obligations at the next invariant index. -/
def twoIterationLoopCfg {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    (hHeader0 : cpsBranchWithin nHeader header cr (inv 0)
      bodyEntry (bodyPre 0) exit_ (exitPost 0))
    (hBody0 : cpsTripleWithin nBody bodyEntry header cr
      (bodyPre 0) (inv 1))
    (hExit0 : Entails (exitPost 0) post)
    (hHeader1 : cpsBranchWithin nHeader header cr (inv 1)
      bodyEntry (bodyPre 1) exit_ (exitPost 1))
    (hBody1 : cpsTripleWithin nBody bodyEntry header cr
      (bodyPre 1) (inv 2))
    (hExit1 : Entails (exitPost 1) post)
    (hFinal2 : cpsTripleWithin nExit header exit_ cr (inv 2) post) :
    CFG.Cert header exit_ cr post :=
  let hcert : loopNatCert nHeader nBody nExit header bodyEntry exit_ cr
      inv bodyPre exitPost post 0 2 := by
    change cpsBranchWithin nHeader header cr (inv 0)
        bodyEntry (bodyPre 0) exit_ (exitPost 0) ∧
      cpsTripleWithin nBody bodyEntry header cr (bodyPre 0) (inv 1) ∧
      Entails (exitPost 0) post ∧
      (cpsBranchWithin nHeader header cr (inv 1)
        bodyEntry (bodyPre 1) exit_ (exitPost 1) ∧
      cpsTripleWithin nBody bodyEntry header cr (bodyPre 1) (inv 2) ∧
      Entails (exitPost 1) post ∧
      cpsTripleWithin nExit header exit_ cr (inv 2) post)
    exact ⟨hHeader0, hBody0, hExit0,
      hHeader1, hBody1, hExit1, hFinal2⟩
  CFG.loopNat hcert

example {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    (hHeader0 : cpsBranchWithin nHeader header cr (inv 0)
      bodyEntry (bodyPre 0) exit_ (exitPost 0))
    (hBody0 : cpsTripleWithin nBody bodyEntry header cr
      (bodyPre 0) (inv 1))
    (hExit0 : Entails (exitPost 0) post)
    (hHeader1 : cpsBranchWithin nHeader header cr (inv 1)
      bodyEntry (bodyPre 1) exit_ (exitPost 1))
    (hBody1 : cpsTripleWithin nBody bodyEntry header cr
      (bodyPre 1) (inv 2))
    (hExit1 : Entails (exitPost 1) post)
    (hFinal2 : cpsTripleWithin nExit header exit_ cr (inv 2) post) :
    (twoIterationLoopCfg hHeader0 hBody0 hExit0
      hHeader1 hBody1 hExit1 hFinal2).nSteps =
        loopBound nHeader nBody nExit 2 :=
  rfl

end Examples
end WP
end EvmAsm.Rv64
