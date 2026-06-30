/-
  EvmAsm.Rv64.WP.Examples

  Small kernel-checked examples for the WP layer.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.WP.CFG

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

end Examples
end WP
end EvmAsm.Rv64
