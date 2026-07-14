/-
  Framed call and sequencing adapters for the strict cursor walkers.

  The leaf contracts in `RlpWalkInitFlatSAsm` and `RlpWalkNextFlatSAsm`
  describe the complete cursor/end/scratch register state.  These adapters
  preserve that state as an arbitrary caller assertion (`Prest`) while adding
  the direct JAL and the caller's larger code requirement.  A caller can use
  the two adapters repeatedly and compose the resulting triples with
  `walk_call_seq`; no cursor, end-pointer, or scratch fact is hidden or
  weakened.
-/

import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.WP.Call

namespace EvmAsm.Codegen.RlpWalkCallSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

#guard EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = 53
#guard EvmAsm.Rv64.RLP.rlp_walk_next_prog.length = 103

/-- Add a direct `jal ra, callee` to a complete caller code requirement. -/
theorem walk_call_within
    {cr calleeCode : CodeReq} {Prest Q : Assertion}
    {n : Nat} (callerPC calleeEntry oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint calleeCode)
    (hcode : ∀ a i,
      (CodeReq.singleton callerPC (.JAL .x1 offset)).union calleeCode a = some i →
        cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      calleeCode ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  exact cpsTripleWithin_extend_code hcode
    (WP.cpsCallWithin (vOld := oldRa) offset hoffset halign hpre hdisj hcallee)

/-- Specialized adapter for the strict `rlp_walk_init` leaf.  `Prest` is
    intentionally arbitrary: HeaderFields callers place cursor/end/scratch
    registers and the immutable input bytes in it, and the leaf's exact raw
    post remains visible in `Q`. -/
theorem rlp_walk_init_call_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (callerPC calleeEntry oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_init_code calleeEntry))
    (hcode : ∀ a i,
      (CodeReq.singleton callerPC (.JAL .x1 offset)).union
        (rlp_walk_init_code calleeEntry) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code calleeEntry)
      ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  exact walk_call_within callerPC calleeEntry oldRa offset hpre hoffset halign hdisj hcode hcallee

/-- Specialized adapter for one strict `rlp_walk_next` call. -/
theorem rlp_walk_next_call_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (callerPC calleeEntry oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_next_code calleeEntry))
    (hcode : ∀ a i,
      (CodeReq.singleton callerPC (.JAL .x1 offset)).union
        (rlp_walk_next_code calleeEntry) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code calleeEntry)
      ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  exact walk_call_within callerPC calleeEntry oldRa offset hpre hoffset halign hdisj hcode hcallee

/-- Compose two already-lifted walker calls.  The midpoint assertion is where
    the first walk's cursor/end/scratch post is supplied to the next call; the
    genuine caller proof supplies that relation explicitly. -/
theorem walk_call_seq
    {cr : CodeReq} {n₁ n₂ : Nat} {entry mid exit_ : Word}
    {P M Q : Assertion}
    (h₁ : cpsTripleWithin n₁ entry mid cr P M)
    (h₂ : cpsTripleWithin n₂ mid exit_ cr M Q) :
    cpsTripleWithin (n₁ + n₂) entry exit_ cr P Q := by
  exact cpsTripleWithin_seq_same_cr h₁ h₂

#print axioms rlp_walk_init_call_within
#print axioms rlp_walk_next_call_within
#print axioms walk_call_seq

end EvmAsm.Codegen.RlpWalkCallSAsm
