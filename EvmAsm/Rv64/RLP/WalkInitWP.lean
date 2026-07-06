/-
  EvmAsm.Rv64.RLP.WalkInitWP

  WP-facing control summaries for `rlp_walk_init`.  The detailed leaf spec has
  nine outcomes; fixed-schema decoders often first need only the coarse split
  on the head `BEQ`: empty input versus nonempty input.
-/

import EvmAsm.Rv64.WP
import EvmAsm.Rv64.RLP.WalkInit

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

/-- First `rlp_walk_init` branch precondition: only the length and zero register
    are needed to split empty input from the nonempty path. -/
def walkInitZeroNonzeroPre (listLen : Word) : Assertion :=
  ((.x11 ↦ᵣ listLen) ** (.x0 ↦ᵣ (0 : Word)))

/-- Taken branch of the first `rlp_walk_init` instruction: `listLen = 0`. -/
def walkInitZeroPost (listLen : Word) : Assertion :=
  ((.x11 ↦ᵣ listLen) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜listLen = (0 : Word)⌝)

/-- Fall-through branch of the first `rlp_walk_init` instruction: `listLen != 0`. -/
def walkInitNonzeroPost (listLen : Word) : Assertion :=
  ((.x11 ↦ᵣ listLen) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜listLen ≠ (0 : Word)⌝)

/-- Coarse zero/nonzero split for the first instruction of `rlp_walk_init`, as a
    standalone singleton-code branch. -/
theorem walkInitZeroNonzeroBranch_singleton_spec (base listLen : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)))
      (walkInitZeroNonzeroPre listLen)
      (base + 156) (walkInitZeroPost listLen)
      (base + 4) (walkInitNonzeroPost listLen) := by
  unfold walkInitZeroNonzeroPre walkInitZeroPost walkInitNonzeroPost
  have h := beq_spec_gen_within .x11 .x0 (156 : BitVec 13) listLen (0 : Word) base
  rw [show base + signExtend13 (156 : BitVec 13) = base + 156 from by
    rw [show signExtend13 (156 : BitVec 13) = (156 : Word) from by decide]] at h
  exact h

/-- Coarse zero/nonzero split for the first instruction of `rlp_walk_init`, lifted
    to the full `rlp_walk_init_code base` requirement. -/
theorem walkInitZeroNonzeroBranch_spec (base listLen : Word) :
    cpsBranchWithin 1 base (rlp_walk_init_code base)
      (walkInitZeroNonzeroPre listLen)
      (base + 156) (walkInitZeroPost listLen)
      (base + 4) (walkInitNonzeroPost listLen) := by
  have hmono : ∀ a i,
      CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)) a = some i →
      rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 0 base
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  exact cpsBranchWithin_extend_code hmono (walkInitZeroNonzeroBranch_singleton_spec base listLen)

/-- WP branch certificate for the zero/nonzero split at the head of `rlp_walk_init`. -/
def walkInitZeroNonzeroBranch (base listLen : Word) :
    WP.Branch base (rlp_walk_init_code base) :=
  WP.Branch.ofSpec (walkInitZeroNonzeroBranch_spec base listLen)

end EvmAsm.Rv64.RLP
