/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepSubtract

  CPS specs for the subtract-and-store path of the MULMOD reducer inner step.
-/

import EvmAsm.Evm64.MulMod.ReduceInnerStepCompare
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The subtract-and-store subpath of `evm_mulmod_reduce512_inner_step`. -/
def evm_mulmod_reduce512_inner_step_subtract_store : Program :=
  LD .x6 .x12 224 ;;
  LD .x7 .x12 64 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x11 .x6 .x7 ;;
  SD .x12 .x5 224 ;;
  LD .x6 .x12 232 ;;
  LD .x7 .x12 72 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 232 ;;
  LD .x6 .x12 240 ;;
  LD .x7 .x12 80 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 240 ;;
  LD .x6 .x12 248 ;;
  LD .x7 .x12 88 ;;
  SUB .x5 .x6 .x7 ;;
  SUB .x5 .x5 .x11 ;;
  SD .x12 .x5 248

/-- The first limb subtract/store block at the subtract path entry. -/
def evm_mulmod_reduce512_inner_step_subtract_limb0 : Program :=
  LD .x6 .x12 224 ;;
  LD .x7 .x12 64 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x11 .x6 .x7 ;;
  SD .x12 .x5 224

abbrev evm_mulmod_reduce512_inner_step_subtract_store_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 144) evm_mulmod_reduce512_inner_step_subtract_store

abbrev evm_mulmod_reduce512_inner_step_subtract_limb0_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 144) evm_mulmod_reduce512_inner_step_subtract_limb0

/-- Folded final memory state after the reducer subtract-store subpath. -/
@[irreducible]
def mulModReduceSubtractMem (sp : Word) (r n : EvmWord) : Assertion :=
  ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 0) **
  ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 1) **
  ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 2) **
  ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded final postcondition for the reducer subtract-store subpath. -/
@[irreducible]
def mulModReduceSubtractPost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ EvmWord.getLimbN (r - n) 3) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 3) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 3) **
  (.x10 ↦ᵣ mulModReduceSubBorrow2a r n) **
  (.x11 ↦ᵣ mulModReduceSubBorrow2 r n) **
  (.x13 ↦ᵣ mulModReduceSubBorrow2b r n) **
  mulModReduceSubtractMem sp r n

/-- Folded postcondition after subtracting and storing limb 0. -/
@[irreducible]
def mulModReduceSubtractLimb0Post
    (sp v10 v13 : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb0 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 0) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 0) **
  (.x10 ↦ᵣ v10) **
  (.x11 ↦ᵣ mulModReduceSubBorrow0 r n) **
  (.x13 ↦ᵣ v13) **
  ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)


/-- The limb0 subtract block as explicit singleton code entries for `runBlock`. -/
theorem evm_mulmod_reduce512_inner_step_subtract_limb0_code_eq_singletons (base : Word) :
    evm_mulmod_reduce512_inner_step_subtract_limb0_code base =
      (CodeReq.singleton (base + 144) (.LD .x6 .x12 224)).union
        ((CodeReq.singleton (base + 148) (.LD .x7 .x12 64)).union
          ((CodeReq.singleton (base + 152) (.SUB .x5 .x6 .x7)).union
            ((CodeReq.singleton (base + 156) (.SLTU .x11 .x6 .x7)).union
              (CodeReq.singleton (base + 160) (.SD .x12 .x5 224))))) := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_subtract_limb0_code
  unfold evm_mulmod_reduce512_inner_step_subtract_limb0
  change CodeReq.ofProg (base + 144)
      [(.LD .x6 .x12 224), (.LD .x7 .x12 64), (.SUB .x5 .x6 .x7),
       (.SLTU .x11 .x6 .x7), (.SD .x12 .x5 224)] a =
    ((CodeReq.singleton (base + 144) (.LD .x6 .x12 224)).union
      ((CodeReq.singleton (base + 148) (.LD .x7 .x12 64)).union
        ((CodeReq.singleton (base + 152) (.SUB .x5 .x6 .x7)).union
          ((CodeReq.singleton (base + 156) (.SLTU .x11 .x6 .x7)).union
            (CodeReq.singleton (base + 160) (.SD .x12 .x5 224)))))) a
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 144 : Word) + 4 = base + 148 by bv_addr]
  rw [show (base + 148 : Word) + 4 = base + 152 by bv_addr]
  rw [show (base + 152 : Word) + 4 = base + 156 by bv_addr]
  rw [show (base + 156 : Word) + 4 = base + 160 by bv_addr]

/-- Untouched resources around the limb0 subtract/store block. -/
@[irreducible]
def mulModReduceSubtractLimb0Frame
    (sp v10 v13 : Word) (r n : EvmWord) : Assertion :=
  (.x10 ↦ᵣ v10) **
  (.x13 ↦ᵣ v13) **
  ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Core postcondition for the resources touched by the limb0 block. -/
@[irreducible]
def mulModReduceSubtractLimb0CorePost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb0 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 0) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 0) **
  (.x11 ↦ᵣ mulModReduceSubBorrow0 r n) **
  ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0)

theorem evm_mulmod_reduce512_inner_step_subtract_limb0_core_spec_within
    (sp base v5 v6 v7 v11 : Word) (r n : EvmWord) :
    cpsTripleWithin 5 (base + 144) (base + 164)
      (evm_mulmod_reduce512_inner_step_subtract_limb0_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x11 ↦ᵣ v11) **
       ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0))
      (mulModReduceSubtractLimb0CorePost sp r n) := by
  rw [evm_mulmod_reduce512_inner_step_subtract_limb0_code_eq_singletons base]
  unfold mulModReduceSubtractLimb0CorePost
  unfold mulModReduceSubLimb0 mulModReduceSubBorrow0
  runBlock

theorem evm_mulmod_reduce512_inner_step_subtract_limb0_spec_within
    (sp base v5 v6 v7 v10 v11 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 5 (base + 144) (base + 164)
      (evm_mulmod_reduce512_inner_step_subtract_limb0_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
       mulModReduceCompareMem sp r n)
      (mulModReduceSubtractLimb0Post sp v10 v13 r n) := by
  have hcore := evm_mulmod_reduce512_inner_step_subtract_limb0_core_spec_within
    sp base v5 v6 v7 v11 r n
  have hfr := cpsTripleWithin_frameR
    (mulModReduceSubtractLimb0Frame sp v10 v13 r n)
    (by unfold mulModReduceSubtractLimb0Frame; pcFree) hcore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold mulModReduceSubtractLimb0Frame
      unfold mulModReduceCompareMem at hp
      xperm_hyp hp)
    (fun _ hp => by
      unfold mulModReduceSubtractLimb0Post
      unfold mulModReduceSubtractLimb0Frame mulModReduceSubtractLimb0CorePost at hp
      xperm_hyp hp)
    hfr

end EvmAsm.Evm64
