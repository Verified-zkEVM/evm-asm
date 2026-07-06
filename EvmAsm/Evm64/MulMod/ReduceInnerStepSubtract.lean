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
  LD .x6 .x12 4064 ;;
  LD .x7 .x12 64 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x11 .x6 .x7 ;;
  SD .x12 .x5 4064 ;;
  LD .x6 .x12 4072 ;;
  LD .x7 .x12 72 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 4072 ;;
  LD .x6 .x12 4080 ;;
  LD .x7 .x12 80 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 4080 ;;
  LD .x6 .x12 4088 ;;
  LD .x7 .x12 88 ;;
  SUB .x5 .x6 .x7 ;;
  SUB .x5 .x5 .x11 ;;
  SD .x12 .x5 4088

/-- The first limb subtract/store block at the subtract path entry. -/
def evm_mulmod_reduce512_inner_step_subtract_limb0 : Program :=
  LD .x6 .x12 4064 ;;
  LD .x7 .x12 64 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x11 .x6 .x7 ;;
  SD .x12 .x5 4064

/-- The second limb subtract/store block, consuming the limb0 borrow. -/
def evm_mulmod_reduce512_inner_step_subtract_limb1 : Program :=
  LD .x6 .x12 4072 ;;
  LD .x7 .x12 72 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 4072

/-- The third limb subtract/store block, consuming the limb1 borrow. -/
def evm_mulmod_reduce512_inner_step_subtract_limb2 : Program :=
  LD .x6 .x12 4080 ;;
  LD .x7 .x12 80 ;;
  SUB .x5 .x6 .x7 ;;
  SLTU .x10 .x6 .x7 ;;
  SLTU .x13 .x5 .x11 ;;
  SUB .x5 .x5 .x11 ;;
  OR' .x11 .x10 .x13 ;;
  SD .x12 .x5 4080

/-- The high limb subtract/store block, consuming the limb2 borrow. -/
def evm_mulmod_reduce512_inner_step_subtract_limb3 : Program :=
  LD .x6 .x12 4088 ;;
  LD .x7 .x12 88 ;;
  SUB .x5 .x6 .x7 ;;
  SUB .x5 .x5 .x11 ;;
  SD .x12 .x5 4088

abbrev evm_mulmod_reduce512_inner_step_subtract_store_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 144) evm_mulmod_reduce512_inner_step_subtract_store

abbrev evm_mulmod_reduce512_inner_step_subtract_limb0_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 144) evm_mulmod_reduce512_inner_step_subtract_limb0

abbrev evm_mulmod_reduce512_inner_step_subtract_limb1_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 164) evm_mulmod_reduce512_inner_step_subtract_limb1

abbrev evm_mulmod_reduce512_inner_step_subtract_limb2_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 196) evm_mulmod_reduce512_inner_step_subtract_limb2

abbrev evm_mulmod_reduce512_inner_step_subtract_limb3_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 228) evm_mulmod_reduce512_inner_step_subtract_limb3

/-- Folded final memory state after the reducer subtract-store subpath. -/
@[irreducible]
def mulModReduceSubtractMem (sp : Word) (r n : EvmWord) : Assertion :=
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (r - n) 3) **
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
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)


/-- Folded postcondition after subtracting and storing limb 1. -/
@[irreducible]
def mulModReduceSubtractLimb1Post (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb1 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 1) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 1) **
  (.x10 ↦ᵣ mulModReduceSubBorrow1a r n) **
  (.x11 ↦ᵣ mulModReduceSubBorrow1 r n) **
  (.x13 ↦ᵣ mulModReduceSubBorrow1b r n) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ mulModReduceSubLimb1 r n) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded postcondition after subtracting and storing limb 2. -/
@[irreducible]
def mulModReduceSubtractLimb2Post (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb2 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 2) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 2) **
  (.x10 ↦ᵣ mulModReduceSubBorrow2a r n) **
  (.x11 ↦ᵣ mulModReduceSubBorrow2 r n) **
  (.x13 ↦ᵣ mulModReduceSubBorrow2b r n) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ mulModReduceSubLimb1 r n) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ mulModReduceSubLimb2 r n) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded postcondition after subtracting and storing the high limb. -/
@[irreducible]
def mulModReduceSubtractLimb3Post (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb3 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 3) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 3) **
  (.x10 ↦ᵣ mulModReduceSubBorrow2a r n) **
  (.x11 ↦ᵣ mulModReduceSubBorrow2 r n) **
  (.x13 ↦ᵣ mulModReduceSubBorrow2b r n) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ mulModReduceSubLimb1 r n) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ mulModReduceSubLimb2 r n) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ mulModReduceSubLimb3 r n) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- The limb0 subtract block as explicit singleton code entries for `runBlock`. -/
theorem evm_mulmod_reduce512_inner_step_subtract_limb0_code_eq_singletons (base : Word) :
    evm_mulmod_reduce512_inner_step_subtract_limb0_code base =
      (CodeReq.singleton (base + 144) (.LD .x6 .x12 4064)).union
        ((CodeReq.singleton (base + 148) (.LD .x7 .x12 64)).union
          ((CodeReq.singleton (base + 152) (.SUB .x5 .x6 .x7)).union
            ((CodeReq.singleton (base + 156) (.SLTU .x11 .x6 .x7)).union
              (CodeReq.singleton (base + 160) (.SD .x12 .x5 4064))))) := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_subtract_limb0_code
  unfold evm_mulmod_reduce512_inner_step_subtract_limb0
  change CodeReq.ofProg (base + 144)
      [(.LD .x6 .x12 4064), (.LD .x7 .x12 64), (.SUB .x5 .x6 .x7),
       (.SLTU .x11 .x6 .x7), (.SD .x12 .x5 4064)] a =
    ((CodeReq.singleton (base + 144) (.LD .x6 .x12 4064)).union
      ((CodeReq.singleton (base + 148) (.LD .x7 .x12 64)).union
        ((CodeReq.singleton (base + 152) (.SUB .x5 .x6 .x7)).union
          ((CodeReq.singleton (base + 156) (.SLTU .x11 .x6 .x7)).union
            (CodeReq.singleton (base + 160) (.SD .x12 .x5 4064)))))) a
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
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
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
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0)

theorem evm_mulmod_reduce512_inner_step_subtract_limb0_core_spec_within
    (sp base v5 v6 v7 v11 : Word) (r n : EvmWord) :
    cpsTripleWithin 5 (base + 144) (base + 164)
      (evm_mulmod_reduce512_inner_step_subtract_limb0_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x11 ↦ᵣ v11) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0))
      (mulModReduceSubtractLimb0CorePost sp r n) := by
  rw [evm_mulmod_reduce512_inner_step_subtract_limb0_code_eq_singletons base]
  unfold mulModReduceSubtractLimb0CorePost
  unfold mulModReduceSubLimb0 mulModReduceSubBorrow0
  have I0 := ld_spec_gen_within .x6 .x12 sp v6 (EvmWord.getLimbN r 0) 4064 (base + 144) (by nofun)
  have I1 := ld_spec_gen_within .x7 .x12 sp v7 (EvmWord.getLimbN n 0) 64 (base + 148) (by nofun)
  have I2 := sub_spec_gen_within .x5 .x6 .x7 (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0) v5
    (base + 152) (by nofun)
  have I3 := sltu_spec_gen_within .x11 .x6 .x7 v11 (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)
    (base + 156) (by nofun)
  have I4 := sd_spec_gen_within .x12 .x5 sp
    (EvmWord.getLimbN r 0 - EvmWord.getLimbN n 0) (EvmWord.getLimbN r 0) 4064 (base + 160)
  runBlock I0 I1 I2 I3 I4

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


/-- The limb1 subtract block as explicit singleton code entries for `runBlock`. -/
theorem evm_mulmod_reduce512_inner_step_subtract_limb1_code_eq_singletons (base : Word) :
    evm_mulmod_reduce512_inner_step_subtract_limb1_code base =
      (CodeReq.singleton (base + 164) (.LD .x6 .x12 4072)).union
        ((CodeReq.singleton (base + 168) (.LD .x7 .x12 72)).union
          ((CodeReq.singleton (base + 172) (.SUB .x5 .x6 .x7)).union
            ((CodeReq.singleton (base + 176) (.SLTU .x10 .x6 .x7)).union
              ((CodeReq.singleton (base + 180) (.SLTU .x13 .x5 .x11)).union
                ((CodeReq.singleton (base + 184) (.SUB .x5 .x5 .x11)).union
                  ((CodeReq.singleton (base + 188) (.OR .x11 .x10 .x13)).union
                    (CodeReq.singleton (base + 192) (.SD .x12 .x5 4072)))))))) := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_subtract_limb1_code
  unfold evm_mulmod_reduce512_inner_step_subtract_limb1
  change CodeReq.ofProg (base + 164)
      [(.LD .x6 .x12 4072), (.LD .x7 .x12 72), (.SUB .x5 .x6 .x7),
       (.SLTU .x10 .x6 .x7), (.SLTU .x13 .x5 .x11), (.SUB .x5 .x5 .x11),
       (.OR .x11 .x10 .x13), (.SD .x12 .x5 4072)] a =
    ((CodeReq.singleton (base + 164) (.LD .x6 .x12 4072)).union
      ((CodeReq.singleton (base + 168) (.LD .x7 .x12 72)).union
        ((CodeReq.singleton (base + 172) (.SUB .x5 .x6 .x7)).union
          ((CodeReq.singleton (base + 176) (.SLTU .x10 .x6 .x7)).union
            ((CodeReq.singleton (base + 180) (.SLTU .x13 .x5 .x11)).union
              ((CodeReq.singleton (base + 184) (.SUB .x5 .x5 .x11)).union
                ((CodeReq.singleton (base + 188) (.OR .x11 .x10 .x13)).union
                  (CodeReq.singleton (base + 192) (.SD .x12 .x5 4072))))))))) a
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 164 : Word) + 4 = base + 168 by bv_addr]
  rw [show (base + 168 : Word) + 4 = base + 172 by bv_addr]
  rw [show (base + 172 : Word) + 4 = base + 176 by bv_addr]
  rw [show (base + 176 : Word) + 4 = base + 180 by bv_addr]
  rw [show (base + 180 : Word) + 4 = base + 184 by bv_addr]
  rw [show (base + 184 : Word) + 4 = base + 188 by bv_addr]
  rw [show (base + 188 : Word) + 4 = base + 192 by bv_addr]

/-- The limb2 subtract block as explicit singleton code entries for `runBlock`. -/
theorem evm_mulmod_reduce512_inner_step_subtract_limb2_code_eq_singletons (base : Word) :
    evm_mulmod_reduce512_inner_step_subtract_limb2_code base =
      (CodeReq.singleton (base + 196) (.LD .x6 .x12 4080)).union
        ((CodeReq.singleton (base + 200) (.LD .x7 .x12 80)).union
          ((CodeReq.singleton (base + 204) (.SUB .x5 .x6 .x7)).union
            ((CodeReq.singleton (base + 208) (.SLTU .x10 .x6 .x7)).union
              ((CodeReq.singleton (base + 212) (.SLTU .x13 .x5 .x11)).union
                ((CodeReq.singleton (base + 216) (.SUB .x5 .x5 .x11)).union
                  ((CodeReq.singleton (base + 220) (.OR .x11 .x10 .x13)).union
                    (CodeReq.singleton (base + 224) (.SD .x12 .x5 4080)))))))) := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_subtract_limb2_code
  unfold evm_mulmod_reduce512_inner_step_subtract_limb2
  change CodeReq.ofProg (base + 196)
      [(.LD .x6 .x12 4080), (.LD .x7 .x12 80), (.SUB .x5 .x6 .x7),
       (.SLTU .x10 .x6 .x7), (.SLTU .x13 .x5 .x11), (.SUB .x5 .x5 .x11),
       (.OR .x11 .x10 .x13), (.SD .x12 .x5 4080)] a =
    ((CodeReq.singleton (base + 196) (.LD .x6 .x12 4080)).union
      ((CodeReq.singleton (base + 200) (.LD .x7 .x12 80)).union
        ((CodeReq.singleton (base + 204) (.SUB .x5 .x6 .x7)).union
          ((CodeReq.singleton (base + 208) (.SLTU .x10 .x6 .x7)).union
            ((CodeReq.singleton (base + 212) (.SLTU .x13 .x5 .x11)).union
              ((CodeReq.singleton (base + 216) (.SUB .x5 .x5 .x11)).union
                ((CodeReq.singleton (base + 220) (.OR .x11 .x10 .x13)).union
                  (CodeReq.singleton (base + 224) (.SD .x12 .x5 4080))))))))) a
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 196 : Word) + 4 = base + 200 by bv_addr]
  rw [show (base + 200 : Word) + 4 = base + 204 by bv_addr]
  rw [show (base + 204 : Word) + 4 = base + 208 by bv_addr]
  rw [show (base + 208 : Word) + 4 = base + 212 by bv_addr]
  rw [show (base + 212 : Word) + 4 = base + 216 by bv_addr]
  rw [show (base + 216 : Word) + 4 = base + 220 by bv_addr]
  rw [show (base + 220 : Word) + 4 = base + 224 by bv_addr]

/-- Untouched resources around the limb1 subtract/store block. -/
@[irreducible]
def mulModReduceSubtractLimb1Frame (sp : Word) (r n : EvmWord) : Assertion :=
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Core postcondition for the resources touched by the limb1 block. -/
@[irreducible]
def mulModReduceSubtractLimb1CorePost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb1 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 1) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 1) **
  (.x10 ↦ᵣ mulModReduceSubBorrow1a r n) **
  (.x11 ↦ᵣ mulModReduceSubBorrow1 r n) **
  (.x13 ↦ᵣ mulModReduceSubBorrow1b r n) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ mulModReduceSubLimb1 r n) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1)

/-- Untouched resources around the limb2 subtract/store block. -/
@[irreducible]
def mulModReduceSubtractLimb2Frame (sp : Word) (r n : EvmWord) : Assertion :=
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ mulModReduceSubLimb1 r n) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Core postcondition for the resources touched by the limb2 block. -/
@[irreducible]
def mulModReduceSubtractLimb2CorePost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb2 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 2) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 2) **
  (.x10 ↦ᵣ mulModReduceSubBorrow2a r n) **
  (.x11 ↦ᵣ mulModReduceSubBorrow2 r n) **
  (.x13 ↦ᵣ mulModReduceSubBorrow2b r n) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ mulModReduceSubLimb2 r n) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2)

theorem evm_mulmod_reduce512_inner_step_subtract_limb1_core_spec_within
    (sp base v5 v6 v7 v10 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 8 (base + 164) (base + 196)
      (evm_mulmod_reduce512_inner_step_subtract_limb1_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mulModReduceSubBorrow0 r n) ** (.x13 ↦ᵣ v13) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1))
      (mulModReduceSubtractLimb1CorePost sp r n) := by
  rw [evm_mulmod_reduce512_inner_step_subtract_limb1_code_eq_singletons base]
  unfold mulModReduceSubtractLimb1CorePost
  unfold mulModReduceSubLimb1 mulModReduceSubTemp1 mulModReduceSubBorrow1
    mulModReduceSubBorrow1a mulModReduceSubBorrow1b mulModReduceSubBorrow0
  unfold mulModReduceSubTemp1
  set b0 := (if BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0) then (1 : Word) else 0)
    with hb0
  have I0 := ld_spec_gen_within .x6 .x12 sp v6 (EvmWord.getLimbN r 1) 4072 (base + 164) (by nofun)
  have I1 := ld_spec_gen_within .x7 .x12 sp v7 (EvmWord.getLimbN n 1) 72 (base + 168) (by nofun)
  have I2 := sub_spec_gen_within .x5 .x6 .x7 (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1) v5
    (base + 172) (by nofun)
  have I3 := sltu_spec_gen_within .x10 .x6 .x7 v10 (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)
    (base + 176) (by nofun)
  have I4 := sltu_spec_gen_within .x13 .x5 .x11 v13
    (EvmWord.getLimbN r 1 - EvmWord.getLimbN n 1) b0 (base + 180) (by nofun)
  have I5 := sub_spec_gen_rd_eq_rs1_within .x5 .x11
    (EvmWord.getLimbN r 1 - EvmWord.getLimbN n 1) b0 (base + 184) (by nofun)
  have I6 := or_spec_gen_within .x11 .x10 .x13 b0
    (if BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1) then (1 : Word) else 0)
    (if BitVec.ult (EvmWord.getLimbN r 1 - EvmWord.getLimbN n 1) b0 then (1 : Word) else 0)
    (base + 188) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x5 sp
    (EvmWord.getLimbN r 1 - EvmWord.getLimbN n 1 - b0) (EvmWord.getLimbN r 1) 4072 (base + 192)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

theorem evm_mulmod_reduce512_inner_step_subtract_limb1_spec_within
    (sp base v10 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 8 (base + 164) (base + 196)
      (evm_mulmod_reduce512_inner_step_subtract_limb1_code base)
      (mulModReduceSubtractLimb0Post sp v10 v13 r n)
      (mulModReduceSubtractLimb1Post sp r n) := by
  have hcore := evm_mulmod_reduce512_inner_step_subtract_limb1_core_spec_within
    sp base (mulModReduceSubLimb0 r n) (EvmWord.getLimbN r 0)
    (EvmWord.getLimbN n 0) v10 v13 r n
  have hfr := cpsTripleWithin_frameR
    (mulModReduceSubtractLimb1Frame sp r n)
    (by unfold mulModReduceSubtractLimb1Frame; pcFree) hcore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold mulModReduceSubtractLimb1Frame
      unfold mulModReduceSubtractLimb0Post at hp
      xperm_hyp hp)
    (fun _ hp => by
      unfold mulModReduceSubtractLimb1Post
      unfold mulModReduceSubtractLimb1Frame mulModReduceSubtractLimb1CorePost at hp
      xperm_hyp hp)
    hfr

theorem evm_mulmod_reduce512_inner_step_subtract_limb2_core_spec_within
    (sp base v5 v6 v7 v10 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 8 (base + 196) (base + 228)
      (evm_mulmod_reduce512_inner_step_subtract_limb2_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mulModReduceSubBorrow1 r n) ** (.x13 ↦ᵣ v13) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2))
      (mulModReduceSubtractLimb2CorePost sp r n) := by
  rw [evm_mulmod_reduce512_inner_step_subtract_limb2_code_eq_singletons base]
  unfold mulModReduceSubtractLimb2CorePost
  unfold mulModReduceSubLimb2 mulModReduceSubTemp2 mulModReduceSubBorrow2
    mulModReduceSubBorrow2a mulModReduceSubBorrow2b
  unfold mulModReduceSubTemp2
  set b1 := mulModReduceSubBorrow1 r n with hb1
  have I0 := ld_spec_gen_within .x6 .x12 sp v6 (EvmWord.getLimbN r 2) 4080 (base + 196) (by nofun)
  have I1 := ld_spec_gen_within .x7 .x12 sp v7 (EvmWord.getLimbN n 2) 80 (base + 200) (by nofun)
  have I2 := sub_spec_gen_within .x5 .x6 .x7 (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2) v5
    (base + 204) (by nofun)
  have I3 := sltu_spec_gen_within .x10 .x6 .x7 v10 (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)
    (base + 208) (by nofun)
  have I4 := sltu_spec_gen_within .x13 .x5 .x11 v13
    (EvmWord.getLimbN r 2 - EvmWord.getLimbN n 2) b1 (base + 212) (by nofun)
  have I5 := sub_spec_gen_rd_eq_rs1_within .x5 .x11
    (EvmWord.getLimbN r 2 - EvmWord.getLimbN n 2) b1 (base + 216) (by nofun)
  have I6 := or_spec_gen_within .x11 .x10 .x13 b1
    (if BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2) then (1 : Word) else 0)
    (if BitVec.ult (EvmWord.getLimbN r 2 - EvmWord.getLimbN n 2) b1 then (1 : Word) else 0)
    (base + 220) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x5 sp
    (EvmWord.getLimbN r 2 - EvmWord.getLimbN n 2 - b1) (EvmWord.getLimbN r 2) 4080 (base + 224)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

theorem evm_mulmod_reduce512_inner_step_subtract_limb2_spec_within
    (sp base : Word) (r n : EvmWord) :
    cpsTripleWithin 8 (base + 196) (base + 228)
      (evm_mulmod_reduce512_inner_step_subtract_limb2_code base)
      (mulModReduceSubtractLimb1Post sp r n)
      (mulModReduceSubtractLimb2Post sp r n) := by
  have hcore := evm_mulmod_reduce512_inner_step_subtract_limb2_core_spec_within
    sp base (mulModReduceSubLimb1 r n) (EvmWord.getLimbN r 1)
    (EvmWord.getLimbN n 1) (mulModReduceSubBorrow1a r n)
    (mulModReduceSubBorrow1b r n) r n
  have hfr := cpsTripleWithin_frameR
    (mulModReduceSubtractLimb2Frame sp r n)
    (by unfold mulModReduceSubtractLimb2Frame; pcFree) hcore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold mulModReduceSubtractLimb2Frame
      unfold mulModReduceSubtractLimb1Post at hp
      xperm_hyp hp)
    (fun _ hp => by
      unfold mulModReduceSubtractLimb2Post
      unfold mulModReduceSubtractLimb2Frame mulModReduceSubtractLimb2CorePost at hp
      xperm_hyp hp)
    hfr


/-- The high-limb subtract block as explicit singleton code entries for `runBlock`. -/
theorem evm_mulmod_reduce512_inner_step_subtract_limb3_code_eq_singletons (base : Word) :
    evm_mulmod_reduce512_inner_step_subtract_limb3_code base =
      (CodeReq.singleton (base + 228) (.LD .x6 .x12 4088)).union
        ((CodeReq.singleton (base + 232) (.LD .x7 .x12 88)).union
          ((CodeReq.singleton (base + 236) (.SUB .x5 .x6 .x7)).union
            ((CodeReq.singleton (base + 240) (.SUB .x5 .x5 .x11)).union
              (CodeReq.singleton (base + 244) (.SD .x12 .x5 4088))))) := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_subtract_limb3_code
  unfold evm_mulmod_reduce512_inner_step_subtract_limb3
  change CodeReq.ofProg (base + 228)
      [(.LD .x6 .x12 4088), (.LD .x7 .x12 88), (.SUB .x5 .x6 .x7),
       (.SUB .x5 .x5 .x11), (.SD .x12 .x5 4088)] a =
    ((CodeReq.singleton (base + 228) (.LD .x6 .x12 4088)).union
      ((CodeReq.singleton (base + 232) (.LD .x7 .x12 88)).union
        ((CodeReq.singleton (base + 236) (.SUB .x5 .x6 .x7)).union
          ((CodeReq.singleton (base + 240) (.SUB .x5 .x5 .x11)).union
            (CodeReq.singleton (base + 244) (.SD .x12 .x5 4088)))))) a
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 228 : Word) + 4 = base + 232 by bv_addr]
  rw [show (base + 232 : Word) + 4 = base + 236 by bv_addr]
  rw [show (base + 236 : Word) + 4 = base + 240 by bv_addr]
  rw [show (base + 240 : Word) + 4 = base + 244 by bv_addr]

/-- Untouched resources around the high-limb subtract/store block. -/
@[irreducible]
def mulModReduceSubtractLimb3Frame (sp : Word) (r n : EvmWord) : Assertion :=
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ mulModReduceSubLimb0 r n) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ mulModReduceSubLimb1 r n) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ mulModReduceSubLimb2 r n) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2)

/-- Core postcondition for the resources touched by the high-limb block. -/
@[irreducible]
def mulModReduceSubtractLimb3CorePost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ mulModReduceSubLimb3 r n) **
  (.x6 ↦ᵣ EvmWord.getLimbN r 3) **
  (.x7 ↦ᵣ EvmWord.getLimbN n 3) **
  (.x10 ↦ᵣ mulModReduceSubBorrow2a r n) **
  (.x11 ↦ᵣ mulModReduceSubBorrow2 r n) **
  (.x13 ↦ᵣ mulModReduceSubBorrow2b r n) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ mulModReduceSubLimb3 r n) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

theorem evm_mulmod_reduce512_inner_step_subtract_limb3_core_spec_within
    (sp base v5 v6 v7 : Word) (r n : EvmWord) :
    cpsTripleWithin 5 (base + 228) (base + 248)
      (evm_mulmod_reduce512_inner_step_subtract_limb3_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ mulModReduceSubBorrow2a r n) **
       (.x11 ↦ᵣ mulModReduceSubBorrow2 r n) **
       (.x13 ↦ᵣ mulModReduceSubBorrow2b r n) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3))
      (mulModReduceSubtractLimb3CorePost sp r n) := by
  rw [evm_mulmod_reduce512_inner_step_subtract_limb3_code_eq_singletons base]
  unfold mulModReduceSubtractLimb3CorePost
  unfold mulModReduceSubLimb3 mulModReduceSubTemp3
  set b2 := mulModReduceSubBorrow2 r n with hb2
  have I0 := ld_spec_gen_within .x6 .x12 sp v6 (EvmWord.getLimbN r 3) 4088 (base + 228) (by nofun)
  have I1 := ld_spec_gen_within .x7 .x12 sp v7 (EvmWord.getLimbN n 3) 88 (base + 232) (by nofun)
  have I2 := sub_spec_gen_within .x5 .x6 .x7 (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3) v5
    (base + 236) (by nofun)
  have I3 := sub_spec_gen_rd_eq_rs1_within .x5 .x11
    (EvmWord.getLimbN r 3 - EvmWord.getLimbN n 3) b2 (base + 240) (by nofun)
  have I4 := sd_spec_gen_within .x12 .x5 sp
    (EvmWord.getLimbN r 3 - EvmWord.getLimbN n 3 - b2) (EvmWord.getLimbN r 3) 4088 (base + 244)
  runBlock I0 I1 I2 I3 I4

theorem evm_mulmod_reduce512_inner_step_subtract_limb3_spec_within
    (sp base : Word) (r n : EvmWord) :
    cpsTripleWithin 5 (base + 228) (base + 248)
      (evm_mulmod_reduce512_inner_step_subtract_limb3_code base)
      (mulModReduceSubtractLimb2Post sp r n)
      (mulModReduceSubtractLimb3Post sp r n) := by
  have hcore := evm_mulmod_reduce512_inner_step_subtract_limb3_core_spec_within
    sp base (mulModReduceSubLimb2 r n) (EvmWord.getLimbN r 2)
    (EvmWord.getLimbN n 2) r n
  have hfr := cpsTripleWithin_frameR
    (mulModReduceSubtractLimb3Frame sp r n)
    (by unfold mulModReduceSubtractLimb3Frame; pcFree) hcore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold mulModReduceSubtractLimb3Frame
      unfold mulModReduceSubtractLimb2Post at hp
      xperm_hyp hp)
    (fun _ hp => by
      unfold mulModReduceSubtractLimb3Post
      unfold mulModReduceSubtractLimb3Frame mulModReduceSubtractLimb3CorePost at hp
      xperm_hyp hp)
    hfr

theorem evm_mulmod_reduce512_inner_step_subtract_limb0_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_subtract_limb0_code base a = some i →
      evm_mulmod_reduce512_inner_step_subtract_store_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_subtract_limb0_code
  unfold evm_mulmod_reduce512_inner_step_subtract_store_code
  refine CodeReq.ofProg_mono_sub (base + 144) (base + 144)
    evm_mulmod_reduce512_inner_step_subtract_store
    evm_mulmod_reduce512_inner_step_subtract_limb0 0 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_subtract_limb1_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_subtract_limb1_code base a = some i →
      evm_mulmod_reduce512_inner_step_subtract_store_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_subtract_limb1_code
  unfold evm_mulmod_reduce512_inner_step_subtract_store_code
  refine CodeReq.ofProg_mono_sub (base + 144) (base + 164)
    evm_mulmod_reduce512_inner_step_subtract_store
    evm_mulmod_reduce512_inner_step_subtract_limb1 5 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 5) = (20 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_subtract_limb2_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_subtract_limb2_code base a = some i →
      evm_mulmod_reduce512_inner_step_subtract_store_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_subtract_limb2_code
  unfold evm_mulmod_reduce512_inner_step_subtract_store_code
  refine CodeReq.ofProg_mono_sub (base + 144) (base + 196)
    evm_mulmod_reduce512_inner_step_subtract_store
    evm_mulmod_reduce512_inner_step_subtract_limb2 13 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 13) = (52 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_subtract_limb3_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_subtract_limb3_code base a = some i →
      evm_mulmod_reduce512_inner_step_subtract_store_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_subtract_limb3_code
  unfold evm_mulmod_reduce512_inner_step_subtract_store_code
  refine CodeReq.ofProg_mono_sub (base + 144) (base + 228)
    evm_mulmod_reduce512_inner_step_subtract_store
    evm_mulmod_reduce512_inner_step_subtract_limb3 21 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 21) = (84 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_subtract_limb0_full_code_spec_within
    (sp base v5 v6 v7 v10 v11 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 5 (base + 144) (base + 164)
      (evm_mulmod_reduce512_inner_step_subtract_store_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
       mulModReduceCompareMem sp r n)
      (mulModReduceSubtractLimb0Post sp v10 v13 r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_subtract_limb0_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_subtract_limb0_spec_within
      sp base v5 v6 v7 v10 v11 v13 r n)

theorem evm_mulmod_reduce512_inner_step_subtract_limb1_full_code_spec_within
    (sp base v10 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 8 (base + 164) (base + 196)
      (evm_mulmod_reduce512_inner_step_subtract_store_code base)
      (mulModReduceSubtractLimb0Post sp v10 v13 r n)
      (mulModReduceSubtractLimb1Post sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_subtract_limb1_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_subtract_limb1_spec_within sp base v10 v13 r n)

theorem evm_mulmod_reduce512_inner_step_subtract_limb2_full_code_spec_within
    (sp base : Word) (r n : EvmWord) :
    cpsTripleWithin 8 (base + 196) (base + 228)
      (evm_mulmod_reduce512_inner_step_subtract_store_code base)
      (mulModReduceSubtractLimb1Post sp r n)
      (mulModReduceSubtractLimb2Post sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_subtract_limb2_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_subtract_limb2_spec_within sp base r n)

theorem evm_mulmod_reduce512_inner_step_subtract_limb3_full_code_spec_within
    (sp base : Word) (r n : EvmWord) :
    cpsTripleWithin 5 (base + 228) (base + 248)
      (evm_mulmod_reduce512_inner_step_subtract_store_code base)
      (mulModReduceSubtractLimb2Post sp r n)
      (mulModReduceSubtractLimb3Post sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_subtract_limb3_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_subtract_limb3_spec_within sp base r n)

theorem mulModReduceSubtractPost_of_limb3Post (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceSubtractLimb3Post sp r n h → mulModReduceSubtractPost sp r n h := by
  intro h hp
  unfold mulModReduceSubtractPost mulModReduceSubtractMem
  unfold mulModReduceSubtractLimb3Post at hp
  rw [mulModReduceSub_getLimbN_zero, mulModReduceSub_getLimbN_one,
    mulModReduceSub_getLimbN_two, mulModReduceSub_getLimbN_three]
  xperm_hyp hp

theorem evm_mulmod_reduce512_inner_step_subtract_store_spec_within
    (sp base v5 v6 v7 v10 v11 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 26 (base + 144) (base + 248)
      (evm_mulmod_reduce512_inner_step_subtract_store_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
       mulModReduceCompareMem sp r n)
      (mulModReduceSubtractPost sp r n) := by
  have h0 := evm_mulmod_reduce512_inner_step_subtract_limb0_full_code_spec_within
    sp base v5 v6 v7 v10 v11 v13 r n
  have h1 := evm_mulmod_reduce512_inner_step_subtract_limb1_full_code_spec_within
    sp base v10 v13 r n
  have h2 := evm_mulmod_reduce512_inner_step_subtract_limb2_full_code_spec_within
    sp base r n
  have h3 := evm_mulmod_reduce512_inner_step_subtract_limb3_full_code_spec_within
    sp base r n
  have h01 := cpsTripleWithin_seq_same_cr h0 h1
  have h012 := cpsTripleWithin_seq_same_cr h01 h2
  have h0123 := cpsTripleWithin_seq_same_cr h012 h3
  change cpsTripleWithin (5 + 8 + 8 + 5) (base + 144) (base + 248)
    (evm_mulmod_reduce512_inner_step_subtract_store_code base)
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
     mulModReduceCompareMem sp r n)
    (mulModReduceSubtractPost sp r n)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (mulModReduceSubtractPost_of_limb3Post sp r n)
    h0123

end EvmAsm.Evm64
