/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

  Lifts n=3 two-iteration loop compositions from sharedDivModCode to divCode,
  and composes with the pre-loop (base → base+448) to produce
  preloop+loop specs (base → base+904).
-/

-- `LoopUnifiedN3` transitively imports `LoopComposeN3`.
import EvmAsm.Evm64.DivMod.LoopUnifiedN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address normalization lemmas for n=3 preloop+loop composition
-- ============================================================================

/-- signExtend12(4) - 3 = 1, for x1 register in loopSetupPost at n=3. -/
theorem x1_val_n3 : signExtend12 (4 : BitVec 12) - (3 : Word) = (1 : Word) := by decide

-- se12_32, se12_40, se12_48, se12_56 are in Base.lean

-- Address normalization: signExtend12/<<</>> → concrete values via simp, then bv_omega.
-- bv_addr only handles (a+k1)+k2=a+k3; these involve subtraction and shifts.
-- Pattern matches LoopComposeN3.lean.
theorem n3_ub1_off0 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4048 := by
  divmod_addr
theorem n3_ub1_off4088 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4040 := by
  divmod_addr
theorem n3_ub1_off4080 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4032 := by
  divmod_addr
theorem n3_ub1_off4072 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4024 := by
  divmod_addr
theorem n3_ub1_off4064 {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4016 := by
  divmod_addr
theorem n3_ub0_off0 {sp : Word} :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4056 := by
  divmod_addr
theorem n3_qa1 {sp : Word} :
    sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4080 := by
  divmod_addr
theorem n3_qa0 {sp : Word} :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  divmod_addr
-- ============================================================================
-- Lift unified n=3  loop from sharedDivModCode to divCode
-- ============================================================================

/-- Lift the unified n=3 2-iteration  loop spec from sharedDivModCode to divCode. -/
theorem divK_loop_n3_unified_divCode (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN3 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3UnifiedPost bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode)
    (divK_loop_n3_unified_spec bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_1 hbltu_0 hcarry2)
