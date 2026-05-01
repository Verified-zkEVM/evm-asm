/-
  EvmAsm.Evm64.DivMod.AddrNormSmokeTests

  Smoke tests for issue #263 slice 2: prove a representative sample of the
  one-off address-equality lemmas catalogued in
  `docs/263-addr-norm-inventory.md` directly with the `divmod_addr` tactic.
  This guards against silent gaps in the `@[divmod_addr]` grindset and
  documents the canonical shapes that the migration in slice 6
  (evm-asm-1ew6 / future) will rely on.

  Each smoke test below mirrors a real lemma from the audit; the comment
  before each block names the source file. None of these should require
  more than `divmod_addr` (which is `grind` first, `simp; bv_omega` fallback).

  This file declares no `theorem` exported to other modules; everything is
  `example`-style so the file can be touched freely.
-/

import EvmAsm.Evm64.DivMod.AddrNorm

namespace EvmAsm.Evm64.DivMod.AddrNormSmokeTests

open EvmAsm.Rv64

-- ============================================================================
-- Compose/FullPathN1Loop.lean shape: {0,4032,4056} & {<<<3} (n1_ub3_off0)
-- ============================================================================
example {sp : Word} :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) =
      sp + signExtend12 4032 := by
  divmod_addr

-- Compose/FullPathN2Loop.lean shape: {0,4040,4056} (n2_ub2_off0)
example {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) =
      sp + signExtend12 4040 := by
  divmod_addr

-- Compose/FullPathN3Loop.lean shape: {4080,4088} (n3_qa1)
example {sp : Word} :
    sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat =
      sp + signExtend12 4080 := by
  divmod_addr

-- Compose/FullPathN3Loop.lean shape: {4088} only (n3_qa0 — k=0 no-op)
example {sp : Word} :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat =
      sp + signExtend12 4088 := by
  divmod_addr

-- Compose/FullPathN4Loop.lean shape: {4056} (u_base_j0 — k=0 no-op)
example {sp : Word} :
    sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat =
      sp + signExtend12 4056 := by
  divmod_addr

-- Compose/FullPathN4Loop.lean shape: {4024,4056,4064} (u_base_off4064_j0)
example {sp : Word} :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4064 =
      sp + signExtend12 4024 := by
  divmod_addr

-- LoopBodyN1.lean shape: {0,4056,4088} (u_addr_eq_n1)
example {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4088 =
      (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4080 := by
  divmod_addr

-- LoopBodyN2.lean shape: {4056,4080,4088} (u_addr_eq_n2)
example {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4088 =
      (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4080 := by
  divmod_addr

-- LoopBodyN3.lean shape: {4056,4072,4080} (u_addr_eq_n3)
example {sp : Word} :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4080 =
      (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4072 := by
  divmod_addr

-- LoopBodyN4.lean shape: {4056,4064,4072} (u_addr_eq_n4)
example {sp : Word} :
    (sp + signExtend12 4056 - (4 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4072 =
      (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4064 := by
  divmod_addr

-- LoopBodyN1.lean shape with extra +32 slot: {0,32,4056,4088} (u_addr8_eq_n1)
example {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4088 + signExtend12 32 =
      (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4080 + signExtend12 32 := by
  divmod_addr

-- LoopComposeN{1,2,3}.lean shape: {0,4056,4088} (u_*_j*_0_eq_j*_4088)
example {sp : Word} :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 0 =
      (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
        signExtend12 4088 := by
  divmod_addr

-- ============================================================================
-- Loop counter / j positivity / j-pred shapes (covered by the @[divmod_addr]
-- entries `slt_jpos_*` and `jpred_*` in `AddrNorm.lean`).
-- ============================================================================

example : BitVec.slt ((1 : Word) + signExtend12 4095) 0 = false := by divmod_addr
example : BitVec.slt ((2 : Word) + signExtend12 4095) 0 = false := by divmod_addr
example : BitVec.slt ((3 : Word) + signExtend12 4095) 0 = false := by divmod_addr
example : (1 : Word) + signExtend12 4095 = (0 : Word) := by divmod_addr
example : (2 : Word) + signExtend12 4095 = (1 : Word) := by divmod_addr
example : (3 : Word) + signExtend12 4095 = (2 : Word) := by divmod_addr

end EvmAsm.Evm64.DivMod.AddrNormSmokeTests
