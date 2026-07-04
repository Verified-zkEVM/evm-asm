/-
  EvmAsm.Codegen.Proofs.U256IsZeroSpec

  Deployed spec for `u256_is_zero` (bead evm-asm-4ch8f.13.5): the
  converted `u256IsZero_prog` (EvmAsm/Codegen/Programs/U256.lean, wave
  1a; correspondence `u256IsZeroFunction_eq_prog`) computes
  `a0 = 1` iff the 32 bytes at the input pointer are all zero.

  ABI (U256.lean doc): a0 = u256 ptr (32B, dword-aligned via the ↦ₘ
  atoms), ra = return; result in a0; clobbers t0/t1/t2/t3
  (x5/x6/x7/x28). Leaf-callable, data-independent timing (no
  short-circuit).

  This file is also the acceptance test of the port playbook
  (docs/agents/port-playbook.md) run end-to-end: scaffold via
  scripts/gen-port-kit.py (already-converted detection), exemplar
  Add/LimbSpec + CallReturn, gate via scripts/port-check.sh.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-- `u256_is_zero` deployed spec: loads the four dwords at
    `ptr/+8/+16/+24`, ORs them into `x5`, and returns
    `x10 = (if the OR is < 1 then 1 else 0)` through `ra`.
    Memory is untouched; `x6/x7/x28` end holding the loaded limbs. -/
theorem u256_is_zero_deployed_spec (base ptr ra v5 v6 v7 v28 w0 w1 w2 w3 : Word) :
    cpsTripleWithin 9 base (ra &&& ~~~1) (CodeReq.ofProg base u256IsZero_prog)
      ((.x10 ↦ᵣ ptr) ** (.x1 ↦ᵣ ra) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) ** ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3))
      ((.x10 ↦ᵣ (if BitVec.ult (w0 ||| w1 ||| w2 ||| w3) 1 then (1 : Word) else 0)) **
       (.x1 ↦ᵣ ra) **
       (.x5 ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) ** (.x6 ↦ᵣ w1) ** (.x7 ↦ᵣ w2) ** (.x28 ↦ᵣ w3) **
       (ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) ** ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) := by
  have L0 := ld_spec_gen_within .x5 .x10 ptr v5 w0 0 base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x10 ptr v6 w1 8 (base + 4) (by nofun)
  have L2 := ld_spec_gen_within .x7 .x10 ptr v7 w2 16 (base + 8) (by nofun)
  have L3 := ld_spec_gen_within .x28 .x10 ptr v28 w3 24 (base + 12) (by nofun)
  have O1 := or_spec_gen_rd_eq_rs1_within .x5 .x6 w0 w1 (base + 16) (by nofun)
  have O2 := or_spec_gen_rd_eq_rs1_within .x5 .x7 (w0 ||| w1) w2 (base + 20) (by nofun)
  have O3 := or_spec_gen_rd_eq_rs1_within .x5 .x28 (w0 ||| w1 ||| w2) w3 (base + 24) (by nofun)
  have SL := sltiu_spec_gen_within .x10 .x5 ptr (w0 ||| w1 ||| w2 ||| w3) 1 (base + 28) (by nofun)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at SL
  have R := EvmAsm.Evm64.ret_spec_within' (base + 32) ra
  -- runBlock can't extend singleton specs to `CodeReq.ofProg <list-literal def>`
  -- directly (leaves unsynthesized frame placeholders); unfold to the union
  -- chain first. Recorded in docs/agents/port-playbook.md pitfalls.
  simp only [u256IsZero_prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  runBlock L0 L1 L2 L3 O1 O2 O3 SL R

/-- The result register is the is-zero indicator: `ult orAll 1` is
    exactly `orAll = 0`, and the four-dword OR vanishes iff every limb
    does. Domain-facing corollary shape for consumers. -/
theorem u256_is_zero_result_eq (w0 w1 w2 w3 : Word) :
    (if BitVec.ult (w0 ||| w1 ||| w2 ||| w3) 1 then (1 : Word) else 0)
      = (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then (1 : Word) else 0) := by
  have hult : ∀ v : Word, BitVec.ult v 1 = decide (v = 0) := fun v => by
    simp only [BitVec.ult, show (1 : Word).toNat = 1 from rfl, Nat.lt_one_iff]
    exact decide_eq_decide.mpr
      ⟨fun h => BitVec.eq_of_toNat_eq (by simp [h]), fun h => by simp [h]⟩
  rw [hult]
  simp [BitVec.or_eq_zero_iff, and_assoc]

end EvmAsm.Codegen.Proofs
