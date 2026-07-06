/-
  EvmAsm.Evm64.MulMod.Compose.ProductReduceValue

  Value-level restatement of `evm_mulmod_product_reduce_evm_mulmod_spec_within`:
  for **every** positive modulus `n` the result slots hold the EVM `MULMOD`
  result word `BitVec.ofNat 256 (a·b mod n)` rather than the raw
  `mulModReduceOuterFoldCarry` fold. Rewriting via the total bridge
  `mulModReduceOuterFoldCarry_productLimb_eq_evmWord` turns the value form back
  into the carry-aware fold and discharges the goal with the A2 spec. Since the
  reducer is genuinely carry-aware, this carries no `n ≤ 2^255` restriction.
-/

import EvmAsm.Evm64.MulMod.Compose.ProductReduce
import EvmAsm.Evm64.MulMod.ProductLimbsValue

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- Value-level form of `evm_mulmod_product_reduce_evm_mulmod_spec_within`: for
    every positive modulus `n` the result limbs equal those of the EVM `MULMOD`
    result word `BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)` instead of the
    raw carry-aware outer fold. -/
theorem evm_mulmod_product_reduce_value_evm_mulmod_spec_within
    (sp base : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word)
    (hn0 : 0 < n.toNat) :
    cpsTripleWithin (440 + (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1))
      (base + 56) ((base + 1816) + 344) (evm_mulmod_program_code base)
      ((evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
        ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
         (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
         (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old))) **
       ((.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
        regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20))
      (((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
        ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
        regOwn .x9 ** regOwn .x14) **
       ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (((.x5 ↦ᵣ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 3) **
          ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 0) **
          ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 1) **
          ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 2) **
          ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 3) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat)) 3)) **
         (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
           regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
           regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
          limbChain (sp + signExtend12 (3992 : BitVec 12)) (fun i => productLimb a b (7 - i)) 8)))) := by
  rw [← mulModReduceOuterFoldCarry_productLimb_eq_evmWord a b n hn0]
  exact evm_mulmod_product_reduce_evm_mulmod_spec_within sp base a b n
    p0 p1 p2 p3 p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
    v16Old v18Old r0 r1 r2 r3

end EvmAsm.Evm64.MulMod.Compose
