/-
  EvmAsm.Evm64.MulMod.AddrNormAttr

  Declares the `mulmod_addr` simp attribute used by `MulMod/AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code
  should import `MulMod/AddrNorm.lean` (which imports this file) — not this
  file directly.

  Skeleton placeholder for GH #91 (MULMOD/MULMOD opcodes, beads slice
  evm-asm-w1s0). No tagged lemmas yet; opcode-specific atomic
  `signExtend12` / `<<<` / `BitVec.toNat` evaluations will be attached as
  `@[mulmod_addr, grind =]` once the MULMOD Compose layer starts emitting
  concrete address arithmetic.
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

/-- Simp set for MULMOD address arithmetic. Will collect atomic evaluations of
    `signExtend12`, `<<<`, and `BitVec.toNat` on concrete literals that arise
    in MULMOD composition proofs. -/
register_simp_attr mulmod_addr
