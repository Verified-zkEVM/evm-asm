/-
  EvmAsm.Evm64.AddMod.AddrNormAttr

  Declares the `addmod_addr` simp attribute used by `AddMod/AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code
  should import `AddMod/AddrNorm.lean` (which imports this file) — not this
  file directly.

  Skeleton placeholder for GH #91 (ADDMOD/MULMOD opcodes, beads slice
  evm-asm-w1s0). No tagged lemmas yet; opcode-specific atomic
  `signExtend12` / `<<<` / `BitVec.toNat` evaluations will be attached as
  `@[addmod_addr, grind =]` once the ADDMOD Compose layer starts emitting
  concrete address arithmetic.
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

/-- Simp set for ADDMOD address arithmetic. Will collect atomic evaluations of
    `signExtend12`, `<<<`, and `BitVec.toNat` on concrete literals that arise
    in ADDMOD composition proofs. -/
register_simp_attr addmod_addr
