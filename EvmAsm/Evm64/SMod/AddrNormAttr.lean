/-
  EvmAsm.Evm64.SMod.AddrNormAttr

  Declares the `smod_addr` simp attribute used by `SMod/AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code
  should import `SMod/AddrNorm.lean` (which imports this file) — not this
  file directly.

  Skeleton placeholder for GH #90 (SDIV/SMOD opcodes, beads slice
  evm-asm-kyp6). No tagged lemmas yet; opcode-specific atomic
  `signExtend12` / `<<<` / `BitVec.toNat` evaluations will be attached as
  `@[smod_addr, grind =]` once the SMOD Compose layer starts emitting
  concrete address arithmetic.
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

/-- Simp set for SMOD address arithmetic. Will collect atomic evaluations of
    `signExtend12`, `<<<`, and `BitVec.toNat` on concrete literals that arise
    in SMOD composition proofs. -/
register_simp_attr smod_addr
