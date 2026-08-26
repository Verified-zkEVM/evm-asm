/-
  EvmAsm.Evm64.SDiv.AddrNormAttr

  Declares the `sdiv_addr` simp attribute used by `SDiv/AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code
  should import `SDiv/AddrNorm.lean` (which imports this file) — not this
  file directly.

  Skeleton placeholder for GH #90 (SDIV/SMOD opcodes, beads slice
  evm-asm-kyp6). No tagged lemmas yet; opcode-specific atomic
  `signExtend12` / `<<<` / `BitVec.toNat` evaluations will be attached as
  `@[sdiv_addr, grind =]` once the SDIV Compose layer starts emitting
  concrete address arithmetic.
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/-- Simp set for SDIV address arithmetic. Will collect atomic evaluations of
    `signExtend12`, `<<<`, and `BitVec.toNat` on concrete literals that arise
    in SDIV composition proofs. -/
register_simp_attr sdiv_addr
