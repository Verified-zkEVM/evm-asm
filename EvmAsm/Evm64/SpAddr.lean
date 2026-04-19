/-
  EvmAsm.Evm64.SpAddr

  Shared helper lemmas for flattening `(sp + 32) + K` address expressions that
  appear in EvmWord-level stack specs. Every two-input 256-bit opcode (ADD,
  SUB, AND, OR, XOR, LT, GT, SLT, SGT, EQ) sits at stack offset `sp + 32` for
  its second operand, so its `evmWordIs (sp + 32) b` post expands to
  `(sp + 32) ↦ₘ b0`, `(sp + 32 + 8) ↦ₘ b1`, `(sp + 32 + 16) ↦ₘ b2`,
  `(sp + 32 + 24) ↦ₘ b3`. Normalising those four addresses to
  `sp + {32,40,48,56}` used to be a three-line `have : ... := by bv_omega`
  + `rw [‹...›]` dance repeated twice (pre-condition + post-condition) in every
  stack spec — ten files, ~20 sites, most of them identical.

  These named rewrites replace the inline dance. They are not tagged as simp
  lemmas so simp normal form remains unchanged; call sites reference them
  explicitly via `rw [spAddr32_8, spAddr32_16, spAddr32_24]`.

  Issue #263.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.Tactics.SeqFrame

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

theorem spAddr32_8  (sp : Word) : sp + 32 + 8  = sp + 40 := by bv_addr
theorem spAddr32_16 (sp : Word) : sp + 32 + 16 = sp + 48 := by bv_addr
theorem spAddr32_24 (sp : Word) : sp + 32 + 24 = sp + 56 := by bv_addr

/-- Third-slot siblings of `spAddr32_*`: flatten `(sp + 64) + {8,16,24}` →
    `sp + {72,80,88}`. Parallel to the `(sp + 32) + …` family above but for
    the third operand of ternary 256-bit opcodes (ADDMOD / MULMOD),
    which lives at stack offset `sp + 64`. Also covers the internal
    address bumps `evmWordIs_sp64_unfold` needs. -/
theorem spAddr64_8  (sp : Word) : sp + 64 + 8  = sp + 72 := by bv_addr
theorem spAddr64_16 (sp : Word) : sp + 64 + 16 = sp + 80 := by bv_addr
theorem spAddr64_24 (sp : Word) : sp + 64 + 24 = sp + 88 := by bv_addr

end EvmAsm.Evm64
