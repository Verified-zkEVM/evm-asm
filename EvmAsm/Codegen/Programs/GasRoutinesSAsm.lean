/-
  EvmAsm.Codegen.Programs.GasRoutinesSAsm

  Verified SAsm ports of the straight-line dynamic-gas leaves (bead
  evm-asm-4ch8f): pure `a0 → a0` register arithmetic, no memory, no
  loops, no calls.  Each routine pins `x10_out` to the exact closed form
  the 4–7 body instructions compute (a genuine functional spec, not a
  tautology), and the body's flat instruction list is byte-identical to
  the emitted guest program — so these are spec-only drop-ins (no EEST
  A/B, no re-emit).
-/

import EvmAsm.Codegen.Programs.DynamicOpcodeGas
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace GasRoutinesSAsm

/-! ## copy_word_gas

    `a0 = size_bytes → a0 = OPCODE_COPY_PER_WORD(3) * ceil32(size) // 32`,
    with `ceil32(size) // 32 = (size + 31) >>> 5`.  Pure register
    arithmetic: `ADDI; SRLI; LI; MUL`, ret. -/

/-- Verified port of `copy_word_gas`: `a0 := 3 * ((a0 + 31) >>> 5)`. -/
def copyWordGasFn (len : Word) : Fn where
  name := "copyWordGas"
  region := Region.empty
  rw := RwRegion.empty
  pre  := fun rf _ A => rf.get .x10 = len ∧ A = empAssertion
  post := fun rf _ A =>
    rf.get .x10 = ((len + 31) >>> 5) * 3 ∧ A = empAssertion
  body := .block "body"
    [ .ADDI .x5 .x10 (31 : BitVec 12),
      .SRLI .x5 .x5 (5 : BitVec 6),
      .LI .x6 (3 : Word),
      .MUL .x10 .x5 .x6 ]

/-- The four body instructions match the emitted routine (excluding the
    shared `ret` epilogue). -/
theorem copyWordGas_byte_tie :
    (copyWordGasFn 0).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = copyWordGas_prog := rfl

#guard ((copyWordGasFn 0).body.flatten 0).length = 4

private theorem se12_31 : signExtend12 (31 : BitVec 12) = (31 : Word) := by decide

/-- Specification: at every entry state with `a0 = len` and an empty
    ambient assertion, the body leaves `a0 = 3 * ((len + 31) >>> 5)` and
    the ambient assertion empty. -/
theorem copyWordGasFn_spec (len : Word) (base : Word) :
    (copyWordGasFn len).Spec base := by
  vcgen
  case copyWordGas.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, hpre, rfl, rfl⟩
    obtain ⟨hx10, hA⟩ := hpre
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    refine ⟨?_, hA⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, hx10, se12_31,
      show (5 : BitVec 6).toNat = 5 from by decide]

end GasRoutinesSAsm

end EvmAsm.Codegen
