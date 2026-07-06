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

/-! ## log_data_gas

    `a0 = num_topics, a1 = data_bytes → a0 = OPCODE_LOG_BASE(375)
    + OPCODE_LOG_TOPIC(375)*num_topics + OPCODE_LOG_DATA_PER_BYTE(8)*data_bytes`.
    Pure register arithmetic: `LI;MUL;ADD;LI;MUL;ADD`, ret. -/

/-- Verified port of `log_data_gas`:
    `a0 := (topics * 375 + 375) + (dataBytes * 8)`. -/
def logDataGasFn (topics dataBytes : Word) : Fn where
  name := "logDataGas"
  region := Region.empty
  rw := RwRegion.empty
  pre  := fun rf _ A =>
    rf.get .x10 = topics ∧ rf.get .x11 = dataBytes ∧ A = empAssertion
  post := fun rf _ A =>
    rf.get .x10 = topics * 375 + 375 + dataBytes * 8 ∧ A = empAssertion
  body := .block "body"
    [ .LI .x5 (375 : Word),
      .MUL .x6 .x10 .x5,
      .ADD .x6 .x6 .x5,
      .LI .x7 (8 : Word),
      .MUL .x7 .x11 .x7,
      .ADD .x10 .x6 .x7 ]

/-- The six body instructions match the emitted routine (excluding the
    shared `ret` epilogue). -/
theorem logDataGas_byte_tie :
    (logDataGasFn 0 0).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = logDataGas_prog := rfl

#guard ((logDataGasFn 0 0).body.flatten 0).length = 6

/-- Specification: at every entry state with `a0 = topics`, `a1 = dataBytes`,
    and an empty ambient assertion, the body leaves
    `a0 = (topics * 375 + 375) + (dataBytes * 8)` and the ambient
    assertion empty. -/
theorem logDataGasFn_spec (topics dataBytes : Word) (base : Word) :
    (logDataGasFn topics dataBytes).Spec base := by
  vcgen
  case logDataGas.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, hpre, rfl, rfl⟩
    obtain ⟨hx10, hx11, hA⟩ := hpre
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    refine ⟨?_, hA⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, hx10, hx11]

end GasRoutinesSAsm

end EvmAsm.Codegen
