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
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.MultiDword

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

/-! ## init_code_cost

    `a0 = init_code_length, a1 = gas_per_word, a2 = u64 out ptr →
    a0 = 0` with `*a2 = gas_per_word * ((a0 + 31) >>> 5)` (EIP-3860).
    Pure register arithmetic plus one dword store through a one-cell
    writable window: `ADDI;SRLI;MUL;SD;LI`, ret. -/

/-- Verified port of `init_code_cost`:
    `*outPtr := gasPerWord * ((len + 31) >>> 5); a0 := 0`. -/
def initCodeCostFn (len gasPerWord outPtr : Word) : Fn where
  name := "initCodeCost"
  region := Region.empty
  rw := ⟨outPtr, 8⟩
  pre  := fun rf _ A =>
    rf.get .x10 = len ∧ rf.get .x11 = gasPerWord ∧ rf.get .x12 = outPtr
      ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = 0 ∧ rf.get .x12 = outPtr
      ∧ ws = dwordBytes (((len + 31) >>> 5) * gasPerWord) ∧ A = empAssertion
  body := .block "body"
    [ .ADDI .x5 .x10 (31 : BitVec 12),
      .SRLI .x5 .x5 (5 : BitVec 6),
      .MUL .x5 .x5 .x11,
      .SD .x12 .x5 (0 : BitVec 12),
      .LI .x10 (0 : Word) ]

/-- The five body instructions match the emitted routine (excluding the
    shared `ret` epilogue). -/
theorem initCodeCost_byte_tie :
    (initCodeCostFn 0 0 0).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = initCodeCost_prog := rfl

#guard ((initCodeCostFn 0 0 0).body.flatten 0).length = 5

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- Specification: at every entry state with `a0 = len`, `a1 = gasPerWord`,
    `a2 = outPtr` (8-aligned, valid), and an empty ambient assertion, the
    body stores `gasPerWord * ((len + 31) >>> 5)` to `*outPtr` and leaves
    `a0 = 0`, the ambient assertion empty. -/
theorem initCodeCostFn_spec (len gasPerWord outPtr : Word) (base : Word)
    (hwf : RwRegion.wf ⟨outPtr, 8⟩) :
    (initCodeCostFn len gasPerWord outPtr).Spec base := by
  have hidx : ∀ rf : RegFile, rf.get .x12 = outPtr →
      ((rf.get .x12 + signExtend12 (0 : BitVec 12)) - outPtr).toNat = 0 := by
    intro rf h
    rw [h, se12_0]; bv_omega
  have hrwbase : (initCodeCostFn len gasPerWord outPtr).rw.base = outPtr := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case initCodeCost.body.mem =>
    rintro rf ws A hws hpre
    have hws8 : ws.length = 8 := hws
    obtain ⟨hx10, hx11, hx12, -⟩ := hpre
    have h5 : (5 : BitVec 6).toNat = 5 := by decide
    simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, inRw,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, hrwbase, se12_0, h5, hx10, hx11, hx12,
      show ws.length = 8 from hws8]
    refine ⟨trivial, trivial, trivial, ?_, trivial, trivial⟩
    have hzero : (outPtr + (0 : Word) - outPtr).toNat = 0 := by bv_omega
    rw [hzero]; exact ⟨by omega, by decide⟩
  case initCodeCost.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, hpre, rfl, rfl⟩
    obtain ⟨hx10, hx11, hx12, hA⟩ := hpre
    have hws8 : ws₀.length = 8 := hws₀
    have h5 : (5 : BitVec 6).toNat = 5 := by decide
    refine ⟨?_, ?_, ?_, hA⟩
    · -- rf'.get .x10 = 0: the last LI set it
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
        storeSem, initCodeCostFn, RegFile.get_set_self, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, se12_0, se12_31, h5, hx10, hx11]
    · -- rf'.get .x12 = outPtr: no instruction writes x12
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
        storeSem, initCodeCostFn, RegFile.get_set_self, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, se12_0, se12_31, h5, hx10,
        hx11, hx12]
    · -- ws' = dwordBytes (((len+31)>>>5)*gasPerWord)
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
        storeSem, initCodeCostFn, RegFile.get_set_self, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, se12_0, se12_31, h5, hx10,
        hx11, hx12]
      have hzero : (outPtr + (0 : Word) - outPtr).toNat = 0 := by bv_omega
      rw [hzero, setBytes_dword_full ws₀ _ hws8]

end GasRoutinesSAsm

end EvmAsm.Codegen
