/- Byte-identical SAsm specification of `keccak256_word_gas`. -/

import EvmAsm.Codegen.Programs.DynamicOpcodeGas
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Keccak256WordGasSAsm

/-- Exact RV64 arithmetic performed by the Amsterdam KECCAK256 dynamic-gas
    leaf, including machine-word wrapping. -/
def keccak256WordGas (size : Word) : Word := ((size + 31) >>> 5) * 6 + 30

def keccak256WordGasFn (size : Word) : Fn where
  name := "keccak256WordGas"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun rf _ A => rf.get .x10 = size ∧ A = empAssertion
  post := fun rf _ A => rf.get .x10 = keccak256WordGas size ∧ A = empAssertion
  body := .block "keccak256WordGas"
    [ .ADDI .x5 .x10 (31 : BitVec 12),
      .SRLI .x5 .x5 (5 : BitVec 6),
      .LI .x6 (6 : Word),
      .MUL .x5 .x5 .x6,
      .ADDI .x10 .x5 (30 : BitVec 12) ]

theorem keccak256WordGas_byte_tie :
    (keccak256WordGasFn 0).body.flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] = keccak256WordGas_prog := by
  rfl

#guard (keccak256WordGasFn 0).body.flatten 0 =
  (keccak256WordGasFn 0).body.flatten 0x80000000

theorem keccak256WordGasFn_spec (size base : Word) :
    (keccak256WordGasFn size).Spec base := by
  vcgen
  case keccak256WordGas.post =>
    rintro rf ws A ⟨rf0, ws0, hlen, ⟨hx10, hA⟩, rfl, rfl⟩
    simp only [keccak256WordGasFn, keccak256WordGas, execBlock_cons,
      execBlock_nil, execInstrRF, aluSem, RegFile.get_set_self,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    constructor
    · congr 1
    · exact hA

#print axioms keccak256WordGasFn_spec

end Keccak256WordGasSAsm
end EvmAsm.Codegen
