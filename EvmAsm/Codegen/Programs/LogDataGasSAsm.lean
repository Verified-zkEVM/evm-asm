/- Byte-identical SAsm specification of `log_data_gas`. -/

import EvmAsm.Codegen.Programs.DynamicOpcodeGas
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace LogDataGasSAsm

/-- Exact RV64 Amsterdam LOG base, topic, and data-byte gas arithmetic. -/
def logDataGas (numTopics dataBytes : Word) : Word :=
  numTopics * 375 + 375 + dataBytes * 8

def logDataGasFn (numTopics dataBytes : Word) : Fn where
  name := "logDataGas"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun rf _ A =>
    rf.get .x10 = numTopics ∧ rf.get .x11 = dataBytes ∧ A = empAssertion
  post := fun rf _ A =>
    rf.get .x10 = logDataGas numTopics dataBytes ∧ A = empAssertion
  body := .block "logDataGas"
    [ .LI .x5 (375 : Word),
      .MUL .x6 .x10 .x5,
      .ADD .x6 .x6 .x5,
      .LI .x7 (8 : Word),
      .MUL .x7 .x11 .x7,
      .ADD .x10 .x6 .x7 ]

theorem logDataGas_byte_tie :
    (logDataGasFn 0 0).body.flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] = logDataGas_prog := by
  rfl

#guard (logDataGasFn 0 0).body.flatten 0 =
  (logDataGasFn 0 0).body.flatten 0x80000000

theorem logDataGasFn_spec (numTopics dataBytes base : Word) :
    (logDataGasFn numTopics dataBytes).Spec base := by
  vcgen
  case logDataGas.post =>
    rintro rf ws A ⟨rf0, ws0, hlen, ⟨hx10, hx11, hA⟩, rfl, rfl⟩
    simp only [logDataGasFn, logDataGas, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, RegFile.get_set_self, RegFile.get_set_ne,
      ne_eq, reduceCtorEq, not_false_eq_true, hx10, hx11]
    constructor <;> trivial

#print axioms logDataGasFn_spec

end LogDataGasSAsm
end EvmAsm.Codegen
