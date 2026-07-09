/-
  EvmAsm.Codegen.Programs.CallExtraGasSAsm

  Verified SAsm port of the CALL/CALLCODE extra-gas helper. The body is
  byte-identical to `callExtraGas_prog`: initialize warm access cost, overwrite
  it for cold account access, optionally add the value-transfer cost, and return
  the result in `a0`.
-/

import EvmAsm.Codegen.Programs.EvmMessageCallGas
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace CallExtraGasSAsm

/-- The CALL-family extra-gas helper:
    `a0 = isCold`, `a1 = valueNonzero` ->
    `a0 = (isCold ? 2600 : 100) + (valueNonzero ? 9000 : 0)`. -/
def callExtraGasFn (isCold valueNonzero : Word) : Fn where
  name := "callExtraGas"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun rf _ A =>
    rf.get .x10 = isCold ∧ rf.get .x11 = valueNonzero ∧ A = empAssertion
  post := fun rf _ A =>
    rf.get .x10 = (if isCold = 0 then 100 else 2600)
        + (if valueNonzero = 0 then 0 else 9000)
      ∧ A = empAssertion
  body :=
    .block "warm" [ .ADDI .x5 .x0 (100 : BitVec 12) ] ;;;
    .when "cold" (.bne .x10 .x0)
      (.block "cold" [ .LUI .x5 (1 : BitVec 20),
        .ADDIW .x5 .x5 (-1496 : BitVec 12) ]) ;;;
    .when "value" (.bne .x11 .x0)
      (.block "value" [ .LUI .x6 (2 : BitVec 20),
        .ADDIW .x6 .x6 (808 : BitVec 12), .ADD .x5 .x5 .x6 ]) ;;;
    .block "out" [ .MV .x10 .x5 ]

/-- The structured body flattens to the emitted helper body, excluding the
    shared `ret` epilogue. -/
theorem callExtraGas_byte_tie :
    (callExtraGasFn 0 0).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = callExtraGas_prog := rfl

#guard ((callExtraGasFn 0 0).body.flatten 0).length = 9

/-- Specification: the helper returns the Amsterdam CALL-family access cost plus
    the value-transfer cost selected by the two input flags. -/
theorem callExtraGasFn_spec (isCold valueNonzero : Word) (base : Word) :
    (callExtraGasFn isCold valueNonzero).Spec base := by
  vcgen
  case callExtraGas.post =>
    intro rf ws A hsp
    simp only [callExtraGasFn, sp] at hsp ⊢
    rcases hsp with ⟨rfBeforeOut, wsBeforeOut, hlenOut, hreachValue, rfl, rfl⟩
    rcases hreachValue with hValue | hNoValue
    · rcases hValue with ⟨rfBeforeValue, wsBeforeValue, hlenValue, hreachCold, rfl, rfl⟩
      rcases hreachCold with hCold | hWarm
      · rcases hCold with ⟨rfEntry, wsEntry, hlenCold, hpreCold, rfl, rfl⟩
        rcases hpreCold with ⟨hreachWarm, h_is_cold⟩
        rcases hreachWarm with ⟨rf0, ws0, hlen0, hpre0, hrfEntry, hws⟩
        subst rfEntry
        subst ws
        simp_all [Cond.holds, execBlock, execInstrRF, aluSem]
        try decide
      · rcases hWarm with ⟨hreachWarm, h_not_cold⟩
        rcases hreachWarm with ⟨rfEntry, wsEntry, hlenWarm, hpreWarm, rfl, rfl⟩
        simp_all [Cond.holds, execInstrRF, aluSem]
        try decide
    · rcases hNoValue with ⟨hreachNoValue, h_not_value⟩
      rcases hreachNoValue with hCold | hWarm
      · rcases hCold with ⟨rfEntry, wsEntry, hlenCold, hpreCold, rfl, rfl⟩
        rcases hpreCold with ⟨hreachWarm, h_is_cold⟩
        rcases hreachWarm with ⟨rf0, ws0, hlen0, hpre0, hrfEntry, hws⟩
        subst rfEntry
        subst ws
        simp_all [Cond.holds, execBlock, execInstrRF, aluSem]
        try decide
      · rcases hWarm with ⟨hreachWarm, h_not_cold⟩
        rcases hreachWarm with ⟨rfEntry, wsEntry, hlenWarm, hpreWarm, rfl, rfl⟩
        simp_all [Cond.holds, execInstrRF, aluSem]
        try decide

#print axioms callExtraGasFn_spec

end CallExtraGasSAsm
end EvmAsm.Codegen
