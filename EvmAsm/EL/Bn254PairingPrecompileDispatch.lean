/-
  EvmAsm.EL.Bn254PairingPrecompileDispatch

  Pure EVM BN254 pairing precompile framing. Pair decoding and pairing checks
  are supplied by the accelerator boundary; this module fixes the
  execution-specs-visible target, gas, length validation, pair slicing, and
  common precompile result shape.
-/

import EvmAsm.EL.Bn254PrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bn254PairingPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev PairingPair := Bn254PairingInputBridge.PairingPair
abbrev AcceleratorInput := Bn254PairingInputBridge.AcceleratorInput
abbrev AcceleratorResult := Bn254PairingResultBridge.AcceleratorResult

/-- BN254 pairing consumes 192-byte G1/G2 pairs. -/
def pairLength : Nat := 192

def g1Offset : Nat := 0
def g2Offset : Nat := 64

def pairingBaseGas : Nat := 45000
def pairingPerPairGas : Nat := 34000

/-- Safe byte projection; short calldata is zero-padded like execution-specs `buffer_read`. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Number of complete 192-byte pairs used by execution-specs gas charging. -/
def numPairs (payload : List Byte) : Nat :=
  payload.length / pairLength

/-- Execution-specs length validity: pairing input must be a multiple of 192 bytes. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length % pairLength == 0

/-- G1 point for pair `pairIndex`, read from the 64-byte window at pair start. -/
def g1Bytes (payload : List Byte) (pairIndex : Nat) : Bn254PairingInputBridge.G1PointBytes :=
  fun i => payloadByte payload (pairLength * pairIndex + g1Offset + i.val)

/-- G2 point for pair `pairIndex`, read from the 128-byte window after the G1 point. -/
def g2Bytes (payload : List Byte) (pairIndex : Nat) : Bn254PairingInputBridge.G2PointBytes :=
  fun i => payloadByte payload (pairLength * pairIndex + g2Offset + i.val)

/-- One accelerator pairing pair extracted from EVM call data. -/
def pairingPair (payload : List Byte) (pairIndex : Nat) : PairingPair :=
  { g1 := g1Bytes payload pairIndex
    g2 := g2Bytes payload pairIndex }

/-- Accelerator input extracted from complete EVM call-data pairs. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { pairs := (List.range (numPairs payload)).map (pairingPair payload)
    numPairs := numPairs payload }

/-- Execution-specs BN254 pairing gas formula. -/
def gasCost (payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .bn254Pairing payload.length |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BN254 pairing precompile dispatch.

Execution-specs charges `45000 + 34000 * (len / 192)`, rejects non-multiple
lengths after that charge, then invokes the pairing check over complete pairs.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bn254Pairing then
    let cost := gasCost input.input
    if _h_gas : cost <= input.gas then
      if _h_len : validInputLength input.input then
        let request := Bn254PairingEcallBridge.requestFromInput (acceleratorInput input.input)
        let result := Bn254PairingEcallBridge.executeBn254PairingEcall accelerator request
        Bn254PrecompileResultBridge.fromPairingResult (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail (input.gas - cost)
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_formula (payload : List Byte) :
    gasCost payload = pairingBaseGas + pairingPerPairGas * numPairs payload := by
  simp [gasCost, pairingBaseGas, pairingPerPairGas, numPairs, pairLength,
    EvmAsm.Evm64.Precompile.precompileGasCost?, EvmAsm.Evm64.Precompile.gasSchedule,
    EvmAsm.Evm64.Precompile.pairingPairs]

theorem validInputLength_iff (payload : List Byte) :
    validInputLength payload = true <-> payload.length % pairLength = 0 := by
  simp [validInputLength]

theorem acceleratorInput_numPairs (payload : List Byte) :
    (acceleratorInput payload).numPairs = numPairs payload := rfl

theorem acceleratorInput_pairs_length (payload : List Byte) :
    (acceleratorInput payload).pairs.length = numPairs payload := by
  simp [acceleratorInput]

theorem g1Bytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 64) :
    g1Bytes payload pairIndex i = payload.getD (pairLength * pairIndex + i.val) 0 := by
  simp [g1Bytes, payloadByte, g1Offset]

theorem g2Bytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 128) :
    g2Bytes payload pairIndex i = payload.getD (pairLength * pairIndex + 64 + i.val) 0 := by
  simp [g2Bytes, payloadByte, g2Offset]

theorem dispatch_non_bn254Pairing
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bn254Pairing) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Pairing)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_not]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Pairing)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas, h_len]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Pairing)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bn254PrecompileResultBridge.pairingOutputBytesFromResult
          (Bn254PairingEcallBridge.executeBn254PairingEcall accelerator
            (Bn254PairingEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas, h_len,
    Bn254PairingEcallBridge.requestFromInput,
    Bn254PairingEcallBridge.executeBn254PairingEcall,
    Bn254PrecompileResultBridge.fromPairingResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Pairing)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 32 := by
  rw [dispatch_success accelerator h_target h_gas h_len h_status]
  simp [Bn254PrecompileResultBridge.pairingOutputBytesFromResult_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Pairing)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas, h_len,
    Bn254PairingEcallBridge.requestFromInput,
    Bn254PairingEcallBridge.executeBn254PairingEcall,
    Bn254PrecompileResultBridge.fromPairingResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bn254Pairing
  · simp only [h_target, ↓reduceDIte]
    by_cases h_gas : gasCost input.input <= input.gas
    · simp only [h_gas, ↓reduceDIte]
      by_cases h_len : validInputLength input.input
      · simp only [h_len, ↓reduceDIte]
        cases h_status : (Bn254PairingEcallBridge.executeBn254PairingEcall accelerator
          (Bn254PairingEcallBridge.requestFromInput
            (acceleratorInput input.input))).status <;>
          simp [Bn254PrecompileResultBridge.fromPairingResult, h_status,
            EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bn254PairingPrecompileDispatch

end EvmAsm.EL
