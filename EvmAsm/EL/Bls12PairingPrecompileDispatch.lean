/-
  EvmAsm.EL.Bls12PairingPrecompileDispatch

  Pure EVM BLS12-381 pairing precompile framing. Pair validation and pairing
  arithmetic are supplied by the accelerator boundary; this module fixes the
  execution-specs-visible target, invalid-length behavior, payload-dependent
  gas, input slicing, and common precompile result shape.
-/

import EvmAsm.EL.Bls12PairingPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12PairingPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev PairingPair := Bls12PairingInputBridge.PairingPair
abbrev AcceleratorInput := Bls12PairingInputBridge.AcceleratorInput
abbrev AcceleratorResult := Bls12PairingResultBridge.AcceleratorResult

/-- Execution-specs BLS12 pairing consumes 384-byte EVM pair encodings. -/
def pairLength : Nat := 384

/-- The compact accelerator G1 prefix inside each 384-byte EVM pair window. -/
def g1Offset : Nat := 0

/-- The compact accelerator G2 prefix starts after the 128-byte EVM G1 window. -/
def g2Offset : Nat := 128

/-- Safe byte projection. Invalid short inputs are rejected before this is used. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Offset of a compact 96-byte G1 coordinate byte inside a 128-byte EVM G1 point. -/
def compactG1Offset (i : Nat) : Nat :=
  if i < 48 then 16 + i else 32 + i

/-- Offset of a compact 192-byte G2 coordinate byte inside a 256-byte EVM G2 point. -/
def compactG2Offset (i : Nat) : Nat :=
  if i < 48 then
    16 + i
  else if i < 96 then
    32 + i
  else if i < 144 then
    48 + i
  else
    64 + i

/-- Execution-specs length check: `len(data) == 0 or len(data) % 384 != 0`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length != 0 && payload.length % pairLength == 0

/-- Number of BLS12 pairing pairs in a valid payload. -/
def pairCount (payload : List Byte) : Nat :=
  payload.length / pairLength

/-- One compact accelerator G1 point projected from the EVM pair window. -/
def g1Bytes (payload : List Byte) (pairIndex : Nat) : Bls12PairingInputBridge.G1PointBytes :=
  fun i => payloadByte payload (pairLength * pairIndex + g1Offset + compactG1Offset i.val)

/-- One compact accelerator G2 point projected from the EVM pair window. -/
def g2Bytes (payload : List Byte) (pairIndex : Nat) : Bls12PairingInputBridge.G2PointBytes :=
  fun i => payloadByte payload (pairLength * pairIndex + g2Offset + compactG2Offset i.val)

/-- One accelerator pairing pair extracted from the execution-specs EVM pair window. -/
def pairingPair (payload : List Byte) (pairIndex : Nat) : PairingPair :=
  { g1 := g1Bytes payload pairIndex
    g2 := g2Bytes payload pairIndex }

/-- Accelerator input extracted from EVM call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { pairs := (List.range (pairCount payload)).map (pairingPair payload)
    numPairs := pairCount payload }

/-- Osaka BLS12 pairing gas cost: `32600 * k + 37700`. -/
def gasCost (payload : List Byte) : Nat :=
  32600 * pairCount payload + 37700

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BLS12 pairing precompile dispatch.

Execution-specs rejects empty or non-384-multiple inputs before charging gas.
Valid-length inputs charge payload-dependent gas and then the accelerator
boundary handles point decoding, subgroup checks, and the pairing product.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bls12Pairing then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        let request := Bls12PairingEcallBridge.requestFromInput (acceleratorInput input.input)
        let result := Bls12PairingEcallBridge.executeBls12PairingEcall accelerator request
        Bls12PairingPrecompileResultBridge.fromPairingResult (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem pairCount_eq (payload : List Byte) :
    pairCount payload = payload.length / pairLength := rfl

theorem gasCost_eq_formula (payload : List Byte) :
    gasCost payload = 32600 * pairCount payload + 37700 := rfl

theorem validInputLength_empty :
    validInputLength ([] : List Byte) = false := by
  simp [validInputLength]

theorem g1Bytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 96) :
    g1Bytes payload pairIndex i =
      payload.getD (pairLength * pairIndex + compactG1Offset i.val) 0 := by
  simp [g1Bytes, payloadByte, g1Offset]

theorem g2Bytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 192) :
    g2Bytes payload pairIndex i =
      payload.getD (pairLength * pairIndex + 128 + compactG2Offset i.val) 0 := by
  simp [g2Bytes, payloadByte, g2Offset]

theorem pairingPair_g1 (payload : List Byte) (pairIndex : Nat) :
    (pairingPair payload pairIndex).g1 = g1Bytes payload pairIndex := rfl

theorem pairingPair_g2 (payload : List Byte) (pairIndex : Nat) :
    (pairingPair payload pairIndex).g2 = g2Bytes payload pairIndex := rfl

theorem acceleratorInput_numPairs (payload : List Byte) :
    (acceleratorInput payload).numPairs = pairCount payload := rfl

theorem acceleratorInput_pairs_length (payload : List Byte) :
    (acceleratorInput payload).pairs.length = pairCount payload := by
  simp [acceleratorInput]

theorem dispatch_non_bls12Pairing
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bls12Pairing) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12Pairing)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12Pairing)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12Pairing)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bls12PairingPrecompileResultBridge.outputBytesFromResult
          (Bls12PairingEcallBridge.executeBls12PairingEcall accelerator
            (Bls12PairingEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12PairingEcallBridge.requestFromInput,
    Bls12PairingEcallBridge.executeBls12PairingEcall,
    Bls12PairingPrecompileResultBridge.fromPairingResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12Pairing)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 32 := by
  rw [dispatch_success accelerator h_target h_len h_gas h_status]
  simp [Bls12PairingPrecompileResultBridge.outputBytesFromResult_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12Pairing)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12PairingEcallBridge.requestFromInput,
    Bls12PairingEcallBridge.executeBls12PairingEcall,
    Bls12PairingPrecompileResultBridge.fromPairingResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bls12Pairing
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        cases h_status : (Bls12PairingEcallBridge.executeBls12PairingEcall accelerator
          (Bls12PairingEcallBridge.requestFromInput
            (acceleratorInput input.input))).status <;>
          simp [Bls12PairingPrecompileResultBridge.fromPairingResult, h_status,
            EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bls12PairingPrecompileDispatch

end EvmAsm.EL
