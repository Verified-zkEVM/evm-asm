/-
  EvmAsm.EL.Blake2fPrecompileDispatch

  Pure EVM BLAKE2F precompile framing. The compression result is supplied by
  the zkVM accelerator boundary; this module fixes the execution-specs-visible
  validation, gas charge, input slicing, and returndata shape.
-/

import EvmAsm.EL.Blake2fPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Blake2fPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte

/-- EIP-152 BLAKE2F payload length: rounds(4) || h(64) || m(128) || t(16) || f(1). -/
def inputLength : Nat := 213

def roundsOffset : Nat := 0
def hOffset : Nat := 4
def mOffset : Nat := 68
def tOffset : Nat := 196
def fOffset : Nat := 212

/-- Total byte-length validation from execution-specs `if len(data) != 213`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length == inputLength

/-- Safe byte projection; callers pair it with `validInputLength`. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Execution-specs rounds decoding: `Uint.from_be_bytes(data[:4])`. -/
def roundsNat (payload : List Byte) : Nat :=
  (payloadByte payload roundsOffset).toNat * 16777216 +
  (payloadByte payload (roundsOffset + 1)).toNat * 65536 +
  (payloadByte payload (roundsOffset + 2)).toNat * 256 +
  (payloadByte payload (roundsOffset + 3)).toNat

def roundsUInt32 (payload : List Byte) : UInt32 :=
  UInt32.ofNat (roundsNat payload)

/-- Final-block flag byte at offset 212. -/
def finalFlag (payload : List Byte) : Byte :=
  payloadByte payload fOffset

/-- Execution-specs final flag validation: `if f not in [0, 1]`. -/
def validFinalFlag (payload : List Byte) : Bool :=
  finalFlag payload == 0 || finalFlag payload == 1

/-- Byte-array view of the BLAKE2F state field `h`. -/
def hBytes (payload : List Byte) : Blake2fInputBridge.StateBytes :=
  fun i => payloadByte payload (hOffset + i.val)

/-- Byte-array view of the BLAKE2F message field `m`. -/
def mBytes (payload : List Byte) : Blake2fInputBridge.MessageBytes :=
  fun i => payloadByte payload (mOffset + i.val)

/-- Byte-array view of the BLAKE2F offset-counter field `t`. -/
def tBytes (payload : List Byte) : Blake2fInputBridge.OffsetBytes :=
  fun i => payloadByte payload (tOffset + i.val)

/-- Accelerator input extracted from EVM call data in the execution-specs layout. -/
def acceleratorInput (payload : List Byte) : Blake2fInputBridge.AcceleratorInput :=
  { rounds := roundsUInt32 payload
    h := hBytes payload
    m := mBytes payload
    t := tBytes payload
    f := finalFlag payload }

def gasCost (payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.blake2fGas (roundsNat payload)

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input ≤ input.gas

/--
Pure BLAKE2F precompile dispatch.

Invalid length fails before charging payload-derived gas. A valid-length input
charges `rounds` gas before final-flag validation, matching the execution-specs
order in `forks/*/vm/precompiled_contracts/blake2f.py`.
-/
def dispatch
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .blake2f then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost ≤ input.gas then
        if _h_flag : validFinalFlag input.input then
          let request := Blake2fEcallBridge.requestFromInput (acceleratorInput input.input)
          let result := Blake2fEcallBridge.executeBlake2fEcall accelerator request
          Blake2fPrecompileResultBridge.toPrecompileResult (input.gas - cost) result
        else
          EvmAsm.Evm64.PrecompileResult.fail (input.gas - cost)
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem roundsNat_empty :
    roundsNat ([] : List Byte) = 0 := rfl

theorem gasCost_eq_roundsNat (payload : List Byte) :
    gasCost payload = roundsNat payload := rfl

theorem finalFlag_eq_getD (payload : List Byte) :
    finalFlag payload = payload.getD fOffset 0 := rfl

theorem acceleratorInput_rounds (payload : List Byte) :
    (acceleratorInput payload).rounds = roundsUInt32 payload := rfl

theorem acceleratorInput_f (payload : List Byte) :
    (acceleratorInput payload).f = finalFlag payload := rfl

theorem dispatch_non_blake2f
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .blake2f) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .blake2f)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .blake2f)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input ≤ input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_invalid_final_flag
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .blake2f)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input ≤ input.gas)
    (h_flag : validFinalFlag input.input = false) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_flag]

theorem dispatch_success
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .blake2f)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input ≤ input.gas)
    (h_flag : validFinalFlag input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).1 =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Blake2fResultBridge.outputBytesList
          (accelerator (acceleratorInput input.input)).2)
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_flag,
    Blake2fEcallBridge.requestFromInput,
    Blake2fEcallBridge.executeBlake2fEcall,
    Blake2fPrecompileResultBridge.toPrecompileResult,
    Blake2fPrecompileResultBridge.outputBytes,
    Blake2fEcallBridge.outputBytesList, h_status]

theorem dispatch_success_output_length
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .blake2f)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input ≤ input.gas)
    (h_flag : validFinalFlag input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).1 =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 64 := by
  rw [dispatch_success accelerator h_target h_len h_gas h_flag h_status]
  simp [Blake2fResultBridge.outputBytesList_length]

theorem dispatch_preservesGasBound
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining ≤ input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .blake2f
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input ≤ input.gas
      · simp only [h_gas, ↓reduceDIte]
        by_cases h_flag : validFinalFlag input.input
        · simp only [h_flag, ↓reduceDIte]
          cases h_status : (Blake2fEcallBridge.executeBlake2fEcall accelerator
            (Blake2fEcallBridge.requestFromInput
              (acceleratorInput input.input))).status <;>
            simp [Blake2fPrecompileResultBridge.toPrecompileResult, h_status,
              EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
        · simp [h_flag, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Blake2fPrecompileDispatch

end EvmAsm.EL
