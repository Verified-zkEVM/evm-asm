/-
  EvmAsm.Stateless.VM.Precompiles

  Dispatch and pure framing helpers for precompile addresses
  (0x01..0x14 + 0x100 for P256VERIFY).

  ## Implementation status

  Per the project plan (see `~/.claude/plans/please-cut-a-branch-warm-wand.md`
  and `PLAN.md` "Stateless Guest"), precompile dispatch started as
  an unimplemented frontier:

  - ECRECOVER, SHA-256, RIPEMD-160, IDENTITY, MODEXP
  - ALT_BN128 ADD / MUL / PAIRING (BN254)
  - BLAKE2F
  - POINT_EVALUATION (EIP-4844 KZG)
  - BLS12-381 G1/G2 ADD/MSM, PAIRING, MAP
  - SECP256R1_VERIFY (P256)

  Unsupported concrete call sites still trigger `REASON_PRECOMPILE + addr`
  per the reason-code table in `Stateless/Unimplemented.lean`. Implemented
  slices in this file expose pure EVM return-data/gas framing first, then
  later CALL/STATICCALL wiring can call those helpers.

  ## What's NOT in this file

  Hashes needed for **block processing** (KECCAK256 for header
  hashing, MPT, code hashing, tx hashing, address derivation;
  SHA-256 for SSZ Merkleization of the output) are bridged
  separately and do NOT route through this file. They live in
  `EvmAsm/EL/Keccak*EcallBridge.lean` (existing) and
  `EvmAsm/Stateless/Bridges/Sha256EcallBridge.lean` (scaffolded
  in PR-K12). See `docs/execution-specs-feedback.md` #1 for the
  cost-picture discussion.

-/

import EvmAsm.EL.Bn254G1AddEcallBridge
import EvmAsm.EL.Bn254G1MulEcallBridge
import EvmAsm.EL.Bn254PairingEcallBridge
import EvmAsm.EL.Bls12G1MsmEcallBridge
import EvmAsm.EL.Bls12G2MsmEcallBridge
import EvmAsm.EL.Bls12PairingEcallBridge
import EvmAsm.EL.Bls12MapFpToG1EcallBridge
import EvmAsm.EL.Bls12MapFp2ToG2EcallBridge
import EvmAsm.EL.Bls12G1AddEcallBridge
import EvmAsm.EL.Bls12G2AddEcallBridge
import EvmAsm.EL.KzgPointEvalEcallBridge
import EvmAsm.EL.ModexpEcallBridge
import EvmAsm.EL.Secp256r1VerifyEcallBridge

namespace EvmAsm.Stateless.VM.Precompiles

abbrev Byte := EvmAsm.EL.Byte
abbrev ByteList := List Byte
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

namespace BN254

/-- Gas constants for the BN254 precompiles at a fork. -/
structure GasSchedule where
  ecadd : Nat
  ecmul : Nat
  pairingBase : Nat
  pairingPerPoint : Nat
  deriving Repr

/-- Byzantium gas schedule from execution-specs. -/
def byzantiumGasSchedule : GasSchedule :=
  { ecadd := 500
    ecmul := 40000
    pairingBase := 100000
    pairingPerPoint := 80000 }

/-- Istanbul-and-later gas schedule, still current in Osaka/BPO forks. -/
def currentGasSchedule : GasSchedule :=
  { ecadd := 150
    ecmul := 6000
    pairingBase := 45000
    pairingPerPoint := 34000 }

/-- BN254 G1 addition precompile address. -/
def addAddress : Nat := 0x06

/-- BN254 G1 scalar multiplication precompile address. -/
def mulAddress : Nat := 0x07

/-- BN254 pairing precompile address. -/
def pairingAddress : Nat := 0x08

/-- BN254 add reads two 64-byte G1 points, with EVM `buffer_read` zero padding. -/
def addInputLength : Nat := 128

/-- BN254 mul reads one 64-byte G1 point and one 32-byte scalar. -/
def mulInputLength : Nat := 96

/-- BN254 pairing consumes 192-byte G1/G2 pairs. -/
def pairingPairLength : Nat := 192

/-- `U256(1).to_be_bytes32()`. -/
def successWordOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]

/-- `U256(0).to_be_bytes32()`. -/
def zeroWordOutput : ByteList :=
  List.replicate 32 (0 : Byte)

/-- Invalid point, malformed pairing length, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

structure Result where
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

namespace Add

abbrev MemoryReader := EvmAsm.EL.Bn254G1AddInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bn254G1AddInputBridge.AcceleratorInput
abbrev AcceleratorOutput := EvmAsm.EL.Bn254G1AddResultBridge.AcceleratorOutput

def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bn254G1AddInputBridge.bn254G1AddInputFromMemory
    memory dataStart (dataStart + 64)

def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) : Result :=
  let result := accelerator (acceleratorInputFromCallData memory dataStart)
  match result.1 with
  | .eok =>
      { status := result.1
        output := EvmAsm.EL.Bn254G1AddResultBridge.outputBytesList result.2
        gasCharged := schedule.ecadd }
  | .efail =>
      { status := result.1, output := emptyOutput, gasCharged := schedule.ecadd }

@[simp] theorem execute_status
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).1 := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 <;>
    simp [execute, h_status]

@[simp] theorem execute_output_eok
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 = .eok) :
    (execute schedule accelerator memory dataStart).output =
      EvmAsm.EL.Bn254G1AddResultBridge.outputBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).2 := by
  simp [execute, h_status]

@[simp] theorem execute_output_efail
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 = .efail) :
    (execute schedule accelerator memory dataStart).output = emptyOutput := by
  simp [execute, h_status]

@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).gasCharged = schedule.ecadd := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 <;>
    simp [execute, h_status]

end Add

namespace Mul

abbrev MemoryReader := EvmAsm.EL.Bn254G1MulInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bn254G1MulInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bn254G1MulResultBridge.AcceleratorResult

def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bn254G1MulInputBridge.bn254G1MulInputFromMemory
    memory dataStart (dataStart + 64)

def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) : Result :=
  let result := accelerator (acceleratorInputFromCallData memory dataStart)
  match result.status with
  | .eok =>
      { status := result.status
        output := EvmAsm.EL.Bn254G1MulResultBridge.g1PointBytesList result.output.point
        gasCharged := schedule.ecmul }
  | .efail =>
      { status := result.status, output := emptyOutput, gasCharged := schedule.ecmul }

@[simp] theorem execute_status
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, h_status]

@[simp] theorem execute_output_eok
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute schedule accelerator memory dataStart).output =
      EvmAsm.EL.Bn254G1MulResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, h_status]

@[simp] theorem execute_output_efail
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute schedule accelerator memory dataStart).output = emptyOutput := by
  simp [execute, h_status]

@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).gasCharged = schedule.ecmul := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, h_status]

end Mul

namespace Pairing

abbrev MemoryReader := EvmAsm.EL.Bn254PairingInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bn254PairingInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bn254PairingResultBridge.AcceleratorResult

def numPairs (dataLength : Nat) : Nat :=
  dataLength / pairingPairLength

def gasCharged (schedule : GasSchedule) (dataLength : Nat) : Nat :=
  schedule.pairingBase + schedule.pairingPerPoint * numPairs dataLength

def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  EvmAsm.EL.Bn254PairingInputBridge.bn254PairingInputFromMemory
    memory dataStart (numPairs dataLength)

def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successWordOutput else zeroWordOutput

def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength % pairingPairLength = 0 then
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := accelerator input
    match result.status with
    | .eok =>
        { status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCharged schedule dataLength }
    | .efail =>
        { status := result.status
          output := emptyOutput
          gasCharged := gasCharged schedule dataLength }
  else
    { status := .efail
      output := emptyOutput
      gasCharged := gasCharged schedule dataLength }

@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successWordOutput := rfl

@[simp] theorem outputFromVerified_false :
    outputFromVerified false = zeroWordOutput := rfl

@[simp] theorem execute_badLength
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength % pairingPairLength ≠ 0) :
    execute schedule accelerator memory dataStart dataLength =
      { status := .efail
        output := emptyOutput
        gasCharged := gasCharged schedule dataLength } := by
  simp [execute, h_length]

@[simp] theorem execute_status_validLength
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength % pairingPairLength = 0) :
    (execute schedule accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_length, h_status]

@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute schedule accelerator memory dataStart dataLength).gasCharged =
      gasCharged schedule dataLength := by
  by_cases h_length : dataLength % pairingPairLength = 0
  · cases h_status :
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
      simp [execute, h_length, h_status]
  · simp [execute, h_length]

end Pairing

theorem successWordOutput_length :
    successWordOutput.length = 32 := by
  simp [successWordOutput]

theorem zeroWordOutput_length :
    zeroWordOutput.length = 32 := by
  simp [zeroWordOutput]

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

end BN254

namespace Modexp

abbrev AcceleratorInput := EvmAsm.EL.ModexpInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.ModexpResultBridge.AcceleratorResult

/-- MODEXP precompile address. -/
def address : Nat := 0x05

/-- Osaka/EIP-7823 maximum byte length for base, exponent, and modulus. -/
def maxComponentLength : Nat := 1024

/-- MODEXP call-data header size: base length, exponent length, modulus length. -/
def headerLength : Nat := 96

/-- Executable-spec `buffer_read(data, start, size)` with zero padding. -/
def bufferRead (data : ByteList) (start size : Nat) : ByteList :=
  (List.range size).map fun i =>
    match data[start + i]? with
    | some b => b
    | none => 0

/-- Decode a big-endian unsigned integer from a byte list. -/
def natFromBytesBE (bytes : ByteList) : Nat :=
  EvmAsm.EL.RLP.Nat.fromBytesBE bytes

/-- Read a 32-byte big-endian length field from MODEXP call data. -/
def readLength (data : ByteList) (offset : Nat) : Nat :=
  natFromBytesBE (bufferRead data offset 32)

def baseLength (data : ByteList) : Nat :=
  readLength data 0

def exponentLength (data : ByteList) : Nat :=
  readLength data 32

def modulusLength (data : ByteList) : Nat :=
  readLength data 64

def exponentStart (data : ByteList) : Nat :=
  headerLength + baseLength data

def modulusStart (data : ByteList) : Nat :=
  exponentStart data + exponentLength data

def exponentHead (data : ByteList) : Nat :=
  natFromBytesBE (bufferRead data (exponentStart data) (min 32 (exponentLength data)))

/-- EIP-2565/Osaka multiplication complexity. -/
def complexity (baseLen modulusLen : Nat) : Nat :=
  let maxLen := max baseLen modulusLen
  let words := (maxLen + 7) / 8
  if maxLen > 32 then 2 * words * words else 16

/-- EIP-2565/Osaka adjusted exponent iteration count. -/
def iterations (exponentLen exponentHead : Nat) : Nat :=
  let count :=
    if exponentLen ≤ 32 ∧ exponentHead = 0 then
      0
    else if exponentLen ≤ 32 then
      exponentHead.log2
    else
      16 * (exponentLen - 32) + exponentHead.log2
  max count 1

/-- Osaka MODEXP gas cost from execution-specs `modexp.gas_cost`. -/
def gasCost (baseLen modulusLen exponentLen exponentHead : Nat) : Nat :=
  max 500 (complexity baseLen modulusLen * iterations exponentLen exponentHead)

def gasCostFromCallData (data : ByteList) : Nat :=
  gasCost (baseLength data) (modulusLength data) (exponentLength data) (exponentHead data)

def componentLengthsValid (data : ByteList) : Prop :=
  baseLength data ≤ maxComponentLength ∧
  exponentLength data ≤ maxComponentLength ∧
  modulusLength data ≤ maxComponentLength

def componentLengthsValidBool (data : ByteList) : Bool :=
  baseLength data ≤ maxComponentLength &&
  exponentLength data ≤ maxComponentLength &&
  modulusLength data ≤ maxComponentLength

def acceleratorInputFromCallData (data : ByteList) : AcceleratorInput :=
  { base := bufferRead data headerLength (baseLength data)
    exp := bufferRead data (exponentStart data) (exponentLength data)
    modulus := bufferRead data (modulusStart data) (modulusLength data) }

/-- Result surface exposed to the caller by the pure MODEXP framing layer.

`exceptional = true` represents Osaka's pre-gas length-cap halt. Otherwise
`gasCharged` is the decoded MODEXP gas cost and `output` is the precompile
return data. -/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

def exceptionalResult : Result :=
  { exceptional := true
    status := .efail
    output := []
    gasCharged := 0 }

def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList) : Result :=
  if componentLengthsValidBool data then
    let gas := gasCostFromCallData data
    if baseLength data = 0 ∧ modulusLength data = 0 then
      { exceptional := false
        status := .eok
        output := []
        gasCharged := gas }
    else
      let result := EvmAsm.EL.ModexpEcallBridge.executeModexpEcall accelerator
        (EvmAsm.EL.ModexpEcallBridge.requestFromInput
          (acceleratorInputFromCallData data))
      match result.status with
      | .eok =>
          { exceptional := false
            status := result.status
            output := result.output.bytes
            gasCharged := gas }
      | .efail =>
          { exceptional := false
            status := result.status
            output := []
            gasCharged := gas }
  else
    exceptionalResult

@[simp] theorem bufferRead_length (data : ByteList) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead]

@[simp] theorem bufferRead_zero (data : ByteList) (start : Nat) :
    bufferRead data start 0 = [] := rfl

theorem acceleratorInputFromCallData_base_length (data : ByteList) :
    (acceleratorInputFromCallData data).base.length = baseLength data := by
  simp [acceleratorInputFromCallData]

theorem acceleratorInputFromCallData_exp_length (data : ByteList) :
    (acceleratorInputFromCallData data).exp.length = exponentLength data := by
  simp [acceleratorInputFromCallData]

theorem acceleratorInputFromCallData_modulus_length (data : ByteList) :
    (acceleratorInputFromCallData data).modulus.length = modulusLength data := by
  simp [acceleratorInputFromCallData]

@[simp] theorem complexity_small (baseLen modulusLen : Nat)
    (h_max : max baseLen modulusLen ≤ 32) :
    complexity baseLen modulusLen = 16 := by
  simp [complexity, Nat.not_lt.mpr h_max]

@[simp] theorem iterations_zero_head (exponentLen : Nat)
    (h_len : exponentLen ≤ 32) :
    iterations exponentLen 0 = 1 := by
  simp [iterations, h_len]

theorem gasCost_minimum (baseLen modulusLen exponentLen exponentHead : Nat) :
    500 ≤ gasCost baseLen modulusLen exponentLen exponentHead := by
  simp [gasCost]

theorem gasCost_zero_lengths :
    gasCost 0 0 0 0 = 500 := rfl

theorem gasCost_one_byte_small_exp :
    gasCost 1 1 1 1 = 500 := rfl

@[simp] theorem execute_badLengths
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList)
    (h_valid : componentLengthsValidBool data = false) :
    execute accelerator data = exceptionalResult := by
  simp [execute, h_valid]

@[simp] theorem execute_zero_base_zero_modulus
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList)
    (h_valid : componentLengthsValidBool data = true)
    (h_base : baseLength data = 0)
    (h_modulus : modulusLength data = 0) :
    execute accelerator data =
      { exceptional := false
        status := .eok
        output := []
        gasCharged := gasCostFromCallData data } := by
  simp [execute, h_valid, h_base, h_modulus]

@[simp] theorem execute_gasCharged_valid
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList)
    (h_valid : componentLengthsValidBool data = true) :
    (execute accelerator data).gasCharged = gasCostFromCallData data := by
  by_cases h_zero : baseLength data = 0 ∧ modulusLength data = 0
  · simp [execute, h_valid, h_zero.1, h_zero.2]
  · have h_not : ¬ (baseLength data = 0 ∧ modulusLength data = 0) := h_zero
    cases h_status :
        (EvmAsm.EL.ModexpEcallBridge.executeModexpEcall accelerator
          (EvmAsm.EL.ModexpEcallBridge.requestFromInput
            (acceleratorInputFromCallData data))).status <;>
      simp [execute, h_valid, h_not, h_status]

end Modexp

namespace BLS12

namespace G1Msm

abbrev MemoryReader := EvmAsm.EL.Bls12G1MsmInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bls12G1MsmInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bls12G1MsmResultBridge.AcceleratorResult

/-- EVM precompile address for BLS12-381 G1 MSM. -/
def address : Nat := 0x0c

/-- Osaka executable-spec G1 MSM call-data item width: 128-byte G1 plus 32-byte scalar. -/
def lengthPerPair : Nat := 160

/-- Osaka executable-spec `GasCosts.PRECOMPILE_BLS_G1MUL`. -/
def g1MulGas : Nat := 12000

/-- Osaka executable-spec BLS discount multiplier. -/
def multiplier : Nat := 1000

/-- Osaka executable-spec max discount for G1 MSM with more than 128 pairs. -/
def g1MaxDiscount : Nat := 519

/-- Osaka executable-spec `G1_K_DISCOUNT`, indexed by `k - 1` for `1 <= k <= 128`. -/
def g1KDiscount : List Nat :=
  [ 1000, 949, 848, 797, 764, 750, 738, 728
  , 719, 712, 705, 698, 692, 687, 682, 677
  , 673, 669, 665, 661, 658, 654, 651, 648
  , 645, 642, 640, 637, 635, 632, 630, 627
  , 625, 623, 621, 619, 617, 615, 613, 611
  , 609, 608, 606, 604, 603, 601, 599, 598
  , 596, 595, 593, 592, 591, 589, 588, 586
  , 585, 584, 582, 581, 580, 579, 577, 576
  , 575, 574, 573, 572, 570, 569, 568, 567
  , 566, 565, 564, 563, 562, 561, 560, 559
  , 558, 557, 556, 555, 554, 553, 552, 551
  , 550, 549, 548, 547, 547, 546, 545, 544
  , 543, 542, 541, 540, 540, 539, 538, 537
  , 536, 536, 535, 534, 533, 532, 532, 531
  , 530, 529, 528, 528, 527, 526, 525, 525
  , 524, 523, 522, 522, 521, 520, 520, 519 ]

/-- Invalid length or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure BLS12-381 G1 MSM framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

def numPairs (dataLength : Nat) : Nat :=
  dataLength / lengthPerPair

def validInputLength (dataLength : Nat) : Bool :=
  dataLength != 0 && dataLength % lengthPerPair == 0

def validInputLengthBool (dataLength : Nat) : Bool :=
  validInputLength dataLength

def discount (k : Nat) : Nat :=
  if k = 0 then
    0
  else if k <= 128 then
    g1KDiscount.getD (k - 1) g1MaxDiscount
  else
    g1MaxDiscount

def gasCharged (dataLength : Nat) : Nat :=
  let k := numPairs dataLength
  k * g1MulGas * discount k / multiplier

def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  EvmAsm.EL.Bls12G1MsmInputBridge.bls12G1MsmInputFromMemory
    memory dataStart (numPairs dataLength)

def exceptionalResult : Result :=
  { exceptional := true
    status := .efail
    output := emptyOutput
    gasCharged := 0 }

/--
Pure BLS12-381 G1 MSM precompile framing. This owns the EVM-side Osaka length
and gas rules, then delegates curve arithmetic to the supplied accelerator.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if validInputLengthBool dataLength then
    let gas := gasCharged dataLength
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall accelerator
      (EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G1MsmResultBridge.g1PointBytesList result.output.point
          gasCharged := gas }
    | .efail =>
        { exceptional := false
          status := result.status
          output := emptyOutput
          gasCharged := gas }
  else
    exceptionalResult

theorem g1KDiscount_length :
    g1KDiscount.length = 128 := by
  set_option maxRecDepth 1000 in decide

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem validInputLengthBool_zero :
    validInputLengthBool 0 = false := by
  simp [validInputLengthBool, validInputLength]

@[simp] theorem validInputLengthBool_bad_mod
    (dataLength : Nat) (h_mod : dataLength % lengthPerPair ≠ 0) :
    validInputLengthBool dataLength = false := by
  simp [validInputLengthBool, validInputLength, h_mod]

@[simp] theorem numPairs_lengthPerPair_mul (k : Nat) :
    numPairs (lengthPerPair * k) = k := by
  simp [numPairs, lengthPerPair]

@[simp] theorem discount_zero :
    discount 0 = 0 := by
  simp [discount]

@[simp] theorem discount_le_128
    (k : Nat) (h_pos : k ≠ 0) (h_le : k <= 128) :
    discount k = g1KDiscount.getD (k - 1) g1MaxDiscount := by
  simp [discount, h_pos, h_le]

@[simp] theorem discount_gt_128
    (k : Nat) (h_gt : Not (k <= 128)) :
    discount k = g1MaxDiscount := by
  have h_pos : k ≠ 0 := by
    intro h_zero
    exact h_gt (by simp [h_zero])
  simp [discount, h_pos, h_gt]

@[simp] theorem gasCharged_valid_pairs (k : Nat) :
    gasCharged (lengthPerPair * k) = k * g1MulGas * discount k / multiplier := by
  simp [gasCharged]

@[simp] theorem acceleratorInputFromCallData_numPairs
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (acceleratorInputFromCallData memory dataStart dataLength).numPairs =
      numPairs dataLength := by
  simp [acceleratorInputFromCallData,
    EvmAsm.EL.Bls12G1MsmInputBridge.bls12G1MsmInputFromMemory_numPairs]

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = false) :
    execute accelerator memory dataStart dataLength = exceptionalResult := by
  simp [execute, h_valid]

@[simp] theorem execute_status_validLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true) :
    (execute accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_valid, h_status,
      EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
      EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output =
      EvmAsm.EL.Bls12G1MsmResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).output.point := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
    EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .efail) :
    (execute accelerator memory dataStart dataLength).output = emptyOutput := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
    EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if validInputLengthBool dataLength then gasCharged dataLength else 0 := by
  by_cases h_valid : validInputLengthBool dataLength
  . cases h_status :
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
      simp [execute, h_valid, h_status,
        EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
        EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]
  . simp [execute, exceptionalResult, h_valid]

end G1Msm

namespace G2Msm

abbrev MemoryReader := EvmAsm.EL.Bls12G2MsmInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bls12G2MsmInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bls12G2MsmResultBridge.AcceleratorResult

/-- EVM precompile address for BLS12-381 G2 MSM. -/
def address : Nat := 0x0e

/-- Osaka executable-spec G2 MSM call-data item width: 256-byte G2 plus 32-byte scalar. -/
def lengthPerPair : Nat := 288

/-- Osaka executable-spec `GasCosts.PRECOMPILE_BLS_G2MUL`. -/
def g2MulGas : Nat := 22500

/-- Osaka executable-spec BLS discount multiplier. -/
def multiplier : Nat := 1000

/-- Osaka executable-spec max discount for G2 MSM with more than 128 pairs. -/
def g2MaxDiscount : Nat := 524

/-- Osaka executable-spec `G2_K_DISCOUNT`, indexed by `k - 1` for `1 <= k <= 128`. -/
def g2KDiscount : List Nat :=
  [ 1000, 1000, 923, 884, 855, 832, 812, 796
  , 782, 770, 759, 749, 740, 732, 724, 717
  , 711, 704, 699, 693, 688, 683, 679, 674
  , 670, 666, 663, 659, 655, 652, 649, 646
  , 643, 640, 637, 634, 632, 629, 627, 624
  , 622, 620, 618, 615, 613, 611, 609, 607
  , 606, 604, 602, 600, 598, 597, 595, 593
  , 592, 590, 589, 587, 586, 584, 583, 582
  , 580, 579, 578, 576, 575, 574, 573, 571
  , 570, 569, 568, 567, 566, 565, 563, 562
  , 561, 560, 559, 558, 557, 556, 555, 554
  , 553, 552, 552, 551, 550, 549, 548, 547
  , 546, 545, 545, 544, 543, 542, 541, 541
  , 540, 539, 538, 537, 537, 536, 535, 535
  , 534, 533, 532, 532, 531, 530, 530, 529
  , 528, 528, 527, 526, 526, 525, 524, 524 ]

/-- Invalid length or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure BLS12-381 G2 MSM framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

def numPairs (dataLength : Nat) : Nat :=
  dataLength / lengthPerPair

def validInputLength (dataLength : Nat) : Bool :=
  dataLength != 0 && dataLength % lengthPerPair == 0

def validInputLengthBool (dataLength : Nat) : Bool :=
  validInputLength dataLength

def discount (k : Nat) : Nat :=
  if k = 0 then
    0
  else if k <= 128 then
    g2KDiscount.getD (k - 1) g2MaxDiscount
  else
    g2MaxDiscount

def gasCharged (dataLength : Nat) : Nat :=
  let k := numPairs dataLength
  k * g2MulGas * discount k / multiplier

def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  EvmAsm.EL.Bls12G2MsmInputBridge.bls12G2MsmInputFromMemory
    memory dataStart (numPairs dataLength)

def exceptionalResult : Result :=
  { exceptional := true
    status := .efail
    output := emptyOutput
    gasCharged := 0 }

/--
Pure BLS12-381 G2 MSM precompile framing. This owns the EVM-side Osaka length
and gas rules, then delegates curve arithmetic to the supplied accelerator.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if validInputLengthBool dataLength then
    let gas := gasCharged dataLength
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall accelerator
      (EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G2MsmResultBridge.g2PointBytesList result.output.point
          gasCharged := gas }
    | .efail =>
        { exceptional := false
          status := result.status
          output := emptyOutput
          gasCharged := gas }
  else
    exceptionalResult

theorem g2KDiscount_length :
    g2KDiscount.length = 128 := by
  set_option maxRecDepth 1000 in decide

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem validInputLengthBool_zero :
    validInputLengthBool 0 = false := by
  simp [validInputLengthBool, validInputLength]

@[simp] theorem validInputLengthBool_bad_mod
    (dataLength : Nat) (h_mod : dataLength % lengthPerPair ≠ 0) :
    validInputLengthBool dataLength = false := by
  simp [validInputLengthBool, validInputLength, h_mod]

@[simp] theorem numPairs_lengthPerPair_mul (k : Nat) :
    numPairs (lengthPerPair * k) = k := by
  simp [numPairs, lengthPerPair]

@[simp] theorem discount_zero :
    discount 0 = 0 := by
  simp [discount]

@[simp] theorem discount_le_128
    (k : Nat) (h_pos : k ≠ 0) (h_le : k <= 128) :
    discount k = g2KDiscount.getD (k - 1) g2MaxDiscount := by
  simp [discount, h_pos, h_le]

@[simp] theorem discount_gt_128
    (k : Nat) (h_gt : Not (k <= 128)) :
    discount k = g2MaxDiscount := by
  have h_pos : k ≠ 0 := by
    intro h_zero
    exact h_gt (by simp [h_zero])
  simp [discount, h_pos, h_gt]

@[simp] theorem gasCharged_valid_pairs (k : Nat) :
    gasCharged (lengthPerPair * k) = k * g2MulGas * discount k / multiplier := by
  simp [gasCharged]

@[simp] theorem acceleratorInputFromCallData_numPairs
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (acceleratorInputFromCallData memory dataStart dataLength).numPairs =
      numPairs dataLength := by
  simp [acceleratorInputFromCallData,
    EvmAsm.EL.Bls12G2MsmInputBridge.bls12G2MsmInputFromMemory_numPairs]

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = false) :
    execute accelerator memory dataStart dataLength = exceptionalResult := by
  simp [execute, h_valid]

@[simp] theorem execute_status_validLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true) :
    (execute accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_valid, h_status,
      EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
      EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output =
      EvmAsm.EL.Bls12G2MsmResultBridge.g2PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).output.point := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
    EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .efail) :
    (execute accelerator memory dataStart dataLength).output = emptyOutput := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
    EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if validInputLengthBool dataLength then gasCharged dataLength else 0 := by
  by_cases h_valid : validInputLengthBool dataLength
  · cases h_status :
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
      simp [execute, h_valid, h_status,
        EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
        EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]
  · simp [execute, exceptionalResult, h_valid]

end G2Msm

namespace Pairing

abbrev MemoryReader := EvmAsm.EL.Bls12PairingInputBridge.MemoryReader
abbrev PairingPair := EvmAsm.EL.Bls12PairingInputBridge.PairingPair
abbrev AcceleratorInput := EvmAsm.EL.Bls12PairingInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bls12PairingResultBridge.AcceleratorResult
abbrev G1PointBytes := EvmAsm.EL.Bls12PairingInputBridge.G1PointBytes
abbrev G2PointBytes := EvmAsm.EL.Bls12PairingInputBridge.G2PointBytes

/-- EVM precompile address for BLS12-381 pairing. -/
def address : Nat := 0x0f

/-- BLS12 pairing consumes one 128-byte G1 point and one 256-byte G2 point per pair. -/
def pairLength : Nat := 384

/-- Osaka executable-spec BLS12 pairing base gas. -/
def baseGas : Nat := 37700

/-- Osaka executable-spec BLS12 pairing per-pair gas. -/
def perPairGas : Nat := 32600

/-- BLS12 pairing returns a 32-byte boolean word on successful accelerator execution. -/
def successWordOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]

/-- BLS12 pairing false result word. -/
def zeroWordOutput : ByteList :=
  List.replicate 32 (0 : Byte)

/-- Invalid length, invalid points, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/-- Number of pairing pairs in a valid EVM BLS12 pairing call payload. -/
def numPairs (dataLength : Nat) : Nat :=
  dataLength / pairLength

/-- Osaka executable-spec gas formula: `32600 * k + 37700`. -/
def gasCostFromLength (dataLength : Nat) : Nat :=
  perPairGas * numPairs dataLength + baseGas

/-- EVM-side validity guard: pairing input must be nonempty and divisible by 384. -/
def inputLengthValid (dataLength : Nat) : Bool :=
  dataLength != 0 && dataLength % pairLength == 0

/--
Result surface exposed by the pure BLS12-381 pairing framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/-- Drop the 16-byte EIP-2537 field-element padding and keep the 48-byte Fp payload. -/
def fpPayloadFromEvmField (memory : MemoryReader) (fieldStart : Nat) : Fin 48 → Byte :=
  fun i => memory (fieldStart + 16 + i.toNat)

/-- Convert a 128-byte EIP-2537 G1 point into the accelerator's 96-byte G1 payload. -/
def g1PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G1PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else
      memory (pointStart + 64 + 16 + (n - 48))

/-- Convert a 256-byte EIP-2537 G2 point into the accelerator's 192-byte G2 payload. -/
def g2PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G2PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else if n < 96 then
      memory (pointStart + 64 + 16 + (n - 48))
    else if n < 144 then
      memory (pointStart + 128 + 16 + (n - 96))
    else
      memory (pointStart + 192 + 16 + (n - 144))

/-- Read one EIP-2537 BLS12 pairing pair: 128-byte G1 followed by 256-byte G2. -/
def pairingPairFromEvmBytes (memory : MemoryReader) (pairStart : Nat) : PairingPair :=
  { g1 := g1PointFromEvmBytes memory pairStart
    g2 := g2PointFromEvmBytes memory (pairStart + 128) }

/-- Read `numPairs` consecutive 384-byte EIP-2537 BLS12 pairing pairs. -/
def pairingPairsFromEvmBytes
    (memory : MemoryReader) (pairsStart numPairs : Nat) : List PairingPair :=
  (List.range numPairs).map
    (fun i => pairingPairFromEvmBytes memory (pairsStart + pairLength * i))

/--
Build the accelerator input from EVM call data after the executable-spec length
check. Point/subgroup validation and pairing arithmetic are supplied by the
accelerator model.
-/
def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  { pairs := pairingPairsFromEvmBytes memory dataStart (numPairs dataLength)
    numPairs := numPairs dataLength }

/-- Convert the accelerator boolean into the EVM 32-byte return word. -/
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successWordOutput else zeroWordOutput

/--
Pure BLS12-381 pairing precompile framing. This models the executable-spec
length guard, gas formula, accelerator call, and 32-byte boolean output.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = 0 then
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }
  else if dataLength % pairLength = 0 then
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall accelerator
      (EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCostFromLength dataLength }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCostFromLength dataLength }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }

theorem successWordOutput_length :
    successWordOutput.length = 32 := by
  simp [successWordOutput]

theorem zeroWordOutput_length :
    zeroWordOutput.length = 32 := by
  simp [zeroWordOutput]

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

theorem pairingPairsFromEvmBytes_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (pairingPairsFromEvmBytes memory pairsStart numPairs).length = numPairs := by
  simp [pairingPairsFromEvmBytes]

theorem acceleratorInputFromCallData_pairs_length
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (acceleratorInputFromCallData memory dataStart dataLength).pairs.length =
      numPairs dataLength := by
  simp [acceleratorInputFromCallData, pairingPairsFromEvmBytes_length]

@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successWordOutput := rfl

@[simp] theorem outputFromVerified_false :
    outputFromVerified false = zeroWordOutput := rfl

@[simp] theorem execute_zeroLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    execute accelerator memory dataStart 0 =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute]

@[simp] theorem execute_badLength_mod
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_nonzero : dataLength ≠ 0)
    (h_mod : dataLength % pairLength ≠ 0) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_nonzero, h_mod]

@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true) :
    (execute accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  have h_nonzero : dataLength ≠ 0 := by
    intro h_zero
    simp [inputLengthValid, h_zero] at h_valid
  have h_mod : dataLength % pairLength = 0 := by
    simpa [inputLengthValid, h_nonzero] using h_valid
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_nonzero, h_mod, h_status,
      EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
      EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output =
      outputFromVerified
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).output.verified := by
  have h_nonzero : dataLength ≠ 0 := by
    intro h_zero
    simp [inputLengthValid, h_zero] at h_valid
  have h_mod : dataLength % pairLength = 0 := by
    simpa [inputLengthValid, h_nonzero] using h_valid
  simp [execute, h_nonzero, h_mod, h_status,
    EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
    EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .efail) :
    (execute accelerator memory dataStart dataLength).output = emptyOutput := by
  have h_nonzero : dataLength ≠ 0 := by
    intro h_zero
    simp [inputLengthValid, h_zero] at h_valid
  have h_mod : dataLength % pairLength = 0 := by
    simpa [inputLengthValid, h_nonzero] using h_valid
  simp [execute, h_nonzero, h_mod, h_status,
    EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
    EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]

theorem outputFromVerified_length (verified : Bool) :
    (outputFromVerified verified).length = 32 := by
  cases verified <;> simp [outputFromVerified, successWordOutput_length, zeroWordOutput_length]

theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output.length = 32 := by
  simp [execute_output_eok accelerator memory dataStart dataLength h_valid h_status,
    outputFromVerified_length]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if inputLengthValid dataLength then gasCostFromLength dataLength else 0 := by
  by_cases h_zero : dataLength = 0
  · subst dataLength
    simp [execute, inputLengthValid]
  · by_cases h_mod : dataLength % pairLength = 0
    · cases h_status :
          (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
        simp [execute, inputLengthValid, h_zero, h_mod, h_status,
          EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
          EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]
    · simp [execute, inputLengthValid, h_zero, h_mod]

end Pairing

namespace MapFpToG1

abbrev MemoryReader := EvmAsm.EL.Bls12MapFpToG1InputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bls12MapFpToG1InputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bls12MapFpToG1ResultBridge.AcceleratorResult

/-- EVM precompile address for BLS12-381 map-Fp-to-G1. -/
def address : Nat := 0x10

/-- Osaka executable-spec fixed gas cost for BLS12-381 map-Fp-to-G1. -/
def gasCost : Nat := 5500

/-- BLS12 map-Fp-to-G1 consumes exactly one 64-byte Fp element. -/
def inputLength : Nat := 64

/-- Invalid length, invalid field element, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure BLS12-381 map-Fp-to-G1 framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 64`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bls12MapFpToG1InputBridge.bls12MapFpToG1InputFromMemory
    memory dataStart

/--
Pure BLS12-381 map-Fp-to-G1 precompile framing. Field-element validation and
map-to-curve arithmetic are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall accelerator
      (EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12MapFpToG1ResultBridge.g1PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]

@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
      EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12MapFpToG1ResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]

theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 96 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12MapFpToG1ResultBridge.g1PointBytesList_length]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
        EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]
  · simp [execute, h_length]

end MapFpToG1

namespace MapFp2ToG2

abbrev MemoryReader := EvmAsm.EL.Bls12MapFp2ToG2InputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bls12MapFp2ToG2InputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.AcceleratorResult

/-- EVM precompile address for BLS12-381 map-Fp2-to-G2. -/
def address : Nat := 0x11

/-- Osaka executable-spec fixed gas cost for BLS12-381 map-Fp2-to-G2. -/
def gasCost : Nat := 23800

/-- BLS12 map-Fp2-to-G2 consumes exactly one 128-byte Fp2 element. -/
def inputLength : Nat := 128

/-- Invalid length, invalid field element, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure BLS12-381 map-Fp2-to-G2 framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 128`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bls12MapFp2ToG2InputBridge.bls12MapFp2ToG2InputFromMemory
    memory dataStart

/--
Pure BLS12-381 map-Fp2-to-G2 precompile framing. Field-element validation and
map-to-curve arithmetic are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall accelerator
      (EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.g2PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]

@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
      EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.g2PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]

theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 192 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.g2PointBytesList_length]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
        EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]
  · simp [execute, h_length]

end MapFp2ToG2


namespace G1Add

abbrev MemoryReader := EvmAsm.EL.Bls12G1AddInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bls12G1AddInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bls12G1AddResultBridge.AcceleratorResult
abbrev G1PointBytes := EvmAsm.EL.Bls12G1AddInputBridge.G1PointBytes

/-- EVM precompile address for BLS12-381 G1 addition. -/
def address : Nat := 0x0b

/-- Osaka executable-spec fixed gas cost for BLS12-381 G1 addition. -/
def gasCost : Nat := 375

/-- BLS12 G1 ADD consumes exactly two 128-byte EIP-2537 G1 points. -/
def inputLength : Nat := 256

/-- Offset of the second input point in the EVM call payload. -/
def p2Offset : Nat := 128

/-- Invalid length, invalid point encoding, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure BLS12-381 G1 ADD framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/-- Convert a 128-byte EIP-2537 G1 point into the accelerator's 96-byte G1 payload. -/
def g1PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G1PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else
      memory (pointStart + 64 + 16 + (n - 48))

/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 256`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  { p1 := g1PointFromEvmBytes memory dataStart
    p2 := g1PointFromEvmBytes memory (dataStart + p2Offset) }

/--
Pure BLS12-381 G1 ADD precompile framing. Point validation and curve arithmetic
are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall accelerator
      (EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G1AddResultBridge.g1PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]

@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
      EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12G1AddResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
    EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
    EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]

theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 96 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12G1AddResultBridge.g1PointBytesList_length]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
        EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]
  · simp [execute, h_length]

end G1Add

namespace G2Add

abbrev MemoryReader := EvmAsm.EL.Bls12G2AddInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bls12G2AddInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bls12G2AddResultBridge.AcceleratorResult
abbrev G2PointBytes := EvmAsm.EL.Bls12G2AddInputBridge.G2PointBytes

/-- EVM precompile address for BLS12-381 G2 addition. -/
def address : Nat := 0x0d

/-- Osaka executable-spec fixed gas cost for BLS12-381 G2 addition. -/
def gasCost : Nat := 600

/-- BLS12 G2 ADD consumes exactly two 256-byte EIP-2537 G2 points. -/
def inputLength : Nat := 512

/-- Offset of the second input point in the EVM call payload. -/
def p2Offset : Nat := 256

/-- Invalid length, invalid point encoding, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure BLS12-381 G2 ADD framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/-- Convert a 256-byte EIP-2537 G2 point into the accelerator's 192-byte G2 payload. -/
def g2PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G2PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else if n < 96 then
      memory (pointStart + 64 + 16 + (n - 48))
    else if n < 144 then
      memory (pointStart + 128 + 16 + (n - 96))
    else
      memory (pointStart + 192 + 16 + (n - 144))

/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 512`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  { p1 := g2PointFromEvmBytes memory dataStart
    p2 := g2PointFromEvmBytes memory (dataStart + p2Offset) }

/--
Pure BLS12-381 G2 ADD precompile framing. Point validation and curve arithmetic
are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall accelerator
      (EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G2AddResultBridge.g2PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]

@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
      EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12G2AddResultBridge.g2PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
    EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
    EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]

theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 192 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12G2AddResultBridge.g2PointBytesList_length]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
        EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]
  · simp [execute, h_length]

end G2Add


end BLS12

namespace KzgPointEvaluation

abbrev MemoryReader := EvmAsm.EL.KzgPointEvalInputBridge.MemoryReader
abbrev Bytes32 := EvmAsm.EL.KzgPointEvalInputBridge.Bytes32
abbrev AcceleratorInput := EvmAsm.EL.KzgPointEvalInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.KzgPointEvalResultBridge.AcceleratorResult

/-- EVM precompile address for EIP-4844 KZG point evaluation. -/
def address : Nat := 0x0a

/-- Osaka/BPO executable-spec fixed gas cost for KZG point evaluation. -/
def gasCost : Nat := 50000

/-- KZG point evaluation consumes exactly 192 bytes. -/
def inputLength : Nat := 192

def versionedHashOffset : Nat := 0
def zOffset : Nat := 32
def yOffset : Nat := 64
def commitmentOffset : Nat := 96
def proofOffset : Nat := 144

/-- `U256(4096).to_be_bytes32()`, i.e. `FIELD_ELEMENTS_PER_BLOB`. -/
def fieldElementsPerBlobOutput : ByteList :=
  List.replicate 30 (0 : Byte) ++ [0x10, 0x00]

/-- `U256(BLS_MODULUS).to_be_bytes32()` from execution-specs. -/
def blsModulusOutput : ByteList :=
  [ 0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48
  , 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05
  , 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe
  , 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01 ]

/-- Successful KZG point evaluation returns `FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS`. -/
def successOutput : ByteList :=
  fieldElementsPerBlobOutput ++ blsModulusOutput

/-- Invalid length, invalid hash/proof, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure precompile framing layer. `exceptional`
records execution-spec `KZGProofError` cases; later CALL/STATICCALL wiring can
translate that into the enclosing EVM failure semantics.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/-- The versioned hash is the first 32 bytes of the precompile payload. -/
def versionedHashFromCallData (memory : MemoryReader) (dataStart : Nat) : Bytes32 :=
  EvmAsm.EL.KzgPointEvalInputBridge.bytes32FromMemory
    memory (dataStart + versionedHashOffset)

/--
Build the accelerator input from the EVM call data. The executable spec first
checks `len(data) == 192`; callers must guard this helper with that exact
length check. Field starts mirror `point_evaluation.py`.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.KzgPointEvalInputBridge.kzgPointEvalInputFromMemory
    memory
    (dataStart + commitmentOffset)
    (dataStart + zOffset)
    (dataStart + yOffset)
    (dataStart + proofOffset)

/-- Convert the accelerator proof-verification result to EVM return data. -/
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successOutput else emptyOutput

/--
Pure KZG point-evaluation precompile framing. This models the executable-spec
guards and return-data shape:

* input length must be exactly 192 bytes;
* the supplied `versionedHashIsValid` hook checks
  `kzg_commitment_to_versioned_hash(commitment) == versioned_hash`;
* the supplied accelerator verifies `(commitment, z, y, proof)`;
* success returns `FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS`.
-/
def execute
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let versionedHash := versionedHashFromCallData memory dataStart
    if versionedHashIsValid versionedHash input then
      let request := EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput input
      let result := EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall
        accelerator request
      match result.status with
      | .eok =>
          { exceptional := !result.output.verified
            status := if result.output.verified then .eok else .efail
            output := outputFromVerified result.output.verified
            gasCharged := gasCost }
      | .efail =>
          { exceptional := true
            status := result.status
            output := emptyOutput
            gasCharged := gasCost }
    else
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }

theorem fieldElementsPerBlobOutput_length :
    fieldElementsPerBlobOutput.length = 32 := by
  decide

theorem blsModulusOutput_length :
    blsModulusOutput.length = 32 := by
  decide

theorem successOutput_length :
    successOutput.length = 64 := by
  decide

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successOutput := rfl

@[simp] theorem outputFromVerified_false :
    outputFromVerified false = emptyOutput := rfl

@[simp] theorem execute_badLength
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute versionedHashIsValid accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]

@[simp] theorem execute_invalidVersionedHash
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = false) :
    execute versionedHashIsValid accelerator memory dataStart inputLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := gasCost } := by
  simp [execute, inputLength, h_hash]

@[simp] theorem execute_output_verified
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok)
    (h_verified :
      (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified = true) :
    (execute versionedHashIsValid accelerator memory dataStart inputLength).output =
      successOutput := by
  simp [execute, inputLength, h_hash, h_status, h_verified,
    EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]

@[simp] theorem execute_output_unverified
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok)
    (h_verified :
      (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified = false) :
    (execute versionedHashIsValid accelerator memory dataStart inputLength).output =
      emptyOutput := by
  simp [execute, inputLength, h_hash, h_status, h_verified,
    EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]

@[simp] theorem execute_gasCharged
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute versionedHashIsValid accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_hash :
        versionedHashIsValid
          (versionedHashFromCallData memory dataStart)
          (acceleratorInputFromCallData memory dataStart)
    · simp [execute, inputLength, h_hash]
    · cases h_status :
          (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
        cases h_verified :
          (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified <;>
        simp [execute, inputLength, h_hash, h_status, h_verified,
          EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
          EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]
  · simp [execute, h_length]

end KzgPointEvaluation

namespace P256Verify

abbrev MemoryReader := EvmAsm.EL.Secp256r1VerifyInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Secp256r1VerifyInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Secp256r1VerifyResultBridge.AcceleratorResult

/-- EVM precompile address for P256VERIFY / secp256r1 verification. -/
def address : Nat := 0x100

/-- Osaka/BPO executable-spec gas cost for P256VERIFY. -/
def gasCost : Nat := 6900

/-- P256VERIFY consumes exactly five 32-byte fields. -/
def inputLength : Nat := 160

/-- Successful P256VERIFY returns `left_pad_zero_bytes(b"\x01", 32)`. -/
def successOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]

/-- Invalid input, invalid signature, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/-- Result surface exposed to the caller by the pure precompile framing layer. -/
structure Result where
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/--
Build the fixed accelerator input fields from the EVM call data. The executable
spec first checks `len(data) == 160`; callers must guard this helper with that
length check. Field starts mirror `p256verify.py`: msg, r, s, qx, qy.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory
    memory dataStart (dataStart + 32) (dataStart + 96)

/-- Convert a successful accelerator boolean to the EVM return-data bytes. -/
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successOutput else emptyOutput

/--
Pure P256VERIFY precompile framing. This models the EVM-side guards and
return-data shape; scalar bounds, curve membership, and signature validation are
part of the supplied accelerator model, matching the existing secp256r1 bridge.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := accelerator input
    match result.status with
    | .eok =>
        { status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCost }
    | .efail =>
        { status := result.status, output := emptyOutput, gasCharged := gasCost }
  else
    { status := .eok, output := emptyOutput, gasCharged := gasCost }

theorem successOutput_length :
    successOutput.length = 32 := by
  simp [successOutput]

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successOutput := rfl

@[simp] theorem outputFromVerified_false :
    outputFromVerified false = emptyOutput := rfl

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { status := .eok, output := emptyOutput, gasCharged := gasCost } := by
  simp [execute, h_length]

@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      outputFromVerified
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified := by
  simp [execute, inputLength, h_status]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged = gasCost := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status]
  · simp [execute, h_length]

end P256Verify

end EvmAsm.Stateless.VM.Precompiles
