/-
  EvmAsm.EL.Bls12G1MsmPrecompileDispatch

  Pure EVM BLS12-381 G1 MSM precompile framing. Point validation and
  multi-scalar multiplication are supplied by the accelerator boundary; this
  module fixes the execution-specs-visible target, invalid-length behavior,
  payload-dependent gas, input slicing, and common precompile result shape.
-/

import EvmAsm.EL.Bls12G1PrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12G1MsmPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev MsmPair := Bls12G1MsmInputBridge.MsmPair
abbrev AcceleratorInput := Bls12G1MsmInputBridge.AcceleratorInput
abbrev AcceleratorResult := Bls12G1MsmResultBridge.AcceleratorResult

/-- Execution-specs G1 MSM consumes 160-byte EVM pair encodings. -/
def pairLength : Nat := 160

/-- The compact accelerator G1 prefix inside each 160-byte EVM pair window. -/
def pointOffset : Nat := 0

/-- The 32-byte scalar starts after the 128-byte EVM G1 point window. -/
def scalarOffset : Nat := 128

/-- Osaka executable-spec `GasCosts.PRECOMPILE_BLS_G1MUL`. -/
def g1MulGas : Nat := 12000

/-- Osaka executable-spec BLS MSM discount multiplier. -/
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

/-- Safe byte projection. Invalid short inputs are rejected before this is used. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Offset of a compact 96-byte G1 coordinate byte inside a 128-byte EVM G1 point. -/
def compactG1Offset (i : Nat) : Nat :=
  if i < 48 then 16 + i else 32 + i

/-- Execution-specs length check: `len(data) == 0 or len(data) % 160 != 0`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length != 0 && payload.length % pairLength == 0

/-- Number of G1 MSM pairs in a valid payload. -/
def pairCount (payload : List Byte) : Nat :=
  payload.length / pairLength

def discount (k : Nat) : Nat :=
  if k = 0 then
    0
  else if k <= 128 then
    g1KDiscount.getD (k - 1) g1MaxDiscount
  else
    g1MaxDiscount

/-- Osaka G1 MSM gas cost: `k * PRECOMPILE_BLS_G1MUL * discount / 1000`. -/
def gasCost (payload : List Byte) : Nat :=
  let k := pairCount payload
  k * g1MulGas * discount k / multiplier

/-- One compact accelerator G1 point projected from the EVM pair window. -/
def pointBytes (payload : List Byte) (pairIndex : Nat) : Bls12G1MsmInputBridge.G1PointBytes :=
  fun i => payloadByte payload (pairLength * pairIndex + pointOffset + compactG1Offset i.val)

/-- Scalar bytes projected from the EVM pair window. -/
def scalarBytes (payload : List Byte) (pairIndex : Nat) : Bls12G1MsmInputBridge.ScalarBytes :=
  fun i => payloadByte payload (pairLength * pairIndex + scalarOffset + i.val)

/-- One accelerator MSM pair extracted from the execution-specs EVM pair window. -/
def msmPair (payload : List Byte) (pairIndex : Nat) : MsmPair :=
  { point := pointBytes payload pairIndex
    scalar := scalarBytes payload pairIndex }

/-- Accelerator input extracted from EVM call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { pairs := (List.range (pairCount payload)).map (msmPair payload)
    numPairs := pairCount payload }

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BLS12 G1 MSM precompile dispatch.

Execution-specs rejects empty or non-160-multiple inputs before charging gas.
Valid-length inputs charge payload-dependent gas and then the accelerator
boundary handles point decoding, subgroup checks, and MSM arithmetic.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bls12G1Msm then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        let request := Bls12G1MsmEcallBridge.requestFromInput (acceleratorInput input.input)
        let result := Bls12G1MsmEcallBridge.executeBls12G1MsmEcall accelerator request
        Bls12G1PrecompileResultBridge.fromMsmResult (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem g1KDiscount_length :
    g1KDiscount.length = 128 := by
  set_option maxRecDepth 1000 in decide

theorem validInputLength_empty :
    validInputLength ([] : List Byte) = false := by
  simp [validInputLength]

theorem pairCount_eq (payload : List Byte) :
    pairCount payload = payload.length / pairLength := rfl

theorem discount_zero :
    discount 0 = 0 := by
  simp [discount]

theorem discount_gt_128 (k : Nat) (h_gt : ¬ k <= 128) :
    discount k = g1MaxDiscount := by
  have h_pos : k ≠ 0 := by
    intro h_zero
    exact h_gt (by simp [h_zero])
  simp [discount, h_pos, h_gt]

theorem gasCost_eq_formula (payload : List Byte) :
    gasCost payload = pairCount payload * g1MulGas * discount (pairCount payload) / multiplier := by
  simp [gasCost]

theorem pointBytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 96) :
    pointBytes payload pairIndex i =
      payload.getD (pairLength * pairIndex + compactG1Offset i.val) 0 := by
  simp [pointBytes, payloadByte, pointOffset]

theorem scalarBytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 32) :
    scalarBytes payload pairIndex i =
      payload.getD (pairLength * pairIndex + 128 + i.val) 0 := by
  simp [scalarBytes, payloadByte, scalarOffset]

theorem msmPair_point (payload : List Byte) (pairIndex : Nat) :
    (msmPair payload pairIndex).point = pointBytes payload pairIndex := rfl

theorem msmPair_scalar (payload : List Byte) (pairIndex : Nat) :
    (msmPair payload pairIndex).scalar = scalarBytes payload pairIndex := rfl

theorem acceleratorInput_numPairs (payload : List Byte) :
    (acceleratorInput payload).numPairs = pairCount payload := rfl

theorem acceleratorInput_pairs_length (payload : List Byte) :
    (acceleratorInput payload).pairs.length = pairCount payload := by
  simp [acceleratorInput]

theorem dispatch_non_bls12G1Msm
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bls12G1Msm) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G1Msm)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G1Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G1Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bls12G1PrecompileResultBridge.msmOutputBytes
          (Bls12G1MsmEcallBridge.executeBls12G1MsmEcall accelerator
            (Bls12G1MsmEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12G1MsmEcallBridge.requestFromInput,
    Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
    Bls12G1PrecompileResultBridge.fromMsmResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G1Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 128 := by
  rw [dispatch_success accelerator h_target h_len h_gas h_status]
  simp [Bls12G1PrecompileResultBridge.msmOutputBytes_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G1Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12G1MsmEcallBridge.requestFromInput,
    Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
    Bls12G1PrecompileResultBridge.fromMsmResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bls12G1Msm
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        cases h_status : (Bls12G1MsmEcallBridge.executeBls12G1MsmEcall accelerator
          (Bls12G1MsmEcallBridge.requestFromInput
            (acceleratorInput input.input))).status <;>
          simp [Bls12G1PrecompileResultBridge.fromMsmResult, h_status,
            EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bls12G1MsmPrecompileDispatch

end EvmAsm.EL
