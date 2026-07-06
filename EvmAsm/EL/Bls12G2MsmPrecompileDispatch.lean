/-
  EvmAsm.EL.Bls12G2MsmPrecompileDispatch

  Pure EVM BLS12-381 G2 MSM precompile framing. Point validation and
  multi-scalar multiplication are supplied by the accelerator boundary; this
  module fixes the execution-specs-visible target, invalid-length behavior,
  payload-dependent gas, input slicing, and common precompile result shape.
-/

import EvmAsm.EL.Bls12G2PrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12G2MsmPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev MsmPair := Bls12G2MsmInputBridge.MsmPair
abbrev AcceleratorInput := Bls12G2MsmInputBridge.AcceleratorInput
abbrev AcceleratorResult := Bls12G2MsmResultBridge.AcceleratorResult

/-- Execution-specs G2 MSM consumes 288-byte EVM pair encodings. -/
def pairLength : Nat := 288

/-- The compact accelerator G2 prefix inside each 288-byte EVM pair window. -/
def pointOffset : Nat := 0

/-- The 32-byte scalar starts after the 256-byte EVM G2 point window. -/
def scalarOffset : Nat := 256

/-- Osaka executable-spec `GasCosts.PRECOMPILE_BLS_G2MUL`. -/
def g2MulGas : Nat := 22500

/-- Osaka executable-spec BLS MSM discount multiplier. -/
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

/-- Safe byte projection. Invalid short inputs are rejected before this is used. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

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

/-- Execution-specs length check: `len(data) == 0 or len(data) % 288 != 0`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length != 0 && payload.length % pairLength == 0

/-- Number of G2 MSM pairs in a valid payload. -/
def pairCount (payload : List Byte) : Nat :=
  payload.length / pairLength

def discount (k : Nat) : Nat :=
  if k = 0 then
    0
  else if k <= 128 then
    g2KDiscount.getD (k - 1) g2MaxDiscount
  else
    g2MaxDiscount

/-- Osaka G2 MSM gas cost: `k * PRECOMPILE_BLS_G2MUL * discount / 1000`. -/
def gasCost (payload : List Byte) : Nat :=
  let k := pairCount payload
  k * g2MulGas * discount k / multiplier

/-- One compact accelerator G2 point projected from the EVM pair window. -/
def pointBytes (payload : List Byte) (pairIndex : Nat) : Bls12G2MsmInputBridge.G2PointBytes :=
  fun i => payloadByte payload (pairLength * pairIndex + pointOffset + compactG2Offset i.val)

/-- Scalar bytes projected from the EVM pair window. -/
def scalarBytes (payload : List Byte) (pairIndex : Nat) : Bls12G2MsmInputBridge.ScalarBytes :=
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
Pure BLS12 G2 MSM precompile dispatch.

Execution-specs rejects empty or non-288-multiple inputs before charging gas.
Valid-length inputs charge payload-dependent gas and then the accelerator
boundary handles point decoding, subgroup checks, and MSM arithmetic.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bls12G2Msm then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        let request := Bls12G2MsmEcallBridge.requestFromInput (acceleratorInput input.input)
        let result := Bls12G2MsmEcallBridge.executeBls12G2MsmEcall accelerator request
        Bls12G2PrecompileResultBridge.fromMsmResult (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem g2KDiscount_length :
    g2KDiscount.length = 128 := by
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
    discount k = g2MaxDiscount := by
  have h_pos : k ≠ 0 := by
    intro h_zero
    exact h_gt (by simp [h_zero])
  simp [discount, h_pos, h_gt]

theorem gasCost_eq_formula (payload : List Byte) :
    gasCost payload = pairCount payload * g2MulGas * discount (pairCount payload) / multiplier := by
  simp [gasCost]

theorem pointBytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 192) :
    pointBytes payload pairIndex i =
      payload.getD (pairLength * pairIndex + compactG2Offset i.val) 0 := by
  simp [pointBytes, payloadByte, pointOffset]

theorem scalarBytes_apply (payload : List Byte) (pairIndex : Nat) (i : Fin 32) :
    scalarBytes payload pairIndex i =
      payload.getD (pairLength * pairIndex + 256 + i.val) 0 := by
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

theorem dispatch_non_bls12G2Msm
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bls12G2Msm) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Msm)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bls12G2PrecompileResultBridge.msmOutputBytes
          (Bls12G2MsmEcallBridge.executeBls12G2MsmEcall accelerator
            (Bls12G2MsmEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12G2MsmEcallBridge.requestFromInput,
    Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
    Bls12G2PrecompileResultBridge.fromMsmResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 256 := by
  rw [dispatch_success accelerator h_target h_len h_gas h_status]
  simp [Bls12G2PrecompileResultBridge.msmOutputBytes_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Msm)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12G2MsmEcallBridge.requestFromInput,
    Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
    Bls12G2PrecompileResultBridge.fromMsmResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bls12G2Msm
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        cases h_status : (Bls12G2MsmEcallBridge.executeBls12G2MsmEcall accelerator
          (Bls12G2MsmEcallBridge.requestFromInput
            (acceleratorInput input.input))).status <;>
          simp [Bls12G2PrecompileResultBridge.fromMsmResult, h_status,
            EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bls12G2MsmPrecompileDispatch

end EvmAsm.EL
