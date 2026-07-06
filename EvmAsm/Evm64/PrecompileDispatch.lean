/-
  EvmAsm.Evm64.PrecompileDispatch

  Pure precompile dispatch outcome surface for GH #116.
-/

import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.Evm64

namespace PrecompileDispatch

/-- Decode a precompile target from an EVM account address. -/
def decode? (addr : Address) : Option Precompile :=
  Precompile.ofAddress? addr

/-- Byte-length-only gas cost for a precompile input, when known without
    payload-specific decoding. -/
def gasCost? (input : PrecompileInput) : Option Nat :=
  Precompile.precompileGasCost? input.target input.input.length

/-- Predicate form used by CALL-family dispatch before invoking a precompile. -/
def precompileGasAffordable (input : PrecompileInput) : Prop :=
  ∃ cost, gasCost? input = some cost ∧ cost ≤ input.gas

/-- Dispatch wrapper for known-cost precompiles. Payload-specific gas schedules
    stay as `none` until their executable-spec bridges provide decoded costs. -/
def dispatch? (input : PrecompileInput) (out : List (BitVec 8)) : Option PrecompileResult :=
  match gasCost? input with
  | none => none
  | some cost =>
      if cost ≤ input.gas then
        some (PrecompileResult.ok out (input.gas - cost))
      else
        some (PrecompileResult.fail input.gas)

/-- Address-level dispatch wrapper used before constructing an opcode-level
    CALL-family state transition. -/
def dispatchAddress? (addr caller : Address) (payload out : List (BitVec 8)) (gas : Nat) :
    Option PrecompileResult :=
  match decode? addr with
  | none => none
  | some target =>
      dispatch?
        { target := target
          caller := caller
          input := payload
          gas := gas }
        out

theorem decode?_address (p : Precompile) :
    decode? p.address = some p := by
  exact Precompile.ofAddress?_address p

theorem decode?_zero :
    decode? (0 : Address) = none := by
  exact Precompile.ofAddress?_zero

theorem decode?_eighteen :
    decode? (0x12 : Address) = none := by
  exact Precompile.ofAddress?_eighteen

theorem decode?_oneHundredOne :
    decode? (0x101 : Address) = none := by
  exact Precompile.ofAddress?_oneHundredOne

theorem gasCost?_eq (input : PrecompileInput) :
    gasCost? input = Precompile.precompileGasCost? input.target input.input.length := rfl

theorem precompileGasAffordable_of_gasCost?_le {input : PrecompileInput} {cost : Nat}
    (h_cost : gasCost? input = some cost) (h_le : cost ≤ input.gas) :
    precompileGasAffordable input := by
  exact ⟨cost, h_cost, h_le⟩

theorem dispatch?_none_of_gasCost?_none {input : PrecompileInput} {out : List (BitVec 8)}
    (h_cost : gasCost? input = none) :
    dispatch? input out = none := by
  simp [dispatch?, h_cost]

theorem dispatch?_ok_of_gasCost?_le {input : PrecompileInput} {out : List (BitVec 8)}
    {cost : Nat} (h_cost : gasCost? input = some cost) (h_le : cost ≤ input.gas) :
    dispatch? input out = some (PrecompileResult.ok out (input.gas - cost)) := by
  simp [dispatch?, h_cost, h_le]

theorem dispatch?_fail_of_gasCost?_gt {input : PrecompileInput} {out : List (BitVec 8)}
    {cost : Nat} (h_cost : gasCost? input = some cost) (h_gt : input.gas < cost) :
    dispatch? input out = some (PrecompileResult.fail input.gas) := by
  have h_not : ¬ cost ≤ input.gas := Nat.not_le.mpr h_gt
  simp [dispatch?, h_cost, h_not]

theorem dispatch?_eq_none_iff {input : PrecompileInput} {out : List (BitVec 8)} :
    dispatch? input out = none ↔ gasCost? input = none := by
  unfold dispatch?
  cases h_cost : gasCost? input with
  | none =>
      simp
  | some cost =>
      by_cases h_le : cost ≤ input.gas <;> simp [h_le]

theorem dispatch?_eq_some_ok_iff
    {input : PrecompileInput} {out : List (BitVec 8)} {gasRemaining : Nat} :
    dispatch? input out = some (PrecompileResult.ok out gasRemaining) ↔
      ∃ cost, gasCost? input = some cost ∧ cost ≤ input.gas ∧
        gasRemaining = input.gas - cost := by
  unfold dispatch?
  cases h_cost : gasCost? input with
  | none =>
      simp
  | some cost =>
      by_cases h_le : cost ≤ input.gas
      · simp only [h_le, ↓reduceIte]
        constructor
        · intro h_eq
          have h_result :
              PrecompileResult.ok out (input.gas - cost) =
                PrecompileResult.ok out gasRemaining := by
            simpa using h_eq
          have h_remaining : gasRemaining = input.gas - cost := by
            cases h_result
            rfl
          exact ⟨cost, rfl, h_le, h_remaining⟩
        · rintro ⟨cost', h_cost', h_le', h_remaining⟩
          injection h_cost' with h_cost_eq
          subst h_cost_eq
          rw [h_remaining]
      · simp only [h_le, ↓reduceIte]
        constructor
        · intro h_eq
          have h_status_eq :=
            congrArg PrecompileResult.status (Option.some.inj h_eq)
          simp [PrecompileResult.fail, PrecompileResult.ok] at h_status_eq
        · rintro ⟨cost', h_cost', h_le', h_remaining⟩
          injection h_cost' with h_cost_eq
          subst h_cost_eq
          exact False.elim (h_le h_le')

theorem dispatch?_eq_some_fail_iff
    {input : PrecompileInput} {out : List (BitVec 8)} {gasRemaining : Nat} :
    dispatch? input out = some (PrecompileResult.fail gasRemaining) ↔
      ∃ cost, gasCost? input = some cost ∧ input.gas < cost ∧
        gasRemaining = input.gas := by
  unfold dispatch?
  cases h_cost : gasCost? input with
  | none =>
      simp
  | some cost =>
      by_cases h_le : cost ≤ input.gas
      · simp only [h_le, ↓reduceIte]
        constructor
        · intro h_eq
          have h_status_eq :=
            congrArg PrecompileResult.status (Option.some.inj h_eq)
          simp [PrecompileResult.fail, PrecompileResult.ok] at h_status_eq
        · rintro ⟨cost', h_cost', h_gt, h_remaining⟩
          injection h_cost' with h_cost_eq
          subst h_cost_eq
          exact False.elim (Nat.not_lt_of_ge h_le h_gt)
      · have h_gt : input.gas < cost := Nat.lt_of_not_ge h_le
        simp only [h_le, ↓reduceIte]
        constructor
        · intro h_eq
          have h_result :
              PrecompileResult.fail input.gas =
                PrecompileResult.fail gasRemaining := by
            simpa using h_eq
          have h_remaining : gasRemaining = input.gas := by
            cases h_result
            rfl
          exact ⟨cost, rfl, h_gt, h_remaining⟩
        · rintro ⟨cost', h_cost', h_gt', h_remaining⟩
          injection h_cost' with h_cost_eq
          subst h_cost_eq
          rw [h_remaining]

theorem dispatch?_preservesGasBound {input : PrecompileInput} {out : List (BitVec 8)}
    {result : PrecompileResult} (h_dispatch : dispatch? input out = some result) :
    PrecompileResult.preservesGasBound input result := by
  unfold dispatch? at h_dispatch
  cases h_cost : gasCost? input with
  | none =>
      simp [h_cost] at h_dispatch
  | some cost =>
      by_cases h_le : cost ≤ input.gas
      · simp [h_cost, h_le] at h_dispatch
        rw [← h_dispatch]
        simp [PrecompileResult.preservesGasBound, PrecompileResult.ok]
      · simp [h_cost, h_le] at h_dispatch
        rw [← h_dispatch]
        simp [PrecompileResult.preservesGasBound, PrecompileResult.fail]

theorem dispatchAddress?_none_of_decode?_none {addr caller : Address}
    {payload out : List (BitVec 8)} {gas : Nat}
    (h_decode : decode? addr = none) :
    dispatchAddress? addr caller payload out gas = none := by
  unfold dispatchAddress?
  rw [h_decode]

theorem dispatchAddress?_none_zero (caller : Address) (payload out : List (BitVec 8))
    (gas : Nat) :
    dispatchAddress? 0 caller payload out gas = none := by
  exact dispatchAddress?_none_of_decode?_none decode?_zero

theorem dispatchAddress?_none_eighteen
    (caller : Address) (payload out : List (BitVec 8)) (gas : Nat) :
    dispatchAddress? 0x12 caller payload out gas = none := by
  exact dispatchAddress?_none_of_decode?_none decode?_eighteen

theorem dispatchAddress?_none_oneHundredOne
    (caller : Address) (payload out : List (BitVec 8)) (gas : Nat) :
    dispatchAddress? 0x101 caller payload out gas = none := by
  exact dispatchAddress?_none_of_decode?_none decode?_oneHundredOne

theorem dispatchAddress?_address (p : Precompile) (caller : Address)
    (payload out : List (BitVec 8)) (gas : Nat) :
    dispatchAddress? p.address caller payload out gas =
      dispatch?
        { target := p
          caller := caller
          input := payload
          gas := gas }
        out := by
  simp [dispatchAddress?, decode?_address p]

theorem dispatchAddress?_eq_some_iff
    {addr caller : Address} {payload out : List (BitVec 8)} {gas : Nat}
    {result : PrecompileResult} :
    dispatchAddress? addr caller payload out gas = some result ↔
      ∃ target, decode? addr = some target ∧
        dispatch?
          { target := target
            caller := caller
            input := payload
            gas := gas }
          out = some result := by
  unfold dispatchAddress?
  cases h_decode : decode? addr with
  | none =>
      simp
  | some target =>
      simp only
      constructor
      · intro h_dispatch
        exact ⟨target, rfl, h_dispatch⟩
      · rintro ⟨target', h_target, h_dispatch⟩
        injection h_target with h_target_eq
        subst h_target_eq
        exact h_dispatch

theorem dispatchAddress?_eq_none_iff
    {addr caller : Address} {payload out : List (BitVec 8)} {gas : Nat} :
    dispatchAddress? addr caller payload out gas = none ↔
      decode? addr = none ∨
        ∃ target, decode? addr = some target ∧
          dispatch?
            { target := target
              caller := caller
              input := payload
              gas := gas }
            out = none := by
  unfold dispatchAddress?
  cases h_decode : decode? addr with
  | none =>
      simp
  | some target =>
      simp only
      constructor
      · intro h_dispatch
        exact Or.inr ⟨target, rfl, h_dispatch⟩
      · intro h_none
        cases h_none with
        | inl h_decode_none =>
            simp at h_decode_none
        | inr h_dispatch =>
            obtain ⟨target', h_target, h_dispatch_none⟩ := h_dispatch
            injection h_target with h_target_eq
            subst h_target_eq
            exact h_dispatch_none

theorem dispatchAddress?_preservesGasBound {addr caller : Address}
    {payload out : List (BitVec 8)} {gas : Nat} {result : PrecompileResult}
    (h_dispatch : dispatchAddress? addr caller payload out gas = some result) :
    result.gasRemaining ≤ gas := by
  unfold dispatchAddress? at h_dispatch
  cases h_decode : decode? addr with
  | none =>
      simp [h_decode] at h_dispatch
  | some target =>
      simp [h_decode] at h_dispatch
      exact dispatch?_preservesGasBound h_dispatch

end PrecompileDispatch

end EvmAsm.Evm64
