/-
  EvmAsm.Evm64.Precompile

  Pure precompile-address registry for GH #116.
-/

import EvmAsm.Evm64.Environment

namespace EvmAsm.Evm64

/-- Canonical Ethereum precompiles targeted by the dispatch/accelerator bridge. -/
inductive Precompile where
  | ecrecover
  | sha256
  | ripemd160
  | identity
  | modexp
  | bn254Add
  | bn254Mul
  | bn254Pairing
  | blake2f
  | pointEvaluation
  | bls12G1Add
  | bls12G1Msm
  | bls12G2Add
  | bls12G2Msm
  | bls12Pairing
  | bls12MapFpToG1
  | bls12MapFp2ToG2
  | p256Verify
  deriving DecidableEq, Repr

namespace Precompile

/-- Canonical EVM account address for each precompile. -/
def address : Precompile → Address
  | ecrecover => 0x01
  | sha256 => 0x02
  | ripemd160 => 0x03
  | identity => 0x04
  | modexp => 0x05
  | bn254Add => 0x06
  | bn254Mul => 0x07
  | bn254Pairing => 0x08
  | blake2f => 0x09
  | pointEvaluation => 0x0a
  | bls12G1Add => 0x0b
  | bls12G1Msm => 0x0c
  | bls12G2Add => 0x0d
  | bls12G2Msm => 0x0e
  | bls12Pairing => 0x0f
  | bls12MapFpToG1 => 0x10
  | bls12MapFp2ToG2 => 0x11
  | p256Verify => 0x100

/-- Decode a canonical Amsterdam precompile account address.

    Addresses near zero that are not active precompiles must decode to `none`
    so the CALL-family path can treat them as ordinary absent accounts before
    precompile dispatch. -/
def ofAddress? (addr : Address) : Option Precompile :=
  if addr = (0x01 : Address) then some ecrecover
  else if addr = (0x02 : Address) then some sha256
  else if addr = (0x03 : Address) then some ripemd160
  else if addr = (0x04 : Address) then some identity
  else if addr = (0x05 : Address) then some modexp
  else if addr = (0x06 : Address) then some bn254Add
  else if addr = (0x07 : Address) then some bn254Mul
  else if addr = (0x08 : Address) then some bn254Pairing
  else if addr = (0x09 : Address) then some blake2f
  else if addr = (0x0a : Address) then some pointEvaluation
  else if addr = (0x0b : Address) then some bls12G1Add
  else if addr = (0x0c : Address) then some bls12G1Msm
  else if addr = (0x0d : Address) then some bls12G2Add
  else if addr = (0x0e : Address) then some bls12G2Msm
  else if addr = (0x0f : Address) then some bls12Pairing
  else if addr = (0x10 : Address) then some bls12MapFpToG1
  else if addr = (0x11 : Address) then some bls12MapFp2ToG2
  else if addr = (0x100 : Address) then some p256Verify
  else none

/-- Predicate form for CALL-family dispatch. -/
def isPrecompileAddress (addr : Address) : Prop :=
  (ofAddress? addr).isSome

/-- Gas-shape classification for precompile dispatch. Some precompiles need
    richer inputs than a byte length; those are represented as hooks for later
    syscall/executable-spec bridges. -/
inductive GasSchedule where
  | fixed (cost : Nat)
  | wordLinear (base perWord : Nat)
  | pairing (base perPair : Nat)
  | modexp
  | blake2f
  | payloadDependent
  deriving DecidableEq, Repr

/-- Number of 32-byte EVM words needed to cover an input byte length. -/
def inputWords (inputLen : Nat) : Nat :=
  (inputLen + 31) / 32

/-- Number of 192-byte BN254 pairing tuples in an input payload. -/
def pairingPairs (inputLen : Nat) : Nat :=
  inputLen / 192

/-- Gas schedule for canonical precompile entry points. -/
def gasSchedule : Precompile → GasSchedule
  | ecrecover => .fixed 3000
  | sha256 => .wordLinear 60 12
  | ripemd160 => .wordLinear 600 120
  | identity => .wordLinear 15 3
  | modexp => .modexp
  | bn254Add => .fixed 150
  | bn254Mul => .fixed 6000
  | bn254Pairing => .pairing 45000 34000
  | blake2f => .blake2f
  | pointEvaluation => .fixed 50000
  | bls12G1Add => .fixed 375
  | bls12G1Msm => .payloadDependent
  | bls12G2Add => .fixed 600
  | bls12G2Msm => .payloadDependent
  | bls12Pairing => .payloadDependent
  | bls12MapFpToG1 => .fixed 5500
  | bls12MapFp2ToG2 => .fixed 23800
  | p256Verify => .fixed 6900

/-- Byte-length-only gas cost when the precompile schedule can be determined
    without decoding the input payload. -/
def precompileGasCost? (p : Precompile) (inputLen : Nat) : Option Nat :=
  match gasSchedule p with
  | .fixed cost => some cost
  | .wordLinear base perWord => some (base + perWord * inputWords inputLen)
  | .pairing base perPair => some (base + perPair * pairingPairs inputLen)
  | .modexp => none
  | .blake2f => none
  | .payloadDependent => none

/-- Blake2f gas is parameterized by the rounds field decoded from the payload. -/
def blake2fGas (rounds : Nat) : Nat :=
  rounds

theorem ofAddress?_address (p : Precompile) :
    ofAddress? p.address = some p := by
  cases p <;> decide

theorem ofAddress?_zero :
    ofAddress? (0 : Address) = none := by
  decide

theorem ofAddress?_eighteen :
    ofAddress? (0x12 : Address) = none := by
  decide

theorem ofAddress?_oneHundredOne :
    ofAddress? (0x101 : Address) = none := by
  decide

theorem isPrecompileAddress_address (p : Precompile) :
    isPrecompileAddress p.address := by
  unfold isPrecompileAddress
  rw [ofAddress?_address p]
  simp

theorem isPrecompileAddress_iff_exists {addr : Address} :
    isPrecompileAddress addr ↔ ∃ p, ofAddress? addr = some p := by
  unfold isPrecompileAddress
  cases h_decode : ofAddress? addr with
  | none =>
      simp
  | some p =>
      simp

theorem not_isPrecompileAddress_iff_none {addr : Address} :
    ¬ isPrecompileAddress addr ↔ ofAddress? addr = none := by
  unfold isPrecompileAddress
  cases ofAddress? addr <;> simp

theorem inputWords_zero : inputWords 0 = 0 := rfl

theorem inputWords_thirty_three : inputWords 33 = 2 := rfl

theorem pairingPairs_one : pairingPairs 192 = 1 := rfl

theorem gasSchedule_sha256 :
    gasSchedule sha256 = .wordLinear 60 12 := rfl

theorem precompileGasCost?_identity_64 :
    precompileGasCost? identity 64 = some 21 := rfl

theorem precompileGasCost?_sha256_33 :
    precompileGasCost? sha256 33 = some 84 := rfl

theorem precompileGasCost?_modexp_none (inputLen : Nat) :
    precompileGasCost? modexp inputLen = none := rfl

theorem precompileGasCost?_blake2f_none (inputLen : Nat) :
    precompileGasCost? blake2f inputLen = none := rfl

theorem precompileGasCost?_eq_none_iff (p : Precompile) (inputLen : Nat) :
    precompileGasCost? p inputLen = none ↔
      p = modexp ∨ p = blake2f ∨ p = bls12G1Msm ∨ p = bls12G2Msm ∨
        p = bls12Pairing := by
  cases p <;> simp [precompileGasCost?, gasSchedule]

theorem precompileGasCost?_isSome_iff (p : Precompile) (inputLen : Nat) :
    (precompileGasCost? p inputLen).isSome ↔
      p ≠ modexp ∧ p ≠ blake2f ∧ p ≠ bls12G1Msm ∧ p ≠ bls12G2Msm ∧
        p ≠ bls12Pairing := by
  cases p <;> simp [precompileGasCost?, gasSchedule]

theorem precompileGasCost?_exists_some_iff (p : Precompile) (inputLen : Nat) :
    (∃ cost, precompileGasCost? p inputLen = some cost) ↔
      p ≠ modexp ∧ p ≠ blake2f ∧ p ≠ bls12G1Msm ∧ p ≠ bls12G2Msm ∧
        p ≠ bls12Pairing := by
  cases p <;> simp [precompileGasCost?, gasSchedule]

theorem blake2fGas_eq_rounds (rounds : Nat) :
    blake2fGas rounds = rounds := rfl

@[simp] theorem not_isPrecompileAddress_zero :
    ¬ isPrecompileAddress (0 : Address) := by
  unfold isPrecompileAddress
  rw [ofAddress?_zero]
  decide

@[simp] theorem not_isPrecompileAddress_eighteen :
    ¬ isPrecompileAddress (0x12 : Address) := by
  unfold isPrecompileAddress
  rw [ofAddress?_eighteen]
  decide

@[simp] theorem not_isPrecompileAddress_oneHundredOne :
    ¬ isPrecompileAddress (0x101 : Address) := by
  unfold isPrecompileAddress
  rw [ofAddress?_oneHundredOne]
  decide

end Precompile

end EvmAsm.Evm64
