/-
  EvmAsm.Rv64.RLP.WithdrawalDecode

  WP-facing specification facade for an RV64 `withdrawal_decode` routine.
  The static schema below intentionally contains only field positions and output
  layout.  It does not contain decoded bytes or values; those are introduced only
  by the postcondition, through the pure `EvmAsm.EL.decodeWithdrawal` function.
-/

import EvmAsm.Rv64.WP
import EvmAsm.Rv64.MemRegion
import EvmAsm.EL.Withdrawal

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP

namespace WithdrawalDecode

/-! ## Static ABI layout -/

/-- Field kind for the fixed EIP-4895 withdrawal schema.  This is static
    layout/control information, not a decoded value. -/
inductive FieldKind where
  | scalarU64
  | address20
  deriving DecidableEq, Repr

/-- One static field of `rlp([index, validator_index, address, amount])`.
    The schema records only where to read a field from and where to write it in
    the ABI output struct. -/
structure FieldLayout where
  inputIndex : Nat
  outputOffset : Nat
  kind : FieldKind
  deriving DecidableEq, Repr

/-- Output struct size used by the codegen ABI: 48 bytes. -/
def outputSize : Nat := 48

/-- Static schema for the ABI output struct:
    `index@0`, `validator_index@8`, `address@16`, `amount@40`. -/
def schema : List FieldLayout :=
  [ { inputIndex := 0, outputOffset := 0,  kind := .scalarU64 }
  , { inputIndex := 1, outputOffset := 8,  kind := .scalarU64 }
  , { inputIndex := 2, outputOffset := 16, kind := .address20 }
  , { inputIndex := 3, outputOffset := 40, kind := .scalarU64 }
  ]

theorem schema_length : schema.length = 4 := rfl

/-! ## Result bytes, derived from the pure decoder result -/

/-- Eight little-endian bytes of a 64-bit word. -/
def u64LEBytes (v : Word) : List Byte :=
  [ v.truncate 8
  , (v >>> 8).truncate 8
  , (v >>> 16).truncate 8
  , (v >>> 24).truncate 8
  , (v >>> 32).truncate 8
  , (v >>> 40).truncate 8
  , (v >>> 48).truncate 8
  , (v >>> 56).truncate 8
  ]

theorem u64LEBytes_length (v : Word) : (u64LEBytes v).length = 8 := rfl

/-- Twenty big-endian bytes of a 160-bit address word. -/
def addressBEBytes (v : BitVec 160) : List Byte :=
  [ (v >>> 152).truncate 8
  , (v >>> 144).truncate 8
  , (v >>> 136).truncate 8
  , (v >>> 128).truncate 8
  , (v >>> 120).truncate 8
  , (v >>> 112).truncate 8
  , (v >>> 104).truncate 8
  , (v >>> 96).truncate 8
  , (v >>> 88).truncate 8
  , (v >>> 80).truncate 8
  , (v >>> 72).truncate 8
  , (v >>> 64).truncate 8
  , (v >>> 56).truncate 8
  , (v >>> 48).truncate 8
  , (v >>> 40).truncate 8
  , (v >>> 32).truncate 8
  , (v >>> 24).truncate 8
  , (v >>> 16).truncate 8
  , (v >>> 8).truncate 8
  , v.truncate 8
  ]

theorem addressBEBytes_length (v : BitVec 160) : (addressBEBytes v).length = 20 := rfl

/-- ABI struct bytes for a successful pure withdrawal decode. -/
def successBytes (w : Withdrawal) : List Byte :=
  u64LEBytes (BitVec.ofNat 64 w.index) ++
  u64LEBytes (BitVec.ofNat 64 w.validatorIndex) ++
  addressBEBytes w.address ++
  List.replicate 4 (0 : Byte) ++
  u64LEBytes (BitVec.ofNat 64 w.amount)

theorem successBytes_length (w : Withdrawal) : (successBytes w).length = outputSize := by
  simp [successBytes, outputSize, u64LEBytes, addressBEBytes]

/-! ## ABI assertions -/

/-- Own an arbitrary byte region of a fixed length.  Used on failure paths,
    where the routine reports failure and the output buffer contents are not
    part of the functional contract. -/
def bytesRegionAny (base : Word) (n : Nat) : Assertion :=
  fun h => ∃ bs : List Byte, bs.length = n ∧ bytesRegion base bs h

theorem bytesRegionAny_pcFree (base : Word) (n : Nat) :
    (bytesRegionAny base n).pcFree := by
  intro h hp
  obtain ⟨bs, _hlen, hbs⟩ := hp
  exact bytesRegion_pcFree base bs h hbs

instance (base : Word) (n : Nat) : Assertion.PCFree (bytesRegionAny base n) :=
  ⟨bytesRegionAny_pcFree base n⟩

/-- Result portion of the ABI postcondition.  Success is exactly
    `decodeWithdrawal input = some w`; failure is exactly `decodeWithdrawal input = none`.
    The static schema above is not consulted here except through the fixed output size. -/
def resultPost (input : List Byte) (outBase : Word) : Assertion :=
  match decodeWithdrawal input with
  | some w =>
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outBase (successBytes w) **
        ⌜decodeWithdrawal input = some w⌝)
  | none =>
      ((.x10 ↦ᵣ (1 : Word)) ** bytesRegionAny outBase outputSize **
        ⌜decodeWithdrawal input = none⌝)

theorem resultPost_success {input : List Byte} {outBase : Word} {w : Withdrawal}
    (hdec : decodeWithdrawal input = some w) :
    resultPost input outBase =
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outBase (successBytes w) **
        ⌜decodeWithdrawal input = some w⌝) := by
  unfold resultPost
  rw [hdec]

theorem resultPost_failure {input : List Byte} {outBase : Word}
    (hdec : decodeWithdrawal input = none) :
    resultPost input outBase =
      ((.x10 ↦ᵣ (1 : Word)) ** bytesRegionAny outBase outputSize **
        ⌜decodeWithdrawal input = none⌝) := by
  unfold resultPost
  rw [hdec]

/-- A minimal ABI precondition for a withdrawal decoder entry.  A concrete
    program proof may strengthen this with scratch registers, stack cells, or
    helper-code frames through the WP precondition. -/
def abiPre (inputBase outBase raVal : Word) (input : List Byte) : Assertion :=
  ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 input.length) **
   (.x12 ↦ᵣ outBase) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) **
   bytesRegion inputBase input ** bytesRegionAny outBase outputSize)

/-- ABI postcondition common to any implementation of `withdrawal_decode`.
    It preserves `ra`, preserves the input bytes, and reports the pure decoder
    result through `resultPost`. Scratch and argument registers not mentioned
    here may be described by a stronger implementation-specific postcondition. -/
def abiPost (inputBase outBase raVal : Word) (input : List Byte) : Assertion :=
  ((.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputBase input **
    resultPost input outBase)

/-- A WP-facing certificate that a concrete control-flow proof implements the
    withdrawal decoder ABI.  The computed precondition is `cfg.pre`, so generated
    proofs can add whatever scratch resources their chosen program needs. -/
abbrev Cert (entry exit_ : Word) (cr : CodeReq)
    (inputBase outBase raVal : Word) (input : List Byte) :=
  WP.CFG.Cert entry exit_ cr (abiPost inputBase outBase raVal input)

def certPre {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase outBase raVal input) : Assertion :=
  cert.pre

theorem certSound {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase outBase raVal input) :
    cpsTripleWithin cert.nSteps entry exit_ cr cert.pre
      (abiPost inputBase outBase raVal input) :=
  cert.sound

/-- Package an implementation triple as a withdrawal decoder certificate. -/
def ofSpec {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre : Assertion} {inputBase outBase raVal : Word} {input : List Byte}
    (h : cpsTripleWithin nSteps entry exit_ cr pre
      (abiPost inputBase outBase raVal input)) :
    Cert entry exit_ cr inputBase outBase raVal input :=
  WP.CFG.block (WP.Entails.refl _) h

end WithdrawalDecode
end EvmAsm.Rv64.RLP
