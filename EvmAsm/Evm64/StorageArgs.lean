/-
  EvmAsm.Evm64.StorageArgs

  Pure stack-argument records and decoder for SLOAD and SSTORE (GH #110).
-/

import EvmAsm.Evm64.EvmWord

namespace EvmAsm.Evm64

namespace StorageArgs

/-- SLOAD stack arguments: one storage slot key. -/
structure SLoad where
  slot : EvmWord
  deriving Repr

/-- SSTORE stack arguments: storage slot key and new value. -/
structure SStore where
  slot : EvmWord
  value : EvmWord
  deriving Repr

inductive Kind where
  | sload
  | sstore
  deriving DecidableEq, Repr

/-- The storage opcode kinds covered by GH #110. -/
def allKinds : List Kind :=
  [.sload, .sstore]

inductive Decoded where
  | sload (args : SLoad)
  | sstore (args : SStore)
  deriving Repr

def argumentCount : Kind → Nat
  | .sload => 1
  | .sstore => 2

def resultCount : Kind → Nat
  | .sload => 1
  | .sstore => 0

def writesStorage : Kind → Bool
  | .sload => false
  | .sstore => true

theorem allKinds_nodup :
    allKinds.Nodup := by
  decide

theorem mem_allKinds (kind : Kind) :
    kind ∈ allKinds := by
  cases kind <;> decide

theorem allKinds_argumentCounts :
    allKinds.map argumentCount = [1, 2] := rfl

theorem allKinds_resultCounts :
    allKinds.map resultCount = [1, 0] := rfl

theorem allKinds_writesStorage :
    allKinds.map writesStorage = [false, true] := rfl

def mkSLoad (slot : EvmWord) : SLoad :=
  { slot := slot }

def mkSStore (slot value : EvmWord) : SStore :=
  { slot := slot, value := value }

def decodedKind : Decoded → Kind
  | .sload _ => .sload
  | .sstore _ => .sstore

/--
Decode SLOAD/SSTORE stack arguments from top-of-stack order:
`slot` for SLOAD and `slot, value` for SSTORE.

Distinctive token: StorageArgs.decodeStorageStack? #110.
-/
def decodeStorageStack? : Kind → List EvmWord → Option Decoded
  | .sload, slot :: _ => some (.sload (mkSLoad slot))
  | .sstore, slot :: value :: _ => some (.sstore (mkSStore slot value))
  | _, _ => none

theorem decodeStorageStack?_sload
    (slot : EvmWord) (rest : List EvmWord) :
    decodeStorageStack? .sload (slot :: rest) =
      some (.sload (mkSLoad slot)) := rfl

theorem decodeStorageStack?_sstore
    (slot value : EvmWord) (rest : List EvmWord) :
    decodeStorageStack? .sstore (slot :: value :: rest) =
      some (.sstore (mkSStore slot value)) := rfl

/--
SLOAD stack decoding succeeds exactly when the stack has a top slot word.

Distinctive token: StorageArgs.decodeStorageStack?_sload_eq_some_iff #110.
-/
theorem decodeStorageStack?_sload_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? .sload stack = some decoded ↔
      ∃ slot rest, stack = slot :: rest ∧ decoded = .sload (mkSLoad slot) := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeStorageStack?] at h_decode
    | cons slot rest =>
        simp [decodeStorageStack?] at h_decode
        cases h_decode
        exact ⟨slot, rest, rfl, rfl⟩
  · rintro ⟨slot, rest, rfl, rfl⟩
    rfl

theorem decodeStorageStack?_sstore_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? .sstore stack = some decoded ↔
      ∃ slot value rest,
        stack = slot :: value :: rest ∧ decoded = .sstore (mkSStore slot value) := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeStorageStack?] at h_decode
    | cons slot tail =>
        cases tail with
        | nil => simp [decodeStorageStack?] at h_decode
        | cons value rest =>
            simp [decodeStorageStack?] at h_decode
            cases h_decode
            exact ⟨slot, value, rest, rfl, rfl⟩
  · rintro ⟨slot, value, rest, rfl, rfl⟩
    rfl

theorem decodeStorageStack?_sload_eq_none_iff
    (stack : List EvmWord) :
    decodeStorageStack? .sload stack = none ↔ stack.length < argumentCount .sload := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [argumentCount]
    | cons slot rest => simp [decodeStorageStack?] at h_decode
  · intro h_len
    cases stack with
    | nil => rfl
    | cons slot rest =>
        simp [argumentCount] at h_len

theorem decodeStorageStack?_sstore_eq_none_iff
    (stack : List EvmWord) :
    decodeStorageStack? .sstore stack = none ↔ stack.length < argumentCount .sstore := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [argumentCount]
    | cons slot tail =>
        cases tail with
        | nil => simp [argumentCount]
        | cons value rest => simp [decodeStorageStack?] at h_decode
  · intro h_len
    cases stack with
    | nil => rfl
    | cons slot tail =>
        cases tail with
        | nil => rfl
        | cons value rest =>
            simp [argumentCount] at h_len
            omega

theorem decodeStorageStack?_eq_some_iff
    (kind : Kind) (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? kind stack = some decoded ↔
      match kind with
      | .sload =>
          ∃ slot rest,
            stack = slot :: rest ∧ decoded = .sload (mkSLoad slot)
      | .sstore =>
          ∃ slot value rest,
            stack = slot :: value :: rest ∧ decoded = .sstore (mkSStore slot value) := by
  cases kind with
  | sload => exact decodeStorageStack?_sload_eq_some_iff stack decoded
  | sstore => exact decodeStorageStack?_sstore_eq_some_iff stack decoded

theorem decodeStorageStack?_sload_kind_of_some
    {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? .sload stack = some decoded) :
    decodedKind decoded = .sload := by
  rw [decodeStorageStack?_sload_eq_some_iff] at h_decode
  rcases h_decode with ⟨slot, rest, h_stack, h_decoded⟩
  subst h_decoded
  rfl

theorem decodeStorageStack?_sstore_kind_of_some
    {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? .sstore stack = some decoded) :
    decodedKind decoded = .sstore := by
  rw [decodeStorageStack?_sstore_eq_some_iff] at h_decode
  rcases h_decode with ⟨slot, value, rest, h_stack, h_decoded⟩
  subst h_decoded
  rfl

theorem decodeStorageStack?_kind_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    decodedKind decoded = kind := by
  cases kind with
  | sload => exact decodeStorageStack?_sload_kind_of_some h_decode
  | sstore => exact decodeStorageStack?_sstore_kind_of_some h_decode

theorem decodeStorageStack?_argumentCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    argumentCount (decodedKind decoded) = argumentCount kind := by
  rw [decodeStorageStack?_kind_of_some h_decode]

theorem decodeStorageStack?_resultCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    resultCount (decodedKind decoded) = resultCount kind := by
  rw [decodeStorageStack?_kind_of_some h_decode]

theorem decodeStorageStack?_writesStorage_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    writesStorage (decodedKind decoded) = writesStorage kind := by
  rw [decodeStorageStack?_kind_of_some h_decode]

theorem decodeStorageStack?_eq_none_iff
    (kind : Kind) (stack : List EvmWord) :
    decodeStorageStack? kind stack = none ↔ stack.length < argumentCount kind := by
  cases kind with
  | sload => exact decodeStorageStack?_sload_eq_none_iff stack
  | sstore => exact decodeStorageStack?_sstore_eq_none_iff stack

theorem decodeStorageStack?_sload_none_of_empty :
    decodeStorageStack? .sload [] = none := rfl

theorem decodeStorageStack?_sstore_none_of_empty :
    decodeStorageStack? .sstore [] = none := rfl

theorem decodeStorageStack?_sstore_none_of_one
    (slot : EvmWord) :
    decodeStorageStack? .sstore [slot] = none := rfl

theorem decodedKind_sload (slot : EvmWord) :
    decodedKind (.sload (mkSLoad slot)) = .sload := rfl

theorem decodedKind_sstore (slot value : EvmWord) :
    decodedKind (.sstore (mkSStore slot value)) = .sstore := rfl

theorem argumentCount_sload : argumentCount .sload = 1 := rfl

theorem argumentCount_sstore : argumentCount .sstore = 2 := rfl

theorem resultCount_sload : resultCount .sload = 1 := rfl

theorem resultCount_sstore : resultCount .sstore = 0 := rfl

theorem writesStorage_sload : writesStorage .sload = false := rfl

theorem writesStorage_sstore : writesStorage .sstore = true := rfl

theorem decoded_sload_slot (slot : EvmWord) :
    (mkSLoad slot).slot = slot := rfl

theorem decoded_sstore_slot (slot value : EvmWord) :
    (mkSStore slot value).slot = slot := rfl

theorem decoded_sstore_value (slot value : EvmWord) :
    (mkSStore slot value).value = value := rfl

end StorageArgs

end EvmAsm.Evm64
