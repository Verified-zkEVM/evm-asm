/-
  EvmAsm.Evm64.KeccakArgsStackDecode

  Pure top-of-stack decoder for KECCAK256/SHA3 arguments (GH #111).
-/

module

public import EvmAsm.Evm64.KeccakArgs

@[expose] public section

namespace EvmAsm.Evm64

namespace KeccakArgsStackDecode

open KeccakArgs

/--
Decode KECCAK256/SHA3 stack arguments from the top-of-stack list order:
`offset, size`.

Distinctive token: KeccakArgsStackDecode.decodeKeccakStack? #111.
-/
def decodeKeccakStack? : List EvmWord → Option Args
  | offset :: size :: _ => some (keccakArgs offset size)
  | _ => none

theorem decodeKeccakStack?_some
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeKeccakStack? (offset :: size :: rest) =
      some (keccakArgs offset size) := rfl

/--
`decodeKeccakStack?` returns `some` exactly when the stack starts with two
elements `offset, size`, and the decoded args are `keccakArgs offset size`.

Distinctive token: KeccakArgsStackDecode.decodeKeccakStack?_eq_some_iff #111.
-/
theorem decodeKeccakStack?_eq_some_iff
    (stack : List EvmWord) (decoded : Args) :
    decodeKeccakStack? stack = some decoded ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧ decoded = keccakArgs offset size := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeKeccakStack?] at h_decode
    | cons offset tail =>
        cases tail with
        | nil => simp [decodeKeccakStack?] at h_decode
        | cons size rest =>
            simp [decodeKeccakStack?] at h_decode
            exact ⟨offset, size, rest, rfl, h_decode.symm⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeKeccakStack?_inputRange_of_some
    {stack : List EvmWord} {decoded : Args}
    (h_decode : decodeKeccakStack? stack = some decoded) :
    ∃ offset size rest,
      stack = offset :: size :: rest ∧
        inputRange decoded = { offset := offset, size := size } := by
  rw [decodeKeccakStack?_eq_some_iff] at h_decode
  rcases h_decode with ⟨offset, size, rest, h_stack, h_decoded⟩
  subst h_decoded
  exact ⟨offset, size, rest, h_stack, rfl⟩

theorem decodeKeccakStack?_inputOffsetNat_of_some
    {stack : List EvmWord} {decoded : Args}
    (h_decode : decodeKeccakStack? stack = some decoded) :
    ∃ offset size rest,
      stack = offset :: size :: rest ∧ inputOffsetNat decoded = offset.toNat := by
  rw [decodeKeccakStack?_eq_some_iff] at h_decode
  rcases h_decode with ⟨offset, size, rest, h_stack, h_decoded⟩
  subst h_decoded
  exact ⟨offset, size, rest, h_stack, rfl⟩

theorem decodeKeccakStack?_inputSizeNat_of_some
    {stack : List EvmWord} {decoded : Args}
    (h_decode : decodeKeccakStack? stack = some decoded) :
    ∃ offset size rest,
      stack = offset :: size :: rest ∧ inputSizeNat decoded = size.toNat := by
  rw [decodeKeccakStack?_eq_some_iff] at h_decode
  rcases h_decode with ⟨offset, size, rest, h_stack, h_decoded⟩
  subst h_decoded
  exact ⟨offset, size, rest, h_stack, rfl⟩

/--
`decodeKeccakStack?` returns `none` exactly when the stack has fewer than
two elements.

Distinctive token: KeccakArgsStackDecode.decodeKeccakStack?_eq_none_iff #111.
-/
theorem decodeKeccakStack?_eq_none_iff
    (stack : List EvmWord) :
    decodeKeccakStack? stack = none ↔ stack.length < 2 := by
  cases stack with
  | nil => simp [decodeKeccakStack?]
  | cons offset tail =>
      cases tail with
      | nil => simp [decodeKeccakStack?]
      | cons size rest => simp [decodeKeccakStack?]

theorem decodeKeccakStack?_none_of_empty :
    decodeKeccakStack? [] = none := rfl

theorem decodeKeccakStack?_none_of_one
    (offset : EvmWord) :
    decodeKeccakStack? [offset] = none := rfl

theorem decoded_inputRange (offset size : EvmWord) :
    inputRange (keccakArgs offset size) =
      { offset := offset, size := size } := rfl

theorem decoded_inputOffsetNat (offset size : EvmWord) :
    inputOffsetNat (keccakArgs offset size) = offset.toNat := rfl

theorem decoded_inputSizeNat (offset size : EvmWord) :
    inputSizeNat (keccakArgs offset size) = size.toNat := rfl

theorem decoded_stackArgumentCount :
    stackArgumentCount = 2 := rfl

theorem decoded_resultCount :
    resultCount = 1 := rfl

end KeccakArgsStackDecode

end EvmAsm.Evm64
