/-
  EvmAsm.Evm64.AccountRlp

  Bridge between RLP-encoded account bytes and the structured `EvmAsm.EL.Account`
  world-state record.

  An Ethereum account RLP-encodes as `RLP([nonce, balance, storageRoot, codeHash])`
  — a 4-item list where `nonce` and `balance` are minimal big-endian RLP *scalars*
  (no leading zero; empty is the zero scalar) and `storageRoot` / `codeHash` are
  fixed 32-byte RLP *strings*. The `code` field is NOT part of this encoding.

  This module mirrors `EvmAsm.EL.Withdrawal` (a 4-field consensus struct) for the
  decode direction and `EvmAsm.Evm64.MptAssertions` (`mptNodeIs`) for the
  separation-logic assertion, and proves:

  * `word256Bytes32_length` / `fromBytesBE_word256Bytes32` — the fixed-width
    32-byte big-endian view of a 256-bit word and its decode inverse.
  * `decodeAccount_encodeAccount` — the full round-trip (for accounts whose nonce
    fits 256 bits and whose `code` is empty, matching the RLP model).
  * `encodeAccount_injective` — distinct such accounts have distinct encodings.
  * `accountRlpIs` + `pcFree_accountRlpIs` — the byte-region ownership assertion.
-/

import EvmAsm.EL.WorldState
import EvmAsm.EL.RLP.Properties
import EvmAsm.EL.RLP.FullDecode
import EvmAsm.EL.RLP.Scalar
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Evm64

open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64

/-! ## Fixed-width big-endian bytes of a 256-bit word -/

/-- `256 ^ 32 = 2 ^ 256` — the two ways to express the 256-bit word cap. -/
private theorem pow256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide

/-- `encodeBytes` adds at most 9 prefix bytes (mirrors the MPT lemma; kept local to
    avoid importing the heavier `MptAssertions` module). -/
private theorem encodeBytes_len_le (data : List (BitVec 8)) (h : data.length < 256 ^ 8) :
    (encodeBytes data).length ≤ data.length + 9 := by
  match data with
  | [b] => by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
  | [] => simp [encodeBytes]
  | b1 :: b2 :: tl =>
    simp only [encodeBytes]
    by_cases hshort : (b1 :: b2 :: tl).length ≤ 55
    · rw [if_pos (by simpa using hshort)]
      simp
    · rw [if_neg (by simpa using hshort)]
      have hlb : (Nat.toBytesBE (b1 :: b2 :: tl).length).length ≤ 8 :=
        Nat.toBytesBE_length_le _ 8 (by exact_mod_cast h)
      simp only [List.length_append, List.length_cons, List.length_nil]
      simp at hlb ⊢
      omega

/-- `n` as exactly `len` big-endian bytes (most-significant first), truncating the
    high end and zero-padding the low end as needed. `toBytesBEFixed len n` decodes
    (big-endian) back to `n % 256 ^ len`. -/
def toBytesBEFixed : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | k + 1, n => toBytesBEFixed k (n / 256) ++ [BitVec.ofNat 8 (n % 256)]

theorem toBytesBEFixed_length (k n : Nat) : (toBytesBEFixed k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hstep : toBytesBEFixed (k + 1) n
        = toBytesBEFixed k (n / 256) ++ [BitVec.ofNat 8 (n % 256)] := rfl
    rw [hstep, List.length_append, ih (n / 256)]
    simp

theorem fromBytesBE_toBytesBEFixed (k n : Nat) :
    Nat.fromBytesBE (toBytesBEFixed k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [toBytesBEFixed, Nat.fromBytesBE_nil, Nat.mod_one]
  | succ k ih =>
    have hstep : toBytesBEFixed (k + 1) n
        = toBytesBEFixed k (n / 256) ++ [BitVec.ofNat 8 (n % 256)] := rfl
    rw [hstep, Nat.fromBytesBE_snoc, ih (n / 256)]
    have h256eq : (2 : Nat) ^ 8 = 256 := by decide
    have hlt : n % 256 < 256 := Nat.mod_lt n (by decide)
    have hb : (BitVec.ofNat 8 (n % 256)).toNat = n % 256 := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (h256eq ▸ hlt)
    rw [hb, show (256 : Nat) ^ (k + 1) = 256 * 256 ^ k from by
          rw [Nat.pow_succ, Nat.mul_comm], Nat.mod_mul]
    omega

/-- The 32 big-endian bytes of a 256-bit word (byte `i` = bits
    `[8·(31−i), 8·(31−i)+8)`). -/
def word256Bytes32 (w : Word256) : List (BitVec 8) :=
  toBytesBEFixed 32 w.toNat

theorem word256Bytes32_length (w : Word256) : (word256Bytes32 w).length = 32 :=
  toBytesBEFixed_length 32 w.toNat

/-- The 32-byte big-endian form decodes back to the word's value: the (leading)
    zero padding does not change the big-endian value. -/
theorem fromBytesBE_word256Bytes32 (w : Word256) :
    Nat.fromBytesBE (word256Bytes32 w) = w.toNat := by
  unfold word256Bytes32
  rw [fromBytesBE_toBytesBEFixed, pow256_32]
  exact Nat.mod_eq_of_lt w.isLt

/-- `BitVec.ofNat 256` of a 256-bit word's `toNat` is the word itself. -/
private theorem ofNat256_toNat (w : BitVec 256) : BitVec.ofNat 256 w.toNat = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

/-! ## Encode / decode -/

/-- The RLP encoding of an account: `RLP([nonce, balance, storageRoot, codeHash])`.
    `nonce` and `balance` are minimal big-endian scalars; `storageRoot` and
    `codeHash` are fixed 32-byte strings. The `code` field is not encoded. -/
def encodeAccount (a : Account) : List (BitVec 8) :=
  encode (.list [.bytes (Nat.toBytesBE a.nonce),
                 .bytes (Nat.toBytesBE a.balance.toNat),
                 .bytes (word256Bytes32 a.storageRoot),
                 .bytes (word256Bytes32 a.codeHash)])

/-- Decode account RLP: a 4-element byte-list whose two scalar elements are
    canonical minimal big-endian (no leading zero; empty is the zero scalar) and
    whose two hash elements are exactly 32 bytes. Any structural deviation,
    non-canonical scalar, wrong hash length, or trailing bytes yields `none`. The
    reconstructed account has empty `code` (code is not part of this encoding). -/
def decodeAccount (bs : List (BitVec 8)) : Option Account :=
  match decodeFully bs with
  | some (.list [.bytes n, .bytes b, .bytes sr, .bytes ch]) =>
      if (n.headD 1 ≠ 0 ∨ n = []) ∧ (b.headD 1 ≠ 0 ∨ b = [])
         ∧ sr.length = 32 ∧ ch.length = 32 then
        some { nonce := Nat.fromBytesBE n,
               balance := BitVec.ofNat 256 (Nat.fromBytesBE b),
               storageRoot := BitVec.ofNat 256 (Nat.fromBytesBE sr),
               codeHash := BitVec.ofNat 256 (Nat.fromBytesBE ch),
               code := [] }
      else none
  | _ => none

/-! ## Length bound (for the decode round-trip and the assertion) -/

/-- A minimal big-endian scalar `< 2 ^ 256` is at most 32 bytes. -/
private theorem toBytesBE_len_le_32 {n : Nat} (h : n < 2 ^ 256) :
    (Nat.toBytesBE n).length ≤ 32 :=
  Nat.toBytesBE_length_le n 32 (by rw [pow256_32]; exact h)

/-- The RLP encoding of an account with `nonce < 2 ^ 256` is far below the
    decoder's `256 ^ 8` length-field bound (the payload is ~110 bytes). -/
theorem encodeAccount_length_lt (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    (encodeAccount a).length < 256 ^ 8 := by
  have hbig : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  have hn32 : (Nat.toBytesBE a.nonce).length ≤ 32 := toBytesBE_len_le_32 hnonce
  have hb32 : (Nat.toBytesBE a.balance.toNat).length ≤ 32 :=
    toBytesBE_len_le_32 a.balance.isLt
  have hsr32 : (word256Bytes32 a.storageRoot).length = 32 := word256Bytes32_length _
  have hch32 : (word256Bytes32 a.codeHash).length = 32 := word256Bytes32_length _
  have e0 : (encodeBytes (Nat.toBytesBE a.nonce)).length ≤ (Nat.toBytesBE a.nonce).length + 9 :=
    encodeBytes_len_le _ (Nat.lt_of_le_of_lt hn32 (by decide))
  have e1 : (encodeBytes (Nat.toBytesBE a.balance.toNat)).length
      ≤ (Nat.toBytesBE a.balance.toNat).length + 9 :=
    encodeBytes_len_le _ (Nat.lt_of_le_of_lt hb32 (by decide))
  have e2 : (encodeBytes (word256Bytes32 a.storageRoot)).length
      ≤ (word256Bytes32 a.storageRoot).length + 9 :=
    encodeBytes_len_le _ (by rw [hsr32]; decide)
  have e3 : (encodeBytes (word256Bytes32 a.codeHash)).length
      ≤ (word256Bytes32 a.codeHash).length + 9 :=
    encodeBytes_len_le _ (by rw [hch32]; decide)
  have hpay : (encode.encodeItems [RLPItem.bytes (Nat.toBytesBE a.nonce),
                 .bytes (Nat.toBytesBE a.balance.toNat),
                 .bytes (word256Bytes32 a.storageRoot),
                 .bytes (word256Bytes32 a.codeHash)]).length ≤ 164 := by
    show (encode (.bytes (Nat.toBytesBE a.nonce)) ++
          (encode (.bytes (Nat.toBytesBE a.balance.toNat)) ++
           (encode (.bytes (word256Bytes32 a.storageRoot)) ++
            (encode (.bytes (word256Bytes32 a.codeHash)) ++ [])))).length ≤ 164
    simp only [List.length_append, List.length_nil]
    show (encodeBytes (Nat.toBytesBE a.nonce)).length +
          ((encodeBytes (Nat.toBytesBE a.balance.toNat)).length +
           ((encodeBytes (word256Bytes32 a.storageRoot)).length +
            ((encodeBytes (word256Bytes32 a.codeHash)).length + 0))) ≤ 164
    omega
  show (encode (.list [.bytes (Nat.toBytesBE a.nonce),
                 .bytes (Nat.toBytesBE a.balance.toNat),
                 .bytes (word256Bytes32 a.storageRoot),
                 .bytes (word256Bytes32 a.codeHash)])).length < 256 ^ 8
  unfold encode
  dsimp only
  by_cases hshort : (encode.encodeItems [RLPItem.bytes (Nat.toBytesBE a.nonce),
                 .bytes (Nat.toBytesBE a.balance.toNat),
                 .bytes (word256Bytes32 a.storageRoot),
                 .bytes (word256Bytes32 a.codeHash)]).length ≤ 55
  · rw [if_pos hshort]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [if_neg hshort]
    have hlb := Nat.toBytesBE_length_le
      (encode.encodeItems [RLPItem.bytes (Nat.toBytesBE a.nonce),
         .bytes (Nat.toBytesBE a.balance.toNat),
         .bytes (word256Bytes32 a.storageRoot),
         .bytes (word256Bytes32 a.codeHash)]).length 8 (by omega)
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-! ## Round-trip and injectivity -/

/-- A minimal big-endian scalar is canonical: it has no leading zero byte (the
    empty list is the canonical zero). -/
private theorem toBytesBE_canonical (n : Nat) :
    (Nat.toBytesBE n).headD 1 ≠ 0 ∨ Nat.toBytesBE n = [] := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; right; exact Nat.toBytesBE_zero
  · left
    obtain ⟨b, tl, hbtl, hb⟩ := Nat.toBytesBE_eq_cons_of_pos n h
    rw [hbtl]; simpa using hb

/-- **Round-trip.** For an account whose nonce fits 256 bits and whose `code` is
    empty (code is not part of the RLP), decoding its encoding recovers it. -/
theorem decodeAccount_encodeAccount (a : Account)
    (hnonce : a.nonce < 2 ^ 256) (hcode : a.code = []) :
    decodeAccount (encodeAccount a) = some a := by
  have hdec : decodeFully (encodeAccount a)
      = some (.list [.bytes (Nat.toBytesBE a.nonce),
                     .bytes (Nat.toBytesBE a.balance.toNat),
                     .bytes (word256Bytes32 a.storageRoot),
                     .bytes (word256Bytes32 a.codeHash)]) := by
    unfold encodeAccount
    exact decodeFully_encode _ (encodeAccount_length_lt a hnonce)
  unfold decodeAccount
  rw [hdec]
  dsimp only
  rw [if_pos ⟨toBytesBE_canonical a.nonce, toBytesBE_canonical a.balance.toNat,
      word256Bytes32_length a.storageRoot, word256Bytes32_length a.codeHash⟩]
  have e2 : BitVec.ofNat 256 (Nat.fromBytesBE (Nat.toBytesBE a.balance.toNat)) = a.balance := by
    rw [Nat.fromBytesBE_toBytesBE]; exact ofNat256_toNat a.balance
  have e3 : BitVec.ofNat 256 (Nat.fromBytesBE (word256Bytes32 a.storageRoot)) = a.storageRoot := by
    rw [fromBytesBE_word256Bytes32]; exact ofNat256_toNat a.storageRoot
  have e4 : BitVec.ofNat 256 (Nat.fromBytesBE (word256Bytes32 a.codeHash)) = a.codeHash := by
    rw [fromBytesBE_word256Bytes32]; exact ofNat256_toNat a.codeHash
  rw [Nat.fromBytesBE_toBytesBE, e2, e3, e4, ← hcode]

/-- **Injectivity** (for accounts with `nonce < 2 ^ 256` and empty `code`):
    distinct such accounts never share an encoding. -/
theorem encodeAccount_injective {a₁ a₂ : Account}
    (h₁ : a₁.nonce < 2 ^ 256) (h₂ : a₂.nonce < 2 ^ 256)
    (hc₁ : a₁.code = []) (hc₂ : a₂.code = [])
    (heq : encodeAccount a₁ = encodeAccount a₂) : a₁ = a₂ := by
  have r₁ := decodeAccount_encodeAccount a₁ h₁ hc₁
  have r₂ := decodeAccount_encodeAccount a₂ h₂ hc₂
  rw [heq, r₂] at r₁
  exact (Option.some.injEq _ _ ▸ r₁).symm

/-! ## The account byte-region assertion -/

/-- `accountRlpIs ptr a` — ownership of the RLP encoding of account `a` at the
    (dword-aligned) byte pointer `ptr`, carrying the decoder's length bound. Models
    `mptNodeIs`. -/
def accountRlpIs (ptr : Word) (a : Account) : Assertion :=
  fun ps => (encodeAccount a).length < 256 ^ 8 ∧ bytesRegion ptr (encodeAccount a) ps

theorem pcFree_accountRlpIs {ptr : Word} {a : Account} : (accountRlpIs ptr a).pcFree :=
  fun ps h => bytesRegion_pcFree ptr (encodeAccount a) ps h.2

instance (ptr : Word) (a : Account) : Assertion.PCFree (accountRlpIs ptr a) :=
  ⟨pcFree_accountRlpIs⟩

end EvmAsm.Evm64
