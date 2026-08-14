/-
  EvmAsm.Evm64.AccountFieldExtractSpec

  Semantic bridge lemmas for the account-field accessor subroutines
  `account_extract_nonce` (RLP field 0, u64) and `account_extract_balance`
  (RLP field 1, u256 BE) — see `EvmAsm/Codegen/Programs/AccountFieldExtract.lean`.

  Each accessor's calling convention (from that file) is:
    a0 = account_rlp ptr, a1 = account_rlp byte length, a2 = output ptr, ra = return;
    a0 (output) = 0 success / 1 failure.
  The accessor zeroes the output, sets the field index in a2 (`0` for nonce, `1`
  for balance), pins the output ptr in a3, and tail-calls the codegen helper
  `rlp_field_to_u64` / `rlp_field_to_u256_be`, which walks the RLP list to the
  n-th item and decodes its (prefix-stripped) content scalar into the output cell.

  ## What this file proves, and why it is not the full accessor Hoare triple

  The account RLP is
    `encode (.list [.bytes (Nat.toBytesBE nonce),
                    .bytes (Nat.toBytesBE balance.toNat),
                    .bytes (word256Bytes32 storageRoot),
                    .bytes (word256Bytes32 codeHash)])`,
  so once the helper has located field `i`'s content byte-list, the *value* it must
  produce is fixed by the RLP model. This file proves that model-level interface —
  the reusable facts a future accessor Hoare triple will consume from the callee's
  (yet-to-exist) spec, stated so they compose directly:

  * `decodeFully_encodeAccount` — the account RLP decodes to its 4-field item list
    (so field 0 content = `Nat.toBytesBE nonce`, field 1 content =
    `Nat.toBytesBE balance.toNat`);
  * `account_nonce_from_field0` / `account_balance_from_field1` — the field-0 /
    field-1 content bytes decode big-endian back to `nonce` / `balance`;
  * `account_nonce_field_len_le_8` (given `nonce < 2^64`, EIP-2681) /
    `account_balance_field_len_le_32` — the length bounds the `…_to_u64` /
    `…_to_u256_be` content decoders require;
  * `account_nonce_field_canonical` / `account_balance_field_canonical` — the
    minimal-big-endian canonicality the content decoders enforce.

  ### The remaining obstacle (why no `cpsTripleWithin` accessor triple here)

  The accessor programs tail-call the **codegen** helpers `rlp_field_to_u64`
  (`GuestAddrs.rlp_field_to_u64`) and the offline-proof helper
  `rlp_field_to_u256_be` (anchored by
  `RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be`), defined as
  `rlpFieldToU64_prog` / `rlpFieldToU256Be_prog` in
  `EvmAsm/Codegen/Programs/Tx.lean`. The latter is no longer in the production
  guest closure (#12386), but its Program remains available for these proofs.
  Those callees:
    1. have **no verified `cpsTripleWithin`/`Cert` spec anywhere in the repo** (the
       verified `rlp_field0_to_u64` in `EvmAsm/Rv64/RLP/Field0ToU64.lean` is a
       narrow *drop-in replacement*, explicitly "not (yet) wired into codegen's
       unverified `rlp_field_to_u64`", and is field-0-only with a different
       value/status calling convention);
    2. read global `.data` spill symbols (`rfu_offset` / `rfu_length`) via
       `AUIPC`/`ADDI` la-relocs and call `rlp_list_nth_item`, so a spec would have
       to model that global memory and the nth-item walk;
    3. are reached by a **fixed guest-address** `JAL`
       (`jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.account_extract_nonce+28)`),
       not a `base`-relative offset, so composing via `WP.cpsCallWithin` (as in
       `Field0ToU64.lean`) additionally needs a fixed-guest-address `CodeReq`
       layout placing the callee at its absolute address.

  Proving the accessor triples is therefore a multi-PR effort gated on first
  landing a verified spec for the codegen `rlp_field_to_u64` / `rlp_field_to_u256_be`
  wrappers. This file lands the model-level bridge those triples will build on;
  no `sorry`/`admit`/`native_decide`/`bv_decide` is used, and every theorem
  depends only on the three classical axioms.
-/

import EvmAsm.Evm64.AccountRlp

namespace EvmAsm.Evm64

open EvmAsm.EL
open EvmAsm.EL.RLP

/-- `BitVec.ofNat 256` of a 256-bit word's `toNat` is the word itself. (Local copy
    of `AccountRlp`'s private `ofNat256_toNat`.) -/
private theorem ofNat256_toNat (w : BitVec 256) : BitVec.ofNat 256 w.toNat = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

/-! ## The account RLP decodes to its 4-field item list -/

/-- **Field-list bridge.** For an account whose nonce fits 256 bits, the RLP
    encoding decodes to the 4-item list whose element `i` is field `i`'s content:
    field 0 = `Nat.toBytesBE nonce`, field 1 = `Nat.toBytesBE balance.toNat`,
    field 2 = `word256Bytes32 storageRoot`, field 3 = `word256Bytes32 codeHash`.

    This is the semantic anchor for both accessors: the (unverified) helper's job
    is to reproduce, at runtime, the content byte-list this lemma pins down. -/
theorem decodeFully_encodeAccount (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    decodeFully (encodeAccount a)
      = some (.list [.bytes (Nat.toBytesBE a.nonce),
                     .bytes (Nat.toBytesBE a.balance.toNat),
                     .bytes (word256Bytes32 a.storageRoot),
                     .bytes (word256Bytes32 a.codeHash)]) := by
  unfold encodeAccount
  exact decodeFully_encode _ (encodeAccount_length_lt a hnonce)

/-! ## Field-value bridges: content bytes decode to the field value -/

/-- **`account_extract_nonce` value.** Field 0's content bytes, decoded big-endian
    (exactly what `rlp_field_to_u64` computes from the located content), recover the
    nonce. -/
theorem account_nonce_from_field0 (a : Account) :
    Nat.fromBytesBE (Nat.toBytesBE a.nonce) = a.nonce :=
  Nat.fromBytesBE_toBytesBE a.nonce

/-- **`account_extract_balance` value.** Field 1's content bytes, decoded
    big-endian into a 256-bit word (exactly what `rlp_field_to_u256_be` computes),
    recover the balance. -/
theorem account_balance_from_field1 (a : Account) :
    BitVec.ofNat 256 (Nat.fromBytesBE (Nat.toBytesBE a.balance.toNat)) = a.balance := by
  rw [Nat.fromBytesBE_toBytesBE]
  exact ofNat256_toNat a.balance

/-! ## Field length bounds (the content decoders' width preconditions) -/

/-- Field 0's content is at most 8 bytes when the nonce fits a `u64` (EIP-2681
    caps the nonce at `2^64 - 1`), so `rlp_field_to_u64`'s `len ≤ 8` precondition
    holds. -/
theorem account_nonce_field_len_le_8 (a : Account) (h : a.nonce < 2 ^ 64) :
    (Nat.toBytesBE a.nonce).length ≤ 8 :=
  Nat.toBytesBE_length_le a.nonce 8 (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]; exact h)

/-- Field 1's content is at most 32 bytes (the balance is a `u256`), so
    `rlp_field_to_u256_be`'s `len ≤ 32` precondition holds. -/
theorem account_balance_field_len_le_32 (a : Account) :
    (Nat.toBytesBE a.balance.toNat).length ≤ 32 :=
  Nat.toBytesBE_length_le a.balance.toNat 32
    (by rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]; exact a.balance.isLt)

/-! ## Field canonicality (the content decoders' minimal-big-endian precondition) -/

/-- Field 0's content is a canonical minimal-big-endian scalar: no leading zero
    byte, and the empty list is the canonical zero. Matches the canonicality rule
    enforced by the content-to-u64 decoder. -/
theorem account_nonce_field_canonical (a : Account) :
    (Nat.toBytesBE a.nonce).headD 1 ≠ 0 ∨ Nat.toBytesBE a.nonce = [] := by
  rcases Nat.eq_zero_or_pos a.nonce with h | h
  · rw [h]; right; exact Nat.toBytesBE_zero
  · left
    obtain ⟨b, tl, hbtl, hb⟩ := Nat.toBytesBE_eq_cons_of_pos a.nonce h
    rw [hbtl]; simpa using hb

/-- Field 1's content is a canonical minimal-big-endian scalar. Matches the
    canonicality rule enforced by the content-to-u256-be decoder. -/
theorem account_balance_field_canonical (a : Account) :
    (Nat.toBytesBE a.balance.toNat).headD 1 ≠ 0 ∨ Nat.toBytesBE a.balance.toNat = [] := by
  rcases Nat.eq_zero_or_pos a.balance.toNat with h | h
  · rw [h]; right; exact Nat.toBytesBE_zero
  · left
    obtain ⟨b, tl, hbtl, hb⟩ := Nat.toBytesBE_eq_cons_of_pos a.balance.toNat h
    rw [hbtl]; simpa using hb

end EvmAsm.Evm64
