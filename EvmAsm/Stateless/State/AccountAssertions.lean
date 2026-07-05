/-
  EvmAsm.Stateless.State.AccountAssertions

  Separation-logic assertions for the guest's account record.

  ## Layout faithfulness (what this describes)

  The guest has **no packed in-memory account struct**: the canonical
  account record is the RLP-encoded byte string
  `rlp([nonce, balance, storage_root, code_hash])` read out of the MPT
  state-trie leaves. Every guest account routine consumes or re-splices
  that byte string:

  * `account_decode` (`EvmAsm/Codegen/Programs/State.lean:61`, contract in
    `EvmAsm/Stateless/State/Account.lean`) — reads the RLP bytes and
    scatters the four decoded fields into four *caller-supplied* output
    slots: nonce as an 8-byte little-endian u64 (`SD`), balance as a
    32-byte big-endian buffer (left-zero-padded), storage_root and
    code_hash as exactly-32-byte copies (parse failure otherwise).
  * `account_extract_nonce` / `account_extract_balance`
    (`EvmAsm/Codegen/Programs/AccountFieldExtract.lean:53/148`) — narrow
    accessors over the same RLP bytes via `rlp_field_to_u64` /
    `rlp_field_to_u256_be` (`EvmAsm/Codegen/Programs/Tx.lean:69/188`),
    with the same u64-LE / 32-byte-BE output conventions.
  * `account_set_storage_root` / `account_set_uint_field`
    (`EvmAsm/Codegen/Programs/StorageWrite.lean:116`,
    `AccountBalance.lean:203`) — consume the RLP bytes and re-emit them
    with one field spliced.

  Accordingly there are **two** assertions:

  * `accountRlpIs ptr acct` — the RLP-encoded record (`bytesRegion` over
    `AccountRecord.rlp`, the spec-level `EvmAsm.EL.RLP.encode` of the
    4-field list). This is what the extractors/splicers own.
  * `accountDecodedIs noncePtr balPtr rootPtr hashPtr acct` — the four
    output slots exactly as `account_decode` writes them.

  Both carry `AccountRecord.WF`, the guest's parse-time validation
  (nonce ≤ 8 bytes, balance ≤ 32 bytes, hash fields exactly 32 bytes).

  ## Honesty ties

  * `decode_account_from_leaf_accountRlp` — the spec-reference decoder
    (`EvmAsm/Stateless/SpecRef/WitnessState.lean`, the port of
    `witness_state.py:_decode_account_from_leaf`) run on
    `AccountRecord.rlp` recovers exactly the record's fields, so the
    assertion's contents parameter is the record the guest's decode
    contract describes.
  * The `LBU` example at the bottom restates the proven byte-read spec
    `bytesRegion_lbu_within` against `accountRlpIs` — the machine-level
    primitive every extractor routine is built from, consuming the
    assertion in a real `cpsTripleWithin`.

  Field-projection specs for the RLP-walking guest routines themselves
  (`account_decode` etc. have no `cpsTripleWithin` specs yet — they are
  codegen `Program` defs with byte-identity drift guards only) are future
  work; this module fixes the assertion vocabulary those specs will be
  stated in.
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Stateless.SpecRef.WitnessState
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Stateless

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-! ## The account record -/

/-- The guest account record: the four fields of the on-trie RLP list
    `[nonce, balance, storage_root, code_hash]`, in the guest's own
    representations (numbers for the two scalars, raw 32-byte strings for
    the two hashes). Field order is pinned by `account_decode`'s
    `rlp_list_nth_item` indices 0..3
    (`EvmAsm/Codegen/Programs/State.lean:78/105/136/162`). -/
structure AccountRecord where
  nonce : Nat
  balance : Nat
  storageRoot : List (BitVec 8)
  codeHash : List (BitVec 8)
  deriving Repr, BEq, DecidableEq

namespace AccountRecord

/-- Guest parse-time validity, exactly `account_decode`'s checks: the
    nonce field fits 8 bytes (`rlp_field_to_u64` rejects longer,
    `Tx.lean:85`), the balance fits 32 bytes (`rlp_field_to_u256_be`
    rejects longer, `Tx.lean:208`), and the two hash fields are exactly
    32 bytes (`State.lean:147/173`). -/
def WF (a : AccountRecord) : Prop :=
  a.nonce < 2 ^ 64 ∧ a.balance < 2 ^ 256 ∧
  a.storageRoot.length = 32 ∧ a.codeHash.length = 32

instance (a : AccountRecord) : Decidable a.WF := by
  unfold WF; infer_instance

/-- The record as a spec-level RLP item: scalars in minimal big-endian
    (the trie encoding), hashes as raw byte strings. -/
def rlpItem (a : AccountRecord) : RLPItem :=
  .list [.bytes (Nat.toBytesBE a.nonce), .bytes (Nat.toBytesBE a.balance),
         .bytes a.storageRoot, .bytes a.codeHash]

/-- The RLP-encoded account record — the byte string the guest routines
    actually consume and produce. -/
def rlp (a : AccountRecord) : List (BitVec 8) :=
  encode a.rlpItem

end AccountRecord

/-! ## The assertions -/

/-- `accountRlpIs ptr acct` — ownership of the RLP-encoded account record
    at (dword-aligned) `ptr`, together with the guest's parse-time
    well-formedness of the fields. This is the resource
    `account_decode` / `account_extract_*` / `account_set_*` read. -/
def accountRlpIs (ptr : Word) (a : AccountRecord) : Assertion :=
  fun ps => a.WF ∧ bytesRegion ptr a.rlp ps

/-- The 32-byte big-endian buffer `account_decode` (and
    `rlp_field_to_u256_be`) writes for a u256 field: the minimal
    big-endian bytes right-aligned in a zeroed 32-byte slot
    (`EvmAsm/Codegen/Programs/State.lean:117-133`, `Tx.lean:195-222`). -/
def beBytes32 (n : Nat) : List (BitVec 8) :=
  List.replicate (32 - (Nat.toBytesBE n).length) 0 ++ Nat.toBytesBE n

/-- `accountDecodedIs` — the four output slots of `account_decode`
    (`EvmAsm/Stateless/State/Account.lean` calling convention): the nonce
    as one little-endian u64 dword at `noncePtr` (`a2`), the balance as a
    32-byte big-endian buffer at `balPtr` (`a3`), and the two 32-byte
    hash fields at `rootPtr` (`a4`) / `hashPtr` (`a5`). The four slots
    are caller-chosen and independent — the guest mandates no packed
    struct, so neither does the assertion. -/
def accountDecodedIs (noncePtr balPtr rootPtr hashPtr : Word)
    (a : AccountRecord) : Assertion :=
  fun ps => a.WF ∧
    ((noncePtr ↦ₘ BitVec.ofNat 64 a.nonce) **
     bytesRegion balPtr (beBytes32 a.balance) **
     bytesRegion rootPtr a.storageRoot **
     bytesRegion hashPtr a.codeHash) ps

/-! ## Basic lemmas -/

theorem accountRlpIs_eq_bytesRegion {ptr : Word} {a : AccountRecord}
    (hwf : a.WF) :
    accountRlpIs ptr a = bytesRegion ptr a.rlp := by
  funext ps
  exact propext ⟨fun h => h.2, fun h => ⟨hwf, h⟩⟩

theorem accountRlpIs_wf {ptr : Word} {a : AccountRecord} {ps : PartialState}
    (h : accountRlpIs ptr a ps) : a.WF := h.1

theorem accountDecodedIs_eq {noncePtr balPtr rootPtr hashPtr : Word}
    {a : AccountRecord} (hwf : a.WF) :
    accountDecodedIs noncePtr balPtr rootPtr hashPtr a =
      ((noncePtr ↦ₘ BitVec.ofNat 64 a.nonce) **
       bytesRegion balPtr (beBytes32 a.balance) **
       bytesRegion rootPtr a.storageRoot **
       bytesRegion hashPtr a.codeHash) := by
  funext ps
  exact propext ⟨fun h => h.2, fun h => ⟨hwf, h⟩⟩

theorem accountDecodedIs_wf {noncePtr balPtr rootPtr hashPtr : Word}
    {a : AccountRecord} {ps : PartialState}
    (h : accountDecodedIs noncePtr balPtr rootPtr hashPtr a ps) : a.WF := h.1

theorem pcFree_accountRlpIs {ptr : Word} {a : AccountRecord} :
    (accountRlpIs ptr a).pcFree :=
  fun ps h => bytesRegion_pcFree ptr a.rlp ps h.2

theorem pcFree_accountDecodedIs
    {noncePtr balPtr rootPtr hashPtr : Word} {a : AccountRecord} :
    (accountDecodedIs noncePtr balPtr rootPtr hashPtr a).pcFree :=
  fun ps h =>
    pcFree_sepConj pcFree_memIs
      (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)))
      ps h.2

instance (ptr : Word) (a : AccountRecord) :
    Assertion.PCFree (accountRlpIs ptr a) := ⟨pcFree_accountRlpIs⟩

instance (noncePtr balPtr rootPtr hashPtr : Word) (a : AccountRecord) :
    Assertion.PCFree (accountDecodedIs noncePtr balPtr rootPtr hashPtr a) :=
  ⟨pcFree_accountDecodedIs⟩

/-! ## Decoded-slot value lemmas -/

/-- The balance buffer is exactly 32 bytes for a well-formed balance. -/
theorem beBytes32_length {n : Nat} (h : n < 2 ^ 256) :
    (beBytes32 n).length = 32 := by
  have hle : (Nat.toBytesBE n).length ≤ 32 :=
    Nat.toBytesBE_length_le n 32 (by exact_mod_cast h)
  unfold beBytes32
  rw [List.length_append, List.length_replicate]
  omega

/-- Reading the 32-byte balance buffer back as a big-endian number
    recovers the balance: the leading zero padding is value-free. The
    projection fact for `account_extract_balance`'s output slot. -/
theorem bytesBEtoNat_beBytes32 (n : Nat) :
    Nat.fromBytesBE (beBytes32 n) = n := by
  unfold beBytes32
  generalize 32 - (Nat.toBytesBE n).length = pad
  induction pad with
  | zero => rw [List.replicate_zero, List.nil_append, Nat.fromBytesBE_toBytesBE]
  | succ p ih =>
    rw [List.replicate_succ, List.cons_append]
    show (0 : BitVec 8).toNat * 256 ^ _ + _ = n
    rw [show (0 : BitVec 8).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add, ih]

/-! ## Spec-decoder projection (the contents are the real record)

`decode_account_from_leaf` is the reference port of
`witness_state.py:_decode_account_from_leaf` — the decode contract
`account_decode` implements. Running it on `AccountRecord.rlp` recovers
the record's fields exactly, so `accountRlpIs`'s contents parameter is
layout-faithful, not a free-floating abstraction. -/

/-- `encodeBytes` of a short (≤ 55-byte) string adds at most one prefix
    byte. -/
theorem encodeBytes_length_le_of_short (data : List (BitVec 8))
    (h : data.length ≤ 55) :
    (encodeBytes data).length ≤ data.length + 1 := by
  match data with
  | [b] =>
    by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
  | [] => simp [encodeBytes]
  | b1 :: b2 :: tl =>
    have hlen : (b1 :: b2 :: tl).length ≤ 55 := h
    simp only [encodeBytes, List.length_cons]
    rw [if_pos (by simpa using hlen)]
    simp

/-- The encoded account record is short (well under the decoder's
    `256 ^ 8` full-decode bound): each scalar field is at most 8/32
    bytes, hashes exactly 32, so the list payload is ≤ 108 bytes and the
    whole encoding ≤ 111 bytes. -/
theorem accountRlp_length_le (a : AccountRecord) (hwf : a.WF) :
    a.rlp.length ≤ 111 := by
  obtain ⟨hnonce, hbal, hroot, hhash⟩ := hwf
  have hnlen : (Nat.toBytesBE a.nonce).length ≤ 8 :=
    Nat.toBytesBE_length_le a.nonce 8 (by exact_mod_cast hnonce)
  have hblen : (Nat.toBytesBE a.balance).length ≤ 32 :=
    Nat.toBytesBE_length_le a.balance 32 (by exact_mod_cast hbal)
  have h1 := encodeBytes_length_le_of_short (Nat.toBytesBE a.nonce) (by omega)
  have h2 := encodeBytes_length_le_of_short (Nat.toBytesBE a.balance) (by omega)
  have h3 := encodeBytes_length_le_of_short a.storageRoot (by omega)
  have h4 := encodeBytes_length_le_of_short a.codeHash (by omega)
  show (encode a.rlpItem).length ≤ 111
  unfold AccountRecord.rlpItem
  show (encode (.list _)).length ≤ 111
  unfold encode
  have hpayload :
      (encode.encodeItems
        [.bytes (Nat.toBytesBE a.nonce), .bytes (Nat.toBytesBE a.balance),
         .bytes a.storageRoot, .bytes a.codeHash]).length ≤ 108 := by
    show ((encode (.bytes (Nat.toBytesBE a.nonce)) ++
      (encode (.bytes (Nat.toBytesBE a.balance)) ++
       (encode (.bytes a.storageRoot) ++
        (encode (.bytes a.codeHash) ++ []))))).length ≤ 108
    simp only [List.length_append, List.length_nil]
    show (encodeBytes _).length + ((encodeBytes _).length +
      ((encodeBytes _).length + ((encodeBytes _).length + 0))) ≤ 108
    omega
  by_cases hshort :
      (encode.encodeItems
        [.bytes (Nat.toBytesBE a.nonce), .bytes (Nat.toBytesBE a.balance),
         .bytes a.storageRoot, .bytes a.codeHash]).length ≤ 55
  · rw [if_pos hshort]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [if_neg hshort]
    have hlb : (Nat.toBytesBE
        (encode.encodeItems
          [.bytes (Nat.toBytesBE a.nonce), .bytes (Nat.toBytesBE a.balance),
           .bytes a.storageRoot, .bytes a.codeHash]).length).length ≤ 2 :=
      Nat.toBytesBE_length_le _ 2 (by omega)
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Nonempty minimal-BE bytes for a positive scalar. -/
private theorem toBytesBE_not_isEmpty {n : Nat} (h : 0 < n) :
    (Nat.toBytesBE n).isEmpty = false := by
  obtain ⟨b, tl, heq, -⟩ := Nat.toBytesBE_eq_cons_of_pos n h
  rw [heq]
  rfl

/-- **The RLP contents decode to the record.** Running the spec-reference
    account-leaf decoder on `AccountRecord.rlp` recovers exactly the
    record's four fields. This pins `accountRlpIs`'s contents to the
    decode contract the guest's `account_decode` implements. -/
theorem decode_account_from_leaf_accountRlp (a : AccountRecord) (hwf : a.WF) :
    SpecRef.decode_account_from_leaf a.rlp =
      .ok ({ nonce := a.nonce, balance := a.balance, codeHash := a.codeHash },
           a.storageRoot) := by
  have hlen : (encode a.rlpItem).length < 256 ^ 8 := by
    have := accountRlp_length_le a hwf
    unfold AccountRecord.rlp at this
    omega
  obtain ⟨-, -, hroot, hhash⟩ := hwf
  unfold SpecRef.decode_account_from_leaf
  show (match decodeFully a.rlp with | _ => _) = _
  rw [show a.rlp = encode a.rlpItem from rfl, decodeFully_encode a.rlpItem hlen]
  show (match a.rlpItem with | _ => _) = _
  unfold AccountRecord.rlpItem
  simp only []
  have hrootne : a.storageRoot.isEmpty = false := by
    cases hsr : a.storageRoot with
    | nil => rw [hsr] at hroot; simp at hroot
    | cons _ _ => rfl
  have hhashne : a.codeHash.isEmpty = false := by
    cases hch : a.codeHash with
    | nil => rw [hch] at hhash; simp at hhash
    | cons _ _ => rfl
  rw [hrootne, hhashne]
  by_cases hn : a.nonce = 0
  · by_cases hb : a.balance = 0
    · simp [hn, hb, Nat.toBytesBE_zero]
      rfl
    · simp [hn, Nat.toBytesBE_zero, toBytesBE_not_isEmpty (Nat.pos_of_ne_zero hb),
        SpecRef.bytesBEtoNat, Nat.fromBytesBE_toBytesBE]
      rfl
  · by_cases hb : a.balance = 0
    · simp [hb, Nat.toBytesBE_zero, toBytesBE_not_isEmpty (Nat.pos_of_ne_zero hn),
        SpecRef.bytesBEtoNat, Nat.fromBytesBE_toBytesBE]
      rfl
    · simp [toBytesBE_not_isEmpty (Nat.pos_of_ne_zero hn),
        toBytesBE_not_isEmpty (Nat.pos_of_ne_zero hb),
        SpecRef.bytesBEtoNat, Nat.fromBytesBE_toBytesBE]
      rfl

/-! ## Machine-level tie-in

The byte-read primitive every account extractor is built from
(`rlp_list_nth_item` / `rlp_field_to_*` walk the record with `LBU`
loads), restated against `accountRlpIs`: reading byte `i` of the account
record yields `a.rlp[i]`, with the assertion preserved. Consumes the
proven `bytesRegion_lbu_within`. -/

example (rd rs1 : Reg) (ptr vOld base : Word) (a : AccountRecord) (i : Nat)
    (hwf : a.WF) (hrd : rd ≠ .x0)
    (halign : ptr.toNat % 8 = 0) (hi : i < a.rlp.length)
    (hover : ptr.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (ptr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (ptr + BitVec.ofNat 64 i)) ** (rd ↦ᵣ vOld) **
       accountRlpIs ptr a)
      ((rs1 ↦ᵣ (ptr + BitVec.ofNat 64 i)) **
       (rd ↦ᵣ ((a.rlp[i]'hi).zeroExtend 64)) ** accountRlpIs ptr a) := by
  rw [accountRlpIs_eq_bytesRegion hwf]
  exact bytesRegion_lbu_within rd rs1 ptr vOld base a.rlp i hrd halign hi
    hover hvalid

-- Concrete cross-check: the spec decoder recovers the fields of a
-- sample record from its `AccountRecord.rlp` bytes (mirrors the
-- `decode_account_from_leaf` sanity `#guard`s in
-- `SpecRef/WitnessState.lean`).
#guard
  let a : AccountRecord :=
    { nonce := 1, balance := 1000000000000000000,
      storageRoot := SpecRef.EMPTY_TRIE_ROOT,
      codeHash := SpecRef.EMPTY_CODE_HASH }
  (SpecRef.decode_account_from_leaf a.rlp).toOption ==
    some ({ nonce := 1, balance := 1000000000000000000,
            codeHash := SpecRef.EMPTY_CODE_HASH }, SpecRef.EMPTY_TRIE_ROOT)

-- The balance output slot round-trips: 32-byte BE buffer → value.
#guard Nat.fromBytesBE (beBytes32 1000000000000000000) = 1000000000000000000

-- The balance buffer is exactly 32 bytes.
#guard (beBytes32 1000000000000000000).length = 32

end EvmAsm.Stateless
