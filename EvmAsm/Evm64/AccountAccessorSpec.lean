/-
  EvmAsm.Evm64.AccountAccessorSpec

  Verified compositional layers for the account field accessors
  `account_extract_nonce` / `account_extract_balance`
  (`EvmAsm/Codegen/Programs/AccountFieldExtract.lean`), which compose the
  verified RlpWalk cursor chain (`rlp_walk_init` → `rlp_walk_next`^k →
  `rlp_content_to_u64` / `rlp_content_to_u256_be`).

  ## What this file proves

  1. **Byte-level structure of the account RLP** (`encodeAccount_eq_cons`):
     `encodeAccount a = 0xf8 :: lenByte :: accountPayload a`, with
     `68 ≤ payload.length ≤ 132` — the account RLP is always a long list with a
     single length byte.

  2. **`rlp_walk_init` over the account bytes**
     (`account_rlp_walk_init_spec_within`): from the accessor's first call, the
     strict list-header walk deterministically SUCCEEDS (status `a2 = 0`),
     leaving the cursor at field 0 (`listBase + 2`) and `end = listBase + len`.
     Derived from the generic single-length-byte instantiation
     `rlp_walk_init_long1_spec_within` of the verified
     `rlp_walk_init_long_spec_within`.

  3. **`rlp_walk_next` over a scalar field**
     (`rlp_walk_next_scalar_spec_within` + the account corollaries
     `account_rlp_walk_next_field0_spec_within` /
     `account_rlp_walk_next_field1_spec_within`): stepping the cursor over the
     RLP encoding of a scalar `n` (any of its four canonical forms: empty
     string, single byte, `0x81`-prefixed byte, multi-byte short string)
     deterministically succeeds with `a0 = cursor + enc.length`, `a1 = 0`,
     `a2 = (Nat.toBytesBE n).length` — so the accessors' derived content
     pointer `a0 - a2` is the content start.

  4. **Content-window identification** (`rlp_scalar_content_window` + account
     corollaries): the `(ptr, len)` window the accessor hands to the content
     decoder holds exactly `Nat.toBytesBE nonce` / `Nat.toBytesBE balance.toNat`,
     so `Nat.fromBytesBE` of it recovers the field value
     (`account_nonce_from_field0` / `account_balance_from_field1` from
     `AccountFieldExtractSpec`).

  5. **Right-alignment** (`toBytesBEFixed_eq_replicate_append`,
     `account_balance_copyN_eq`): the u256 decoder's copy of the balance window
     into the zeroed 32-byte cell is exactly `word256Bytes32 a.balance`.  The
     window-splitting lemma this rests on, `copyN_eq_append`, now sits beside
     `copyN` itself in `Rv64/RLP/ContentToU256Be.lean` — the RLP *encoder*'s
     payload copy needs it too.

  6. **`rlp_content_to_u64` over the nonce window**
     (`account_rlp_content_to_u64_nonce_spec_within`): the content decode
     deterministically succeeds with `a0 = nonce` (EIP-2681 refutes too-long,
     the bounded-value success arm; `len = 0` is the zero case).

  7. **`rlp_content_to_u256_be` over the balance window**
     (`account_rlp_content_to_u256_be_balance_spec_within`): the content decode
     deterministically succeeds with `a0 = 0` and the output cell holding
     `word256Bytes32 a.balance`.

  ## From here to the full accessor `cpsTripleWithin` triples

  The `rlp_content_to_u64` pinned-`x6` gap is CLOSED: the ContentToU64 specs
  now take an arbitrary `x6Old` (the callee's own `MV x6 x10` at index 2
  overwrites it), and `account_rlp_content_to_u64_nonce_spec_within` below
  inherits that generic scratch — both content decoders are now directly
  consumable by the accessors' call compositions.

  The **caller-side frame composition** — the accessor bodies' stack frame
  (`ADDI x2 x2 ±16/±32` + `SD`/`LD` of `ra`/`s0`/`s1`), output cell, three
  `WP.cpsCallWithin` fixed-guest-address calls, and branch merges — lives in
  `EvmAsm/Evm64/AccountAccessorTopSpec.lean`, which composes the layers
  proved here into the top-level accessor triples.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Evm64.AccountRlp
import EvmAsm.Evm64.AccountFieldExtractSpec
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.WP.Call

namespace EvmAsm.Evm64

open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.Tactics

/-! ## 1. Byte-level structure of the account RLP -/

/-- `Nat.toBytesBE` of a positive byte-sized value is the single byte. -/
theorem toBytesBE_of_pos_lt_256 (n : Nat) (h0 : 0 < n) (h : n < 256) :
    Nat.toBytesBE n = [BitVec.ofNat 8 n] := by
  match n, h0 with
  | m + 1, _ =>
    rw [Nat.toBytesBE_succ, Nat.div_eq_of_lt h, Nat.toBytesBE_zero,
      Nat.mod_eq_of_lt h, List.nil_append]

/-- `encodeBytes` never returns the empty list. -/
theorem encodeBytes_length_pos (data : List (BitVec 8)) :
    0 < (encodeBytes data).length := by
  match data with
  | [] => simp [encodeBytes]
  | [b] => by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
  | b1 :: b2 :: tl =>
    simp only [encodeBytes]
    by_cases hshort : (b1 :: b2 :: tl).length ≤ 55
    · rw [if_pos (by simpa using hshort)]; simp
    · rw [if_neg (by simpa using hshort)]; simp

/-- Short-form `encodeBytes` adds at most one prefix byte. -/
theorem encodeBytes_length_le_succ (data : List (BitVec 8)) (h : data.length ≤ 55) :
    (encodeBytes data).length ≤ data.length + 1 := by
  match data with
  | [] => simp [encodeBytes]
  | [b] => by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
  | b1 :: b2 :: tl =>
    simp only [encodeBytes]
    rw [if_pos (by simpa using h)]
    simp

/-- `encodeBytes` of a 32-byte string is the `0xa0` prefix plus the string. -/
theorem encodeBytes_of_length_32 (data : List (BitVec 8)) (h : data.length = 32) :
    encodeBytes data = (0xa0 : BitVec 8) :: data := by
  have := encodeBytes_short_of_length_ne_one data (by omega) (by omega)
  rw [this, h]
  rfl

/-- The account list payload: the four encoded fields, right-nested as
    `encode.encodeItems` produces them. -/
def accountPayload (a : Account) : List (BitVec 8) :=
  encodeBytes (Nat.toBytesBE a.nonce) ++
    (encodeBytes (Nat.toBytesBE a.balance.toNat) ++
      (encodeBytes (word256Bytes32 a.storageRoot) ++
        encodeBytes (word256Bytes32 a.codeHash)))

theorem encodeItems_eq_accountPayload (a : Account) :
    encode.encodeItems [RLPItem.bytes (Nat.toBytesBE a.nonce),
        .bytes (Nat.toBytesBE a.balance.toNat),
        .bytes (word256Bytes32 a.storageRoot),
        .bytes (word256Bytes32 a.codeHash)]
      = accountPayload a := by
  show encode (.bytes (Nat.toBytesBE a.nonce)) ++
      (encode (.bytes (Nat.toBytesBE a.balance.toNat)) ++
        (encode (.bytes (word256Bytes32 a.storageRoot)) ++
          (encode (.bytes (word256Bytes32 a.codeHash)) ++ []))) = accountPayload a
  rw [List.append_nil]
  rfl

/-- Lower bound: the account payload is at least 68 bytes (two ≥ 1-byte scalar
    fields plus two 33-byte hash fields), hence always a long list. -/
theorem accountPayload_length_ge (a : Account) : 68 ≤ (accountPayload a).length := by
  have h0 := encodeBytes_length_pos (Nat.toBytesBE a.nonce)
  have h1 := encodeBytes_length_pos (Nat.toBytesBE a.balance.toNat)
  have h2 : (encodeBytes (word256Bytes32 a.storageRoot)).length = 33 := by
    rw [encodeBytes_of_length_32 _ (word256Bytes32_length _)]; simp [word256Bytes32_length]
  have h3 : (encodeBytes (word256Bytes32 a.codeHash)).length = 33 := by
    rw [encodeBytes_of_length_32 _ (word256Bytes32_length _)]; simp [word256Bytes32_length]
  simp only [accountPayload, List.length_append]
  omega

/-- Upper bound: for `nonce < 2 ^ 256` the payload is at most 132 bytes, hence
    the length field is a single byte. -/
theorem accountPayload_length_le (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    (accountPayload a).length ≤ 132 := by
  have hn32 : (Nat.toBytesBE a.nonce).length ≤ 32 :=
    Nat.toBytesBE_length_le a.nonce 32 (by
      rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]; exact hnonce)
  have hb32 : (Nat.toBytesBE a.balance.toNat).length ≤ 32 :=
    Nat.toBytesBE_length_le a.balance.toNat 32 (by
      rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]; exact a.balance.isLt)
  have h0 := encodeBytes_length_le_succ (Nat.toBytesBE a.nonce) (by omega)
  have h1 := encodeBytes_length_le_succ (Nat.toBytesBE a.balance.toNat) (by omega)
  have h2 : (encodeBytes (word256Bytes32 a.storageRoot)).length = 33 := by
    rw [encodeBytes_of_length_32 _ (word256Bytes32_length _)]; simp [word256Bytes32_length]
  have h3 : (encodeBytes (word256Bytes32 a.codeHash)).length = 33 := by
    rw [encodeBytes_of_length_32 _ (word256Bytes32_length _)]; simp [word256Bytes32_length]
  simp only [accountPayload, List.length_append]
  omega

/-- **Account RLP cons form.** The account RLP is always the long-list form
    with a single length byte: `0xf8 :: lenByte :: payload`. -/
theorem encodeAccount_eq_cons (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    encodeAccount a
      = (0xf8 : BitVec 8) :: BitVec.ofNat 8 (accountPayload a).length :: accountPayload a := by
  have hge := accountPayload_length_ge a
  have hle := accountPayload_length_le a hnonce
  unfold encodeAccount encode
  rw [encodeItems_eq_accountPayload a]
  rw [if_neg (by omega)]
  rw [toBytesBE_of_pos_lt_256 (accountPayload a).length (by omega) (by omega)]
  rfl

theorem encodeAccount_length_eq (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    (encodeAccount a).length = 2 + (accountPayload a).length := by
  rw [encodeAccount_eq_cons a hnonce]
  simp
  omega

/-! ## 2. `rlp_walk_init` deterministic success over the account bytes -/

/-- **Generic single-length-byte long-list `rlp_walk_init` success.** For a
    buffer of shape `0xf8 :: lenB :: payload` with `lenB` the payload length
    (`56 ≤ payload.length < 256`) and `a1` the exact total length, the strict
    list-header walk succeeds: cursor lands at `listBase + 2` (the first child
    item), `a1 = end`, status `a2 = 0`. Instantiates the verified
    `rlp_walk_init_long_spec_within` at `listOff = 0`, `lol = 1`. -/
theorem rlp_walk_init_long1_spec_within
    (base listBase raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (lenB : BitVec 8) (payload : List (BitVec 8))
    (hlenB : lenB.toNat = payload.length)
    (hmin : 56 ≤ payload.length)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (2 + payload.length) < 2 ^ 64)
    (hvalid0 : isValidByteAccess listBase = true)
    (hvalid1 : isValidByteAccess (listBase + 1) = true) :
    cpsTripleWithin 32 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (BitVec.ofNat 64 (2 + payload.length))) **
        (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase ((0xf8 : BitVec 8) :: lenB :: payload))
      ((.x10 ↦ᵣ (listBase + 2)) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (2 + payload.length))) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase ((0xf8 : BitVec 8) :: lenB :: payload)) := by
  set bytes := (0xf8 : BitVec 8) :: lenB :: payload with hbytes
  have hplen : payload.length < 256 := by have := lenB.isLt; omega
  have hoff : (0 : Nat) < bytes.length := by simp [hbytes]
  have hoff1 : (0 : Nat) + 1 < bytes.length := by simp [hbytes]
  have hb0 : bytes[(0 : Nat)]'hoff = (0xf8 : BitVec 8) := by simp [hbytes]
  have hb1 : bytes[(0 : Nat) + 1]'hoff1 = lenB := by simp [hbytes]
  have hpfx : (bytes[(0 : Nat)]'hoff).zeroExtend 64 = (0xf8 : Word) := by rw [hb0]; decide
  have hsub1 : ((0xf8 : Word) - (0xf7 : Word)).toNat = 1 := by decide
  have hse : ((0xf8 : Word) - (0xf7 : Word)) + signExtend12 (1 : BitVec 12) = (2 : Word) := by
    decide
  have e0 : listBase + BitVec.ofNat 64 (0 : Nat) = listBase := by bv_omega
  have h2L : 2 + payload.length < 2 ^ 64 := by omega
  have hlen' : (BitVec.ofNat 64 (2 + payload.length) : Word) ≠ (0 : Word) := by
    intro hc
    have hc' := congrArg BitVec.toNat hc
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2L] at hc'
    simp at hc'
  have h_ge : ¬ BitVec.ult ((bytes[(0 : Nat)]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    rw [hpfx]; decide
  have h_ge_f8 : ¬ BitVec.ult ((bytes[(0 : Nat)]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    rw [hpfx]; decide
  have hllen : (0 : Nat) + 1 + ((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ bytes.length := by
    rw [hpfx, hsub1]; simp [hbytes]
  have hlover : listBase.toNat + ((0 : Nat) + 1 +
      ((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 := by
    rw [hpfx, hsub1]; omega
  have hlvalid : ∀ k, k < ((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (listBase + BitVec.ofNat 64 ((0 : Nat) + 1 + k)) = true := by
    intro k hk
    rw [hpfx, hsub1] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hvalid1
  have h_fits : ¬ BitVec.ult ((listBase + BitVec.ofNat 64 (0 : Nat)) +
      BitVec.ofNat 64 (2 + payload.length))
      ((listBase + BitVec.ofNat 64 (0 : Nat)) +
        (((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true := by
    rw [hpfx, hse, e0]
    simp only [BitVec.ult, decide_eq_true_eq]
    bv_omega
  have h_llz : (bytes[(0 : Nat) + 1]'hoff1).zeroExtend 64 ≠ (0 : Word) := by
    rw [hb1]
    intro hc
    have hc' := congrArg BitVec.toNat hc
    rw [BitVec.toNat_setWidth] at hc'
    simp at hc'
    omega
  have hdrop : (bytes.drop ((0 : Nat) + 1)).take
      (((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) = [lenB] := by
    rw [hpfx, hsub1]
    simp [hbytes]
  have hfromB : Nat.fromBytesBE [lenB] = payload.length := by
    simp [Nat.fromBytesBE, hlenB]
  have h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop ((0 : Nat) + 1)).take
      (((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))) (56 : Word) = true := by
    rw [hdrop, hfromB]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show ((56 : Word)).toNat = 56 from by decide]
    omega
  have h_match : ((listBase + BitVec.ofNat 64 (0 : Nat)) +
      (((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
      BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop ((0 : Nat) + 1)).take
        (((bytes[(0 : Nat)]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
      = (listBase + BitVec.ofNat 64 (0 : Nat)) + BitVec.ofNat 64 (2 + payload.length) := by
    rw [hdrop, hfromB, hpfx, hse, e0]
    bv_omega
  have ht := rlp_walk_init_long_spec_within base listBase raVal
    (BitVec.ofNat 64 (2 + payload.length)) a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    bytes 0 hsalign hoff (by omega) (by rwa [e0]) hlen' h_ge h_ge_f8 hllen hlover hlvalid hoff1
    h_fits h_llz h_min h_match
  rw [hpfx, hsub1, hse, e0] at ht
  exact cpsTripleWithin_mono_nSteps (by omega) ht

/-- **`rlp_walk_init` over the account RLP succeeds deterministically.** From
    the accessor's first call (`a0 = listBase`, `a1 = |encodeAccount a|`), the
    strict header walk returns cursor `= listBase + 2` (field 0), `a1 = end`,
    status `a2 = 0` — the accessor's `BNE a2, x0` failure branch is not taken. -/
theorem account_rlp_walk_init_spec_within
    (base listBase raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid0 : isValidByteAccess listBase = true)
    (hvalid1 : isValidByteAccess (listBase + 1) = true) :
    cpsTripleWithin 32 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (BitVec.ofNat 64 (encodeAccount a).length)) **
        (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase (encodeAccount a))
      ((.x10 ↦ᵣ (listBase + 2)) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a)) := by
  have hlen := encodeAccount_length_eq a hnonce
  have hcons := encodeAccount_eq_cons a hnonce
  rw [hlen] at hover ⊢
  rw [hcons]
  exact rlp_walk_init_long1_spec_within base listBase raVal a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old (BitVec.ofNat 8 (accountPayload a).length) (accountPayload a)
    (by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := accountPayload_length_le a hnonce; omega))
    (by have := accountPayload_length_ge a; omega)
    hsalign hover hvalid0 hvalid1

/-! ## 3. `rlp_walk_next` deterministic success over a scalar field -/

/-- **`rlp_walk_next` over the RLP encoding of a scalar.** If the bytes at
    cursor offset `srcOff` are `encodeBytes (Nat.toBytesBE n) ++ rest` (any of
    the scalar's canonical short forms: empty string `0x80`, single byte,
    `0x81`-prefixed high byte, or multi-byte short string) and the item fits
    strictly before `end = srcBase + endLen`, the step deterministically
    succeeds: `a0 = cursor + |enc|`, `a1 = 0`, `a2 = |Nat.toBytesBE n|` — so
    the accessors' derived content pointer `a0 - a2` is the content start. -/
theorem rlp_walk_next_scalar_spec_within
    (base srcBase raVal a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (srcBytes rest : List (BitVec 8)) (srcOff endLen n : Nat)
    (henc : srcBytes.drop srcOff = encodeBytes (Nat.toBytesBE n) ++ rest)
    (h55 : (Nat.toBytesBE n).length ≤ 55)
    (hfit : srcOff + (encodeBytes (Nat.toBytesBE n)).length ≤ endLen)
    (hend : endLen ≤ srcBytes.length)
    (hsalign : srcBase.toNat % 8 = 0)
    (hover : srcBase.toNat + endLen < 2 ^ 64)
    (hvalid : ∀ k, k < endLen → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 endLen)) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (encodeBytes (Nat.toBytesBE n)).length))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE n).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  have hen1 : 0 < (encodeBytes (Nat.toBytesBE n)).length := encodeBytes_length_pos _
  have hlt : srcOff < endLen := by omega
  have hoff : srcOff < srcBytes.length := by omega
  have h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff)
      (srcBase + BitVec.ofNat 64 endLen) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]
    bv_omega
  have hdrop0 : srcBytes.drop srcOff = srcBytes[srcOff]'hoff :: srcBytes.drop (srcOff + 1) :=
    List.drop_eq_getElem_cons hoff
  by_cases hn1 : (Nat.toBytesBE n).length = 1
  · -- single-byte content: `n ∈ [1, 255]`, either the raw byte or `0x81`-prefixed
    obtain ⟨b, hb⟩ : ∃ b, Nat.toBytesBE n = [b] := by
      cases htn : Nat.toBytesBE n with
      | nil => rw [htn] at hn1; simp at hn1
      | cons b tl =>
        rw [htn] at hn1
        have htl : tl = [] := List.eq_nil_of_length_eq_zero (by simpa using hn1)
        exact ⟨b, by rw [htl]⟩
    have hbn : b.toNat = n := by
      have hrt := Nat.fromBytesBE_toBytesBE n
      rw [hb] at hrt
      simpa [Nat.fromBytesBE] using hrt
    have hn256 : n < 256 := by have := b.isLt; omega
    by_cases h128 : n < 128
    · -- raw single byte (`prefix < 0x80`)
      have hencE : encodeBytes (Nat.toBytesBE n) = [b] := by
        rw [hb]
        simp only [encodeBytes]
        rw [if_pos (by omega)]
      have hel : (encodeBytes (Nat.toBytesBE n)).length = 1 := by rw [hencE]; rfl
      have henc' := henc
      rw [hdrop0, hencE, List.cons_append] at henc'
      injection henc' with hb0 _
      have h_single : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word)
          = true := by
        rw [hb0]
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_setWidth,
          show ((0x80 : Word)).toNat = 128 from by decide]
        omega
      have ht := rlp_walk_next_single_spec_within base srcBase
        (srcBase + BitVec.ofNat 64 endLen) raVal a2Old t0Old t1Old srcBytes srcOff hsalign hoff
        (by omega) (hvalid srcOff hlt) h_inb h_single
      have ht' := cpsTripleWithin_frameR
        ((.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old)) (by pcFree) ht
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at ht'
      have e10 : (srcBase + BitVec.ofNat 64 srcOff) + (1 : Word)
          = srcBase + BitVec.ofNat 64 (srcOff + (encodeBytes (Nat.toBytesBE n)).length) := by
        rw [hel]; bv_omega
      rw [e10] at ht'
      have e12 : (BitVec.ofNat 64 (Nat.toBytesBE n).length : Word) = (1 : Word) := by
        rw [hn1]; decide
      rw [e12]
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht')
      have hp1 := sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
          (regIs_implies_regOwn .x29))) h hp
      xperm_hyp hp1
    · -- `0x81`-prefixed high byte (`content[0] ≥ 0x80`)
      have hencE : encodeBytes (Nat.toBytesBE n) = [BitVec.ofNat 8 0x81, b] := by
        rw [hb]
        simp only [encodeBytes]
        rw [if_neg (by omega)]
      have hel : (encodeBytes (Nat.toBytesBE n)).length = 2 := by rw [hencE]; rfl
      have hfit2 : srcOff + 2 ≤ endLen := by rw [hel] at hfit; exact hfit
      have hoff1 : srcOff + 1 < srcBytes.length := by omega
      have henc' := henc
      rw [hdrop0, hencE] at henc'
      simp only [List.cons_append, List.nil_append] at henc'
      injection henc' with hb0 htail
      have hdrop1 : srcBytes.drop (srcOff + 1)
          = srcBytes[srcOff + 1]'hoff1 :: srcBytes.drop (srcOff + 1 + 1) :=
        List.drop_eq_getElem_cons hoff1
      rw [hdrop1] at htail
      injection htail with hb1 _
      have hze81 : ((BitVec.ofNat 8 0x81 : BitVec 8)).zeroExtend 64 = (0x81 : Word) := by decide
      have h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word)
          = true := by rw [hb0, hze81]; decide
      have h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word)
          = true := by rw [hb0, hze81]; decide
      have h_bound : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          ((srcBase + BitVec.ofNat 64 endLen) - (srcBase + BitVec.ofNat 64 srcOff))
          = true := by
        rw [hb0, hze81]
        simp only [BitVec.ult, decide_eq_true_eq]
        bv_omega
      have h_len1 : (srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) := by
        rw [hb0, hze81]; decide
      have h_content : ¬ BitVec.ult ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0x80 : Word)
          = true := by
        rw [hb1]
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_setWidth,
          show ((0x80 : Word)).toNat = 128 from by decide]
        omega
      have ht := rlp_walk_next_short_string_single_spec_within base srcBase
        (srcBase + BitVec.ofNat 64 endLen) raVal a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
        srcOff hsalign hoff hoff1 (by omega) (by omega) (hvalid srcOff hlt)
        (hvalid (srcOff + 1) (by omega)) h_inb h_lo h_hi h_bound h_len1 h_content
      rw [h_len1] at ht
      have e10 : (srcBase + BitVec.ofNat 64 (srcOff + 1)) + (1 : Word)
          = srcBase + BitVec.ofNat 64 (srcOff + (encodeBytes (Nat.toBytesBE n)).length) := by
        rw [hel]; bv_omega
      rw [e10] at ht
      have e12 : (BitVec.ofNat 64 (Nat.toBytesBE n).length : Word) = (1 : Word) := by
        rw [hn1]; decide
      rw [e12]
      exact cpsTripleWithin_mono_nSteps (by omega) ht
  · -- multi-byte short string (`len = 0` or `len ≥ 2`): `0x80 + len` prefix
    have hencE : encodeBytes (Nat.toBytesBE n)
        = BitVec.ofNat 8 (0x80 + (Nat.toBytesBE n).length) :: Nat.toBytesBE n := by
      rw [encodeBytes_short_of_length_ne_one _ h55 hn1]
      rfl
    have hel : (encodeBytes (Nat.toBytesBE n)).length = (Nat.toBytesBE n).length + 1 := by
      rw [hencE]; simp
    have hfit' : srcOff + ((Nat.toBytesBE n).length + 1) ≤ endLen := by
      rw [hel] at hfit; exact hfit
    have henc' := henc
    rw [hdrop0, hencE, List.cons_append] at henc'
    injection henc' with hb0 _
    have hzeq : ((BitVec.ofNat 8 (0x80 + (Nat.toBytesBE n).length) : BitVec 8)).zeroExtend 64
        = BitVec.ofNat 64 (0x80 + (Nat.toBytesBE n).length) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have h1 : (0x80 + (Nat.toBytesBE n).length) % 2 ^ 8
          = 0x80 + (Nat.toBytesBE n).length := Nat.mod_eq_of_lt (by omega)
      rw [h1]
    have h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word)
        = true := by
      rw [hb0, hzeq]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
        show ((0x80 : Word)).toNat = 128 from by decide]
      omega
    have h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word)
        = true := by
      rw [hb0, hzeq]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
        show ((0xb8 : Word)).toNat = 184 from by decide]
      omega
    have hsub80 : (srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)
        = BitVec.ofNat 64 (Nat.toBytesBE n).length := by
      rw [hb0, hzeq]
      bv_omega
    have h_bound : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
        ((srcBase + BitVec.ofNat 64 endLen) - (srcBase + BitVec.ofNat 64 srcOff))
        = true := by
      rw [hsub80]
      simp only [BitVec.ult, decide_eq_true_eq]
      bv_omega
    have h_lenne : (srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) ≠ (1 : Word) := by
      rw [hsub80]
      intro hc
      have hc' := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        show ((1 : Word)).toNat = 1 from by decide] at hc'
      omega
    have ht := rlp_walk_next_short_string_spec_within base srcBase
      (srcBase + BitVec.ofNat 64 endLen) raVal a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
      srcOff hsalign hoff (by omega) (hvalid srcOff hlt) h_inb h_lo h_hi h_bound h_lenne
    rw [hsub80] at ht
    have e10 : (srcBase + BitVec.ofNat 64 (srcOff + 1))
          + BitVec.ofNat 64 (Nat.toBytesBE n).length
        = srcBase + BitVec.ofNat 64 (srcOff + (encodeBytes (Nat.toBytesBE n)).length) := by
      rw [hel]; bv_omega
    rw [e10] at ht
    exact cpsTripleWithin_mono_nSteps (by omega) ht

/-! ### Account instantiations: fields 0 (nonce) and 1 (balance) -/

/-- The bytes after the account list header are the four encoded fields. -/
theorem encodeAccount_drop_two (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    (encodeAccount a).drop 2
      = encodeBytes (Nat.toBytesBE a.nonce) ++
          (encodeBytes (Nat.toBytesBE a.balance.toNat) ++
            (encodeBytes (word256Bytes32 a.storageRoot) ++
              encodeBytes (word256Bytes32 a.codeHash))) := by
  rw [encodeAccount_eq_cons a hnonce]
  rfl

/-- The bytes after the header and field 0 start with field 1 (balance). -/
theorem encodeAccount_drop_field1 (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    (encodeAccount a).drop (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
      = encodeBytes (Nat.toBytesBE a.balance.toNat) ++
          (encodeBytes (word256Bytes32 a.storageRoot) ++
            encodeBytes (word256Bytes32 a.codeHash)) := by
  rw [encodeAccount_eq_cons a hnonce,
    show 2 + (encodeBytes (Nat.toBytesBE a.nonce)).length
      = (encodeBytes (Nat.toBytesBE a.nonce)).length + 1 + 1 from by omega,
    List.drop_succ_cons, List.drop_succ_cons]
  show (accountPayload a).drop (encodeBytes (Nat.toBytesBE a.nonce)).length = _
  simp only [accountPayload]
  exact List.drop_left

private theorem nonce_len_le_55 (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    (Nat.toBytesBE a.nonce).length ≤ 55 := by
  have h32 := Nat.toBytesBE_length_le a.nonce 32 (by
    rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]; exact hnonce)
  omega

private theorem balance_len_le_55 (a : Account) :
    (Nat.toBytesBE a.balance.toNat).length ≤ 55 := by
  have h32 := Nat.toBytesBE_length_le a.balance.toNat 32 (by
    rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]; exact a.balance.isLt)
  omega

/-- **First `rlp_walk_next` over the account bytes (field 0 = nonce).** From the
    cursor at `listBase + 2` (walk-init's success output), the step succeeds
    deterministically: `a0 = listBase + (2 + |enc nonce|)` (start of field 1),
    `a1 = 0`, `a2 = |Nat.toBytesBE nonce|` (the nonce content length). -/
theorem account_rlp_walk_next_field0_spec_within
    (base listBase raVal a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (listBase + 2)) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a))
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase (encodeAccount a)) := by
  have hfit : 2 + (encodeBytes (Nat.toBytesBE a.nonce)).length ≤ (encodeAccount a).length := by
    rw [encodeAccount_length_eq a hnonce]
    have hP : (encodeBytes (Nat.toBytesBE a.nonce)).length ≤ (accountPayload a).length := by
      simp only [accountPayload, List.length_append]; omega
    omega
  have ht := rlp_walk_next_scalar_spec_within base listBase raVal a2Old t0Old t1Old t2Old t3Old
    t4Old (encodeAccount a) _ 2 (encodeAccount a).length a.nonce
    (encodeAccount_drop_two a hnonce) (nonce_len_le_55 a hnonce) hfit (le_refl _)
    hsalign hover hvalid
  rw [show (BitVec.ofNat 64 (2 : Nat) : Word) = (2 : Word) from by decide] at ht
  exact ht

/-- **Second `rlp_walk_next` over the account bytes (field 1 = balance).** From
    the cursor at the start of field 1 (field 0's step output), the step
    succeeds deterministically with `a2 = |Nat.toBytesBE balance.toNat|`. -/
theorem account_rlp_walk_next_field1_spec_within
    (base listBase raVal a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a))
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase (encodeAccount a)) := by
  have hfit : (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
      + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length ≤ (encodeAccount a).length := by
    rw [encodeAccount_length_eq a hnonce]
    have hP : (encodeBytes (Nat.toBytesBE a.nonce)).length
        + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length ≤ (accountPayload a).length := by
      simp only [accountPayload, List.length_append]; omega
    omega
  exact rlp_walk_next_scalar_spec_within base listBase raVal a2Old t0Old t1Old t2Old t3Old
    t4Old (encodeAccount a) _ (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
    (encodeAccount a).length a.balance.toNat
    (encodeAccount_drop_field1 a hnonce) (balance_len_le_55 a) hfit (le_refl _)
    hsalign hover hvalid

/-! ## 4. Content-window identification -/

/-- Split a scalar's short-form encoding into (≤ 1-byte) prefix ++ content. -/
theorem encodeBytes_toBytesBE_split (n : Nat) (h55 : (Nat.toBytesBE n).length ≤ 55) :
    ∃ pre : List (BitVec 8),
      encodeBytes (Nat.toBytesBE n) = pre ++ Nat.toBytesBE n ∧
      pre.length + (Nat.toBytesBE n).length = (encodeBytes (Nat.toBytesBE n)).length := by
  by_cases hn1 : (Nat.toBytesBE n).length = 1
  · obtain ⟨b, hb⟩ : ∃ b, Nat.toBytesBE n = [b] := by
      cases htn : Nat.toBytesBE n with
      | nil => rw [htn] at hn1; simp at hn1
      | cons b tl =>
        rw [htn] at hn1
        have htl : tl = [] := List.eq_nil_of_length_eq_zero (by simpa using hn1)
        exact ⟨b, by rw [htl]⟩
    by_cases hb8 : b.toNat < 0x80
    · have hencE : encodeBytes (Nat.toBytesBE n) = [b] := by
        rw [hb]
        simp only [encodeBytes]
        rw [if_pos hb8]
      exact ⟨[], by rw [hencE, hb]; rfl, by rw [hencE, hn1]; rfl⟩
    · have hencE : encodeBytes (Nat.toBytesBE n) = [BitVec.ofNat 8 0x81, b] := by
        rw [hb]
        simp only [encodeBytes]
        rw [if_neg hb8]
      exact ⟨[BitVec.ofNat 8 0x81], by rw [hencE, hb]; rfl, by rw [hencE, hn1]; rfl⟩
  · have hencE : encodeBytes (Nat.toBytesBE n)
        = BitVec.ofNat 8 (0x80 + (Nat.toBytesBE n).length) :: Nat.toBytesBE n := by
      rw [encodeBytes_short_of_length_ne_one _ h55 hn1]
      rfl
    exact ⟨[BitVec.ofNat 8 (0x80 + (Nat.toBytesBE n).length)],
      by rw [hencE]; rfl, by rw [hencE]; simp; omega⟩

/-- **The content window is the scalar's bytes.** The `(ptr, len)` window the
    accessors derive after a successful `rlp_walk_next` (`ptr = a0 - a2`, i.e.
    offset `srcOff + |enc| - |content|`; `len = a2`) holds exactly
    `Nat.toBytesBE n`. -/
theorem rlp_scalar_content_window
    (srcBytes rest : List (BitVec 8)) (srcOff n : Nat)
    (henc : srcBytes.drop srcOff = encodeBytes (Nat.toBytesBE n) ++ rest)
    (h55 : (Nat.toBytesBE n).length ≤ 55) :
    (srcBytes.drop ((srcOff + (encodeBytes (Nat.toBytesBE n)).length)
        - (Nat.toBytesBE n).length)).take (Nat.toBytesBE n).length
      = Nat.toBytesBE n := by
  obtain ⟨pre, hpre, hlen⟩ := encodeBytes_toBytesBE_split n h55
  have hoffd : (srcOff + (encodeBytes (Nat.toBytesBE n)).length) - (Nat.toBytesBE n).length
      = srcOff + pre.length := by omega
  rw [hoffd]
  have hdd : srcBytes.drop (srcOff + pre.length)
      = (Nat.toBytesBE n) ++ rest := by
    rw [← List.drop_drop, henc, hpre, List.append_assoc, List.drop_left]
  rw [hdd]
  exact List.take_left

/-- Field 0's content window holds the nonce bytes, hence decodes to the nonce. -/
theorem account_nonce_content_window (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    ((encodeAccount a).drop ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
        - (Nat.toBytesBE a.nonce).length)).take (Nat.toBytesBE a.nonce).length
      = Nat.toBytesBE a.nonce :=
  rlp_scalar_content_window (encodeAccount a) _ 2 a.nonce
    (encodeAccount_drop_two a hnonce) (nonce_len_le_55 a hnonce)

/-- Field 0's content window decodes (big-endian) to the nonce itself: exactly
    the value `rlp_content_to_u64`'s success arm produces from that window. -/
theorem account_nonce_content_value (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    Nat.fromBytesBE
        (((encodeAccount a).drop ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            - (Nat.toBytesBE a.nonce).length)).take (Nat.toBytesBE a.nonce).length)
      = a.nonce := by
  rw [account_nonce_content_window a hnonce]
  exact Nat.fromBytesBE_toBytesBE a.nonce

/-- Field 1's content window holds the balance bytes. -/
theorem account_balance_content_window (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    ((encodeAccount a).drop
        (((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length)
          - (Nat.toBytesBE a.balance.toNat).length)).take
        (Nat.toBytesBE a.balance.toNat).length
      = Nat.toBytesBE a.balance.toNat :=
  rlp_scalar_content_window (encodeAccount a) _
    (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length) a.balance.toNat
    (encodeAccount_drop_field1 a hnonce) (balance_len_le_55 a)

/-- Field 1's content window decodes (big-endian) to the balance value: the
    value `rlp_content_to_u256_be`'s success arm right-aligns into the 32-byte
    output cell. -/
theorem account_balance_content_value (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    BitVec.ofNat 256 (Nat.fromBytesBE
        (((encodeAccount a).drop
            (((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
                + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length)
              - (Nat.toBytesBE a.balance.toNat).length)).take
            (Nat.toBytesBE a.balance.toNat).length))
      = a.balance := by
  rw [account_balance_content_window a hnonce]
  exact account_balance_from_field1 a

/-! ## 5. Right-alignment: `copyN` into a zeroed 32-byte cell is fixed-width BE -/

/-- `toBytesBEFixed` of zero is all-zero bytes. -/
theorem toBytesBEFixed_zero (k : Nat) : toBytesBEFixed k 0 = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show toBytesBEFixed k (0 / 256) ++ [BitVec.ofNat 8 (0 % 256)] = _
    rw [Nat.zero_div, ih, show BitVec.ofNat 8 (0 % 256) = (0 : BitVec 8) from by decide,
      List.replicate_succ']

/-- Fixed-width big-endian is the zero-padded minimal big-endian. -/
theorem toBytesBEFixed_eq_replicate_append (k : Nat) :
    ∀ n : Nat, n < 256 ^ k →
      toBytesBEFixed k n
        = List.replicate (k - (Nat.toBytesBE n).length) 0 ++ Nat.toBytesBE n := by
  induction k with
  | zero =>
    intro n h
    have hn : n = 0 := by rw [Nat.pow_zero] at h; omega
    subst hn
    rw [Nat.toBytesBE_zero]
    rfl
  | succ k ih =>
    intro n h
    rcases Nat.eq_zero_or_pos n with hz | hp
    · subst hz
      rw [Nat.toBytesBE_zero, toBytesBEFixed_zero]
      simp
    · have hstep : toBytesBEFixed (k + 1) n
          = toBytesBEFixed k (n / 256) ++ [BitVec.ofNat 8 (n % 256)] := rfl
      have hdiv : n / 256 < 256 ^ k := by
        have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := by rw [Nat.pow_succ]
        rw [hpow] at h
        omega
      have hsucc : Nat.toBytesBE n
          = Nat.toBytesBE (n / 256) ++ [BitVec.ofNat 8 (n % 256)] := by
        match n, hp with
        | m + 1, _ => exact Nat.toBytesBE_succ m
      rw [hstep, ih (n / 256) hdiv, hsucc]
      have hlen : (k + 1) - (Nat.toBytesBE (n / 256) ++ [BitVec.ofNat 8 (n % 256)]).length
          = k - (Nat.toBytesBE (n / 256)).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hlen, List.append_assoc]

/-- The 32-byte BE form of a 256-bit word is its minimal BE bytes, left-padded
    with zeros. -/
theorem word256Bytes32_eq_replicate_append (w : Word256) :
    word256Bytes32 w
      = List.replicate (32 - (Nat.toBytesBE w.toNat).length) 0 ++ Nat.toBytesBE w.toNat :=
  toBytesBEFixed_eq_replicate_append 32 w.toNat (by
    rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]; exact w.isLt)

/-- **The right-aligned copy of field 1's content is the 32-byte BE balance.**
    Identifies `rlp_content_to_u256_be`'s success output (over the account
    bytes) with `word256Bytes32 a.balance`. -/
theorem account_balance_copyN_eq (a : Account) (hnonce : a.nonce < 2 ^ 256) :
    copyN (List.replicate 32 (0 : BitVec 8)) (encodeAccount a)
        (32 - (Nat.toBytesBE a.balance.toNat).length)
        (((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length)
          - (Nat.toBytesBE a.balance.toNat).length)
        (Nat.toBytesBE a.balance.toNat).length
      = word256Bytes32 a.balance := by
  have hle32 := account_balance_field_len_le_32 a
  obtain ⟨pre, hpre, hplen⟩ :=
    encodeBytes_toBytesBE_split a.balance.toNat (balance_len_le_55 a)
  have hfit : (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
      + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length ≤ (encodeAccount a).length := by
    rw [encodeAccount_length_eq a hnonce]
    have hP : (encodeBytes (Nat.toBytesBE a.nonce)).length
        + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length ≤ (accountPayload a).length := by
      simp only [accountPayload, List.length_append]; omega
    omega
  rw [copyN_eq_append _ _ _ _ _
    (by rw [List.length_replicate]; omega) (by omega)]
  rw [account_balance_content_window a hnonce]
  rw [show (32 - (Nat.toBytesBE a.balance.toNat).length)
      + (Nat.toBytesBE a.balance.toNat).length = 32 from by omega]
  rw [List.take_replicate, List.drop_replicate]
  rw [show min (32 - (Nat.toBytesBE a.balance.toNat).length) 32
      = 32 - (Nat.toBytesBE a.balance.toNat).length from by omega,
    show (32 : Nat) - 32 = 0 from by omega]
  rw [word256Bytes32_eq_replicate_append a.balance]
  simp

/-! ## 6. `rlp_content_to_u64` over the nonce content window -/

/-- **`rlp_content_to_u64` over field 0's content window decodes the nonce.**
    From the content pointer/length the accessor derives after the field-0
    `rlp_walk_next` (`ptr = a0 - a2`, `len = a2`), the content decoder
    deterministically succeeds with `a0 = nonce` (as a u64), `a1 = 0` — the
    too-long arm is refuted by EIP-2681 (`nonce < 2^64` ⇒ `len ≤ 8`), and the
    `len = 0` arm yields zero.

    `t1`/`x6` takes an arbitrary incoming value `x6Old` (the callee's own
    `MV x6 x10` overwrites it), so this is directly consumable by
    `accountExtractNonce_prog`'s call composition — the accessor does not pin
    `x6` before its `jal rlp_content_to_u64`. -/
theorem account_rlp_content_to_u64_nonce_spec_within
    (base listBase raVal t0Old x6Old t2Old t3Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.nonce).length + 9) base (raVal &&& ~~~1)
      (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
            - (Nat.toBytesBE a.nonce).length))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase (encodeAccount a)) **
       ((.x10 ↦ᵣ (BitVec.ofNat 64 a.nonce)) ** (.x11 ↦ᵣ (0 : Word)))) := by
  have hn256 : a.nonce < 2 ^ 256 := by
    have hle : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  set cLen := (Nat.toBytesBE a.nonce).length with hcLen
  set cOff := (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length) - cLen with hcOff
  have hle8 : cLen ≤ 8 := account_nonce_field_len_le_8 a hnonce
  obtain ⟨pre, hpre, hplen⟩ := encodeBytes_toBytesBE_split a.nonce (nonce_len_le_55 a hn256)
  have hfit : 2 + (encodeBytes (Nat.toBytesBE a.nonce)).length ≤ (encodeAccount a).length := by
    rw [encodeAccount_length_eq a hn256]
    have hP : (encodeBytes (Nat.toBytesBE a.nonce)).length ≤ (accountPayload a).length := by
      simp only [accountPayload, List.length_append]; omega
    omega
  have hslen : cOff + cLen ≤ (encodeAccount a).length := by omega
  have ht := rlp_content_to_u64_spec_within base listBase raVal t0Old x6Old t2Old t3Old
    (encodeAccount a) cOff cLen (by omega) hsalign hslen (by omega)
    (fun k hk => hvalid (cOff + k) (by omega))
  refine cpsTripleWithin_weaken (fun h hp => hp) (fun h hp => ?_) ht
  refine sepConj_mono_right (fun h' hbody => ?_) h hp
  rcases hbody with h1 | h2 | h3
  · -- too-long (`8 < len`): refuted by EIP-2681
    obtain ⟨_, hb', _, _, _, hin⟩ := h1
    exact absurd ((sepConj_pure_right hb').1 hin).2 (by omega)
  · -- `len = 0`: the canonical zero — so the value is the (zero) nonce
    obtain ⟨ha, hb', hdisj, hunion, hx10, hin⟩ := h2
    have hlen0 : cLen = 0 := ((sepConj_pure_right hb').1 hin).2
    have hn0 : a.nonce = 0 := by
      have hnil : Nat.toBytesBE a.nonce = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcLen]; exact hlen0)
      have hrt := Nat.fromBytesBE_toBytesBE a.nonce
      rw [hnil, Nat.fromBytesBE_nil] at hrt
      omega
    have he : (0 : Word) = BitVec.ofNat 64 a.nonce := by rw [hn0]; decide
    exact ⟨ha, hb', hdisj, hunion, he ▸ hx10, ((sepConj_pure_right hb').1 hin).1⟩
  · -- success: the window decodes to the nonce
    obtain ⟨ha, hb', hdisj, hunion, hx10, hin⟩ := h3
    have hval : BitVec.ofNat 64
        (Nat.fromBytesBE (((encodeAccount a).drop cOff).take cLen))
        = BitVec.ofNat 64 a.nonce := by
      have hv := account_nonce_content_value a hn256
      rw [← hcLen, ← hcOff] at hv
      rw [hv]
    exact ⟨ha, hb', hdisj, hunion, hval ▸ hx10, ((sepConj_pure_right hb').1 hin).1⟩

/-! ## 7. `rlp_content_to_u256_be` over the balance content window -/

/-- **`rlp_content_to_u256_be` over field 1's content window produces the
    32-byte BE balance.** From the content pointer/length the accessor derives
    after the field-1 `rlp_walk_next`, the content decoder deterministically
    succeeds with status `a0 = 0` and the output cell holding exactly
    `word256Bytes32 a.balance` — the too-long arm is refuted by
    `balance < 2^256` (`len ≤ 32`), and both the `len = 0` and copy arms produce
    the fixed-width BE
    form (`account_balance_copyN_eq`). Unlike the u64 decoder, this spec has no
    pinned scratch register, so it is directly consumable by the accessor's
    call composition. -/
theorem account_rlp_content_to_u256_be_balance_spec_within
    (base listBase outPtr raVal x5Old x6Old x7Old x28Old x29Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 256)
    (hsalign : listBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.balance.toNat).length + 16) base (raVal &&& ~~~1)
      (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          (((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
              + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length)
            - (Nat.toBytesBE a.balance.toNat).length))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
        (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a) ** memOwnU256 outPtr)
      (((.x11 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.balance.toNat).length)) **
        (.x12 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase (encodeAccount a)) **
       ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (word256Bytes32 a.balance))) := by
  set cLen := (Nat.toBytesBE a.balance.toNat).length with hcLen
  set cOff := ((2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
      + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length) - cLen with hcOff
  have hle32 : cLen ≤ 32 := account_balance_field_len_le_32 a
  obtain ⟨pre, hpre, hplen⟩ :=
    encodeBytes_toBytesBE_split a.balance.toNat (balance_len_le_55 a)
  have hfit : (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length)
      + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length ≤ (encodeAccount a).length := by
    rw [encodeAccount_length_eq a hnonce]
    have hP : (encodeBytes (Nat.toBytesBE a.nonce)).length
        + (encodeBytes (Nat.toBytesBE a.balance.toNat)).length ≤ (accountPayload a).length := by
      simp only [accountPayload, List.length_append]; omega
    omega
  have hslen : cOff + cLen ≤ (encodeAccount a).length := by omega
  have ht := rlp_content_to_u256_be_spec_within base listBase outPtr raVal x5Old x6Old x7Old
    x28Old x29Old (encodeAccount a) cOff cLen (by omega) hsalign hoalign hslen (by omega)
    hoover (fun k hk => hvalid (cOff + k) (by omega)) hdvalid
  refine cpsTripleWithin_weaken (fun h hp => hp) (fun h hp => ?_) ht
  refine sepConj_mono_right (fun h' hbody => ?_) h hp
  rcases hbody with h1 | h2 | h3
  · -- too-long (`32 < len`): refuted since the balance is a u256
    obtain ⟨_, hb', _, _, _, hin⟩ := h1
    exact absurd ((sepConj_pure_right hb').1 hin).2 (by omega)
  · -- `len = 0`: zero balance — the zeroed cell IS its 32-byte BE form
    obtain ⟨ha, hb', hdisj, hunion, hx10, hin⟩ := h2
    have hlen0 : cLen = 0 := ((sepConj_pure_right hb').1 hin).2
    have hz : a.balance.toNat = 0 := by
      have hnil : Nat.toBytesBE a.balance.toNat = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcLen]; exact hlen0)
      have hrt := Nat.fromBytesBE_toBytesBE a.balance.toNat
      rw [hnil, Nat.fromBytesBE_nil] at hrt
      omega
    have he : List.replicate 32 (0 : BitVec 8) = word256Bytes32 a.balance := by
      simp only [word256Bytes32, hz, toBytesBEFixed_zero]
    exact ⟨ha, hb', hdisj, hunion, hx10, he ▸ ((sepConj_pure_right hb').1 hin).1⟩
  · -- success: the right-aligned copy is `word256Bytes32 a.balance`
    obtain ⟨ha, hb', hdisj, hunion, hx10, hin⟩ := h3
    have he : copyN (List.replicate 32 (0 : BitVec 8)) (encodeAccount a) (32 - cLen) cOff cLen
        = word256Bytes32 a.balance := by
      have hc := account_balance_copyN_eq a hnonce
      rw [← hcLen, ← hcOff] at hc
      exact hc
    exact ⟨ha, hb', hdisj, hunion, hx10, he ▸ ((sepConj_pure_right hb').1 hin).1⟩
