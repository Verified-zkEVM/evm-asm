/-
  Whole-program caller-contract scaffolding for `accountDecode_prog`
  (`Programs/State.lean`, PR-K27, 136 instructions, entry
  `GuestAddrs.account_decode`).

  An account is the RLP list `[nonce, balance, storage_root, code_hash]`.
  The accessor decodes it into four caller-supplied output slots:

    a2 : nonce         out ptr (8 bytes; written LE u64, big-endian decode)
    a3 : balance       out ptr (32 bytes; BE, left-zero-padded, right-aligned)
    a4 : storage_root  out ptr (32 bytes; exact 32-byte copy)
    a5 : code_hash     out ptr (32 bytes; exact 32-byte copy)

  Calling convention (matches the program's prologue saves):
    a0 (input)  : account RLP bytes ptr        (saved into s0/x8)
    a1 (input)  : account RLP byte length       (saved into s1/x9)
    a2 (input)  : nonce out ptr                 (saved into s2/x18)
    a3 (input)  : balance out ptr               (saved into s3/x19)
    a4 (input)  : storage_root out ptr          (saved into s4/x20)
    a5 (input)  : code_hash out ptr             (saved into s5/x21)
    ra (input)  : return
    a0 (output) : 0 success / 1 parse fail

  ALL four fields are decoded via `rlp_list_nth_item` (`LI x12 = 0/1/2/3`),
  each: nth_item call → `BNE x10,x0` (parse fail) → a per-field length check →
  a byte-materialisation loop.  The four field materialisers differ:

    * field 0 (nonce): leading-zero-tolerant value bound (significant bytes
      fit u64); a top-tested big-endian
      accumulation loop building a u64 register value, then `SD`.
    * field 1 (balance): leading-zero-tolerant value bound (significant bytes
      fit u256); 32-byte out zeroed, significant bytes right-aligned.
    * field 2 (storage_root): length ∈ {0, 32} (Bytes32 / EMPTY fold) — stays a
      length constraint; leading zeros are part of the hash.
    * field 3 (code_hash): length ∈ {0, 32} — same.

  The only linked callee is `rlp_list_nth_item`, so the full linked closure is
  `adCode ∪ RlpListNthItemSAsm.code`.

  This module hosts the code layout, disjointness/mono lemmas, the semantic
  decode model (genuine per-field `Success`/`Failure` ties -- mirroring
  `WithdrawalDecodeSpec`), and the caller-facing success/failure outcomes.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.Programs.State
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec
import EvmAsm.Stateless.SpecRef.WitnessState

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

/-! ## Code layout -/

/-- The accessor body's fixed guest base address. -/
abbrev AB : Word := (GuestAddrs.account_decode : Word)

set_option maxRecDepth 8000 in
theorem ad_length : accountDecode_prog.length = 174 := by decide

/-- The wrapper's own re-emitted instructions at `account_decode`. -/
def adCode : CodeReq := CodeReq.ofProg AB accountDecode_prog

/-- The full linked closure: this accessor plus the strict `rlp_list_nth_item`
    subroutine (the only cross-`jal` callee). -/
def fullCode : CodeReq := adCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem ad_disjoint :
    adCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold adCode EvmAsm.Codegen.RlpListNthItemSAsm.code
    EvmAsm.Codegen.RlpListNthItemSAsm.B AB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [ad_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [ad_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide

#print axioms ad_disjoint

theorem ad_mono : ∀ a i, adCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-- The strict `rlp_list_nth_item` subroutine (called for every field) is a
    sub-union of the full closure. -/
theorem k20_mono :
    ∀ a i, EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right ad_disjoint (fun _ _ h => h) a i hi

#print axioms ad_mono
#print axioms k20_mono

/-! ## Semantic decode model

    Every field decodes via K20's `Success`/`Failure` relation on the same
    strict RLP list.  GH #11523: nonce/balance are **value** bounds on the
    leading-zero-stripped content (u64 / u256), matching
    `witness_state.py:112-118` `int.from_bytes` (e5a8caf1b).  storage_root /
    code_hash stay **length** ∈ {0,32} (`Root`/`Hash32` = Bytes32).  No
    decode-determinism is assumed: each failure arm names the *actual* failing
    stage (mirroring `WithdrawalDecodeSpec`). -/

open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Content bytes of one RLP string field at relative offset `o` length `l`. -/
def fieldContent (bytes : List (BitVec 8)) (o l : Nat) : List (BitVec 8) :=
  (bytes.drop o).take l

/-- Leading-zero count of a big-endian integer encoding (all-zero → full length). -/
def numLeadingZerosBE (bs : List (BitVec 8)) : Nat :=
  (bs.takeWhile (· == 0)).length

/-- Significant (leading-zero-stripped) length.  Empty after strip ⇒ 0. -/
def significantLen (bs : List (BitVec 8)) : Nat :=
  bs.length - numLeadingZerosBE bs

/-- Significant content bytes (drop leading zeros). -/
def significantBytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs.drop (numLeadingZerosBE bs)

/-- Relative offset of the first significant byte within a field. -/
def significantOff (bytes : List (BitVec 8)) (o l : Nat) : Nat :=
  o + numLeadingZerosBE (fieldContent bytes o l)

/-- Value-bound for nonce: significant encoding fits in 8 bytes (u64).
    Equivalent to `int.from_bytes(field, "big") < 2^64` for big-endian content. -/
def nonceValueOk (bytes : List (BitVec 8)) (o l : Word) : Prop :=
  significantLen (fieldContent bytes o.toNat l.toNat) ≤ 8

/-- Value-bound for balance: significant encoding fits in 32 bytes (u256). -/
def balanceValueOk (bytes : List (BitVec 8)) (o l : Word) : Prop :=
  significantLen (fieldContent bytes o.toNat l.toNat) ≤ 32

/-- Big-endian accumulation of `len` content bytes starting at relative offset
    `off`, matching the nonce loop `x7 := (x7 <<< 8) ||| byte` after the
    leading-zero strip.  Callers pass the *significant* off/len. -/
def beAccum (bytes : List (BitVec 8)) (off : Nat) : Nat → Word
  | 0 => 0
  | (i + 1) => (beAccum bytes off i) <<< 8 |||
      ((bytes.getD (off + i) 0).zeroExtend 64)

@[simp] theorem beAccum_zero (bytes : List (BitVec 8)) (off : Nat) :
    beAccum bytes off 0 = 0 := rfl

theorem beAccum_succ (bytes : List (BitVec 8)) (off i : Nat) :
    beAccum bytes off (i + 1) =
      (beAccum bytes off i <<< (8 : Nat)) |||
        (bytes.getD (off + i) 0).zeroExtend 64 := rfl

/-- If every processed content byte is zero, the big-endian accumulator is
    zero (the `←` direction of the nonce verdict). -/
theorem beAccum_eq_zero_of_allZero (bytes : List (BitVec 8)) (off n : Nat)
    (hz : ∀ k, k < n → bytes.getD (off + k) 0 = 0) :
    beAccum bytes off n = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [beAccum_succ, ih (fun k hk => hz k (by omega)),
        hz m (by omega)]
      decide

/-- For a nonce field of at most 8 content bytes the accumulator never
    overflows: its natural value is bounded by `2^(8n)`. -/
theorem beAccum_toNat_lt (bytes : List (BitVec 8)) (off n : Nat) (hn : n ≤ 8) :
    (beAccum bytes off n).toNat < 2 ^ (8 * n) := by
  induction n with
  | zero => simp [beAccum]
  | succ m ih =>
      have hm : m ≤ 8 := by omega
      have hib := ih hm
      have hib56 : (beAccum bytes off m).toNat < 2 ^ 56 :=
        lt_of_lt_of_le hib (Nat.pow_le_pow_right (by omega) (by omega))
      rw [beAccum_succ, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      have hnowrap : (beAccum bytes off m).toNat * 2 ^ 8 % 2 ^ 64
          = (beAccum bytes off m).toNat * 2 ^ 8 := by
        apply Nat.mod_eq_of_lt
        calc (beAccum bytes off m).toNat * 2 ^ 8 < 2 ^ 56 * 2 ^ 8 :=
              Nat.mul_lt_mul_of_pos_right hib56 (by norm_num)
          _ = 2 ^ 64 := by norm_num
      rw [hnowrap]
      have hleft : (beAccum bytes off m).toNat * 2 ^ 8 < 2 ^ (8 * (m + 1)) := by
        rw [show 8 * (m + 1) = 8 * m + 8 from by ring, pow_add]
        exact Nat.mul_lt_mul_of_pos_right hib (by norm_num)
      have hbyte : (BitVec.setWidth 64 (bytes.getD (off + m) 0)).toNat
          < 2 ^ (8 * (m + 1)) := by
        rw [BitVec.toNat_setWidth]
        have hb := (bytes.getD (off + m) 0).isLt
        have h8 : (2 : Nat) ^ 8 ≤ 2 ^ (8 * (m + 1)) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hmod : (bytes.getD (off + m) 0).toNat % 2 ^ 64
            = (bytes.getD (off + m) 0).toNat :=
          Nat.mod_eq_of_lt (by omega)
        omega
      exact Nat.or_lt_two_pow hleft hbyte

/-- `→` direction of the nonce bridge: a zero accumulator over ≤ 8 content
    bytes forces every content byte to be zero. -/
theorem beAccum_allZero_of_eq_zero (bytes : List (BitVec 8)) (off : Nat) :
    ∀ n, n ≤ 8 → beAccum bytes off n = 0 →
      ∀ k, k < n → bytes.getD (off + k) 0 = 0 := by
  intro n
  induction n with
  | zero => intro _ _ k hk; omega
  | succ m ih =>
      intro hn h k hk
      have hm : m ≤ 8 := by omega
      rw [beAccum_succ] at h
      obtain ⟨hleft, hright⟩ := BitVec.or_eq_zero_iff.mp h
      have haccm : beAccum bytes off m = 0 := by
        have hlt : (beAccum bytes off m).toNat < 2 ^ 56 :=
          lt_of_lt_of_le (beAccum_toNat_lt bytes off m hm)
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hval : (beAccum bytes off m <<< (8 : Nat)).toNat
            = (beAccum bytes off m).toNat * 2 ^ 8 := by
          rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          apply Nat.mod_eq_of_lt
          calc (beAccum bytes off m).toNat * 2 ^ 8 < 2 ^ 56 * 2 ^ 8 :=
                Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
            _ = 2 ^ 64 := by norm_num
        have hshift : (beAccum bytes off m).toNat * 2 ^ 8 = 0 := by
          rw [← hval, hleft]; rfl
        have hz : (beAccum bytes off m).toNat = 0 := by
          rcases Nat.mul_eq_zero.mp hshift with h' | h'
          · exact h'
          · exact absurd h' (by norm_num)
        exact BitVec.eq_of_toNat_eq (by rw [hz]; rfl)
      have hbytem : bytes.getD (off + m) 0 = 0 := by
        have hcong : (bytes.getD (off + m) 0).toNat % 2 ^ 64 = 0 := by
          have := congrArg BitVec.toNat hright
          simpa [BitVec.toNat_setWidth] using this
        have hbb := (bytes.getD (off + m) 0).isLt
        rw [Nat.mod_eq_of_lt (by omega)] at hcong
        exact BitVec.eq_of_toNat_eq (by rw [hcong]; rfl)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
      · exact ih hm haccm k hk'
      · subst hk'; exact hbytem

/-- **The nonce verdict bridge.** For a field of at most 8 content bytes,
    the accumulator is zero exactly when every content byte is zero. -/
theorem beAccum_eq_zero_iff (bytes : List (BitVec 8)) (off n : Nat) (hn : n ≤ 8) :
    beAccum bytes off n = 0 ↔
      ∀ k, k < n → bytes.getD (off + k) 0 = 0 :=
  ⟨fun h => beAccum_allZero_of_eq_zero bytes off n hn h,
   fun h => beAccum_eq_zero_of_allZero bytes off n h⟩

/-- Nonce u64 after a successful decode: accumulate the significant bytes. -/
def nonceAccum (bytes : List (BitVec 8)) (o l : Nat) : Word :=
  beAccum bytes (significantOff bytes o l) (significantLen (fieldContent bytes o l))

/-- The 32-byte balance buffer after a successful decode: zeroed 32-byte region
    with the *significant* content bytes right-aligned (strip then
    `out + (32 - sigLen)` forward copy), matching the program post-#11523. -/
def balanceCopied (bytes : List (BitVec 8)) (o1 : Word) (l1 : Nat) : List (BitVec 8) :=
  let sig := significantBytes (fieldContent bytes o1.toNat l1)
  copyIntoRegion (List.replicate 32 (0 : BitVec 8)) sig (32 - sig.length) 0 sig.length

theorem balanceCopied_length (bytes : List (BitVec 8)) (o1 : Word) (l1 : Nat) :
    (balanceCopied bytes o1 l1).length = 32 := by
  unfold balanceCopied; rw [copyIntoRegion_length]; simp

theorem numLeadingZerosBE_le (bs : List (BitVec 8)) :
    numLeadingZerosBE bs ≤ bs.length := by
  unfold numLeadingZerosBE
  induction bs with
  | nil => decide
  | cons b bs ih =>
    rw [List.takeWhile_cons]
    split_ifs with hb
    · simp only [List.length_cons]; exact Nat.succ_le_succ ih
    · simp only [List.length_nil]; exact Nat.zero_le _

theorem significantLen_le (bs : List (BitVec 8)) :
    significantLen bs ≤ bs.length := by
  unfold significantLen; have := numLeadingZerosBE_le bs; omega

/-- `((bs.drop o).take l).drop k = (bs.drop (o+k)).take (l-k)`. -/
theorem drop_take_drop_eq (bs : List (BitVec 8)) (o l k : Nat) :
    ((bs.drop o).take l).drop k = (bs.drop (o + k)).take (l - k) := by
  rw [List.drop_take, List.drop_drop]

/-- Significant window as a slice of the ambient byte buffer. -/
theorem significantBytes_eq_slice (bytes : List (BitVec 8)) (o l : Nat)
    (_hbound : o + l ≤ bytes.length) :
    let nlz := numLeadingZerosBE (fieldContent bytes o l)
    significantBytes (fieldContent bytes o l) = (bytes.drop (o + nlz)).take (l - nlz) := by
  intro nlz
  unfold significantBytes fieldContent
  exact drop_take_drop_eq bytes o l nlz

/-- Significant length equals field length minus leading zeros. -/
theorem significantLen_eq_field (bytes : List (BitVec 8)) (o l : Nat)
    (hbound : o + l ≤ bytes.length) :
    significantLen (fieldContent bytes o l) = l - numLeadingZerosBE (fieldContent bytes o l) := by
  unfold significantLen fieldContent
  have hlen : ((bytes.drop o).take l).length = l := by
    rw [List.length_take, List.length_drop]; omega
  rw [hlen]

private theorem ads_getD_drop_take (src : List (BitVec 8)) (sOff i n : Nat)
    (hi : i < n) (hbound : sOff + n ≤ src.length) :
    ((src.drop sOff).take n).getD i 0 = src.getD (sOff + i) 0 := by
  have hlen : ((src.drop sOff).take n).length = n := by
    rw [List.length_take, List.length_drop]; omega
  have hi' : i < ((src.drop sOff).take n).length := by omega
  have hs : sOff + i < src.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    List.getElem?_eq_getElem hs, Option.getD_some]
  rw [List.getElem_take, List.getElem_drop]

/-- Copying `k` bytes from a longer take-window equals copying from the exact take. -/
private theorem ads_copyInto_take_short (dest win : List (BitVec 8)) (dOff k m : Nat)
    (hk : k ≤ m) :
    copyIntoRegion dest (win.take m) dOff 0 k = copyIntoRegion dest (win.take k) dOff 0 k := by
  induction k generalizing dest m with
  | zero => rfl
  | succ k ih =>
    simp only [copyIntoRegion]
    have hget : (win.take m).getD k 0 = (win.take (k + 1)).getD k 0 := by
      by_cases hkm : k < win.length
      · have hm : k < (win.take m).length := by rw [List.length_take]; omega
        have hk1 : k < (win.take (k + 1)).length := by rw [List.length_take]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm,
          List.getElem?_eq_getElem hk1, Option.getD_some, List.getElem_take]
      · have hm : (win.take m).length ≤ k := by rw [List.length_take]; omega
        have hk1 : (win.take (k + 1)).length ≤ k := by rw [List.length_take]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hm,
          List.getElem?_eq_none hk1]
    have hrec : copyIntoRegion dest (win.take m) dOff 0 k =
        copyIntoRegion dest (win.take (k + 1)) dOff 0 k := by
      have h1 := ih dest m (by omega)
      have h2 := ih dest (k + 1) (by omega)
      rw [h1, h2]
    simp only [Nat.zero_add]
    rw [hrec, hget]

/-- `copyIntoRegion` from an ambient buffer at `srcOff` equals copying the
    sliced window as a standalone source list. -/
theorem copyIntoRegion_of_slice (dest src : List (BitVec 8)) (dOff sOff n : Nat)
    (hbound : sOff + n ≤ src.length) :
    copyIntoRegion dest src dOff sOff n =
      copyIntoRegion dest ((src.drop sOff).take n) dOff 0 n := by
  induction n generalizing dest with
  | zero => rfl
  | succ n ih =>
    simp only [copyIntoRegion]
    have hih := ih dest (by omega)
    rw [hih]
    have hget : ((src.drop sOff).take (n + 1)).getD n 0 = src.getD (sOff + n) 0 :=
      ads_getD_drop_take src sOff n (n + 1) (by omega) hbound
    simp only [Nat.zero_add] at hget ⊢
    have hrec : copyIntoRegion dest ((src.drop sOff).take (n + 1)) dOff 0 n =
        copyIntoRegion dest ((src.drop sOff).take n) dOff 0 n :=
      ads_copyInto_take_short dest (src.drop sOff) dOff n (n + 1) (by omega)
    rw [hrec, hget]

/-- Loop form of `balanceCopied`: right-aligned copy from ambient significant window. -/
theorem balanceCopied_eq_loop (bytes : List (BitVec 8)) (o1 : Word) (l1 : Nat)
    (hbound : o1.toNat + l1 ≤ bytes.length) :
    let sigN := significantLen (fieldContent bytes o1.toNat l1)
    let sigO := significantOff bytes o1.toNat l1
    copyIntoRegion (List.replicate 32 (0 : BitVec 8)) bytes (32 - sigN) sigO sigN =
      balanceCopied bytes o1 l1 := by
  intro sigN sigO
  unfold balanceCopied
  have hslice := significantBytes_eq_slice bytes o1.toNat l1 hbound
  have hsigN : sigN = l1 - numLeadingZerosBE (fieldContent bytes o1.toNat l1) :=
    significantLen_eq_field bytes o1.toNat l1 hbound
  have hsigO : sigO = o1.toNat + numLeadingZerosBE (fieldContent bytes o1.toNat l1) := rfl
  have hsrc : sigO + sigN ≤ bytes.length := by
    rw [hsigO, hsigN]
    have hlenField : (fieldContent bytes o1.toNat l1).length = l1 := by
      unfold fieldContent; rw [List.length_take, List.length_drop]; omega
    have hnlz := numLeadingZerosBE_le (fieldContent bytes o1.toNat l1)
    omega
  have hcopy := copyIntoRegion_of_slice (List.replicate 32 (0 : BitVec 8)) bytes
    (32 - sigN) sigO sigN hsrc
  rw [hcopy]
  have hwin : (bytes.drop sigO).take sigN =
      significantBytes (fieldContent bytes o1.toNat l1) := by
    dsimp only [sigO, sigN] at hslice ⊢
    simpa [significantOff, significantLen_eq_field bytes o1.toNat l1 hbound] using hslice.symm
  rw [hwin]
  -- length of significantBytes = sigN by definition of significantLen
  have hlenEq : (significantBytes (fieldContent bytes o1.toNat l1)).length = sigN := by
    dsimp only [sigN, significantBytes, significantLen]
    rw [List.length_drop]
  rw [← hlenEq]


/-- A fixed 32-byte content copy (storage_root / code_hash): the 32 content
    bytes at relative offset `o` copied forward into the caller's old 32-byte
    output slot. -/
def fixed32Copied (bytes oldOut : List (BitVec 8)) (o : Word) : List (BitVec 8) :=
  copyIntoRegion oldOut bytes 0 o.toNat 32

theorem fixed32Copied_length (bytes oldOut : List (BitVec 8)) (o : Word)
    (hlen : oldOut.length = 32) :
    (fixed32Copied bytes oldOut o).length = 32 := by
  unfold fixed32Copied; rw [copyIntoRegion_length]; exact hlen

/-! ### The zero-length hash fold (GH #11483)

`witness_state.py:118-119` folds a **zero-length** `storage_root` / `code_hash`
to `EMPTY_TRIE_ROOT` / `EMPTY_CODE_HASH` rather than rejecting it; the guest
previously required exactly 32 bytes, so it false-rejected a leaf the spec
accepts.  The assembly now dispatches `len = 0` to a block that stores the
constant (four `LD`/`SD` pairs from `iw_empty_trie_root` / `aie_empty_code_hash`);
lengths outside `{0, 32}` still fail exactly as before.

These are the two constants as baked into those `.data` sections. -/

/-- `EMPTY_TRIE_ROOT = keccak256(rlp(b''))`, matching `iw_empty_trie_root`
    (`MptInsertWalk.lean:349`). -/
def adEmptyTrieRootBytes : List (BitVec 8) :=
  [ 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6,
    0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e,
    0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0,
    0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21 ]

theorem adEmptyTrieRootBytes_length : adEmptyTrieRootBytes.length = 32 := by decide

/-- `EMPTY_CODE_HASH = keccak256(b'')`, matching `aie_empty_code_hash`. -/
def adEmptyCodeHashBytes : List (BitVec 8) :=
  [ 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
    0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
    0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70 ]

theorem adEmptyCodeHashBytes_length : adEmptyCodeHashBytes.length = 32 := by decide

/-! The concrete `keccak256 []` reduction is deliberately split from the
    sentinel theorem below.  Unfolding the 24-round Keccak permutation directly
    at each use exhausts the default recursion depth; the one-block absorption
    and the existing accelerator KAT keep that cost contained in one lemma. -/

private theorem adEmptyCodeHash_absorb_block :
    keccakAbsorbBlock (List.replicate 25 (0 : BitVec 64)) (keccakPad []) =
      [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64,
       0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0x8000000000000000#64,
       0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] := by
  decide

private theorem adEmptyCodeHash_keccak_empty :
    keccak256 [] =
      ((Accel.keccakF (List.ofFn (n := 25) (fun j =>
        if j.val = 0 then 0x0000000000000001
        else if j.val = 16 then 0x8000000000000000
        else 0))).take 4).flatMap (fun lane => natToBytesLE 8 lane.toNat) := by
  have hchunks : chunkBytes 136 (keccakPad []) = [keccakPad []] := by
    simp [chunkBytes, chunkBytesAux, keccakPad, keccakRateBytes]
  have hchunks' : chunkBytes keccakRateBytes (keccakPad []) = [keccakPad []] := by
    simpa [keccakRateBytes] using hchunks
  unfold keccak256
  rw [hchunks']
  simp only [keccakAbsorb]
  rw [adEmptyCodeHash_absorb_block]
  congr 2

/-- The baked-in code-hash sentinel is the SpecRef `EMPTY_CODE_HASH` value. -/
theorem adEmptyCodeHashBytes_eq_spec :
    adEmptyCodeHashBytes = EMPTY_CODE_HASH := by
  rw [show EMPTY_CODE_HASH = keccak256 [] from rfl,
    adEmptyCodeHash_keccak_empty, Accel.keccakF_kat_empty]
  decide

/-- A hash output cell: the 32 copied content bytes, or the fold constant when
    the field was zero-length.  `fixed32Copied` cannot express the folded case
    for any offset — it is an unconditional copy from the input buffer — which
    is why the cell needs the length, not just the offset. -/
def hashCell (bytes oldOut : List (BitVec 8)) (o : Word) (l : Nat)
    (fold : List (BitVec 8)) : List (BitVec 8) :=
  if l = 0 then fold else fixed32Copied bytes oldOut o

theorem hashCell_length (bytes oldOut : List (BitVec 8)) (o : Word) (l : Nat)
    (fold : List (BitVec 8)) (hold : oldOut.length = 32) (hfold : fold.length = 32) :
    (hashCell bytes oldOut o l fold).length = 32 := by
  unfold hashCell; split
  · exact hfold
  · exact fixed32Copied_length bytes oldOut o hold

/-- On a nonzero field length the cell is the ordinary 32-byte content copy — the
    fold arm is unreachable.  This is what lets the `AccountRecord` composition
    keep its `fixed32Copied` reasoning unchanged: a record's `rlp` encodes
    `a.storageRoot` with `WF`-guaranteed length 32, so the folded arm names a
    leaf outside `AccountRecord.rlp`'s image (GH #11484). -/
theorem hashCell_of_ne_zero (bytes oldOut : List (BitVec 8)) (o : Word) (l : Nat)
    (fold : List (BitVec 8)) (hl : l ≠ 0) :
    hashCell bytes oldOut o l fold = fixed32Copied bytes oldOut o := by
  simp only [hashCell, hl, if_false]

/-- On a zero field length the cell is the fold constant. -/
theorem hashCell_zero (bytes oldOut : List (BitVec 8)) (o : Word)
    (fold : List (BitVec 8)) :
    hashCell bytes oldOut o 0 fold = fold := by
  simp only [hashCell, if_pos]

/-- Split a 32-byte region into its four little-endian dword cells, as an
    assertion equality (matching `adBalanceSetup`'s zeroing precondition). -/
theorem bytesRegion32_dwords_eq (base : Word) (bs : List (BitVec 8)) (h_len : bs.length = 32) :
    bytesRegion base bs =
    ((base ↦ₘ packBytes (bs.take 8)) ** ((base + 8) ↦ₘ packBytes ((bs.drop 8).take 8)) **
     ((base + 16) ↦ₘ packBytes (((bs.drop 8).drop 8).take 8)) **
     ((base + 24) ↦ₘ packBytes ((((bs.drop 8).drop 8).drop 8).take 8))) := by
  have hne0 : bs ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hne1 : bs.drop 8 ≠ [] := List.ne_nil_of_length_pos (by simp only [List.length_drop]; omega)
  have hne2 : (bs.drop 8).drop 8 ≠ [] :=
    List.ne_nil_of_length_pos (by simp only [List.length_drop]; omega)
  have hne3 : ((bs.drop 8).drop 8).drop 8 ≠ [] :=
    List.ne_nil_of_length_pos (by simp only [List.length_drop]; omega)
  have hdrop : ((((bs.drop 8).drop 8).drop 8).drop 8) = [] :=
    List.eq_nil_of_length_eq_zero (by simp only [List.length_drop]; omega)
  rw [bytesRegion_eq_cons base bs hne0, bytesRegion_eq_cons (base + 8) (bs.drop 8) hne1,
      bytesRegion_eq_cons (base + 8 + 8) ((bs.drop 8).drop 8) hne2,
      bytesRegion_eq_cons (base + 8 + 8 + 8) (((bs.drop 8).drop 8).drop 8) hne3,
      hdrop, bytesRegion_nil, sepConj_emp_right',
      show base + 8 + 8 = base + 16 from by bv_omega,
      show base + 16 + 8 = base + 24 from by bv_omega]

/-! ## The fold constants' guest addresses

    Both live in the `.data` RAM window and both are 8-byte aligned, which is
    what makes the `LD` side of each pair well-formed. -/

/-- `iw_empty_trie_root` (`MptInsertWalk.lean:349`). -/
abbrev ITR : Word := (GuestAddrs.iw_empty_trie_root : Word)

/-- `aie_empty_code_hash`. -/
abbrev ECH : Word := (GuestAddrs.aie_empty_code_hash : Word)

theorem itr_align : ITR.toNat % 8 = 0 := by decide
theorem ech_align : ECH.toNat % 8 = 0 := by decide

/-- The two `.data` constants the fold arms read, as one assertion.  Threaded
    through the field-2/3 backbones into `account_decode`'s precondition: the
    routine now *reads* guest data, which it did not before #11483. -/
def adFoldConstants : Assertion :=
  bytesRegion ITR adEmptyTrieRootBytes ** bytesRegion ECH adEmptyCodeHashBytes

theorem pcFree_adFoldConstants : adFoldConstants.pcFree := by
  unfold adFoldConstants
  exact pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)

/-- The genuine success verdict: all four fields decode as K20 successes, with
    nonce/balance satisfying **value** bounds (GH #11523: significant bytes fit
    u64 / u256 — leading zeros are padding) and the two hash fields either
    exactly 32 bytes or zero-length (the #11483 fold).  The output values are
    tied to the actual content:
      * nonce   = `nonceAccum` of field 0 (strip then `beAccum`),
      * balance = right-aligned 32-byte copy of significant field-1 bytes,
      * root / code_hash = 32-byte copy at `o2` / `o3`, or the EMPTY constant
        when the field was zero-length. -/
def Decoded (bytes : List (BitVec 8)) (listBase : Word) (listLen : Nat)
    (o0 l0 o1 l1 o2 l2 o3 l3 : Word) : Prop :=
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 0 o0 l0 ∧
  nonceValueOk bytes o0 l0 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 1 o1 l1 ∧
  balanceValueOk bytes o1 l1 ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2 ∧
  (l2.toNat = 32 ∨ l2.toNat = 0) ∧
  EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 3 o3 l3 ∧
  (l3.toNat = 32 ∨ l3.toNat = 0)

/-- The four output slots after a **successful** decode, each cell tied to the
    actual decoded field value. -/
def outputSuccess (nonceOut balanceOut rootOut codeOut o0 o1 o2 o3 : Word)
    (l0 l1 l2 l3 : Nat) (bytes oldRoot oldCode : List (BitVec 8)) : Assertion :=
  (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0) **
  bytesRegion balanceOut (balanceCopied bytes o1 l1) **
  bytesRegion rootOut (hashCell bytes oldRoot o2 l2 adEmptyTrieRootBytes) **
  bytesRegion codeOut (hashCell bytes oldCode o3 l3 adEmptyCodeHashBytes)

/-- An account-decode **failure** outcome, matching the program's short-circuit
    dispatch (field 0 list → field 0 value overflow → field 1 list → field 1
    value overflow → field 2 list → field 2 len∉{0,32} → field 3 list → field 3
    len∉{0,32}).  Each arm names the *actual* failing stage via K20's semantics
    (no determinism assumed).  Mirrors `WithdrawalDecodeSpec.DecodeFailure`. -/
inductive DecodeFailure (bytes : List (BitVec 8)) (listBase : Word)
    (listLen : Nat) : Prop
  -- ⚠️ GH #11483: `field2Len`/`field3Len` carry `≠ 0` as well as `≠ 32`, because a
  -- zero-length hash field no longer fails — it folds to the EMPTY constant. Without
  -- the second side condition this predicate would be inhabitable for an input the
  -- program *accepts*, i.e. it would stop characterising the failure set even though
  -- the whole-program theorem stayed true (a weaker post is still sound). The point
  -- of the predicate is to say what the routine rejects, so it has to track the fold.
  -- GH #11523: `field0Len`/`field1Len` are **value** overflows (significant length
  -- exceeds u64/u256 width), not raw RLP string length caps.
  | field0List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 0) :
      DecodeFailure bytes listBase listLen
  | field0Len (o0 l0 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 0 o0 l0)
      (hoven : ¬ nonceValueOk bytes o0 l0) :
      DecodeFailure bytes listBase listLen
  | field1List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 1) :
      DecodeFailure bytes listBase listLen
  | field1Len (o1 l1 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 1 o1 l1)
      (hoven : ¬ balanceValueOk bytes o1 l1) :
      DecodeFailure bytes listBase listLen
  | field2List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 2) :
      DecodeFailure bytes listBase listLen
  | field2Len (o2 l2 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 2 o2 l2)
      (hlen : l2.toNat ≠ 32) (hzero : l2.toNat ≠ 0) :
      DecodeFailure bytes listBase listLen
  | field3List
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen 3) :
      DecodeFailure bytes listBase listLen
  | field3Len (o3 l3 : Word)
      (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen 3 o3 l3)
      (hlen : l3.toNat ≠ 32) (hzero : l3.toNat ≠ 0) :
      DecodeFailure bytes listBase listLen

end EvmAsm.Codegen.AccountDecodeSpec
