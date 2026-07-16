/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptySpec

  Whole-program caller contract for `accountIsEip161Empty_prog` (K137,
  `AccountFields.lean`, 108 instructions, entry
  `GuestAddrs.account_is_eip161_empty`).

  The routine decodes an Ethereum account RLP
  `[nonce, balance, storage_root, code_hash]` via three calls to
  `rlp_list_nth_item` (K20, fields 0/1/3) and writes to a u64 output cell
  whether the account is EIP-161 empty:

      is_empty  ⟺  nonce == 0  ∧  balance == 0  ∧  code_hash == EMPTY_CODE_HASH

  Each field is inspected with a byte-wise LBU loop (the #10340 byte-safe
  code-hash compare, replacing the earlier misaligned 32-byte dword LDs):
    * nonce   (field 0): length ≤ 8, big-endian accumulate + test == 0;
    * balance (field 1): length ≤ 32, all content bytes == 0;
    * code_hash (field 3): length == 32, bytes == EMPTY_CODE_HASH.

  This module hosts the genuine semantic model (`beAccFrom`,
  `aieEmptyCodeHashBytes`, `accountEip161Empty`), the byte-scan bridge
  lemmas, and the code-layout infrastructure.  Composition of the whole
  108-instruction triple (`account_is_eip161_empty_spec_within`) builds on
  the three byte-scan loop lemmas here.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountFields
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## Code layout -/

/-- The accessor body's fixed guest base address. -/
abbrev AB : Word := (GuestAddrs.account_is_eip161_empty : Word)

/-- Code requirement for the 108-instruction accessor body. -/
def aieCode : CodeReq := CodeReq.ofProg AB accountIsEip161Empty_prog

/-- The full code region: the accessor body ∪ the `rlp_list_nth_item`
    subroutine it calls three times. -/
def fullCode : CodeReq := aieCode.union RlpListNthItemSAsm.code

theorem aie_prog_length : accountIsEip161Empty_prog.length = 108 := by decide

/-! ## The empty-code-hash constant (`aie_empty_code_hash` `.data` bytes) -/

/-- The 32 bytes of `EMPTY_CODE_HASH = keccak256(b'')`, exactly as baked
    into the `aie_empty_code_hash` `.data` constant. -/
def aieEmptyCodeHashBytes : List (BitVec 8) :=
  [ 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
    0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
    0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70 ]

theorem aieEmptyCodeHashBytes_length : aieEmptyCodeHashBytes.length = 32 := by decide

/-! ## Big-endian accumulate (the nonce scan's `x7`)

    Mirrors the guest's per-byte `x7 := (x7 <<< 8) ||| bs[off+i]` scan:
    `beAccFrom bs off n` is the big-endian value of the `n` content bytes
    of `bs` starting at absolute index `off`. -/

def beAccFrom (bs : List (BitVec 8)) (off : Nat) : Nat → Word
  | 0     => 0
  | i + 1 => (beAccFrom bs off i <<< (8 : Nat)) ||| (bs.getD (off + i) 0).zeroExtend 64

@[simp] theorem beAccFrom_zero (bs : List (BitVec 8)) (off : Nat) :
    beAccFrom bs off 0 = 0 := rfl

theorem beAccFrom_succ (bs : List (BitVec 8)) (off i : Nat) :
    beAccFrom bs off (i + 1) =
      (beAccFrom bs off i <<< (8 : Nat)) ||| (bs.getD (off + i) 0).zeroExtend 64 := rfl

/-- If every processed content byte is zero, the big-endian accumulator is
    zero (the `←` direction of the nonce verdict). -/
theorem beAccFrom_eq_zero_of_allZero (bs : List (BitVec 8)) (off n : Nat)
    (hz : ∀ k, k < n → bs.getD (off + k) 0 = 0) :
    beAccFrom bs off n = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [beAccFrom_succ, ih (fun k hk => hz k (by omega)),
        hz m (by omega)]
      decide

/-- For a nonce field of at most 8 content bytes the accumulator never
    overflows: its natural value is bounded by `2^(8n)`. -/
theorem beAccFrom_toNat_lt (bs : List (BitVec 8)) (off n : Nat) (hn : n ≤ 8) :
    (beAccFrom bs off n).toNat < 2 ^ (8 * n) := by
  induction n with
  | zero => simp [beAccFrom]
  | succ m ih =>
      have hm : m ≤ 8 := by omega
      have hib := ih hm
      have hib56 : (beAccFrom bs off m).toNat < 2 ^ 56 :=
        lt_of_lt_of_le hib (Nat.pow_le_pow_right (by omega) (by omega))
      rw [beAccFrom_succ, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      have hnowrap : (beAccFrom bs off m).toNat * 2 ^ 8 % 2 ^ 64
          = (beAccFrom bs off m).toNat * 2 ^ 8 := by
        apply Nat.mod_eq_of_lt
        calc (beAccFrom bs off m).toNat * 2 ^ 8 < 2 ^ 56 * 2 ^ 8 :=
              Nat.mul_lt_mul_of_pos_right hib56 (by norm_num)
          _ = 2 ^ 64 := by norm_num
      rw [hnowrap]
      have hleft : (beAccFrom bs off m).toNat * 2 ^ 8 < 2 ^ (8 * (m + 1)) := by
        rw [show 8 * (m + 1) = 8 * m + 8 from by ring, pow_add]
        exact Nat.mul_lt_mul_of_pos_right hib (by norm_num)
      have hbyte : (BitVec.setWidth 64 (bs.getD (off + m) 0)).toNat < 2 ^ (8 * (m + 1)) := by
        rw [BitVec.toNat_setWidth]
        have hb := (bs.getD (off + m) 0).isLt
        have h8 : (2 : Nat) ^ 8 ≤ 2 ^ (8 * (m + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        have hmod : (bs.getD (off + m) 0).toNat % 2 ^ 64 = (bs.getD (off + m) 0).toNat :=
          Nat.mod_eq_of_lt (by omega)
        omega
      exact Nat.or_lt_two_pow hleft hbyte

/-- `→` direction of the nonce bridge: a zero accumulator over ≤ 8 content
    bytes forces every content byte to be zero. -/
theorem beAccFrom_allZero_of_eq_zero (bs : List (BitVec 8)) (off : Nat) :
    ∀ n, n ≤ 8 → beAccFrom bs off n = 0 → ∀ k, k < n → bs.getD (off + k) 0 = 0 := by
  intro n
  induction n with
  | zero => intro _ _ k hk; omega
  | succ m ih =>
      intro hn h k hk
      have hm : m ≤ 8 := by omega
      rw [beAccFrom_succ] at h
      obtain ⟨hleft, hright⟩ := BitVec.or_eq_zero_iff.mp h
      have haccm : beAccFrom bs off m = 0 := by
        have hlt : (beAccFrom bs off m).toNat < 2 ^ 56 :=
          lt_of_lt_of_le (beAccFrom_toNat_lt bs off m hm)
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hval : (beAccFrom bs off m <<< (8 : Nat)).toNat
            = (beAccFrom bs off m).toNat * 2 ^ 8 := by
          rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          apply Nat.mod_eq_of_lt
          calc (beAccFrom bs off m).toNat * 2 ^ 8 < 2 ^ 56 * 2 ^ 8 :=
                Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
            _ = 2 ^ 64 := by norm_num
        have hshift : (beAccFrom bs off m).toNat * 2 ^ 8 = 0 := by
          rw [← hval, hleft]; rfl
        have hz : (beAccFrom bs off m).toNat = 0 := by
          rcases Nat.mul_eq_zero.mp hshift with h' | h'
          · exact h'
          · exact absurd h' (by norm_num)
        exact BitVec.eq_of_toNat_eq (by rw [hz]; rfl)
      have hbytem : bs.getD (off + m) 0 = 0 := by
        have hcong : (bs.getD (off + m) 0).toNat % 2 ^ 64 = 0 := by
          have := congrArg BitVec.toNat hright
          simpa [BitVec.toNat_setWidth] using this
        have hbb := (bs.getD (off + m) 0).isLt
        rw [Nat.mod_eq_of_lt (by omega)] at hcong
        exact BitVec.eq_of_toNat_eq (by rw [hcong]; rfl)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
      · exact ih hm haccm k hk'
      · subst hk'; exact hbytem

/-- **The nonce verdict bridge.**  For a field of at most 8 content bytes,
    the guest's big-endian accumulator is zero exactly when every content
    byte is zero — so testing `x7 == 0` is the lenient EIP-161 "nonce is
    zero" check (accepts non-canonical zero encodings). -/
theorem beAccFrom_eq_zero_iff (bs : List (BitVec 8)) (off n : Nat) (hn : n ≤ 8) :
    beAccFrom bs off n = 0 ↔ ∀ k, k < n → bs.getD (off + k) 0 = 0 :=
  ⟨fun h => beAccFrom_allZero_of_eq_zero bs off n hn h,
   fun h => beAccFrom_eq_zero_of_allZero bs off n h⟩

/-! ## The genuine EIP-161-empty verdict

    Tied to the three `rlp_list_nth_item` successes and the actual content
    bytes: the nonce decodes big-endian to `0`, every balance content byte
    is `0`, and the code-hash content equals `EMPTY_CODE_HASH`. -/

def accountEip161Empty (bytes : List (BitVec 8)) (base : Word) (listLen : Nat) : Prop :=
  ∃ o0 l0 o1 l1 o3 l3 : Word,
    -- field 0 (nonce): lenient — every content byte is zero
    Success bytes base listLen 0 o0 l0 ∧ l0.toNat ≤ 8 ∧
      (∀ k, k < l0.toNat → bytes.getD (o0.toNat + k) 0 = 0) ∧
    -- field 1 (balance): lenient — every content byte is zero
    Success bytes base listLen 1 o1 l1 ∧ l1.toNat ≤ 32 ∧
      (∀ k, k < l1.toNat → bytes.getD (o1.toNat + k) 0 = 0) ∧
    -- field 3 (code_hash): exact — content equals EMPTY_CODE_HASH
    Success bytes base listLen 3 o3 l3 ∧ l3.toNat = 32 ∧
      (∀ k, k < 32 → bytes.getD (o3.toNat + k) 0 = aieEmptyCodeHashBytes.getD k 0)

end EvmAsm.Codegen.AccountIsEip161EmptySpec
