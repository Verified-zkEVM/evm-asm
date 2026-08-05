/-
  EvmAsm.Codegen.Programs.AccountDecodeBridge

  Content lemmas for #11345: turning `account_decode`'s `outputSuccess` cells
  into the field values of an `AccountRecord`.

  `outputSuccess` (AccountDecodeSpec.lean:157) states the four output slots as
  *functions of the found offsets* — `beAccum`, `balanceCopied`, two
  `fixed32Copied`.  `accountDecodedIs` (AccountAssertions.lean:135) states them
  as the record's fields.  Bridging the two is what #11345 needs; from there
  `decode_account_from_leaf_accountRlp` (AccountAssertions.lean:294) already
  closes to `SpecRef.decode_account_from_leaf`.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec

namespace EvmAsm.Codegen.AccountDecodeBridge

open EvmAsm.Rv64 EvmAsm.EL.RLP
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)
open EvmAsm.Codegen.AccountDecodeSpec (beAccum balanceCopied fixed32Copied)

/-- A full-width copy at a nonzero **source** offset is the corresponding slice.

    `copyIntoRegion_self` (AccountBalanceHelperSpec.lean:118) is the `srcOff = 0`
    case; `fixed32Copied` copies from `o.toNat`, so it needs this form.  The
    `srcOff + n ≤ src.length` hypothesis is load-bearing: `copyIntoRegion` pads
    out-of-range reads with `0` via `getD` while `take` simply returns a shorter
    list, so without it the two sides differ in length. -/
theorem copyIntoRegion_eq_slice (dst src : List (BitVec 8)) (srcOff n : Nat)
    (hdst : dst.length = n) (hsrc : srcOff + n ≤ src.length) :
    copyIntoRegion dst src 0 srcOff n = (src.drop srcOff).take n := by
  have hlen : (copyIntoRegion dst src 0 srcOff n).length
      = ((src.drop srcOff).take n).length := by
    rw [copyIntoRegion_length, hdst, List.length_take, List.length_drop]
    omega
  refine List.ext_getElem hlen ?_
  intro j h1 h2
  rw [copyIntoRegion_length, hdst] at h1
  rw [copyIntoRegion_getElem dst src 0 srcOff n j (by omega)]
  rw [if_pos ⟨Nat.zero_le _, by omega⟩, Nat.sub_zero]
  rw [List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-! ## The big-endian accumulator

`beAccum` shifts the ACCUMULATOR and ors the new byte in at the bottom.  That is
the mirror image of `bgv_u32le`'s little-endian `toNat_or_shift`
(BgvU32leSpec.lean:66), which shifts the BYTE — so that lemma does not apply
here and this sibling is needed instead.  Same proof shape: establish
disjointness bitwise, then `BitVec.add_eq_or_of_and_eq_zero`. -/

/-- Shifting the accumulator left by a byte and or-ing a byte in at the bottom
    is multiply-and-add.  `acc.toNat < 2 ^ 56` is what keeps the shift from
    dropping high bits. -/
theorem toNat_shift_or (acc : Word) (z : BitVec 8) (hacc : acc.toNat < 2 ^ 56) :
    ((acc <<< 8) ||| z.zeroExtend 64).toNat = acc.toNat * 256 + z.toNat := by
  have hdisj : (acc <<< 8) &&& z.zeroExtend 64 = 0#64 := by
    ext i
    have hi : i < 64 := by assumption
    simp only [BitVec.getElem_and, BitVec.getElem_zero, Bool.and_eq_false_iff]
    by_cases hlt : i < 8
    · left
      simp [BitVec.getElem_shiftLeft, hlt]
    · right
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_setWidth]
      have hz : z.toNat < 2 ^ 8 := z.isLt
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hz (by norm_num))]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hz
        (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, BitVec.toNat_add_of_and_eq_zero hdisj]
  have hz : z.toNat < 2 ^ 8 := z.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hz (by norm_num)),
    Nat.mod_eq_of_lt (show acc.toNat * 2 ^ 8 < 2 ^ 64 by
      calc acc.toNat * 2 ^ 8 < 2 ^ 56 * 2 ^ 8 :=
            Nat.mul_lt_mul_of_lt_of_le hacc (Nat.le_refl _) (Nat.two_pow_pos 8)
        _ = 2 ^ 64 := by norm_num)]
  norm_num

/-- **The nonce accumulator is a big-endian read.**  `beAccum` builds its value
    one byte at a time, most-significant first; that is exactly `fromBytesBE` of
    the slice it walks.

    `n ≤ 8` is what keeps every intermediate accumulator under `2 ^ 56`, so the
    shift in `toNat_shift_or` never drops a high bit. -/
theorem beAccum_eq_fromBytesBE (bytes : List (BitVec 8)) (off : Nat) :
    ∀ n, n ≤ 8 → off + n ≤ bytes.length →
      beAccum bytes off n
        = BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop off).take n)) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ k ih =>
      intro hk hlen
      have hprev := ih (by omega) (by omega)
      have hidx : off + k < bytes.length := by omega
      -- the slice grows by one byte at the top end
      have hsnoc : (bytes.drop off).take (k + 1)
          = (bytes.drop off).take k ++ [bytes.getD (off + k) 0] := by
        rw [List.take_add_one]
        congr 1
        rw [List.getElem?_drop, List.getElem?_eq_getElem hidx,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        rfl
      -- the running accumulator stays inside 56 bits
      have htakeLen : ((bytes.drop off).take k).length = k := by
        rw [List.length_take, List.length_drop]; omega
      have hbound : Nat.fromBytesBE ((bytes.drop off).take k) < 2 ^ 56 := by
        have h1 := Nat.fromBytesBE_lt ((bytes.drop off).take k)
        rw [htakeLen] at h1
        have hk7 : k ≤ 7 := by omega
        have h2 : (256 : Nat) ^ k ≤ 256 ^ 7 :=
          Nat.pow_le_pow_right (by norm_num) hk7
        have h3 : (256 : Nat) ^ 7 = 2 ^ 56 := by norm_num
        omega
      have hacc : (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop off).take k))).toNat
          = Nat.fromBytesBE ((bytes.drop off).take k) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hbound (by norm_num))]
      show (beAccum bytes off k) <<< 8 ||| _ = _
      rw [hprev]
      apply BitVec.eq_of_toNat_eq
      rw [toNat_shift_or _ _ (by rw [hacc]; exact hbound), hacc, hsnoc,
        Nat.fromBytesBE_snoc, BitVec.toNat_ofNat]
      have hlt : Nat.fromBytesBE ((bytes.drop off).take k) * 256
          + (bytes.getD (off + k) 0).toNat < 2 ^ 64 := by
        have hb : (bytes.getD (off + k) 0).toNat < 256 := (bytes.getD (off + k) 0).isLt
        omega
      rw [Nat.mod_eq_of_lt hlt]

/-! ## Content forms

Each output cell, expressed against the *content* of the field the walk
selected.  Stated with the content equation as a hypothesis — the composition
supplies it from `success_content_of_decodeFully_list`, exactly as
`result_value_of_success` did for #11351 — so these are usable before the
offset plumbing exists. -/

/-- A fixed 32-byte output cell holds the selected field. -/
theorem fixed32Copied_of_content (bytes oldOut : List (BitVec 8)) (o : Word)
    (fld : List (BitVec 8)) (hold : oldOut.length = 32)
    (hbound : o.toNat + 32 ≤ bytes.length)
    (hcontent : (bytes.drop o.toNat).take 32 = fld) :
    fixed32Copied bytes oldOut o = fld := by
  unfold fixed32Copied
  rw [copyIntoRegion_eq_slice oldOut bytes o.toNat 32 hold hbound, hcontent]

/-- The nonce cell holds the big-endian value of the selected field. -/
theorem beAccum_of_content (bytes : List (BitVec 8)) (o : Word) (n : Nat)
    (fld : List (BitVec 8)) (hn : n ≤ 8) (hbound : o.toNat + n ≤ bytes.length)
    (hcontent : (bytes.drop o.toNat).take n = fld) :
    beAccum bytes o.toNat n = BitVec.ofNat 64 (Nat.fromBytesBE fld) := by
  rw [beAccum_eq_fromBytesBE bytes o.toNat n hn hbound, hcontent]

/-- The balance cell holds the selected field **right-aligned** in 32 zero
    bytes — which is exactly `beBytes32`'s left-padding, once the field is
    identified with the minimal big-endian encoding. -/
theorem balanceCopied_of_content (bytes : List (BitVec 8)) (o : Word) (n : Nat)
    (fld : List (BitVec 8)) (hn : n ≤ 32) (hbound : o.toNat + n ≤ bytes.length)
    (hcontent : (bytes.drop o.toNat).take n = fld) :
    balanceCopied bytes o n = List.replicate (32 - n) 0 ++ fld := by
  subst hcontent
  have hfld : ((bytes.drop o.toNat).take n).length = n := by
    rw [List.length_take, List.length_drop]; omega
  unfold balanceCopied
  have hlen : (copyIntoRegion (List.replicate 32 (0 : BitVec 8)) bytes (32 - n) o.toNat n).length
      = (List.replicate (32 - n) (0 : BitVec 8) ++ (bytes.drop o.toNat).take n).length := by
    rw [copyIntoRegion_length, List.length_replicate, List.length_append,
      List.length_replicate, hfld]
    omega
  refine List.ext_getElem hlen ?_
  intro j h1 h2
  rw [copyIntoRegion_length, List.length_replicate] at h1
  rw [copyIntoRegion_getElem _ bytes (32 - n) o.toNat n j (by simp; omega)]
  by_cases hj : 32 - n ≤ j
  · rw [if_pos ⟨hj, by omega⟩,
      List.getElem_append_right (by rw [List.length_replicate]; omega)]
    simp only [List.length_replicate]
    rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [if_neg (by omega),
      List.getElem_append_left (by rw [List.length_replicate]; omega)]
    rw [List.getElem_replicate, List.getElem_replicate]

end EvmAsm.Codegen.AccountDecodeBridge
