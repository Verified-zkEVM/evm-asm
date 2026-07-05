/-
  EvmAsm.Evm64.Calldata.LoadWindowWord

  Pure bridge between the CALLDATALOAD RV64 byte-window output word
  (`calldataLoadWindowOutputWordFromArgs`, four big-endian packed limbs) and
  the executable calldata semantics (`loadedWordFromArgs` /
  `callDataLoadWord`, a big-endian 32-byte fold).  Also provides the pure
  dispatch lemmas for the bounds-check branch: an offset with any nonzero
  upper limb is at least `2^64` (hence past any calldata buffer), and an
  offset with zero upper limbs is exactly its low limb.
-/

import EvmAsm.Evm64.Calldata.LoadStackCode

namespace EvmAsm.Evm64
namespace Calldata

/-! ### Packed-limb / loaded-word `toNat` forms -/

/-- One big-endian byte-append step at the `toNat` level: appending an
    8-bit byte multiplies the prefix by 256 and adds the byte. -/
private theorem toNat_append_byte {m : Nat} (x : BitVec m) (y : BitVec 8) :
    (x ++ y).toNat = x.toNat * 256 + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt x.toNat,
    Nat.shiftLeft_eq]

/-- `mloadPackedLimb` as a big-endian byte fold at the `toNat` level. -/
theorem mloadPackedLimb_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (mloadPackedLimb b0 b1 b2 b3 b4 b5 b6 b7).toNat =
      ((((((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat)
        * 256 + b4.toNat) * 256 + b5.toNat) * 256 + b6.toNat) * 256
        + b7.toNat := by
  unfold mloadPackedLimb
  rw [toNat_append_byte, toNat_append_byte, toNat_append_byte,
    toNat_append_byte, toNat_append_byte, toNat_append_byte, toNat_append_byte]

/-- `mloadLoadedWord` as a 4-limb value at the `toNat` level. -/
theorem mloadLoadedWord_toNat (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).toNat =
      l0.toNat + l1.toNat * 2 ^ 64 + l2.toNat * 2 ^ 128
        + l3.toNat * 2 ^ 192 := by
  rw [EvmWord.toNat_getLimb_decompose (mloadLoadedWord l0 l1 l2 l3),
    EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3,
    getLimbN_mloadLoadedWord_0, getLimbN_mloadLoadedWord_1,
    getLimbN_mloadLoadedWord_2, getLimbN_mloadLoadedWord_3]

/-! ### The window/word bridge -/

/--
The RV64 CALLDATALOAD in-bounds window output word IS the executable
calldata load semantics: packing the 32 window bytes big-endian into four
little-endian 64-bit limbs equals the big-endian byte fold
`callDataLoadWord`.

Distinctive token:
Calldata.LoadWindowWord.calldataLoadWindowOutputWordFromArgs_eq_loadedWordFromArgs.
-/
theorem calldataLoadWindowOutputWordFromArgs_eq_loadedWordFromArgs
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    calldataLoadWindowOutputWordFromArgs data args =
      CallDataLoadArgs.loadedWordFromArgs data args := by
  apply BitVec.eq_of_toNat_eq
  rw [CallDataLoadArgs.loadedWordFromArgs_toNat]
  unfold calldataLoadWindowOutputWordFromArgs mloadLoadedWordFromBytes
  rw [mloadLoadedWord_toNat, mloadPackedLimb_toNat, mloadPackedLimb_toNat,
    mloadPackedLimb_toNat, mloadPackedLimb_toNat]
  simp only [CallDataLoadArgs.windowByteFromArgs_eq]
  have h_range : List.range 32 =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
       20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by rfl
  unfold callDataLoadNat
  rw [h_range]
  simp only [List.foldl_cons, List.foldl_nil, appendByte]
  omega

/-! ### Dispatch pure lemmas (upper-limb bounds test) -/

/-- With all three upper limbs zero, an `EvmWord`'s value is exactly its
    low limb's value.  This is the pure fact behind the CALLDATALOAD
    dispatch reading only the low offset dword on the in-bounds arm. -/
theorem toNat_eq_getLimbN0_toNat_of_upper_or_zero
    {w : EvmWord}
    (h_upper : w.getLimbN 1 ||| w.getLimbN 2 ||| w.getLimbN 3 = 0) :
    w.toNat = (w.getLimbN 0).toNat := by
  obtain ⟨h_or12, h3⟩ := BitVec.or_eq_zero_iff.mp h_upper
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h_or12
  have h_val := EvmWord.toNat_getLimb_decompose w
  rw [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3,
    h1, h2, h3] at h_val
  simpa using h_val

/-- With any upper limb nonzero, an `EvmWord`'s value is at least `2^64` —
    in particular past the end of any calldata buffer whose length fits in
    a 64-bit register.  This is the pure fact behind the dispatch's
    OR-reduce of the three upper offset limbs. -/
theorem two_pow_64_le_toNat_of_upper_or_ne_zero
    {w : EvmWord}
    (h_upper : w.getLimbN 1 ||| w.getLimbN 2 ||| w.getLimbN 3 ≠ 0) :
    2 ^ 64 ≤ w.toNat := by
  have h_val := EvmWord.toNat_getLimb_decompose w
  rw [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h_val
  by_cases h1 : w.getLimbN 1 = 0
  · by_cases h2 : w.getLimbN 2 = 0
    · have h3 : w.getLimbN 3 ≠ 0 :=
        fun h3 => h_upper (by rw [h1, h2, h3]; simp)
      have h_pos := BitVec.toNat_pos_of_ne_zero h3
      omega
    · have h_pos := BitVec.toNat_pos_of_ne_zero h2
      omega
  · have h_pos := BitVec.toNat_pos_of_ne_zero h1
    omega

/-! ### Out-of-bounds corollaries (the zero-fill arm's semantics) -/

/-- Upper offset limbs nonzero → the CALLDATALOAD result is zero (the
    offset is at least `2^64`, past any register-sized calldata length). -/
theorem callDataLoadWord_zero_of_upper_or_ne_zero
    {data : List (BitVec 8)} {offsetWord : EvmWord} {len : Word}
    (h_len : data.length = len.toNat)
    (h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
      offsetWord.getLimbN 3 ≠ 0) :
    callDataLoadWord data offsetWord.toNat = 0 := by
  apply callDataLoadWord_of_ge_length
  have h_ge := two_pow_64_le_toNat_of_upper_or_ne_zero h_upper
  have h_lt := len.isLt
  omega

/-- Upper offset limbs zero but the low limb at or past the calldata
    length → the CALLDATALOAD result is zero. -/
theorem callDataLoadWord_zero_of_low_ge_len
    {data : List (BitVec 8)} {offsetWord : EvmWord} {len : Word}
    (h_len : data.length = len.toNat)
    (h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
      offsetWord.getLimbN 3 = 0)
    (h_ge : ¬ offsetWord.getLimbN 0 < len) :
    callDataLoadWord data offsetWord.toNat = 0 := by
  apply callDataLoadWord_of_ge_length
  rw [h_len, toNat_eq_getLimbN0_toNat_of_upper_or_zero h_upper]
  rw [BitVec.lt_def] at h_ge
  omega

/-- Upper offset limbs zero and the low limb strictly below the calldata
    length → the offset is in bounds as a `Nat` index.  This feeds the
    in-bounds window arm. -/
theorem offset_toNat_lt_length_of_inbounds
    {data : List (BitVec 8)} {offsetWord : EvmWord} {len : Word}
    (h_len : data.length = len.toNat)
    (h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
      offsetWord.getLimbN 3 = 0)
    (h_lt : offsetWord.getLimbN 0 < len) :
    offsetWord.toNat < data.length := by
  rw [h_len, toNat_eq_getLimbN0_toNat_of_upper_or_zero h_upper]
  exact BitVec.lt_def.mp h_lt

end Calldata
end EvmAsm.Evm64
