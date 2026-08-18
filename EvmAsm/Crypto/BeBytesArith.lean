/-
  EvmAsm.Crypto.BeBytesArith

  Structure lemmas for `beBytesToNat` — the big-endian bytes ↔ `Nat` abstraction.

  WHY A SHARED MODULE: `beBytesToNat` is defined in `Crypto/PowLadder.lean`, but
  its two basic structure lemmas (`_cons`, `_append`) were proved `private` there
  and then **re-proved privately in two more files** — `Bn254FieldConvSAsm.lean`
  and `P256BeToLeSAsm.lean` each carry their own copy of `beBytesToNat_append`
  and of the generalized-accumulator lemma behind it. Any file that wants to give
  a byte-level post a numeric meaning needs these, so they get one public home
  here rather than a fourth copy.

  ⚠️ The three existing private copies are deliberately left in place: making
  them public in `PowLadder` would rebuild every crypto and codegen dependent,
  and rewriting the two program modules is unrelated to the proof obligation this
  module was added for (#12225). They should be retired in favour of this module
  the next time either file is touched.
-/
import EvmAsm.Crypto.PowLadder

namespace EvmAsm.Crypto

/-- Generalized-accumulator unfolding of the `beBytesToNat` foldl: the seed
    contributes one base-256 digit per remaining byte. -/
theorem beBytesToNat_foldl (bs : List (BitVec 8)) (acc : Nat) :
    List.foldl (fun a (b : BitVec 8) => a * 256 + b.toNat) acc bs
      = acc * 256 ^ bs.length + beBytesToNat bs := by
  induction bs generalizing acc with
  | nil => simp [beBytesToNat]
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (acc * 256 + b.toNat)]
    have hbe : beBytesToNat (b :: bs)
        = List.foldl (fun a (c : BitVec 8) => a * 256 + c.toNat) (b.toNat) bs := by
      simp [beBytesToNat]
    rw [hbe, ih b.toNat]
    have h : acc * 256 * 256 ^ bs.length = acc * 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ bs.length) 256, ← Nat.mul_assoc]
    rw [Nat.add_mul, h]
    omega

/-- Concatenation shifts the prefix by one base-256 digit per suffix byte. -/
theorem beBytesToNat_append (a b : List (BitVec 8)) :
    beBytesToNat (a ++ b) = beBytesToNat a * 256 ^ b.length + beBytesToNat b := by
  unfold beBytesToNat
  rw [List.foldl_append, beBytesToNat_foldl b]
  rfl

/-- The leading byte is the most significant base-256 digit. -/
theorem beBytesToNat_cons (b : BitVec 8) (bs : List (BitVec 8)) :
    beBytesToNat (b :: bs) = b.toNat * 256 ^ bs.length + beBytesToNat bs := by
  have h : (b :: bs) = [b] ++ bs := rfl
  rw [h, beBytesToNat_append]
  simp [beBytesToNat]

/-- **Peel one digit off a suffix.** The workhorse for index-descending loops:
    a routine that has processed the last `k` bytes of a 32-byte buffer has
    computed `beBytesToNat (l.drop (32 - k))`, and one more step peels the byte
    at the new index off the front of that suffix. -/
theorem beBytesToNat_drop_succ (l : List (BitVec 8)) (n : Nat) (hn : n < l.length) :
    beBytesToNat (l.drop n)
      = (l.getD n 0).toNat * 256 ^ (l.length - n - 1) + beBytesToNat (l.drop (n + 1)) := by
  rw [List.drop_eq_getElem_cons hn, beBytesToNat_cons, List.length_drop,
    List.getElem_eq_getD 0, Nat.sub_sub]

end EvmAsm.Crypto
