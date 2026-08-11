/-
  EvmAsm.Codegen.Programs.RlpEncodeListPrefixCanonical

  **The length-of-length canonicality side condition of `rlp_encode_list_prefix`, at
  every width** (GH #10780 item 1).

  ## What was already there, and why it was not enough

  `long2_first_length_byte_ne_zero` (`RlpEncodeListPrefixLong2Spec.lean:119`) proves the
  first length byte is nonzero for `256 ≤ len < 65536` — the `lenlen = 2` arm. It is
  stated over the literal shift `len >>> 8`, so it says nothing at any other width, and
  its proof re-derives the bound from that arm's own hypotheses.

  #10780 asks for the property itself, not one instance of it:

  > A length-of-length (`0xb7`/`0xf7` long form) carries no leading zeros. A long-form
  > header with one still *parses* and hashes differently — wrong in a way no decoder
  > complains about.

  This module proves it for **`lenlen ∈ 1..8`**, in the form the routine's own loop
  produces, so the `lenlen ≥ 3` arm inherits it instead of re-deriving it per width.

  ## ⭐ Reuse, not new mathematics

  The width is `u64ByteLen` (`RlpListEncodedSizeSAsm.lean:70`) — the *same* function
  `rlp_encode_bytes` uses for its length-of-length ladder, and the same one the prefix
  routine's `idx8`–`idx29` ladder computes into `x28`. Everything here is a consequence
  of two bounds that `u64ByteLen`'s own definition already contains; no new model is
  introduced, and deliberately so — see the scoping note at the bottom.

  ## Shape

  Stated over `len >>> (8 * (lenlen - 1))` rather than over a list index, because that is
  what the machine loop's **first** iteration computes: `idx34` sets `x29 := lenlen - 1`,
  `idx36` forms `x31 := x29 <<< 3 = 8 * (lenlen - 1)`, and `idx37` does
  `x5 := x10 >>> x31`. So the statement is about the byte the routine actually stores
  first, not about a re-derivation of what it ought to store.
-/
import EvmAsm.Codegen.Programs.RlpListEncodedSizeSAsm

namespace EvmAsm.Codegen

namespace RlpEncodeListPrefixCanonical

open EvmAsm.Rv64
open EvmAsm.Codegen.RlpListEncodedSizeSAsm (u64ByteLen u64ByteLen_le)

/-! ## The two bounds `u64ByteLen` already contains

    `u64ByteLen` is an `if`-ladder over `2 ^ (8 * k)` thresholds, so both bounds fall out
    of `split_ifs`. They are extracted as named lemmas because the canonicality argument
    needs them at a *symbolic* width, where the ladder is no longer a literal chain. -/

/-- **Upper bound.** `len` fits in `u64ByteLen len` bytes. -/
theorem lt_pow_u64ByteLen (v : Word) : v.toNat < 2 ^ (8 * u64ByteLen v) := by
  have h8 : v.toNat < 2 ^ 64 := v.isLt
  unfold u64ByteLen
  split_ifs <;> norm_num <;> omega

/-- **Lower bound — the sharp one.** At a nonzero width, `len` does *not* fit in one
    fewer byte. This is exactly minimality of the length-of-length, and it is what makes
    the leading byte nonzero. -/
theorem pow_le_u64ByteLen (v : Word) (h : 1 ≤ u64ByteLen v) :
    2 ^ (8 * (u64ByteLen v - 1)) ≤ v.toNat := by
  unfold u64ByteLen at h ⊢
  split_ifs at h ⊢
  all_goals try norm_num at h ⊢
  all_goals omega

/-- The width is zero only for zero — so `1 ≤ u64ByteLen len` is not an extra
    hypothesis on any long-form path, where `56 ≤ len`. -/
theorem one_le_u64ByteLen {v : Word} (h : 0 < v.toNat) : 1 ≤ u64ByteLen v := by
  unfold u64ByteLen
  split_ifs <;> omega

/-! ## ⭐ The canonicality theorem -/

/-- The first stored length byte, as a `Nat`: `len` shifted down by all the bytes below
    it. Named so the statement below reads as a claim about a byte rather than about a
    shift expression. -/
private theorem shift_eq_div (v : Word) (k : Nat) :
    (v >>> k).toNat = v.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight]
  norm_num [Nat.shiftRight_eq_div_pow]

/-- ⭐ **The length-of-length carries no leading zero, at every width.**

    The byte the loop stores first is `len / 2 ^ (8 * (lenlen - 1))`. The sharp lower
    bound puts it at `≥ 1`; the upper bound puts it `< 256`, so the truncation to 8 bits
    cannot wrap it back to zero.

    This is #10780 item 1 in general. `long2_first_length_byte_ne_zero` is the
    `lenlen = 2` instance, and is recovered below. -/
theorem first_length_byte_ne_zero {len : Word} (h : 0 < len.toNat) :
    BitVec.ofNat 8 (len >>> (8 * (u64ByteLen len - 1))).toNat ≠ 0 := by
  have hk : 1 ≤ u64ByteLen len := one_le_u64ByteLen h
  have hlo : 2 ^ (8 * (u64ByteLen len - 1)) ≤ len.toNat := pow_le_u64ByteLen len hk
  have hhi : len.toNat < 2 ^ (8 * u64ByteLen len) := lt_pow_u64ByteLen len
  -- the leading byte, as a plain division
  have hdiv : (len >>> (8 * (u64ByteLen len - 1))).toNat
      = len.toNat / 2 ^ (8 * (u64ByteLen len - 1)) := shift_eq_div len _
  -- it is at least 1 …
  have hge : 1 ≤ len.toNat / 2 ^ (8 * (u64ByteLen len - 1)) :=
    (Nat.one_le_div_iff (Nat.two_pow_pos _)).mpr hlo
  -- … and below 256, since one more byte of width is a factor of 256
  have hsplit : 8 * u64ByteLen len = 8 * (u64ByteLen len - 1) + 8 := by omega
  have hlt : len.toNat / 2 ^ (8 * (u64ByteLen len - 1)) < 256 := by
    rw [hsplit, Nat.pow_add] at hhi
    exact Nat.div_lt_of_lt_mul (by simpa using hhi)
  intro hzero
  have h0 : len.toNat / 2 ^ (8 * (u64ByteLen len - 1)) = 0 := by
    have hc := congrArg BitVec.toNat hzero
    rwa [BitVec.toNat_ofNat, hdiv, Nat.mod_eq_of_lt hlt,
      show BitVec.toNat (0 : BitVec 8) = 0 from rfl] at hc
  omega

/-- The `lenlen = 2` arm is recovered, so this genuinely generalises
    `long2_first_length_byte_ne_zero` rather than sitting beside it. -/
theorem first_length_byte_ne_zero_long2 {len : Word}
    (h_lo : 256 ≤ len.toNat) (h_hi : len.toNat < 65536) :
    BitVec.ofNat 8 (len >>> (8 : Nat)).toNat ≠ 0 := by
  have hwidth : u64ByteLen len = 2 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have := first_length_byte_ne_zero (len := len) (by omega)
  rwa [hwidth] at this

/-- Non-vacuity at the widths the long2 arm cannot speak about: `lenlen = 3` and
    `lenlen = 8`, the first uncovered arm and the widest one. -/
private theorem width_three : u64ByteLen (0x010000 : Word) = 3 := by decide

private theorem width_eight : u64ByteLen (0xFF00000000000000 : Word) = 8 := by decide

/-! ## ⛔ Scoping note for the `lenlen ≥ 3` arm — the model already exists

    `RlpEncodeListPrefixLong2Spec.lean:47-52` proposes, for the general arm, an invariant
    reading *"`out[1..k]` holds the top `k` bytes of `len` and `x29 = lenlen - 1 - k`"*.
    ⚠️ That is `writeShift` (`RlpEncodeBytesSAsm.lean:357`) partially applied, and the
    whole chain it needs is **already proven** — for `rlp_encode_bytes`, which has the
    identical length-of-length loop:

    | existing declaration | what it gives the general arm |
    |---|---|
    | `writeShift dst di v m` (`RlpEncodeBytesSAsm.lean:357`) | the loop's exact effect: `m` bytes from index `di`, most significant first |
    | `writeShift_zero` / `writeShift_succ` (`:364`, `:367`) | the equation lemmas a machine-loop induction rewrites with |
    | `beShift` + `beShift_length` + `beShift_getElem?` (`:269`, `:273`, `:~292`) | per-index byte formula, in the `len >>> 8i` form the loop produces |
    | `beShift_eq_toBytesBE` (`:282`) | at its own length `beShift` **is** the minimal big-endian encoding |
    | `u64ByteLen_eq_toBytesBE_length` (`:160`) | the ladder's `x28` is that length |

    ⇒ The general arm's postcondition is `writeShift outBytes 1 len.toNat (u64ByteLen len)`,
    and the model side of *"holds the top `k` bytes"* is `beShift`. What is genuinely
    missing is the **machine** half only: a loop invariant over `rlpEncodeListPrefix_prog`
    idx35–41 (trip count `u64ByteLen len ∈ 1..8`, `x29` counting down while `x30` counts
    up), plus the ladder dispatch through idx8–idx29.

    ⚠️ None of `beShift` / `writeShift` / `u64ByteLen_eq_toBytesBE_length` is currently
    reachable from either prefix spec module — they are used only by the
    `rlp_encode_bytes` family. Re-deriving them per width is the ~200-lines-per-byte cost
    that note warns about, and it is avoidable. This module takes the same route for the
    canonicality half: `u64ByteLen`, reused, rather than a per-arm bound. -/

end RlpEncodeListPrefixCanonical

end EvmAsm.Codegen
