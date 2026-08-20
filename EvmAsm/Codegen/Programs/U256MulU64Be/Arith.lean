/-
  EvmAsm.Codegen.Programs.U256MulU64Be.Arith

  **Numeric meaning of `u256_mul_u64_be`'s accumulator** (#12225).

  `mulWhole_spec` and `mulWhole_inPlace_spec` state their posts OPERATIONALLY:
  the output window ends up holding `copyState (mulState aBytes b 32) outBytes 32`.
  That pins the exact bytes but says nothing numeric — a reader who wants "this
  routine multiplies" has to take `mulState`'s definition on faith. This module
  closes that: `leBytesToNat_mulState` ties the fold to `Nat` multiplication, so
  the family's last operationally-only member gets an arithmetic contract like the
  other five (`beBytesToNat_u256AddBeBytes`, `beBytesToNat_u256SubBeBytes`,
  `beBytesToNat_u256FromU64Bytes`, `u256IsZeroFlat_spec_domain`, and `u256_lt_be`
  whose post was numeric already).

  ## How the pieces compose, and what was already here

  ⚠️ Almost all of the hard work was ALREADY DONE elsewhere in this directory, and
  an earlier revision of this file re-proved two lemmas of it. Recording the map
  so the next reader does not repeat that:

  * `leBytesToNat_rippleState` (`OuterLoop.lean`) — the INNER ripple's value
    identity, the nested induction. This is the part that looks hardest and is
    already finished.
  * `mulState_getD_ge` (`WholeOuter.lean`) — every accumulator slot at index
    `i + 8` or above is still zero after `i` folded bytes. This is the invariant
    that makes `mulOuterStep`'s single-byte truncating `hi` write lossless, and it
    is why that write is not the overflow bug it looks like: `m / 2^64` alone
    reaches 254, so a nonzero slot would silently drop a carry with nothing to
    propagate it.
  * `getD_rippleState_of_ge` (`OuterLoop.lean`) — the ripple touches only
    `i … i + k − 1`.
  * `leBytesToNat_set`, `leBytesToNat_reverse`, `mulCarry_le_one` — `Basic.lean`
    and `OuterLoop.lean`.

  So the only genuinely missing step was the OUTER induction, below.

  ## The invariant, and why it is phrased with `drop`

  After folding `i` big-endian input bytes the accumulator holds the product of
  the LOW `i` bytes of the source with `b`:

      leBytesToNat (mulState a b i) = beBytesToNat (a.drop (32 - i)) * b.toNat

  `a.drop (32 - i)` is the last `i` bytes, which is exactly the part folded so
  far, and `beBytesToNat_drop_succ` peels one digit off the front of that suffix —
  the same drop-indexed shape that closed the adder and subtractor in #12606. At
  `i = 32` the drop is the whole list, giving the theorem.
-/
import EvmAsm.Codegen.Programs.U256MulU64Be.WholeOuter
import EvmAsm.Codegen.Programs.U256MulU64Be.WholeCopy
import EvmAsm.Crypto.BeBytesArith

-- ⚠️ `autoImplicit` would silently bind a misspelled or unimported name as a
-- fresh implicit variable, turning a missing import into a theorem about an
-- arbitrary object rather than a build error. It did exactly that to `copyState`
-- while this file was being written.
set_option autoImplicit false

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm.Rv64

/-- `256 ^ 8 = 2 ^ 64` — the bridge between the accumulator's byte stride and the
    u64 operand's width. Used to see that `mulOuterStep`'s `hi` write lands
    exactly one u64 above the ripple window. -/
private theorem pow256_eight : (256 : Nat) ^ 8 = 2 ^ 64 := by
  rw [pow256_eq]

/-- The high half of one outer step's product fits in a byte with room for the
    ripple carry. `mulhu_le_254` states this for two `Word`s; the source byte here
    is a `BitVec 8`, so this is the same bound at the narrower type. -/
private theorem byte_mul_high_le (byte : BitVec 8) (b : Word) :
    byte.toNat * b.toNat / 2 ^ 64 ≤ 254 := by
  have hbyte : byte.toNat ≤ 255 := by have := byte.isLt; omega
  have hb : b.toNat ≤ 2 ^ 64 - 1 := by have := b.isLt; omega
  have : byte.toNat * b.toNat ≤ 255 * (2 ^ 64 - 1) := Nat.mul_le_mul hbyte hb
  omega

/-- **One outer step, numerically**: folding source byte `a[31 - i]` adds
    `byte · b · 256^i` to the accumulator's value.

    This is where the truncating `hi` write is discharged. `mulState_getD_ge` puts
    a zero at slot `i + 8`, so `leBytesToNat_set`'s subtraction term vanishes and
    `hi = m / 2^64 + carry ≤ 254 + 1 < 256` survives `BitVec.ofNat 8` intact. -/
theorem leBytesToNat_mulOuterStep (a : List (BitVec 8)) (b : Word) (i : Nat)
    (hi32 : i < 32) :
    leBytesToNat (mulOuterStep a b (mulState a b i) i)
      = leBytesToNat (mulState a b i)
        + (a.getD (31 - i) 0).toNat * b.toNat * 256 ^ i := by
  have hacc : (mulState a b i).length = 40 := mulState_len a b i
  unfold mulOuterStep
  dsimp only
  split
  · -- the zero-byte skip: nothing is added, and the byte contributes nothing
    rename_i hz
    rw [hz]
    simp
  · set acc := mulState a b i with haccdef
    set byte := a.getD (31 - i) 0 with hbyte
    set m := byte.toNat * b.toNat with hm
    set rr := rippleState acc (m % 2 ^ 64) i 8 with hrr
    set cc := mulCarry acc (m % 2 ^ 64) i 8 with hcc
    -- slot i+8 is untouched by the ripple and zero in the accumulator
    have hrlen : rr.length = 40 := by rw [hrr, length_rippleState, hacc]
    have hidx : i + 8 < rr.length := by rw [hrlen]; omega
    have hrz : rr.getD (i + 8) 0 = 0 := by
      rw [hrr, getD_rippleState_of_ge acc (m % 2 ^ 64) i 8 (i + 8) (by omega)]
      exact mulState_getD_ge a b i (i + 8) (by omega)
    have hrz' : (rr[i + 8]'hidx).toNat = 0 := by
      have : rr[i + 8]'hidx = rr.getD (i + 8) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        rfl
      rw [this, hrz]
      rfl
    -- the written byte does not truncate
    have hcle : cc ≤ 1 := by rw [hcc]; exact mulCarry_le_one _ _ _ _
    have hhle : m / 2 ^ 64 ≤ 254 := by rw [hm]; exact byte_mul_high_le byte b
    have hsum : m / 2 ^ 64 + cc + (rr.getD (i + 8) 0).toNat = m / 2 ^ 64 + cc := by
      rw [hrz]; rfl
    have hnotrunc :
        (BitVec.ofNat 8 (m / 2 ^ 64 + cc + (rr.getD (i + 8) 0).toNat)).toNat
          = m / 2 ^ 64 + cc := by
      rw [hsum, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    -- the ripple's value identity, at the full eight rounds
    have hrip := leBytesToNat_rippleState acc (m % 2 ^ 64) i 8 hacc hi32 (le_refl 8)
    have hlohi : (m % 2 ^ 64) / 256 ^ 8 = 0 := by
      rw [pow256_eight]
      exact Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity))
    rw [hlohi, Nat.zero_add] at hrip
    -- assemble
    rw [leBytesToNat_set rr (i + 8) _ hidx, hrz', Nat.mul_zero, Nat.sub_zero,
      hnotrunc]
    -- goal: leBytesToNat rr + 256^(i+8) * (m/2^64 + cc)
    --         = leBytesToNat acc + m * 256^i
    have hpow : (256 : Nat) ^ (i + 8) = 256 ^ i * 2 ^ 64 := by
      rw [pow_add, pow256_eight]
    have hdm : 2 ^ 64 * (m / 2 ^ 64) + m % 2 ^ 64 = m := Nat.div_add_mod m (2 ^ 64)
    -- add the carry term to both sides so `hrip` applies, then cancel it
    have hkey : leBytesToNat rr + 256 ^ (i + 8) * (m / 2 ^ 64 + cc)
        + cc * 256 ^ (i + 8)
      = leBytesToNat acc + m * 256 ^ i + cc * 256 ^ (i + 8) := by
      have hl : leBytesToNat rr + 256 ^ (i + 8) * (m / 2 ^ 64 + cc)
            + cc * 256 ^ (i + 8)
          = (leBytesToNat rr + cc * 256 ^ (i + 8))
            + 256 ^ (i + 8) * (m / 2 ^ 64) + cc * 256 ^ (i + 8) := by ring
      rw [hl, hrip]
      conv_rhs => rw [← hdm]
      rw [hpow]
      ring
    omega

/-- ⭐ **The outer invariant**: after folding `i` big-endian source bytes, the
    accumulator's value is the product of the source's low `i` bytes with `b`. -/
theorem leBytesToNat_mulState (a : List (BitVec 8)) (b : Word)
    (hlen : a.length = 32) :
    ∀ i, i ≤ 32 →
      leBytesToNat (mulState a b i)
        = EvmAsm.Crypto.beBytesToNat (a.drop (32 - i)) * b.toNat := by
  intro i
  induction i with
  | zero =>
    intro _
    show leBytesToNat (List.replicate 40 (0 : BitVec 8)) = _
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [EvmAsm.Crypto.beBytesToNat, leBytesToNat_eq_zero_of_all_zero]
  | succ i ih =>
    intro hle
    have hi32 : i < 32 := by omega
    show leBytesToNat (mulOuterStep a b (mulState a b i) i) = _
    rw [leBytesToNat_mulOuterStep a b i hi32, ih (by omega)]
    -- peel the next big-endian digit off the suffix
    have hdrop : 32 - (i + 1) = 31 - i := by omega
    have hnext : 31 - i + 1 = 32 - i := by omega
    have hlt : 31 - i < a.length := by rw [hlen]; omega
    rw [hdrop, EvmAsm.Crypto.beBytesToNat_drop_succ a (31 - i) hlt, hlen, hnext]
    have hexp : 32 - (31 - i) - 1 = i := by omega
    rw [hexp]
    ring

/-- ⭐⭐ **`u256_mul_u64_be` computes the product.** The accumulator that
    `mulWhole_spec` names as `mulState aBytes b 32` has value
    `beBytesToNat aBytes * b.toNat` — full 320-bit precision, before
    `copyState` narrows it to the 32-byte output window.

    Together with `mulWhole_spec` this gives the routine a NUMERIC contract:
    what lands in the accumulator is the mathematical product of the big-endian
    source and the u64 operand, not merely "whatever the model computes". -/
theorem leBytesToNat_mulState_full (a : List (BitVec 8)) (b : Word)
    (hlen : a.length = 32) :
    leBytesToNat (mulState a b 32) = EvmAsm.Crypto.beBytesToNat a * b.toNat := by
  have h := leBytesToNat_mulState a b hlen 32 (le_refl 32)
  simpa using h

/-! ## The output window

    The accumulator is 320 bits; the routine's OUTPUT is the low 32 bytes of it,
    reversed back into big-endian order by `copyState`. So the caller-facing
    claim is the product **modulo 2^256**, and that narrowing is where a caller's
    overflow reasoning has to start. -/

/-- Every slot the copy loop has reached holds the corresponding accumulator
    byte, index-reversed. After `i` rounds those are exactly `32 - i … 31`.

    ⚠️ `i ≤ 32` is load-bearing, not decoration. Nat truncation makes `31 - i`
    collapse to `0` once `i ≥ 32`, so a 33rd round would write `acc[32]` into
    slot 0 and the conclusion would be FALSE there. omega caught this. -/
private theorem copyState_getD_copied (acc outBytes : List (BitVec 8))
    (i : Nat) (hi : i ≤ 32) (hout : outBytes.length = 32) :
    ∀ j, 32 - i ≤ j → j < 32 →
      (copyState acc outBytes i).getD j 0 = acc.getD (31 - j) 0 := by
  induction i with
  | zero => intro j hlo hj; omega
  | succ i ih =>
    intro j hlo hj
    show ((copyState acc outBytes i).set (31 - i) (acc.getD i 0)).getD j 0 = _
    by_cases h : 31 - i = j
    · subst h
      have hl32 : (copyState acc outBytes i).length = 32 := copyState_len _ _ i hout
      have hlen : 31 - i < (copyState acc outBytes i).length := by omega
      have hji : 31 - (31 - i) = i := by omega
      rw [hji, List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]
      rfl
    · rw [getD_set_ne_local h]
      exact ih (by omega) j (by omega) hj

/-- **The copy is a reverse of the accumulator's low 32 bytes.** `copyState`
    writes `out[31 - i] := acc[i]`, so after all 32 rounds the output window is
    the little-endian accumulator prefix read back big-endian.

    Both sides are compared through `getElem?` rather than `getElem`: the
    `getElem` form carries a bound proof, and `get_elem_tactic` tries to `decide`
    that bound, which sends it off evaluating `copyState acc outBytes 32` on
    symbolic arguments until the heartbeat limit. `getElem?` has no proof
    argument and sidesteps that entirely. -/
theorem copyState_eq_reverse_take (acc outBytes : List (BitVec 8))
    (hacc : acc.length = 40) (hout : outBytes.length = 32) :
    copyState acc outBytes 32 = (acc.take 32).reverse := by
  have htlen : (acc.take 32).length = 32 := by
    rw [List.length_take, hacc]
    omega
  have hlenL : (copyState acc outBytes 32).length = 32 := copyState_len _ _ 32 hout
  have hlenR : ((acc.take 32).reverse).length = 32 := by
    rw [List.length_reverse, htlen]
  -- `l[n]? = some (l.getD n 0)` inside a length-32 list, uniformly for both sides
  have hsome : ∀ (l : List (BitVec 8)), l.length = 32 → ∀ n, n < 32 →
      l[n]? = some (l.getD n 0) := by
    intro l hl n hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  apply List.ext_getElem?
  intro n
  by_cases hn : n < 32
  · -- the reversed take, at index n, is the accumulator byte at 31 - n
    have hnt : n < (acc.take 32).length := by omega
    have hrevD : ((acc.take 32).reverse).getD n 0 = acc.getD (31 - n) 0 := by
      have hlhs : ((acc.take 32).reverse).getD n 0
          = ((acc.take 32).reverse)[n]'(by rw [hlenR]; omega) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [hlenR]; omega)]
        rfl
      have hidx : 31 - n < 32 := by omega
      rw [hlhs, reverse_getElem (acc.take 32) n hnt htlen, List.getElem_eq_getD 0,
        List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hidx,
        ← List.getD_eq_getElem?_getD]
    have hcopyD : (copyState acc outBytes 32).getD n 0 = acc.getD (31 - n) 0 :=
      copyState_getD_copied acc outBytes 32 (le_refl 32) hout n (by omega) hn
    rw [hsome _ hlenL n hn, hsome _ hlenR n hn, hcopyD, hrevD]
  · have h1 : (copyState acc outBytes 32)[n]? = none :=
      List.getElem?_eq_none (by omega)
    have h2 : ((acc.take 32).reverse)[n]? = none :=
      List.getElem?_eq_none (by omega)
    rw [h1, h2]

/-- ⭐⭐⭐ **`u256_mul_u64_be`'s output is the product, modulo 2^256.**

    This is the caller-facing numeric contract. `mulWhole_spec`'s post names the
    output window's contents as `copyState (mulState aBytes b 32) outBytes 32`;
    reading that window big-endian gives exactly

        (beBytesToNat aBytes * b.toNat) % 2 ^ 256

    ⚠️ The `% 2 ^ 256` is not slack in the proof — it is the routine's actual
    behaviour. The accumulator carries the full 320-bit product (see
    `leBytesToNat_mulState_full`), and the copy keeps only its low 32 bytes; the
    high 8 are dropped on the floor. A caller that needs to know the product did
    NOT overflow has to establish that separately, and `mulOverflow` is the
    routine's own signal for it. The final `#guard` below exhibits an input where
    the truncation is real, so this is not a distinction without a difference. -/
theorem beBytesToNat_mulOutput (a outBytes : List (BitVec 8)) (b : Word)
    (hlen : a.length = 32) (hout : outBytes.length = 32) :
    EvmAsm.Crypto.beBytesToNat (copyState (mulState a b 32) outBytes 32)
      = (EvmAsm.Crypto.beBytesToNat a * b.toNat) % 2 ^ 256 := by
  have hacc : (mulState a b 32).length = 40 := mulState_len a b 32
  rw [copyState_eq_reverse_take _ _ hacc hout]
  rw [← leBytesToNat_reverse, List.reverse_reverse, leBytesToNat_take,
    leBytesToNat_mulState_full a b hlen]
  rw [pow256_eq]

/-! ### Non-vacuity

    The theorem says the fold computes the product; these pin it at concrete
    points, INCLUDING the maximal input where a dropped carry in
    `mulOuterStep`'s truncating `hi` write would show up. `0xff…ff × 0xff…ff`
    exercises every outer step's `hi` at its largest. -/

private def mulTestA : List (BitVec 8) := List.replicate 30 (0 : BitVec 8) ++ [1, 2]
private def mulTestMax : List (BitVec 8) := List.replicate 32 (0xff : BitVec 8)

#guard mulTestA.length == 32 && mulTestMax.length == 32

-- a = 258 (big-endian 0x…0102).
#guard leBytesToNat (mulState mulTestA 0xffffffffffffffff 32) == 258 * 0xffffffffffffffff

-- The maximal case: every outer step's `hi` is at its largest here.
#guard leBytesToNat (mulState mulTestMax 0xffffffffffffffff 32)
  == (2 ^ 256 - 1) * (2 ^ 64 - 1)

-- b = 0 and b = 1 boundaries.
#guard leBytesToNat (mulState mulTestMax 0 32) == 0
#guard leBytesToNat (mulState mulTestMax 1 32) == 2 ^ 256 - 1

-- The `mulState_getD_ge` invariant that licenses the truncating write, concretely:
-- slot 8 is zero after one folded byte, and slot 0 is not — so it is a real
-- restriction on the index range, not vacuously true everywhere.
#guard (mulState mulTestMax 1 1).getD 8 0 == 0
#guard (mulState mulTestMax 1 1).getD 0 0 != 0

-- The product genuinely exceeds 256 bits, so `copyState`'s narrowing is doing
-- something: the full accumulator differs from its low 32 bytes.
#guard leBytesToNat (mulState mulTestMax 0xffffffffffffffff 32) > 2 ^ 256

-- ⭐ And the output window's truncation is REAL, not a formality: reading the
-- 32-byte result big-endian gives the product mod 2^256, which differs from the
-- product itself on this input. So `beBytesToNat_mulOutput`'s `% 2 ^ 256` is
-- describing behaviour, not weakening a statement that could have been exact.
#guard EvmAsm.Crypto.beBytesToNat
    (copyState (mulState mulTestMax 0xffffffffffffffff 32)
      (List.replicate 32 (0 : BitVec 8)) 32)
  == ((2 ^ 256 - 1) * (2 ^ 64 - 1)) % 2 ^ 256
#guard ((2 ^ 256 - 1) * (2 ^ 64 - 1)) % 2 ^ 256 != (2 ^ 256 - 1) * (2 ^ 64 - 1)

end EvmAsm.Codegen.U256MulU64Be
