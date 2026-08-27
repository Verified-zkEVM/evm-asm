/-
  EvmAsm.Codegen.Programs.DivisorAndPadGateCover

  **Coverage for the last two tractable #12867 gates** — `u256_div_u64_be`'s
  nonzero divisor and `blsg_lt_p`'s zero-pad restriction.  They fail in opposite
  directions, which is why they are worth putting side by side.

  ## 1. `u256_div_u64_be` — half the stated gate is not a hypothesis

  The row states the gate as *"nonzero divisor `0 < b < 2^64`"*.  The theorem
  `u256DivU64BeInPlaceFlat_spec` carries exactly one hypothesis about `b`:

      (hbPos : 0 < b.toNat)

  There is no upper-bound hypothesis, and there could not usefully be one:
  `b : Word` is `BitVec 64`, so `b.toNat < 2 ^ 64` holds of every inhabitant.
  `divisorGate_upper_bound_is_free` proves it, and `divisorGate_iff` collapses
  the stated two-sided gate to what it actually is — `b ≠ 0`.

  The row's own note already said "the Word representation supplies the upper
  bound"; this makes that a theorem rather than an aside, and drops the half of
  the gate that restricts nothing.

  ⚠️ Contrast with `rlp_walk_init`'s long-form-1 arm (#12957), where the row
  stated a *lower* bound and the type of a neighbouring hypothesis silently
  supplied a real *upper* one.  Here the row states an upper bound that the type
  makes vacuous.  Same root — a gate whose extent is decided partly by types
  rather than wholly by its stated hypotheses — and it can go either way, so
  neither direction should be assumed when reading a gate.

  ## 2. `blsg_lt_p` — the pad gate is load-bearing, and here is the divergence

  The row asserts, in prose, that the zero-pad restriction is

      "Load-bearing, not decorative: the reference decodes all 64 bytes, so a
       nonzero pad byte makes the value ≥ 2^384 > p and the reference rejects,
       while the guest scan never reads those bytes and would not."

  That is a claim that the two sides **diverge** off-gate, and it is exactly the
  sort of claim worth making machine-checked, because it is the whole argument
  for the gate's existence.  `padGate_is_load_bearing` exhibits the witness pair:

  * `wGood` — 64 zero bytes;
  * `wBad`  — a `1` at pad index 15, then 48 zero bytes.

  They have **the same 48-byte suffix**, and the suffix is all the guest ever
  sees: the triple's precondition carries `bytesRegion inPtr (w.drop 16)`.  So
  the guest cannot distinguish them by construction.  The reference can:
  `bytes_to_fq wGood` succeeds and `bytes_to_fq wBad` fails, because a nonzero
  byte at index 15 contributes `256 ^ 48 = 2 ^ 384`, above `blsP`.

  ⇒ Off-gate the two sides genuinely disagree, on inputs the guest is blind to.
  The gate is not a convenience; dropping it would make the row false.

  Issue: #12867.
-/
import EvmAsm.Rv64.Word
import EvmAsm.Stateless.SpecRef.PrecompilesBls

namespace EvmAsm.Codegen.DivisorAndPadGateCover

open EvmAsm.Rv64 EvmAsm.Stateless.SpecRef.Bls12

/-! ### `u256_div_u64_be` — the divisor gate -/

/-- The upper half of the stated gate holds of **every** `Word`, so it restricts
    nothing. -/
theorem divisorGate_upper_bound_is_free (b : Word) : b.toNat < 2 ^ 64 := b.isLt

/-- ⇒ the gate is exactly `b ≠ 0`.  `u256DivU64BeInPlaceFlat_spec` carries only
    `hbPos : 0 < b.toNat`; the row's `< 2 ^ 64` is not a hypothesis. -/
theorem divisorGate_iff (b : Word) : 0 < b.toNat ∧ b.toNat < 2 ^ 64 ↔ b ≠ 0 := by
  constructor
  · rintro ⟨hpos, -⟩ rfl
    simp at hpos
  · intro hne
    refine ⟨Nat.pos_of_ne_zero (fun h => hne ?_), divisorGate_upper_bound_is_free b⟩
    exact BitVec.eq_of_toNat_eq (by simpa using h)

/-- The gate admits the divisors the production call sites supply — the row
    names literal `8` at K73's `+120`/`+168`. -/
theorem divisorGate_admits_eight : (8 : Word) ≠ 0 := by decide

/-- ⛔ …and excludes exactly one value.  Without this the gate could have been
    vacuous, in which case the row would not be `.conditional`. -/
theorem divisorGate_excludes_only_zero (b : Word) : ¬ (b ≠ 0) ↔ b = 0 := by
  simp

/-! ### `blsg_lt_p` — the zero-pad gate -/

/-- 64 zero bytes: a well-formed wire felt, pad included. -/
def wGood : List (BitVec 8) := List.replicate 64 0

/-- The same 48-byte felt suffix, but with a `1` in the last pad byte. -/
def wBad : List (BitVec 8) :=
  List.replicate 15 0 ++ [1] ++ List.replicate 48 0

/-- ⛔ **The pad gate is load-bearing**, and this is the divergence the row
    asserts in prose.

    `wGood` and `wBad` have the **same 48-byte suffix**, which is all the guest
    reads — the triple's precondition carries `bytesRegion inPtr (w.drop 16)` and
    nothing else about `w`. So no execution of the routine can tell them apart.
    The reference reads all 64 bytes and rejects `wBad`, because a nonzero byte
    at pad index 15 contributes `256 ^ 48 = 2 ^ 384 > blsP`.

    ⇒ Off-gate the two sides disagree on inputs the guest is blind to. Dropping
    `hpad` would not weaken the row, it would falsify it. -/
theorem padGate_is_load_bearing :
    wGood.length = 64 ∧ wBad.length = 64 ∧
    wGood.drop 16 = wBad.drop 16 ∧
    (bytes_to_fq wGood).isOk = true ∧
    (bytes_to_fq wBad).isOk = false := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `wGood` satisfies the gate and `wBad` violates it at exactly one index, so
    the witness pair really does straddle `hpad` rather than differing in some
    other way. -/
theorem padGate_separates_the_pair :
    (∀ i, i < 16 → wGood.getD i 0 = 0) ∧ ¬ (∀ i, i < 16 → wBad.getD i 0 = 0) := by
  refine ⟨?_, ?_⟩
  · decide
  · intro h
    exact absurd (h 15 (by omega)) (by decide)

end EvmAsm.Codegen.DivisorAndPadGateCover
