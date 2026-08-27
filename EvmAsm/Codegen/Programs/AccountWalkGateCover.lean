/-
  EvmAsm.Codegen.Programs.AccountWalkGateCover

  **Coverage for the two account-walk arm gates** — `rlp_walk_init`'s
  long-form-1 arm and `rlp_walk_next`'s scalar arm.  Both rows stated a gate and
  cited nothing (#12867), and stating each one exactly turns up something the
  row's prose did not say.

  ## 1. `rlp_walk_init_long1_spec_within` — the gate is a BAND, not a half-line

  The row gives the gate as *"`56 ≤ payload.length` — the long-form-1 arm
  specifically"*.  That is only the lower half.  The theorem also carries

      (lenB : BitVec 8) (hlenB : lenB.toNat = payload.length)

  and `lenB` is **eight bits wide**, so `payload.length ≤ 255` follows with no
  further assumption — `walkInitLong1_upper_bound_is_implicit`.  The effective
  gate is the band `56 ≤ payload.length ≤ 255`.

  The upper bound is not wrong — one length byte is exactly what "long-form-1"
  means — but it arrives from the *type of a different hypothesis* rather than
  from the stated one, which is the kind of thing a reader checking whether
  their input qualifies would have to reconstruct.  `walkInitLong1_band` states
  it once.

  ## 2. `rlp_walk_next_scalar_spec_within` — the gate, in terms of the value

  The row gives *"`(Nat.toBytesBE n).length ≤ 55` — scalar short form"*, a
  condition on the *encoding* of `n`.  A caller has `n`, not its encoding, so
  the useful form is the equivalent condition on the value:

      (Nat.toBytesBE n).length ≤ 55  ↔  n < 256 ^ 55

  `scalarGate_iff`.  Both directions are already available — `≤` from
  `Nat.toBytesBE_length_le`, `≥` by contraposing `lt_pow_toBytesBE_length` —
  so this is an exact characterisation rather than a sample, and the boundary
  falls out of it instead of being asserted.

  ⚠️ Note on method: none of this is done by `decide`.  `Nat.toBytesBE` is
  defined by well-founded recursion and does not reduce, so even
  `(Nat.toBytesBE 42).length ≤ 55` is not decidable by evaluation — the
  instance gets stuck at `Nat.decLe`.  Point instances here would have needed
  the same two lemmas the general statement uses, so the general statement is
  strictly better value.

  Issue: #12867.
-/
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeBridge

namespace EvmAsm.Codegen.AccountWalkGateCover

open EvmAsm.EL.RLP EvmAsm.Codegen.RlpBytesEncodedSizeSAsm

/-! ### `rlp_walk_init`, long-form-1 arm -/

/-- The upper half of the gate, which the row does not state: `lenB : BitVec 8`
    and `hlenB : lenB.toNat = payload.length` cap the payload at 255 with no
    further assumption. -/
theorem walkInitLong1_upper_bound_is_implicit
    (lenB : BitVec 8) (payload : List (BitVec 8))
    (hlenB : lenB.toNat = payload.length) :
    payload.length ≤ 255 := by
  have := lenB.isLt
  omega

/-- ⇒ the effective gate is a **band**. -/
theorem walkInitLong1_band
    (lenB : BitVec 8) (payload : List (BitVec 8))
    (hlenB : lenB.toNat = payload.length) (hmin : 56 ≤ payload.length) :
    56 ≤ payload.length ∧ payload.length ≤ 255 :=
  ⟨hmin, walkInitLong1_upper_bound_is_implicit lenB payload hlenB⟩

/-- Both ends are inhabited, so the band is not degenerate: 56 is the smallest
    qualifying payload and 255 the largest, each with the `lenB` that witnesses
    `hlenB`. -/
theorem walkInitLong1_band_ends_inhabited :
    ((56 : BitVec 8).toNat = (List.replicate 56 (0 : BitVec 8)).length ∧
      56 ≤ (List.replicate 56 (0 : BitVec 8)).length) ∧
    ((255 : BitVec 8).toNat = (List.replicate 255 (0 : BitVec 8)).length ∧
      56 ≤ (List.replicate 255 (0 : BitVec 8)).length) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [List.length_replicate] <;> decide

/-- ⛔ Below the band: a 55-byte payload fails `hmin`, so the short-form arm and
    this one really do partition at 56 rather than overlapping. -/
theorem walkInitLong1_excludes_55 :
    ¬ (56 ≤ (List.replicate 55 (0 : BitVec 8)).length) := by simp

/-- ⛔ Above the band: **no** `lenB : BitVec 8` witnesses a 256-byte payload, so
    the exclusion is structural rather than a missing case. This is what makes
    the implicit upper bound a real restriction and not an artifact of how the
    hypothesis is spelled. -/
theorem walkInitLong1_excludes_256 :
    ∀ lenB : BitVec 8, lenB.toNat ≠ 256 := by
  intro lenB
  have := lenB.isLt
  omega

/-! ### `rlp_walk_next`, scalar arm -/

/-- **The scalar gate, as a condition on the value.** The row states it on the
    encoding; a caller holds `n`. -/
theorem scalarGate_iff (n : Nat) :
    (Nat.toBytesBE n).length ≤ 55 ↔ n < 256 ^ 55 := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le (lt_pow_toBytesBE_length n)
      (Nat.pow_le_pow_right (by omega) h)
  · intro h
    exact Nat.toBytesBE_length_le n 55 h

/-- An ordinary scalar is admitted — via the characterisation, since
    `Nat.toBytesBE` does not reduce. -/
theorem scalarGate_admits_ordinary : (Nat.toBytesBE 42).length ≤ 55 :=
  (scalarGate_iff 42).mpr (by
    calc (42 : Nat) < 256 ^ 1 := by omega
      _ ≤ 256 ^ 55 := Nat.pow_le_pow_right (by omega) (by omega))

/-- ⛔ The boundary, both sides, straight off the characterisation: `256 ^ 55`
    is the least excluded value and everything below it is admitted. -/
theorem scalarGate_boundary :
    (Nat.toBytesBE (256 ^ 55 - 1)).length ≤ 55 ∧
    ¬ (Nat.toBytesBE (256 ^ 55)).length ≤ 55 := by
  refine ⟨(scalarGate_iff _).mpr (by omega), ?_⟩
  intro h
  exact absurd ((scalarGate_iff _).mp h) (by omega)

end EvmAsm.Codegen.AccountWalkGateCover
