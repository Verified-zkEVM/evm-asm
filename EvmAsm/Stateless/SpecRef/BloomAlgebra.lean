/-
  EvmAsm.Stateless.SpecRef.BloomAlgebra

  GH #11348 — the algebra `logs_bloom` needs in order to have a counterpart for
  `bloom_or_into` at all.

  THE MISMATCH. The guest routine ORs two materialised 256-byte blooms. The reference
  `logs_bloom` (`Fork.lean:101`) never does that: it is a `foldl` of *bit-sets* into a
  single accumulator, and `add_to_bloom` (`:89`) writes three bits with `List.set`.
  Nothing in the tree relates the two — there are **zero** theorems about either function.
  Without the decomposition below the guest's pointwise OR has no reference counterpart
  and the row could only be `noCounterpart`.

  ⭐ THE LOAD-BEARING FACT, and where the difficulty actually is. `add_to_bloom` is
  *`bloomOr` with a fixed mask*:

      add_to_bloom b e = bloomOr b (add_to_bloom zeroBloom e)

  That looks obvious and is not, because the three bit indices derived from one entry can
  **collide into the same byte**. So the three `List.set`s are *not* a disjoint update, and
  the proof cannot proceed by "each set touches a different index". It goes through
  `setOr_getD` instead: one OR-write is characterised pointwise, and the three-step fold is
  then unfolded with a case split at each step on whether that step's index is the one
  being read. Collisions are handled by `Nat.lor` associativity/idempotence rather than
  avoided.

  ⚠️ SCOPE, per `docs/leaf-routine-targets.md:46`: this is the **fold** only. The per-log
  index derivation — `keccak256` and the 11-bit extraction — is explicitly out of scope for
  #11348 and is treated here as an opaque function of the entry.
-/

import EvmAsm.Stateless.SpecRef.Fork

namespace EvmAsm.Stateless.SpecRef

/-- The all-zero bloom: `logs_bloom`'s fold seed. -/
def zeroBloom : Bytes := List.replicate 256 (0 : BitVec 8)

/-- Pointwise OR of two 256-byte blooms — the operation the guest routine performs.
    Written in the same `(List.range 256).map` shape as the guest's post so the two line
    up syntactically. -/
def bloomOr (a b : Bytes) : Bytes :=
  (List.range 256).map (fun k => a.getD k 0 ||| b.getD k 0)

@[simp] theorem bloomOr_length (a b : Bytes) : (bloomOr a b).length = 256 := by
  simp [bloomOr]

theorem bloomOr_getD (a b : Bytes) {k : Nat} (hk : k < 256) :
    (bloomOr a b).getD k 0 = a.getD k 0 ||| b.getD k 0 := by
  rw [bloomOr, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk]
  rfl

/-- ⭐ **One OR-write, read pointwise.** The step `add_to_bloom` repeats three times.
    Stated for an arbitrary index so the collision case is just `k = i` firing twice. -/
theorem setOr_getD (bl : Bytes) (i : Nat) (v : Nat) {k : Nat}
    (hi : i < bl.length) :
    ((bl.set i (BitVec.ofNat 8 ((bl.getD i 0).toNat ||| v))).getD k 0)
      = if k = i then BitVec.ofNat 8 ((bl.getD i 0).toNat ||| v) else bl.getD k 0 := by
  by_cases hk : k = i
  · subst hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega), if_pos rfl]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hk), if_neg hk,
      List.getD_eq_getElem?_getD]

/-- OR-ing a byte-sized natural into a byte is the bitvector OR. Bridges the reference's
    `Nat`-level `|||` (inside `BitVec.ofNat 8`) to the guest's `BitVec` OR. -/
theorem ofNat_or_eq (x : BitVec 8) {v : Nat} (hv : v < 256) :
    BitVec.ofNat 8 (x.toNat ||| v) = x ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt]
  exact Nat.or_lt_two_pow (n := 8) hx hv

/-! ## The decomposition

    `add_to_bloom` writes three bits with `List.set`; the guest ORs two whole blooms.
    The bridge is one distribution lemma plus an induction — no case explosion, because
    colliding indices are absorbed by `Nat.lor` associativity rather than ruled out. -/

/-- Two 256-byte blooms are equal when they agree byte by byte. -/
theorem bloom_ext {a b : Bytes} (ha : a.length = 256) (hb : b.length = 256)
    (h : ∀ k, k < 256 → a.getD k 0 = b.getD k 0) : a = b := by
  apply List.ext_getElem (by omega)
  intro k h1 h2
  have hk := h k (by omega)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hk

/-- The zero bloom reads zero everywhere in range. -/
theorem zeroBloom_getD {k : Nat} (hk : k < 256) : (zeroBloom : Bytes).getD k 0 = 0 := by
  rw [zeroBloom, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hk]

@[simp] theorem zeroBloom_length : (zeroBloom : Bytes).length = 256 := by
  rw [zeroBloom, List.length_replicate]

/-- OR with the zero byte, in the `OfNat` form the goals actually carry (core's
    `BitVec.zero_or` is stated for `0#w` and does not match syntactically). -/
private theorem zero_or_byte (x : BitVec 8) : (0 : BitVec 8) ||| x = x := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- One OR-write, as `add_to_bloom` performs it. -/
def setOr (bl : Bytes) (i v : Nat) : Bytes :=
  bl.set i (BitVec.ofNat 8 ((bl.getD i 0).toNat ||| v))

@[simp] theorem setOr_length (bl : Bytes) (i v : Nat) :
    (setOr bl i v).length = bl.length := by
  simp [setOr]

/-- `setOr`, read at an arbitrary index. Named so later rewrites never have to unfold
    `setOr` in a goal that mentions it twice. -/
theorem setOr_getD' (bl : Bytes) (i v k : Nat) (hi : i < bl.length) :
    (setOr bl i v).getD k 0
      = if k = i then BitVec.ofNat 8 ((bl.getD i 0).toNat ||| v) else bl.getD k 0 := by
  rw [setOr]; exact setOr_getD bl i v hi

theorem foldl_setOr_length (ps : List (Nat × Nat)) (b : Bytes) :
    (ps.foldl (fun bl p => setOr bl p.1 p.2) b).length = b.length := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih => simp only [List.foldl_cons]; rw [ih]; simp

/-- OR-ing with the all-zero bloom is the identity. -/
theorem bloomOr_zeroBloom (b : Bytes) (hb : b.length = 256) :
    bloomOr b zeroBloom = b := by
  refine bloom_ext (by simp) hb (fun k hk => ?_)
  rw [bloomOr_getD _ _ hk, zeroBloom_getD hk]
  exact BitVec.or_zero

/-- ⭐ **Any run of OR-writes decomposes into a pointwise OR with its own mask.**

    The mask is what the same run produces from the zero bloom. At the written index the
    step is `Nat.lor` associativity, which is exactly what makes *colliding* bit indices
    harmless — a second write to the same byte re-associates instead of clobbering. -/
theorem foldl_setOr_eq_bloomOr :
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, p.1 < 256 ∧ p.2 < 256) →
      ∀ (b : Bytes), b.length = 256 →
        ps.foldl (fun bl p => setOr bl p.1 p.2) b
          = bloomOr b (ps.foldl (fun bl p => setOr bl p.1 p.2) zeroBloom) := by
  intro ps
  induction ps with
  | nil =>
    intro _ b hb
    simpa using (bloomOr_zeroBloom b hb).symm
  | cons p rest ih =>
    intro hps b hb
    obtain ⟨hp1, hp2⟩ := hps p (by simp)
    have hrest : ∀ q ∈ rest, q.1 < 256 ∧ q.2 < 256 := fun q hq => hps q (by simp [hq])
    have hMlen : (rest.foldl (fun bl q => setOr bl q.1 q.2) zeroBloom).length = 256 := by
      rw [foldl_setOr_length, zeroBloom_length]
    simp only [List.foldl_cons]
    have hL := ih hrest (setOr b p.1 p.2) (by rw [setOr_length]; exact hb)
    have hR := ih hrest (setOr zeroBloom p.1 p.2)
      (by rw [setOr_length, zeroBloom_length])
    rw [hL, hR]
    refine bloom_ext (by simp) (by simp) (fun k hk => ?_)
    rw [bloomOr_getD _ _ hk, bloomOr_getD _ _ hk, bloomOr_getD _ _ hk,
      setOr_getD' b p.1 p.2 k (by omega),
      setOr_getD' zeroBloom p.1 p.2 k (by rw [zeroBloom_length]; omega)]
    by_cases hki : k = p.1
    · subst hki
      rw [if_pos rfl, if_pos rfl, zeroBloom_getD hk,
        show ((0 : BitVec 8)).toNat ||| p.2 = p.2 from by simp,
        ofNat_or_eq _ hp2, BitVec.or_assoc]
    · rw [if_neg hki, if_neg hki, zeroBloom_getD hk, zero_or_byte]

/-! ## Tying it to `add_to_bloom` and `logs_bloom` -/

/-- The (byte index, bit value) pair `add_to_bloom` derives from one 16-bit window of the
    entry's hash. ⚠️ The derivation itself — `keccak256` and the 11-bit extraction — is
    **out of scope** for #11348 (`docs/leaf-routine-targets.md:46`: the fold, not the
    per-log index derivation); it is treated here as an opaque function of the entry. -/
def bloomPair (e : Bytes) (idx : Nat) : Nat × Nat :=
  let hashed := keccak256 e
  let bit_to_set := bytesBEtoNat ((hashed.drop idx).take 2) &&& 0x07FF
  let bit_index := 0x07FF - bit_to_set
  (bit_index / 8, 1 <<< (7 - bit_index % 8))

/-- The three writes one entry performs. -/
def bloomPairs (e : Bytes) : List (Nat × Nat) := [0, 2, 4].map (bloomPair e)

/-- The bound, stated on the *shape* rather than on the hash expression: a bit index is
    at most `0x7FF`, so its byte is at most 255; the bit value is `1 <<< k` with `k ≤ 7`,
    so at most 128. -/
private theorem pair_bounds (x : Nat) :
    (2047 - x) / 8 < 256 ∧ 1 <<< (7 - (2047 - x) % 8) < 256 := by
  refine ⟨by omega, ?_⟩
  have hk : 7 - (2047 - x) % 8 ≤ 7 := by omega
  calc 1 <<< (7 - (2047 - x) % 8) = 2 ^ (7 - (2047 - x) % 8) := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]
    _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hk
    _ < 256 := by omega

theorem bloomPairs_bounds (e : Bytes) :
    ∀ p ∈ bloomPairs e, p.1 < 256 ∧ p.2 < 256 := by
  intro p hp
  simp only [bloomPairs, List.mem_map] at hp
  obtain ⟨idx, -, rfl⟩ := hp
  exact pair_bounds _

/-- `add_to_bloom` IS a run of OR-writes. -/
theorem add_to_bloom_eq_foldl (b e : Bytes) :
    add_to_bloom b e = (bloomPairs e).foldl (fun bl p => setOr bl p.1 p.2) b := by
  rw [bloomPairs, List.foldl_map]
  rfl

/-- ⭐ **The entry-level bridge.** Adding an entry to a bloom is OR-ing in the mask that
    entry produces on its own — which is what makes the guest's whole-bloom OR meaningful
    as a reference operation. -/
theorem add_to_bloom_eq_bloomOr (b e : Bytes) (hb : b.length = 256) :
    add_to_bloom b e = bloomOr b (add_to_bloom zeroBloom e) := by
  rw [add_to_bloom_eq_foldl, add_to_bloom_eq_foldl]
  exact foldl_setOr_eq_bloomOr (bloomPairs e) (bloomPairs_bounds e) b hb

theorem add_to_bloom_length (b e : Bytes) :
    (add_to_bloom b e).length = b.length := by
  rw [add_to_bloom_eq_foldl, foldl_setOr_length]

/-! ## `logs_bloom` decomposes over concatenation

    This is the statement the guest routine needs: OR-ing two materialised blooms is
    exactly what `logs_bloom` does to two log segments. -/

/-- Every write one log performs: its address, then each topic. -/
def logPairs (log : Log) : List (Nat × Nat) :=
  bloomPairs log.address ++ log.topics.flatMap bloomPairs

theorem logPairs_bounds (log : Log) :
    ∀ p ∈ logPairs log, p.1 < 256 ∧ p.2 < 256 := by
  intro p hp
  rw [logPairs, List.mem_append] at hp
  rcases hp with h | h
  · exact bloomPairs_bounds _ p h
  · rw [List.mem_flatMap] at h
    obtain ⟨tp, -, hmem⟩ := h
    exact bloomPairs_bounds _ p hmem

/-- One log's contribution, as a run of OR-writes. -/
theorem logStep_eq_foldl (bloom : Bytes) (log : Log) :
    log.topics.foldl add_to_bloom (add_to_bloom bloom log.address)
      = (logPairs log).foldl (fun bl p => setOr bl p.1 p.2) bloom := by
  rw [logPairs, List.foldl_append, ← add_to_bloom_eq_foldl]
  generalize add_to_bloom bloom log.address = acc
  induction log.topics generalizing acc with
  | nil => rfl
  | cons tp rest ih =>
    rw [List.foldl_cons, List.flatMap_cons, List.foldl_append,
      ← add_to_bloom_eq_foldl, ih]

theorem logs_bloom_eq_foldl (logs : List Log) :
    logs_bloom logs
      = (logs.flatMap logPairs).foldl (fun bl p => setOr bl p.1 p.2) zeroBloom := by
  rw [logs_bloom, show (List.replicate 256 (0x00 : BitVec 8)) = zeroBloom from rfl]
  generalize (zeroBloom : Bytes) = acc
  induction logs generalizing acc with
  | nil => rfl
  | cons log rest ih =>
    rw [List.foldl_cons, List.flatMap_cons, List.foldl_append, logStep_eq_foldl, ih]

theorem logs_bloom_length (logs : List Log) : (logs_bloom logs).length = 256 := by
  rw [logs_bloom_eq_foldl, foldl_setOr_length, zeroBloom_length]

/-- ⭐ **The decomposition the guest routine implements.** `bloom_or_into` ORs two
    materialised 256-byte blooms; this says that is exactly `logs_bloom` of the
    concatenated log segments.

    Without it the guest's pointwise OR has no reference counterpart at all and the row
    could only be `noCounterpart`. -/
theorem logs_bloom_append (l₁ l₂ : List Log) :
    logs_bloom (l₁ ++ l₂) = bloomOr (logs_bloom l₁) (logs_bloom l₂) := by
  have hb : ∀ p ∈ l₂.flatMap logPairs, p.1 < 256 ∧ p.2 < 256 := by
    intro p hp
    rw [List.mem_flatMap] at hp
    obtain ⟨lg, -, hmem⟩ := hp
    exact logPairs_bounds lg p hmem
  rw [logs_bloom_eq_foldl, logs_bloom_eq_foldl, logs_bloom_eq_foldl,
    List.flatMap_append, List.foldl_append]
  exact foldl_setOr_eq_bloomOr _ hb _ (by rw [foldl_setOr_length, zeroBloom_length])

/-! ## Non-vacuity pins

    `logs_bloom` runs `keccak256`, so these evaluate the real derivation rather than a
    stub — which is the point: they would catch a decomposition that happened to hold
    only for the all-zero mask. -/

section Pins

private def mkLog (a : Bytes) (ts : List Bytes) : Log :=
  { address := a, topics := ts, data := [] }

private def L1 : Log := mkLog [(0x11 : BitVec 8)] [[(0x22 : BitVec 8)]]
private def L2 : Log := mkLog [(0x33 : BitVec 8)] []

-- the empty segment is the identity, on both sides
#guard logs_bloom ([] : List Log) == zeroBloom
#guard logs_bloom [L1] == bloomOr (logs_bloom [L1]) (logs_bloom [])
-- a genuine two-segment split
#guard logs_bloom [L1, L2] == bloomOr (logs_bloom [L1]) (logs_bloom [L2])
-- order does not matter, because OR is commutative — and the blooms really do differ
#guard logs_bloom [L1, L2] == logs_bloom [L2, L1]
#guard logs_bloom [L1] != logs_bloom [L2]
-- the width is preserved
#guard (logs_bloom [L1, L2]).length == 256

end Pins

end EvmAsm.Stateless.SpecRef
