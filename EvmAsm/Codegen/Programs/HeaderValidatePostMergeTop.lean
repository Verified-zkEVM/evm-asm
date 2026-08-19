/-
  K67 `header_validate_post_merge` — top-level composition.

  This file assembles the whole-routine `cpsTripleWithin` for
  `headerValidatePostMerge_prog` from the proved pieces:

  * `k67PrologueSetup` (stack frame + `rlp_walk_init` call, LoopBody),
  * the init dispatch (instruction 11, `BNE x12, x0` at `K + 44`),
  * `k67PrologueFall` (cursor/end commit, LoopBody),
  * `k67LoopFold` (the 15-field scan loop, Round),
  * `k67PostLoop` (nonce + ommers compare chains, PostLoopPhases),
  * `k67StatusTail0..4` and `k67Epilogue` (LoopClose).

  §1 (`k67InitFailedPure`, `k67InitOutcomeNorm`, `k67InitOutcome_to_norm`,
  `k67QfailInit`, `k67InitBranch`) handles the init outcome: the walker's
  9-way `initOutcome` is normalized to a 2-way success/failure disjunction,
  then dispatched at the `BNE x12, x0` — success enters the loop invariant,
  failure exits at the status-4 station `K + 628` (which the loop's own
  `k67Qfail` also targets; the exits list carries both posts at that label).
-/
import EvmAsm.Codegen.Programs.HeaderValidatePostMergePostLoopPhases
import EvmAsm.Rv64.SAsm.LoopFuel

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## §1  Init outcome normalization and dispatch -/

/-- The seven `rlp_walk_init` failure pures (any one makes the walker return a
    nonzero status in `x12`): window empty, not a list prefix, short-form
    content-size mismatch, long-form content end beyond the window, noncanonical
    leading-zero length-of-length, should-have-been-short declared length, and
    long-form content end mismatching the window end. -/
def k67InitFailedPure (base : Word) (bytes : List (BitVec 8)) (len : Nat)
    (hoff : 0 < bytes.length) : Prop :=
  (BitVec.ofNat 64 len = (0 : Word)) ∨
  (BitVec.ofNat 64 len ≠ (0 : Word) ∧
    BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true) ∨
  (BitVec.ofNat 64 len ≠ (0 : Word) ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    base + (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
      signExtend12 (1 : BitVec 12)) ≠ base + BitVec.ofNat 64 len) ∨
  (BitVec.ofNat 64 len ≠ (0 : Word) ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    BitVec.ult (base + BitVec.ofNat 64 len)
      (base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true) ∨
  (BitVec.ofNat 64 len ≠ (0 : Word) ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    ¬ BitVec.ult (base + BitVec.ofNat 64 len)
      (base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true ∧
    bytes[1]? = some (0 : BitVec 8)) ∨
  (BitVec.ofNat 64 len ≠ (0 : Word) ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    ¬ BitVec.ult (base + BitVec.ofNat 64 len)
      (base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true ∧
    bytes[1]? ≠ some (0 : BitVec 8) ∧
    BitVec.ult (BitVec.ofNat 64 (EvmAsm.EL.RLP.Nat.fromBytesBE
      ((bytes.drop 1).take
        (((bytes[0]'hoff).zeroExtend 64) - (0xf7 : Word)).toNat)))
      (56 : Word) = true) ∨
  (BitVec.ofNat 64 len ≠ (0 : Word) ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    ¬ BitVec.ult (base + BitVec.ofNat 64 len)
      (base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true ∧
    bytes[1]? ≠ some (0 : BitVec 8) ∧
    ¬ BitVec.ult (BitVec.ofNat 64 (EvmAsm.EL.RLP.Nat.fromBytesBE
      ((bytes.drop 1).take
        (((bytes[0]'hoff).zeroExtend 64) - (0xf7 : Word)).toNat)))
      (56 : Word) = true ∧
    base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12)) +
      BitVec.ofNat 64 (EvmAsm.EL.RLP.Nat.fromBytesBE
        ((bytes.drop 1).take
          (((bytes[0]'hoff).zeroExtend 64) - (0xf7 : Word)).toNat)) ≠
      base + BitVec.ofNat 64 len)

/-- The walker-success post at the init return site: `x12 = 0` and the cursor
    value is one of the two accepted content-start forms (short-form
    `base + 1`, long-form `base + (1 + lengthOfLength)`), each with its
    exact-fit pure. -/
def k67InitOk (base : Word) (bytes : List (BitVec 8)) (len : Nat)
    (hoff : 0 < bytes.length) : Assertion := fun h =>
  ∃ v10 : Word,
    (((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ (base + BitVec.ofNat 64 len)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜(v10 = base + signExtend12 (1 : BitVec 12) ∧
          BitVec.ofNat 64 len ≠ (0 : Word) ∧
          ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          base + (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
            signExtend12 (1 : BitVec 12)) = base + BitVec.ofNat 64 len) ∨
        (v10 = base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12)) ∧
          BitVec.ofNat 64 len ≠ (0 : Word) ∧
          ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          ¬ BitVec.ult (base + BitVec.ofNat 64 len)
            (base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true ∧
          bytes[1]? ≠ some (0 : BitVec 8) ∧
          ¬ BitVec.ult (BitVec.ofNat 64 (EvmAsm.EL.RLP.Nat.fromBytesBE
            ((bytes.drop 1).take
              (((bytes[0]'hoff).zeroExtend 64) - (0xf7 : Word)).toNat)))
            (56 : Word) = true ∧
          base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 (EvmAsm.EL.RLP.Nat.fromBytesBE
              ((bytes.drop 1).take
                (((bytes[0]'hoff).zeroExtend 64) - (0xf7 : Word)).toNat)) =
            base + BitVec.ofNat 64 len)⌝) h)

/-- The walker-failure post: some status `v12 ≠ 0`, some cursor `v10`, and one
    of the seven failure pures. -/
def k67InitFail (base : Word) (bytes : List (BitVec 8)) (len : Nat)
    (hoff : 0 < bytes.length) : Assertion := fun h =>
  ∃ v10 v11 v12 : Word,
    (((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) **
      ⌜k67InitFailedPure base bytes len hoff ∧ v12 ≠ (0 : Word)⌝) h)

/-- Two-way normal form of the nine-way `initOutcome`. -/
def k67InitOutcomeNorm (base : Word) (bytes : List (BitVec 8)) (len : Nat)
    (hoff : 0 < bytes.length) : Assertion := fun h =>
  k67InitOk base bytes len hoff h ∨ k67InitFail base bytes len hoff h

/-- The nine `initOutcome` arms collapse to the two-way norm: the two
    `x12 = 0` arms are successes, the other seven are failures. -/
theorem k67InitOutcome_to_norm (base : Word) (bytes : List (BitVec 8))
    (len : Nat) (hoff : 0 < bytes.length) :
    ∀ h, RlpListNthItemSAsm.initOutcome base bytes len hoff h →
      k67InitOutcomeNorm base bytes len hoff h := by
  intro h hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq
  · -- arm 1: window empty (x12 = 2)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inr ⟨_, _, (2 : Word), hA, hB, hd, hu, h10, hA', hB', hd',
      hu', h11, hA'', hB'', hd'', hu'', h12, hpure.1, Or.inl hpure.2, by decide⟩
  · -- arm 2: not a list prefix (x12 = 1)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inr ⟨_, _, (1 : Word), hA, hB, hd, hu, h10, hA', hB', hd',
      hu', h11, hA'', hB'', hd'', hu'', h12, hpure.1, Or.inr (Or.inl hpure.2), by decide⟩
  · -- arm 3: short-list success (x12 = 0)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inl ⟨_, hA, hB, hd, hu, h10, hA', hB', hd', hu', h11,
      hA'', hB'', hd'', hu'', h12, hpure.1, Or.inl ⟨rfl, hpure.2⟩⟩
  · -- arm 4: short list, content-length misfit (x12 = 3)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inr ⟨_, _, (3 : Word), hA, hB, hd, hu, h10, hA', hB', hd',
      hu', h11, hA'', hB'', hd'', hu'', h12, hpure.1, Or.inr (Or.inr (Or.inl hpure.2)), by decide⟩
  · -- arm 5: long list, content past window (x12 = 4)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inr ⟨_, _, (4 : Word), hA, hB, hd, hu, h10, hA', hB', hd',
      hu', h11, hA'', hB'', hd'', hu'', h12, hpure.1, Or.inr (Or.inr (Or.inr (Or.inl hpure.2))), by decide⟩
  · -- arm 6: long list, non-canonical leading zero (x12 = 5)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inr ⟨_, _, (5 : Word), hA, hB, hd, hu, h10, hA', hB', hd',
      hu', h11, hA'', hB'', hd'', hu'', h12, hpure.1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure.2)))), by decide⟩
  · -- arm 7: long list, declared length < 56 (x12 = 6)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inr ⟨_, _, (6 : Word), hA, hB, hd, hu, h10, hA', hB', hd',
      hu', h11, hA'', hB'', hd'', hu'', h12, hpure.1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure.2))))), by decide⟩
  · -- arm 8: long list, content-end misfit (x12 = 7)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inr ⟨_, _, (7 : Word), hA, hB, hd, hu, h10, hA', hB', hd',
      hu', h11, hA'', hB'', hd'', hu'', h12, hpure.1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpure.2))))), by decide⟩
  · -- arm 9: long-list success (x12 = 0)
    obtain ⟨hA, hB, hd, hu, h10, hrest⟩ := hq
    obtain ⟨hA', hB', hd', hu', h11, hrest'⟩ := hrest
    obtain ⟨hA'', hB'', hd'', hu'', h12, hpure⟩ := hrest'
    exact Or.inl ⟨_, hA, hB, hd, hu, h10, hA', hB', hd', hu', h11,
      hA'', hB'', hd'', hu'', h12, hpure.1, Or.inr ⟨rfl, hpure.2⟩⟩

/-- Three-pin analogue of `k67Pins10_to_regOwns`, converting the `x1`/`x10`/`x11`
    pins that the init success path carries into the ownership atoms the loop
    invariant expects. -/
theorem k67Pins3_to_regOwns :
    ∀ (v1 v10 v11 : Word) h,
      ((.x1 ↦ᵣ v1) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11)) h →
      (regOwn .x1 ** regOwn .x10 ** regOwn .x11) h := by
  intro v1 v10 v11 h hp
  obtain ⟨g0, g1, d0, u0, h1, hrest⟩ := hp
  obtain ⟨g2, g3, d1, u1, h10, h11⟩ := hrest
  exact ⟨g0, g1, d0, u0, ⟨v1, h1⟩, g2, g3, d1, u1, ⟨v10, h10⟩, ⟨v11, h11⟩⟩

/-- The init-failure post at the status-4 stub entry `K + 628`: the state after
    the init branch was taken (pure `k67InitFailedPure` fact plus a nonzero
    status word in `x12`).  Distinct from the fold's `k67Qfail` (which carries
    a `WalkFailure` from inside the loop); both live at label `K + 628` in the
    composed exit list. -/
def k67QfailInit (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (v18 v19 v21 : Word) (svals : Reg → Word) (hoff : 0 < bytes.length) :
    Assertion := fun h =>
  ∃ (v10 v11 v12 : Word),
    (((.x1 ↦ᵣ (K + 44)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** (.x8 ↦ᵣ base) **
      (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
      ⌜k67InitFailedPure base bytes bytes.length hoff ∧ v12 ≠ (0 : Word)⌝) h

/-- The init branch: prologue + `rlp_walk_init` call + the `BNE x12, x0` at
    `K + 44`.  On init success control falls through to the loop header
    `K + 56` in the fuel-invariant entry state (with the walked-chain start
    offset existential); on init failure it jumps to the status-4 stub at
    `K + 628` in the `k67QfailInit` state. -/
theorem k67InitBranch (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (ret v8 v9 v18 v19 v20 v21 v12 v5 v6 v7 v28 v29 v30 v31 : Word)
    (hsalign : base.toNat % 8 = 0)
    (hoff : 0 < bytes.length)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true)
    (hll_len : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length)
    (hll_over : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      base.toNat +
        (0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤
        2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      ∀ k, k < ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (base + BitVec.ofNat 64 (0 + 1 + k)) = true) :
    cpsNBranchWithin (10 + (1 + 81) + (1 + 2)) K fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) **
        (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (k67OmBytes) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40))
      [(K + 56, fun h => ∃ startOff : Nat,
        (k67FuelInv sp0 base omConst bytes startOff
          (k67PrologueVals ret v8 v9 v18 v19 v20) v21
          (cycleFuel startOff bytes.length) ** ⌜startOff ≤ bytes.length⌝) h),
        (K + 628, k67QfailInit sp0 base omConst bytes v18 v19 v21
          (k67PrologueVals ret v8 v9 v18 v19 v20) hoff)] := by
  have hsetup := k67PrologueSetup sp0 (sp0 + signExtend12 (-48 : BitVec 12))
    base omConst ret v8 v9 v18 v19 v20 v21 v12 v5 v6 v7 v28 v29 v30 v31 bytes
    bytes.length rfl hsalign hoff (by omega) hvalid hll_len hll_over hll_valid
  have hsetupN : cpsTripleWithin (10 + (1 + 81)) K (K + 44) fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) **
        (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (k67OmBytes) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40))
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (K + 44)) **
        bytesRegion base bytes ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) **
        (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          (k67PrologueVals ret v8 v9 v18 v19 v20) **
        bytesRegion omConst (k67OmBytes) ** regOwn .x13 ** regOwn .x14) **
        k67InitOutcomeNorm base bytes bytes.length hoff)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      have hq' : ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (K + 44)) **
          bytesRegion base bytes ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) **
          (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x18 ↦ᵣ v18) **
          (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            (k67PrologueVals ret v8 v9 v18 v19 v20) **
          bytesRegion omConst (k67OmBytes) ** regOwn .x13 ** regOwn .x14) **
          RlpListNthItemSAsm.initOutcome base bytes bytes.length hoff) h := by
        dsimp only [k67InitCommon, k67Ambient] at hq
        xperm_hyp hq
      have hconv := sepConj_mono_right
        (k67InitOutcome_to_norm base bytes bytes.length hoff) h hq'
      xperm_hyp hconv) hsetup
  have hnode : cpsNBranchWithin (1 + 2) (K + 44) fullCode
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (K + 44)) **
        bytesRegion base bytes ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) **
        (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          (k67PrologueVals ret v8 v9 v18 v19 v20) **
        bytesRegion omConst (k67OmBytes) ** regOwn .x13 ** regOwn .x14) **
        k67InitOutcomeNorm base bytes bytes.length hoff))
      [(K + 56, fun h => ∃ startOff : Nat,
        (k67FuelInv sp0 base omConst bytes startOff
          (k67PrologueVals ret v8 v9 v18 v19 v20) v21
          (cycleFuel startOff bytes.length) ** ⌜startOff ≤ bytes.length⌝) h),
        (K + 628, k67QfailInit sp0 base omConst bytes v18 v19 v21
          (k67PrologueVals ret v8 v9 v18 v19 v20) hoff)] := by
    apply cpsNBranchWithin_weaken_pre (fun h hp =>
      (sepConj_or_split _ hp).symm)
    apply k67NBranch_pre_or
    · -- init failed: BNE x12, x0 taken to the status-4 stub at K + 628.
      apply cpsNBranchWithin_weaken_pre (fun h hp =>
        sepConj_exists_right _ hp)
      apply cpsNBranchWithin_exists_pre; intro v10
      apply cpsNBranchWithin_weaken_pre (fun h hp =>
        sepConj_exists_right _ hp)
      apply cpsNBranchWithin_exists_pre; intro v11
      apply cpsNBranchWithin_weaken_pre (fun h hp =>
        sepConj_exists_right _ hp)
      apply cpsNBranchWithin_exists_pre; intro v12f
      refine cpsNBranchWithin_weaken_pre
        (P := (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (K + 44)) **
          bytesRegion base bytes ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) **
          (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x18 ↦ᵣ v18) **
          (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            (k67PrologueVals ret v8 v9 v18 v19 v20) **
          bytesRegion omConst (k67OmBytes) ** regOwn .x13 ** regOwn .x14) **
          ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12f))) **
          ⌜k67InitFailedPure base bytes bytes.length hoff ∧
            v12f ≠ (0 : Word)⌝))
        (fun h hp => by
          extract_pure_deep hp
          refine (sepConj_pure_right _).2 ⟨?_, hp.1⟩
          have htail := hp.2
          xperm_hyp htail) ?_
      apply cpsNBranchWithin_pure_pre; rintro ⟨hifp, hne⟩
      have h11 := bne_spec_gen_within .x12 .x0
        (brOff (GuestAddrs.header_validate_post_merge + 628)
          (GuestAddrs.header_validate_post_merge + 44))
        v12f (0 : Word) (K + 44)
      rw [show (K + 44 : Word) + 4 = K + 48 from by
        rw [BitVec.add_assoc,
          show (44 : Word) + (4 : Word) = (48 : Word) from by decide],
        show (K + 44 : Word) +
            signExtend13 (brOff
              (GuestAddrs.header_validate_post_merge + 628)
              (GuestAddrs.header_validate_post_merge + 44)) = K + 628 from by
          rw [show brOff (GuestAddrs.header_validate_post_merge + 628)
              (GuestAddrs.header_validate_post_merge + 44) =
              (584 : BitVec 13) from by decide,
            show signExtend13 (584 : BitVec 13) = (584 : Word) from by decide,
            BitVec.add_assoc,
            show (44 : Word) + (584 : Word) = (628 : Word) from by decide]]
        at h11
      have hmem11 :=
        CodeReq.ofProg_mem_at K (K + 44) k67Prog 11
          (.BNE .x12 .x0 (brOff
            (GuestAddrs.header_validate_post_merge + 628)
            (GuestAddrs.header_validate_post_merge + 44)))
          (by rw [show BitVec.ofNat 64 (4 * 11) = (44 : Word) from by decide])
          (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)
      have h11C := cpsBranchWithin_extend_code
        (fun a' i h => k67_mono a' i (hmem11 a' i h)) h11
      have htake := cpsBranchWithin_takenStripPure2 h11C (fun _ hQf => by
        obtain ⟨_, _, _, _, _, hBP⟩ := hQf
        exact absurd ((sepConj_pure_right _).1 hBP).2 hne)
      let Ff : Assertion :=
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (K + 44)) **
        bytesRegion base bytes **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) **
        (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          (k67PrologueVals ret v8 v9 v18 v19 v20) **
        bytesRegion omConst (k67OmBytes) ** regOwn .x13 ** regOwn .x14 **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11)
      have hFf : Ff.pcFree := by
        dsimp only [Ff]
        repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
          | exact bytesRegion_pcFree _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | apply pcFree_sepConj
      have htakeF : cpsTripleWithin 1 (K + 44) (K + 628) fullCode
          (((.x12 ↦ᵣ v12f) ** (.x0 ↦ᵣ (0 : Word))) ** Ff)
          (((.x12 ↦ᵣ v12f) ** (.x0 ↦ᵣ (0 : Word))) ** Ff) :=
        cpsTripleWithin_frameR Ff hFf htake
      apply cpsNBranchWithin_mono_nSteps (show 1 ≤ 1 + 2 by omega)
      apply cpsNBranchWithin_of_triple
        (Q := k67QfailInit sp0 base omConst bytes v18 v19 v21
          (k67PrologueVals ret v8 v9 v18 v19 v20) hoff)
        (by apply List.Mem.tail; apply List.Mem.head)
      refine cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Ff]; xperm_hyp hp) ?_ htakeF
      intro h hq
      refine ⟨v10, v11, v12f, ?_⟩
      refine (sepConj_pure_right _).2 ⟨?_, hifp, hne⟩
      dsimp only [Ff] at hq
      xperm_hyp hq
    · -- init succeeded: fall through the BNE, run the two MVs, enter the loop.
      apply cpsNBranchWithin_weaken_pre (fun h hp =>
        sepConj_exists_right _ hp)
      apply cpsNBranchWithin_exists_pre; intro v10
      refine cpsNBranchWithin_weaken_pre
        (P := (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (K + 44)) **
          bytesRegion base bytes ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) **
          (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x18 ↦ᵣ v18) **
          (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            (k67PrologueVals ret v8 v9 v18 v19 v20) **
          bytesRegion omConst (k67OmBytes) ** regOwn .x13 ** regOwn .x14) **
          ((.x10 ↦ᵣ v10) **
            (.x11 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x12 ↦ᵣ (0 : Word)))) **
          ⌜(v10 = base + signExtend12 (1 : BitVec 12) ∧
              BitVec.ofNat 64 bytes.length ≠ (0 : Word) ∧
              ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
                (0xc0 : Word) = true ∧
              BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) =
                true ∧
              base + (((bytes[0]'hoff).zeroExtend 64 - 0xc0) +
                signExtend12 (1 : BitVec 12)) =
                base + BitVec.ofNat 64 bytes.length) ∨
            (v10 = base + (((bytes[0]'hoff).zeroExtend 64 - 0xf7) +
                signExtend12 (1 : BitVec 12)) ∧
              BitVec.ofNat 64 bytes.length ≠ (0 : Word) ∧
              ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
                (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
                (0xf8 : Word) = true ∧
              ¬ BitVec.ult (base + BitVec.ofNat 64 bytes.length)
                (base + (((bytes[0]'hoff).zeroExtend 64 - 0xf7) +
                  signExtend12 (1 : BitVec 12))) = true ∧
              bytes[1]? ≠ some (0 : BitVec 8) ∧
              ¬ BitVec.ult (BitVec.ofNat 64
                  (EvmAsm.EL.RLP.Nat.fromBytesBE ((bytes.drop 1).take
                    (((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat))))
                (56 : Word) = true ∧
              base + (((bytes[0]'hoff).zeroExtend 64 - 0xf7) +
                  signExtend12 (1 : BitVec 12)) +
                BitVec.ofNat 64 (EvmAsm.EL.RLP.Nat.fromBytesBE
                  ((bytes.drop 1).take
                    (((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat))) =
                base + BitVec.ofNat 64 bytes.length)⌝))
        (fun h hp => by
          extract_pure_deep hp
          refine (sepConj_pure_right _).2 ⟨?_, hp.1⟩
          have htail := hp.2
          xperm_hyp htail) ?_
      apply cpsNBranchWithin_pure_pre; intro hsucc
      have h11 := bne_spec_gen_within .x12 .x0
        (brOff (GuestAddrs.header_validate_post_merge + 628)
          (GuestAddrs.header_validate_post_merge + 44))
        (0 : Word) (0 : Word) (K + 44)
      rw [show (K + 44 : Word) + 4 = K + 48 from by
        rw [BitVec.add_assoc,
          show (44 : Word) + (4 : Word) = (48 : Word) from by decide],
        show (K + 44 : Word) +
            signExtend13 (brOff
              (GuestAddrs.header_validate_post_merge + 628)
              (GuestAddrs.header_validate_post_merge + 44)) = K + 628 from by
          rw [show brOff (GuestAddrs.header_validate_post_merge + 628)
              (GuestAddrs.header_validate_post_merge + 44) =
              (584 : BitVec 13) from by decide,
            show signExtend13 (584 : BitVec 13) = (584 : Word) from by decide,
            BitVec.add_assoc,
            show (44 : Word) + (584 : Word) = (628 : Word) from by decide]]
        at h11
      have hmem11 :=
        CodeReq.ofProg_mem_at K (K + 44) k67Prog 11
          (.BNE .x12 .x0 (brOff
            (GuestAddrs.header_validate_post_merge + 628)
            (GuestAddrs.header_validate_post_merge + 44)))
          (by rw [show BitVec.ofNat 64 (4 * 11) = (44 : Word) from by decide])
          (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)
      have h11C := cpsBranchWithin_extend_code
        (fun a' i h => k67_mono a' i (hmem11 a' i h)) h11
      have hntake := cpsBranchWithin_ntakenStripPure2 h11C (fun _ hQf => by
        obtain ⟨_, _, _, _, _, hBP⟩ := hQf
        exact absurd ((sepConj_pure_right _).1 hBP).2 (by decide))
      have hfall := k67PrologueFall sp0 base omConst v10
        (base + BitVec.ofNat 64 bytes.length)
        (BitVec.ofNat 64 bytes.length) v18 v19 v21
        (k67PrologueVals ret v8 v9 v18 v19 v20) bytes
      let Fn : Assertion :=
        (.x1 ↦ᵣ (K + 44)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        (.x8 ↦ᵣ base) ** (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ v21) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          (k67PrologueVals ret v8 v9 v18 v19 v20) **
        bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)
      have hFn : Fn.pcFree := by
        dsimp only [Fn]
        repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
          | exact bytesRegion_pcFree _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | apply pcFree_sepConj
      have hntakeF : cpsTripleWithin 1 (K + 44) (K + 48) fullCode
          (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** Fn)
          (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** Fn) :=
        cpsTripleWithin_frameR Fn hFn hntake
      have hseq := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by dsimp only [Fn] at hp ⊢; xperm_hyp hp)
        hntakeF hfall
      apply cpsNBranchWithin_mono_nSteps
        (show 1 + 2 ≤ 1 + 2 by omega)
      apply cpsNBranchWithin_of_triple
        (Q := fun h => ∃ startOff : Nat,
          (k67FuelInv sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21
            (cycleFuel startOff bytes.length) **
            ⌜startOff ≤ bytes.length⌝) h)
        (by apply List.Mem.head)
      refine cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Fn]; xperm_hyp hp) ?_ hseq
      intro h hq
      have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 :=
        EvmAsm.Evm64.signExtend12_ofNat_small (m := 1) (by omega)
      cases hsucc with
      | inl hshort =>
        obtain ⟨hv10, hlen0, _, _, _⟩ := hshort
        refine ⟨1, (sepConj_pure_right _).2 ⟨?_, by omega⟩⟩
        unfold k67FuelInv
        refine ⟨0, 1, 0, bytes.length, bytes.length, ?_⟩
        apply (sepConj_pure_right _).2
        refine ⟨?_, rfl, by omega, by omega,
          RlpListNthItemSAsm.StrictPrefix.zero,
          fun h2 => absurd h2 (by omega), fun h8 => absurd h8 (by omega)⟩
        unfold k67LoopInv
        simp only []
        simp only [show ((0 : Nat) ≤ 1) ↔ True from by decide, if_true]
        rw [show BitVec.ofNat 64 0 = (0 : Word) from by decide]
        rw [hv10, hse] at hq
        have hP : (((.x18 ↦ᵣ (base + BitVec.ofNat 64 1)) ** (.x19 ↦ᵣ (base +
            BitVec.ofNat 64 bytes.length)) ** (.x20 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 +
              signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) **
            (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x21 ↦ᵣ v21) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              (k67PrologueVals ret v8 v9 v18 v19 v20) **
            bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
            ((.x1 ↦ᵣ (K + 44)) ** (.x10 ↦ᵣ (base + BitVec.ofNat 64 1)) **
              (.x11 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)))) h := by
          xperm_hyp hq
        have hconv := sepConj_mono_right
          (k67Pins3_to_regOwns (K + 44) (base + BitVec.ofNat 64 1)
            (base + BitVec.ofNat 64 bytes.length)) h hP
        xperm_hyp hconv
      | inr hlong =>
        obtain ⟨hv10, hlen0, _, hult2, hfit2, _, _, hfitE⟩ := hlong
        have hfitE' : base +
            (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + (1 : Word)) +
            BitVec.ofNat 64 (EvmAsm.EL.RLP.Nat.fromBytesBE
              (List.take (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)
                (List.drop 1 bytes))) =
            base + BitVec.ofNat 64 bytes.length := hfitE
        refine ⟨(((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat + 1),
          (sepConj_pure_right _).2 ⟨?_, ?_⟩⟩
        · unfold k67FuelInv
          refine ⟨0, (((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat + 1), 0,
            bytes.length, bytes.length, ?_⟩
          apply (sepConj_pure_right _).2
          refine ⟨?_, rfl, ?_, by omega,
            RlpListNthItemSAsm.StrictPrefix.zero,
            fun h2 => absurd h2 (by omega), fun h8 => absurd h8 (by omega)⟩
          · unfold k67LoopInv
            simp only []
            simp only [show ((0 : Nat) ≤ 1) ↔ True from by decide, if_true]
            rw [show BitVec.ofNat 64 0 = (0 : Word) from by decide]
            rw [hv10] at hq
            have hid : base +
                (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)) =
                base + BitVec.ofNat 64
                  (((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat + 1) := by
              rw [hse]
              bv_omega
            rw [hid] at hq
            have hP : (((.x18 ↦ᵣ (base + BitVec.ofNat 64
                (((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat + 1))) **
                (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
                (.x20 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
                (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
                (.x8 ↦ᵣ base) **
                (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x21 ↦ᵣ v21) **
                regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
                regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
                regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
                frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
                  (k67PrologueVals ret v8 v9 v18 v19 v20) **
                bytesRegion base bytes **
                bytesRegion omConst (k67OmBytes)) **
                ((.x1 ↦ᵣ (K + 44)) ** (.x10 ↦ᵣ (base + BitVec.ofNat 64
                  (((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat + 1))) **
                  (.x11 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)))) h := by
              xperm_hyp hq
            have hconv := sepConj_mono_right
              (k67Pins3_to_regOwns (K + 44) (base + BitVec.ofNat 64
                (((bytes[0]'hoff).zeroExtend 64 - 0xf7).toNat + 1))
                (base + BitVec.ofNat 64 bytes.length)) h hP
            xperm_hyp hconv
          · simp only [BitVec.ult, decide_eq_true_eq] at hult2 hfit2
            rw [hse] at hfit2 hfitE
            have hb0 : ((bytes[0]'hoff).zeroExtend 64).toNat =
                (bytes[0]'hoff).toNat := EvmAsm.Rv64.SAsm.toNat_zeroExtend_byte _
            have hb0' : (bytes[0]'hoff).toNat < 256 := (bytes[0]'hoff).isLt
            have hge : 248 ≤ (bytes[0]'hoff).toNat := by
              rw [hb0, show (0xf8 : Word).toNat = 248 from by decide] at hult2
              omega
            have hll : (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 8 := by
              rw [BitVec.toNat_sub, hb0,
                show (0xf7 : Word).toNat = 247 from by decide]
              omega
            have hdecl := EvmAsm.EL.RLP.Nat.fromBytesBE_lt
              ((bytes.drop 1).take
                (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
            rw [List.length_take, List.length_drop] at hdecl
            by_cases hbig : (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 1) ≤
                bytes.length
            · exact hbig
            · exfalso
              have hlen8 : bytes.length ≤ 8 := by omega
              have hdecl2 := hdecl.trans_le
                (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))
              have hdecl3 : EvmAsm.EL.RLP.Nat.fromBytesBE
                  ((bytes.drop 1).take
                    (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) <
                  256 ^ 7 := hdecl2.trans_le
                (Nat.pow_le_pow_right (by decide) (by omega))
              clear hsetup hsetupN hseq hq
              bv_omega
        · simp only [BitVec.ult, decide_eq_true_eq] at hult2 hfit2
          rw [hse] at hfit2 hfitE
          have hb0 : ((bytes[0]'hoff).zeroExtend 64).toNat =
              (bytes[0]'hoff).toNat := EvmAsm.Rv64.SAsm.toNat_zeroExtend_byte _
          have hb0' : (bytes[0]'hoff).toNat < 256 := (bytes[0]'hoff).isLt
          have hge : 248 ≤ (bytes[0]'hoff).toNat := by
            rw [hb0, show (0xf8 : Word).toNat = 248 from by decide] at hult2
            omega
          have hll : (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 8 := by
            rw [BitVec.toNat_sub, hb0,
              show (0xf7 : Word).toNat = 247 from by decide]
            omega
          have hdecl := EvmAsm.EL.RLP.Nat.fromBytesBE_lt
            ((bytes.drop 1).take
              (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
          rw [List.length_take, List.length_drop] at hdecl
          by_cases hbig : (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 1) ≤
              bytes.length
          · exact hbig
          · exfalso
            have hlen8 : bytes.length ≤ 8 := by omega
            have hdecl2 := hdecl.trans_le
              (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))
            have hdecl3 : EvmAsm.EL.RLP.Nat.fromBytesBE
                ((bytes.drop 1).take
                  (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) <
                256 ^ 7 := hdecl2.trans_le
              (Nat.pow_le_pow_right (by decide) (by omega))
            clear hsetup hsetupN hseq hq
            bv_omega
  exact cpsTripleWithin_seq_cpsNBranchWithin_same_cr hsetupN hnode

/-! ## Front assembly: init branch folded through the field-scan loop -/

/-- Rotate the head exit of an N-branch to the end of the exit list.  The
    reachability semantics is order-insensitive, so this is a pure list
    manipulation. -/
theorem k67NBranch_rotate {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {l : Word} {Q : Assertion}
    {rest : List (Word × Assertion)} :
    cpsNBranchWithin n entry cr P ((l, Q) :: rest) →
    cpsNBranchWithin n entry cr P (rest ++ [(l, Q)]) := by
  intro h R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, exit, hexit, hpc', hpost⟩ := h R hR s hcr hPR hpc
  refine ⟨k, hk, s', hstep, exit, ?_, hpc', hpost⟩
  simp only [List.mem_cons] at hexit
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hexit with he | he
  · exact Or.inr he
  · exact Or.inl he

/-- Front assembly: the init branch (prologue + `rlp_walk_init` + dispatch)
    composed with the field-scan loop fold.  From the routine entry state,
    control reaches one of the three loop stations (difficulty at `K + 604`,
    walk failure at `K + 628`, clean exit at `K + 116`) or the init-failure
    station at `K + 628`.  The loop stations carry the walked-chain start
    offset existentially. -/
theorem k67FrontStations (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (ret v8 v9 v18 v19 v20 v21 v12 v5 v6 v7 v28 v29 v30 v31 : Word)
    (hsalign : base.toNat % 8 = 0)
    (hoff : 0 < bytes.length)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true)
    (hll_len : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length)
    (hll_over : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      base.toNat +
        (0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤
        2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      ∀ k, k < ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (base + BitVec.ofNat 64 (0 + 1 + k)) = true) :
    cpsNBranchWithin ((10 + (1 + 81) + (1 + 2)) + 101 * (2 * bytes.length + 1))
      K fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) **
        (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (k67OmBytes) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40))
      [(K + 604, fun h => ∃ startOff : Nat,
          k67Qdiff sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h),
        (K + 628, fun h => ∃ startOff : Nat,
          k67Qfail sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h),
        (K + 116, fun h => ∃ startOff : Nat,
          (k67Qclean sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 **
            ⌜startOff ≤ bytes.length⌝) h),
        (K + 628, k67QfailInit sp0 base omConst bytes v18 v19 v21
          (k67PrologueVals ret v8 v9 v18 v19 v20) hoff)] := by
  have hib := k67InitBranch sp0 base omConst bytes ret v8 v9 v18 v19 v20 v21
    v12 v5 v6 v7 v28 v29 v30 v31 hsalign hoff hover9 hvalid hll_len hll_over
    hll_valid
  have hfold : cpsNBranchWithin (101 * (2 * bytes.length + 1)) (K + 56)
      fullCode
      (fun h => ∃ startOff : Nat,
        (k67FuelInv sp0 base omConst bytes startOff
          (k67PrologueVals ret v8 v9 v18 v19 v20) v21
          (cycleFuel startOff bytes.length) ** ⌜startOff ≤ bytes.length⌝) h)
      [(K + 604, fun h => ∃ startOff : Nat,
          k67Qdiff sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h),
        (K + 628, fun h => ∃ startOff : Nat,
          k67Qfail sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h),
        (K + 116, fun h => ∃ startOff : Nat,
          (k67Qclean sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 **
            ⌜startOff ≤ bytes.length⌝) h)] := by
    apply cpsNBranchWithin_exists_pre; intro startOff
    apply cpsNBranchWithin_pure_pre; intro hstart
    have hb : 101 * (cycleFuel startOff bytes.length + 1) ≤
        101 * (2 * bytes.length + 1) := by
      unfold cycleFuel remainingBytes; omega
    refine cpsNBranchWithin_mono_nSteps hb ?_
    refine cpsNBranchWithin_weaken_posts
      (k67LoopFold sp0 base omConst bytes startOff
        (k67PrologueVals ret v8 v9 v18 v19 v20) v21 hsalign hover9 hvalid
        (cycleFuel startOff bytes.length)) ?_
    intro ex hex
    simp only [List.mem_cons] at hex
    rcases hex with hex | hex | hex | hnil
    · subst hex
      exact ⟨(K + 604, fun h => ∃ startOff : Nat,
          k67Qdiff sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h),
        List.Mem.head _, rfl, fun h hq => ⟨startOff, hq⟩⟩
    · subst hex
      exact ⟨(K + 628, fun h => ∃ startOff : Nat,
          k67Qfail sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h),
        List.Mem.tail _ (List.Mem.head _), rfl, fun h hq => ⟨startOff, hq⟩⟩
    · subst hex
      exact ⟨(K + 116, fun h => ∃ startOff : Nat,
          (k67Qclean sp0 base omConst bytes startOff
            (k67PrologueVals ret v8 v9 v18 v19 v20) v21 **
            ⌜startOff ≤ bytes.length⌝) h),
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl,
        fun h hq => ⟨startOff, (sepConj_pure_right _).2 ⟨hq, hstart⟩⟩⟩
    · simp at hnil
  exact cpsNBranchWithin_extend_head_nbranch hib hfold

/-! ## §2b  Post-loop continuation and the six-station assembly -/

/-- Continuation of the clean loop-exit station at `K + 116` through the merged
    post-loop compare block: the semantic facts carried by `k67Qclean`
    (walked chain plus field decodes) discharge every `k67PostLoop` premise.
    The `omConst` region is instantiated with the real `empty_ommers_hash`
    address, because the constant-region byte-validity premise is only
    derivable concretely. -/
theorem k67PostLoopStations (sp0 base : Word) (bytes : List (BitVec 8))
    (v21 : Word) (svals : Reg → Word)
    (hsalign : base.toNat % 8 = 0)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin 124 (K + 116) fullCode
      (fun h => ∃ startOff : Nat,
        (k67Qclean sp0 base ((GuestAddrs.empty_ommers_hash : Word)) bytes
          startOff svals v21 ** ⌜startOff ≤ bytes.length⌝) h)
      [(K + 596, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
          (v29 v30 v31 : Word),
        k67QOk sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
          (base + BitVec.ofNat 64 (n1 - base).toNat)
          (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
          ((n1 - l1 - base).toNat) v29 v30 v31 v21 svals h),
        (K + 620, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
          (v29 v30 v31 : Word),
        k67QOmmersFail sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
          (base + BitVec.ofNat 64 (n1 - base).toNat)
          (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
          ((n1 - l1 - base).toNat) v29 v30 v31 v21 svals h),
        (K + 612, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
          (v28 v29 v30 v31 : Word),
        k67QNonceFail sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
          (base + BitVec.ofNat 64 (n1 - base).toNat)
          (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
          ((n1 - l1 - base).toNat) v28 v29 v30 v31 v21 svals h)] := by
  apply cpsNBranchWithin_exists_pre; intro startOff
  apply cpsNBranchWithin_pure_pre; intro hstart
  apply cpsNBranchWithin_weaken_pre (fun h hp => by
    unfold k67Qclean at hp; exact hp)
  apply cpsNBranchWithin_exists_pre; intro cur14
  apply cpsNBranchWithin_exists_pre; intro next14
  apply cpsNBranchWithin_exists_pre; intro len14
  apply cpsNBranchWithin_exists_pre; intro n1
  apply cpsNBranchWithin_exists_pre; intro l1
  apply cpsNBranchWithin_exists_pre; intro n7
  apply cpsNBranchWithin_exists_pre; intro v6
  apply cpsNBranchWithin_exists_pre; intro v7
  apply cpsNBranchWithin_exists_pre; intro v28
  apply cpsNBranchWithin_exists_pre; intro v29
  apply cpsNBranchWithin_exists_pre; intro v30
  apply cpsNBranchWithin_exists_pre; intro v31
  apply cpsNBranchWithin_pure_pre
  rintro ⟨hp15, hsni1, hsni7, hsni14, hdec14, hcur14, hnext14le⟩
  cases hsni1 with
  | succ _ _ n0 _ _ _ hitem0 hsni0 =>
    cases hsni0 with
    | zero _ _ _ hitem1 =>
      obtain ⟨-, -, hn0le⟩ :=
        BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hitem0 hstart
          hover9
      obtain ⟨hn1E, -, hn1le⟩ :=
        BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hitem1 hn0le
          hover9
      obtain ⟨hnextE, -, -⟩ :=
        BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hdec14 hcur14
          hover9
      obtain ⟨hspan14E, -, hspan14le⟩ :=
        rlpItemDecode_field0_content_span hdec14 hcur14 hover9
      obtain ⟨hspan1E, -, hspan1le⟩ :=
        rlpItemDecode_field0_content_span hitem1 hn0le hover9
      have hcsE14 : len14 = (8 : Word) →
          next14 - len14 =
            base + BitVec.ofNat 64 (next14 - len14 - base).toNat :=
        fun _ => hspan14E
      have hib14 : len14 = (8 : Word) →
          (next14 - len14 - base).toNat + 8 ≤ bytes.length := by
        intro hlen
        have hl : len14.toNat = 8 := by rw [hlen]; decide
        rw [hl] at hspan14le; exact hspan14le
      have haddr8 : len14 = (8 : Word) → ∀ (j' : Nat) (_hj' : j' < 8),
          next14 - (8 : Word) + signExtend12 (BitVec.ofNat 12 j') =
            base + BitVec.ofNat 64 ((next14 - len14 - base).toNat + j') := by
        intro hlen j' _hj'
        rw [EvmAsm.Evm64.signExtend12_ofNat_small (by omega)]
        have h1 := hspan14E
        rw [hlen] at h1
        have hb : (next14 - len14 - base).toNat + 8 ≤ bytes.length := by
          have hl : len14.toNat = 8 := by rw [hlen]; decide
          rw [hl] at hspan14le; exact hspan14le
        bv_omega
      have hcsE1 : BitVec.ofNat 64 l1.toNat = (32 : Word) →
          base + BitVec.ofNat 64 (n1 - base).toNat - (32 : Word) =
            base + BitVec.ofNat 64 (n1 - l1 - base).toNat := by
        intro hlen1
        have hl1 : l1.toNat = 32 := by bv_omega
        have hl1W : l1 = (32 : Word) := by bv_omega
        rw [← hn1E, hl1W]
        rw [hl1W] at hspan1E
        exact hspan1E
      have hib1 : BitVec.ofNat 64 l1.toNat = (32 : Word) →
          (n1 - l1 - base).toNat + 32 ≤ bytes.length := by
        intro hlen1
        have hl1 : l1.toNat = 32 := by bv_omega
        rw [hl1] at hspan1le; exact hspan1le
      have haddr32 : BitVec.ofNat 64 l1.toNat = (32 : Word) →
          ∀ (j' : Nat) (_hj' : j' < 32),
          base + BitVec.ofNat 64 (n1 - base).toNat - (32 : Word) +
              signExtend12 (BitVec.ofNat 12 j') =
            base + BitVec.ofNat 64 ((n1 - l1 - base).toNat + j') := by
        intro hlen1 j' _hj'
        rw [EvmAsm.Evm64.signExtend12_ofNat_small (by omega), hcsE1 hlen1]
        have hb := hib1 hlen1
        bv_omega
      have hvalid2 : ∀ (j' : Nat) (_hj' : j' < 32),
          isValidByteAccess (((GuestAddrs.empty_ommers_hash : Word)) +
            BitVec.ofNat 64 j') = true := by
        intro j' hj'
        interval_cases j' <;> decide
      have htakenN : ∀ (j' : Nat) (_hj' : j' < 8),
          (K + BitVec.ofNat 64 (132 + 8 * j')) +
              signExtend13 (EvmAsm.Codegen.brOff
                (GuestAddrs.header_validate_post_merge + 612)
                (GuestAddrs.header_validate_post_merge + 132 + 8 * j')) =
            K + 612 := by
        intro j' hj'
        interval_cases j' <;> decide
      have htakenO : ∀ (j' : Nat) (_hj' : j' < 32),
          (K + BitVec.ofNat 64 (212 + 12 * j') + 8) +
              signExtend13 (EvmAsm.Codegen.brOff
                (GuestAddrs.header_validate_post_merge + 620)
                (GuestAddrs.header_validate_post_merge + 220 + 12 * j')) =
            K + 620 := by
        intro j' hj'
        interval_cases j' <;> decide
      have hlookLBUN : ∀ (j' : Nat) (hj' : j' < 8),
          k67Prog.get ⟨32 + 2 * j', by rw [k67_length]; omega⟩ =
            Instr.LBU .x7 .x6 (BitVec.ofNat 12 j') := by
        intro j' hj'
        interval_cases j' <;> rfl
      have hlookBNEN : ∀ (j' : Nat) (hj' : j' < 8),
          k67Prog.get ⟨33 + 2 * j', by rw [k67_length]; omega⟩ =
            Instr.BNE .x7 .x0 (EvmAsm.Codegen.brOff
              (GuestAddrs.header_validate_post_merge + 612)
              (GuestAddrs.header_validate_post_merge + 132 + 8 * j')) := by
        intro j' hj'
        interval_cases j' <;> rfl
      have hlookLBU1 : ∀ (j' : Nat) (hj' : j' < 32),
          k67Prog.get ⟨53 + 3 * j', by rw [k67_length]; omega⟩ =
            Instr.LBU .x7 .x6 (BitVec.ofNat 12 j') := by
        intro j' hj'
        interval_cases j' <;> rfl
      have hlookLBU2 : ∀ (j' : Nat) (hj' : j' < 32),
          k67Prog.get ⟨54 + 3 * j', by rw [k67_length]; omega⟩ =
            Instr.LBU .x28 .x5 (BitVec.ofNat 12 j') := by
        intro j' hj'
        interval_cases j' <;> rfl
      have hlookBNEO : ∀ (j' : Nat) (hj' : j' < 32),
          k67Prog.get ⟨55 + 3 * j', by rw [k67_length]; omega⟩ =
            Instr.BNE .x7 .x28 (EvmAsm.Codegen.brOff
              (GuestAddrs.header_validate_post_merge + 620)
              (GuestAddrs.header_validate_post_merge + 220 + 12 * j')) := by
        intro j' hj'
        interval_cases j' <;> rfl
      have hmain := k67PostLoop sp0 base
        ((GuestAddrs.empty_ommers_hash : Word))
        (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
        (base + BitVec.ofNat 64 (n1 - base).toNat)
        (BitVec.ofNat 64 l1.toNat)
        v6 v7 v28 v29 v30 v31 v21 svals
        ((next14 - len14 - base).toNat) ((n1 - l1 - base).toNat)
        hsalign (by omega) hvalid hcsE14 hib14 hib1 hcsE1 hvalid2 rfl haddr8
        haddr32
        (fun j' => EvmAsm.Codegen.brOff
          (GuestAddrs.header_validate_post_merge + 612)
          (GuestAddrs.header_validate_post_merge + 132 + 8 * j'))
        (fun j' => EvmAsm.Codegen.brOff
          (GuestAddrs.header_validate_post_merge + 620)
          (GuestAddrs.header_validate_post_merge + 220 + 12 * j'))
        htakenN htakenO hlookLBUN hlookBNEN hlookLBU1 hlookLBU2 hlookBNEO
      refine cpsNBranchWithin_weaken_pre
        (P := k67PLPre sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
          (base + BitVec.ofNat 64 (n1 - base).toNat)
          (BitVec.ofNat 64 l1.toNat) v6 v7 v28 v29 v30 v31 v21 svals)
        (fun h hp => by dsimp only [k67PLPre]; xperm_hyp hp) ?_
      refine cpsNBranchWithin_weaken_posts hmain ?_
      intro ex hex
      simp only [List.mem_cons] at hex
      rcases hex with hex | hex | hex | hnil
      · subst hex
        exact ⟨(K + 596, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
            (v29 v30 v31 : Word),
          k67QOk sp0 base ((GuestAddrs.empty_ommers_hash : Word))
            (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
            (base + BitVec.ofNat 64 (n1 - base).toNat)
            (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
            ((n1 - l1 - base).toNat) v29 v30 v31 v21 svals h),
          List.Mem.head _, rfl,
          fun h hq => ⟨startOff, next14, len14, n1, l1, v29, v30, v31, hq⟩⟩
      · subst hex
        exact ⟨(K + 620, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
            (v29 v30 v31 : Word),
          k67QOmmersFail sp0 base ((GuestAddrs.empty_ommers_hash : Word))
            (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
            (base + BitVec.ofNat 64 (n1 - base).toNat)
            (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
            ((n1 - l1 - base).toNat) v29 v30 v31 v21 svals h),
          List.Mem.tail _ (List.Mem.head _), rfl,
          fun h hq => ⟨startOff, next14, len14, n1, l1, v29, v30, v31, hq⟩⟩
      · subst hex
        exact ⟨(K + 612, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
            (v28 v29 v30 v31 : Word),
          k67QNonceFail sp0 base ((GuestAddrs.empty_ommers_hash : Word))
            (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
            (base + BitVec.ofNat 64 (n1 - base).toNat)
            (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
            ((n1 - l1 - base).toNat) v28 v29 v30 v31 v21 svals h),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl,
          fun h hq =>
            ⟨startOff, next14, len14, n1, l1, v28, v29, v30, v31, hq⟩⟩
      · simp at hnil

/-- The full front of `header_validate_post_merge`, assembled: from the
    routine entry state at `K`, control reaches one of the six stations —
    the three post-loop exits, the init-failure stub, or the two loop-exit
    failure stations. -/
theorem k67ToStations (sp0 base : Word) (bytes : List (BitVec 8))
    (ret v8 v9 v18 v19 v20 v21 v12 v5 v6 v7 v28 v29 v30 v31 : Word)
    (hsalign : base.toNat % 8 = 0)
    (hoff : 0 < bytes.length)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true)
    (hll_len : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length)
    (hll_over : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      base.toNat +
        (0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤
        2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      ∀ k, k < ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (base + BitVec.ofNat 64 (0 + 1 + k)) = true) :
    cpsNBranchWithin
      ((10 + (1 + 81) + (1 + 2)) + 101 * (2 * bytes.length + 1) + 124) K
      fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) **
        (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes **
        bytesRegion ((GuestAddrs.empty_ommers_hash : Word)) (k67OmBytes) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40))
      [(K + 596, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
          (v29 v30 v31 : Word),
        k67QOk sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
          (base + BitVec.ofNat 64 (n1 - base).toNat)
          (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
          ((n1 - l1 - base).toNat) v29 v30 v31 v21
          (k67PrologueVals ret v8 v9 v18 v19 v20) h),
        (K + 620, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
          (v29 v30 v31 : Word),
        k67QOmmersFail sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
          (base + BitVec.ofNat 64 (n1 - base).toNat)
          (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
          ((n1 - l1 - base).toNat) v29 v30 v31 v21
          (k67PrologueVals ret v8 v9 v18 v19 v20) h),
        (K + 612, fun h => ∃ (_startOff : Nat) (next14 len14 n1 l1 : Word)
          (v28 v29 v30 v31 : Word),
        k67QNonceFail sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          (base + BitVec.ofNat 64 bytes.length) bytes next14 len14
          (base + BitVec.ofNat 64 (n1 - base).toNat)
          (BitVec.ofNat 64 l1.toNat) ((next14 - len14 - base).toNat)
          ((n1 - l1 - base).toNat) v28 v29 v30 v31 v21
          (k67PrologueVals ret v8 v9 v18 v19 v20) h),
        (K + 628, k67QfailInit sp0 base ((GuestAddrs.empty_ommers_hash : Word))
          bytes v18 v19 v21 (k67PrologueVals ret v8 v9 v18 v19 v20) hoff),
        (K + 604, fun h => ∃ startOff : Nat,
          k67Qdiff sp0 base ((GuestAddrs.empty_ommers_hash : Word)) bytes
            startOff (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h),
        (K + 628, fun h => ∃ startOff : Nat,
          k67Qfail sp0 base ((GuestAddrs.empty_ommers_hash : Word)) bytes
            startOff (k67PrologueVals ret v8 v9 v18 v19 v20) v21 h)] := by
  have hfs := k67FrontStations sp0 base
    ((GuestAddrs.empty_ommers_hash : Word)) bytes ret v8 v9 v18 v19 v20 v21
    v12 v5 v6 v7 v28 v29 v30 v31 hsalign hoff hover9 hvalid hll_len hll_over
    hll_valid
  have hpost := k67PostLoopStations sp0 base bytes v21
    (k67PrologueVals ret v8 v9 v18 v19 v20) hsalign hover9 hvalid
  exact cpsNBranchWithin_extend_head_nbranch
    (k67NBranch_rotate (k67NBranch_rotate hfs)) hpost
