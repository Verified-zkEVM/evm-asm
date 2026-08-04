/-
  EvmAsm.Codegen.Programs.CheckGasLimitBridge

  GH #11349 — the reference tie for `check_gas_limit`, row 7 of
  `docs/leaf-routine-targets.md`.

  WHAT ALREADY EXISTED. `checkGasLimit_spec` (`CheckGasLimitSAsm.lean:63`) is already a
  byte-transparent `cpsTripleWithin 10` **at the linked guest address** — this row needed
  no new machine proof at all, which is the general finding from the #11344–#11352 batch:
  seven of the nine routines were already proven and what was missing was the tie to the
  reference.

  WHAT WAS MISSING. The post pins `a0` to `cglStatus` (`:53`), a local three-valued
  verdict. The reference is `SpecRef.check_gas_limit` (`SpecRef/SeamShell.lean:200`), a
  `Bool` over unbounded `Uint`. Nothing related them.

  ⭐ WHY THIS NEEDS NO OVERFLOW HYPOTHESIS — the interesting part. The reference is
  written with two *additions*:

      if gas_limit ≥ parent + delta      then false
      else if gas_limit + delta ≤ parent then false

  and over `Uint = Nat` those cannot overflow, whereas the guest works in u64 where they
  could. A naive bridge would therefore carry an envelope hypothesis and the row would be
  `domainRestricted`. It does not need one, because **the guest never forms either sum**:
  it computes `|new − parent|` (`cglDelta`, `:50`) and compares against `parent / 1024`.
  Those two guards are together equivalent to the single inequality `|gl − pl| < delta`,
  so the addition never has to happen on either side. `cglDelta`'s subtraction is
  wrap-free by construction — it subtracts the smaller from the larger.

  ⇒ full-domain agreement, verdict `.agrees`, and no side condition whatsoever. Worth
  recording because the *shape* of the reference invites the opposite conclusion.

  ⚠️ WHAT IS NOT CLAIMED. The guest distinguishes *why* it rejected — `1` for below the
  5000 minimum, `2` for an out-of-range adjustment — and the reference returns a bare
  `false`. That refinement is guest-specific, so the bridge is stated as an **iff on
  acceptance** (`a0 = 0` exactly when the reference accepts) rather than pretending the
  three-valued status has a counterpart.
-/

import EvmAsm.Codegen.Programs.CheckGasLimitSAsm
import EvmAsm.Stateless.SpecRef.SeamShell

namespace EvmAsm.Codegen

open EvmAsm.Rv64

namespace CheckGasLimitSAsm

/-- The adjustment magnitude, read as a natural. The subtraction is wrap-free because
    `cglDelta` always subtracts the smaller operand from the larger. -/
theorem cglDelta_toNat (nl pl : Word) :
    (cglDelta nl pl).toNat
      = if pl.toNat < nl.toNat then nl.toNat - pl.toNat else pl.toNat - nl.toNat := by
  unfold cglDelta
  by_cases h : BitVec.ult pl nl
  · have hlt : pl.toNat < nl.toNat := BitVec.ult_iff_toNat_lt.mp h
    rw [if_pos h, if_pos hlt,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_of_lt hlt))]
  · have hge : ¬ pl.toNat < nl.toNat := fun hc =>
      h (BitVec.ult_iff_toNat_lt.mpr hc)
    rw [if_neg h, if_neg hge,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_of_not_lt hge))]

/-- The `parent / 1024` allowance, read as a natural. -/
theorem cglAllowance_toNat (pl : Word) : (pl >>> 10).toNat = pl.toNat / 1024 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The reference's two additions, collapsed to the single magnitude test the guest
    performs. Stated purely over `Nat` so the arithmetic is visible to `omega` — this is
    where "no envelope hypothesis is needed" is actually discharged. -/
private theorem cgl_nat_iff (g p : Nat) :
    (¬ g < 5000 ∧ (if p < g then g - p else p - g) < p / 1024)
      ↔ EvmAsm.Stateless.SpecRef.check_gas_limit g p = true := by
  unfold EvmAsm.Stateless.SpecRef.check_gas_limit
  simp only [EvmAsm.Stateless.SpecRef.GasCosts.LIMIT_ADJUSTMENT_FACTOR,
    EvmAsm.Stateless.SpecRef.GasCosts.LIMIT_MINIMUM]
  have hcases : ∀ d : Nat,
      (if p < g then g - p else p - g) = d →
      ((¬ g < 5000 ∧ d < p / 1024)
        ↔ (if g ≥ p + p / 1024 then false
            else if g + p / 1024 ≤ p then false
            else if g < 5000 then false else true) = true) := by
    intro d hdef
    rcases Nat.lt_or_ge p g with hc | hc
    · rw [if_pos hc] at hdef
      by_cases h1 : g ≥ p + p / 1024
      · rw [if_pos h1]
        simp only [Bool.false_eq_true, iff_false]
        rintro ⟨-, hb⟩; omega
      · rw [if_neg h1]
        by_cases h2 : g + p / 1024 ≤ p
        · rw [if_pos h2]
          simp only [Bool.false_eq_true, iff_false]
          rintro ⟨-, -⟩; omega
        · rw [if_neg h2]
          by_cases h3 : g < 5000
          · rw [if_pos h3]
            simp only [Bool.false_eq_true, iff_false]
            rintro ⟨ha, -⟩; omega
          · rw [if_neg h3]
            simp only [iff_true]
            exact ⟨h3, by omega⟩
    · rw [if_neg (Nat.not_lt.mpr hc)] at hdef
      by_cases h1 : g ≥ p + p / 1024
      · rw [if_pos h1]
        simp only [Bool.false_eq_true, iff_false]
        rintro ⟨-, hb⟩; omega
      · rw [if_neg h1]
        by_cases h2 : g + p / 1024 ≤ p
        · rw [if_pos h2]
          simp only [Bool.false_eq_true, iff_false]
          rintro ⟨-, hb⟩; omega
        · rw [if_neg h2]
          by_cases h3 : g < 5000
          · rw [if_pos h3]
            simp only [Bool.false_eq_true, iff_false]
            rintro ⟨ha, -⟩; omega
          · rw [if_neg h3]
            simp only [iff_true]
            exact ⟨h3, by omega⟩
  exact hcases _ rfl

/-- ⭐ **The acceptance bridge.** The routine returns `0` exactly when the reference
    accepts the pair. No envelope hypothesis: see this module's header on why the
    reference's two additions never have to be formed. -/
theorem cglStatus_eq_zero_iff (nl pl : Word) :
    cglStatus nl pl = 0
      ↔ EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true := by
  rw [← cgl_nat_iff]
  unfold cglStatus
  by_cases hmin : BitVec.ult nl (5000 : Word)
  · have hm : nl.toNat < 5000 := by
      have := BitVec.ult_iff_toNat_lt.mp hmin
      simpa using this
    rw [if_pos hmin]
    simp [hm]
  · have hm : ¬ nl.toNat < 5000 := fun hcc =>
      hmin (BitVec.ult_iff_toNat_lt.mpr (by simpa using hcc))
    rw [if_neg hmin]
    by_cases hdlt : BitVec.ult (cglDelta nl pl) (pl >>> 10)
    · have hlt := BitVec.ult_iff_toNat_lt.mp hdlt
      rw [cglDelta_toNat, cglAllowance_toNat] at hlt
      rw [if_pos hdlt]
      simp [hm, hlt]
    · have hn : ¬ (cglDelta nl pl).toNat < (pl >>> 10).toNat := fun hcc =>
        hdlt (BitVec.ult_iff_toNat_lt.mpr hcc)
      rw [cglDelta_toNat, cglAllowance_toNat] at hn
      rw [if_neg hdlt]
      simp [hm, hn]

/-! ## The port's clause-2 restatement, proved rather than relied upon

    `fork.py:1259-1264` writes the lower guard as `gas_limit ≤ parent − delta`; the
    `SpecRef` port writes `gas_limit + delta ≤ parent`. That is a deliberate
    improvement — Python ints are arbitrary-precision so `parent − delta` is safe there,
    whereas a `Uint` subtraction would truncate on underflow — but it is an
    *algebraic* equivalence, not a syntactic identity, and it holds only because
    `delta ≤ parent`.

    ⭐ That is the one place this correspondence could silently diverge from the Python
    while looking faithful, so it is proved here. The general form states the dependency
    explicitly: a future change to `LIMIT_ADJUSTMENT_FACTOR` keeps the equivalence for
    any factor ≥ 1, and a port that mirrored clause 2 literally with a truncating
    subtraction would need exactly this side condition. -/

/-- The equivalence, with its hypothesis exposed: moving the subtrahend across is sound
    exactly when it does not underflow. -/
theorem sub_le_iff_le_add_of_le (g p d : Nat) (hd : d ≤ p) :
    (g ≤ p - d) ↔ (g + d ≤ p) := by omega

/-- ⭐ The instance the port relies on. `delta = parent / 1024 ≤ parent` for any divisor,
    so the port's clause 2 and the Python's clause 2 accept exactly the same pairs. -/
theorem clause2_port_faithful (g p : Nat) :
    (g ≤ p - p / EvmAsm.Stateless.SpecRef.GasCosts.LIMIT_ADJUSTMENT_FACTOR)
      ↔ (g + p / EvmAsm.Stateless.SpecRef.GasCosts.LIMIT_ADJUSTMENT_FACTOR ≤ p) :=
  sub_le_iff_le_add_of_le g p _ (Nat.div_le_self _ _)

-- the underflow the port avoids is real: at parent = 0 the Python form would truncate
#guard (decide (5 ≤ 0 - 0 / 1024)) == (decide (5 + 0 / 1024 ≤ 0))
#guard (decide (0 ≤ 0 - 0 / 1024)) == (decide (0 + 0 / 1024 ≤ 0))

/-! ## Non-vacuity pins

    Both sides evaluated at the boundaries the rule turns on: the 5000 minimum, and the
    `parent / 1024` window on each side, including the exact boundary value where `<`
    versus `≤` would diverge. -/

section Pins

private def w (n : Nat) : Word := BitVec.ofNat 64 n
private def agree (nl pl : Nat) : Bool :=
  (cglStatus (w nl) (w pl) == 0) == EvmAsm.Stateless.SpecRef.check_gas_limit nl pl

-- below the 5000 minimum: rejected by both, whatever the adjustment
#guard agree 4999 1024000
#guard cglStatus (w 4999) (w 1024000) != 0
-- parent = 1024000 ⇒ allowance = 1000. Inside the window, both ends.
#guard agree 1024000 1024000
#guard cglStatus (w 1024000) (w 1024000) == 0
#guard agree 1024999 1024000
#guard agree 1023001 1024000
-- exactly at the boundary: `<` not `≤`, so REJECTED. This is the pin that would catch
-- an off-by-one in either direction.
#guard agree 1025000 1024000
#guard cglStatus (w 1025000) (w 1024000) != 0
#guard agree 1023000 1024000
#guard cglStatus (w 1023000) (w 1024000) != 0
-- a large parent, to exercise the division rather than small-number coincidences
#guard agree 30000000 30000000
#guard agree 60000000 30000000

end Pins

/-! ## The consumer — the same triple, acceptance stated against the reference -/

/-- ⭐ **`check_gas_limit` at its linked address, against `SpecRef`.** The same triple as
    `checkGasLimit_spec` — same step bound, same footprint, same preconditions — with the
    post additionally recording that `a0 = 0` holds **exactly** when the reference
    accepts. A post-weakening; the machine proof is untouched.

    The reference appears in the statement, which is what makes this (rather than the
    lemma alone) the theorem the registry row names. -/
theorem checkGasLimit_ref_spec (nl pl ret : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 10 (GuestAddrs.check_gas_limit : Word) ret
      (CodeReq.ofProg (GuestAddrs.check_gas_limit : Word) checkGasLimit_prog)
      (((.x10 : Reg) ↦ᵣ nl) ** ((.x11 : Reg) ↦ᵣ pl) **
        ((.x1 : Reg) ↦ᵣ ret) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      ((((.x10 : Reg) ↦ᵣ cglStatus nl pl) ** ((.x11 : Reg) ↦ᵣ pl) **
        ((.x1 : Reg) ↦ᵣ ret) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7) **
       ⌜cglStatus nl pl = 0
          ↔ EvmAsm.Stateless.SpecRef.check_gas_limit nl.toNat pl.toNat = true⌝) := by
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_)
    (checkGasLimit_spec nl pl ret halignRet)
  exact (sepConj_pure_right h).2 ⟨hq, cglStatus_eq_zero_iff nl pl⟩

end CheckGasLimitSAsm

end EvmAsm.Codegen
