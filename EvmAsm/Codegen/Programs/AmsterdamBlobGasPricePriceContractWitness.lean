import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody10Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody11Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14TerminalSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Composition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundParityComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundQBackComposition
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceU256Sat
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceTaylorTie
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody8Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterFold
import EvmAsm.Rv64.MemSat

set_option maxRecDepth 8000

/-!
  Constructive satisfiability witness for `priceContract` (#12346, K70 seam):
  the `excess = 0` input.  This is a NON-VACUITY witness for one input value,
  not a discharge of the contract: it proves that the machine, from the
  concrete `excess = 0` entry state, runs `priceContract` to the status-0 exit
  in 8271 steps.  Inputs with `excess ≠ 0` are NOT covered here (they require
  the full 495-round fold).

  Route (measured, verified against the per-window specs):
    setup 27  (`price_setup_spec`, PriceK+36 → PriceK+144)
    round 4028 (`taylor_round` at j=0, acc=[D,0,0,0,0,0] with D = taylorDW;
                 the +804 round-zero exit and the 10 overflow exits are dead,
                 only the QBACK backedge fires)
    second loop-head pass 14 (loop_test_or_chainP 13 + loop_test_beqz_branch 1,
                 acc now [0×6] so beqz-taken fires at +804)
    exitdiv+tail 4183 (round_zero_exitdiv_tail_swapped, +804 → +968)
  body total 8252; whole routine 8271 = 1+8+8252+8+1+1 (ABI shell).
  Model: `taylor_price_outcome_zero` gives priceOutcome 0 = (0, natToBeBytes 32 1).
-/

namespace EvmAsm.Codegen.AmsterdamBlobGasPricePriceContractWitness

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat

/-- Drop an exit whose post is absurd (`∀ h, Q h → False`) from an N-branch's
    exit list.  Used to eliminate the dead overflow exits of `taylor_round` at
    `excess = 0`, where each carries a pure that reduces to false. -/
private theorem cpsNBranchWithin_drop_absurd_head
    {nSteps : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {m : Word} {Q : Assertion} {rest : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry cr P ((m, Q) :: rest))
    (hQ : ∀ h, Q h → False) :
    cpsNBranchWithin nSteps entry cr P rest := by
  intro R hRfree s hcr hP hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hRfree s hcr hP hpc
  refine ⟨k, hk, s', hstep, ex, ?_, hpc', hQR⟩
  rw [List.mem_cons] at hmem
  rcases hmem with heq | hrest
  · subst heq
    have hQl := holdsFor_sepConj_elim_left hQR
    obtain ⟨hq, _, hqw⟩ := hQl
    exact (hQ hq hqw).elim
  · exact hrest

/-- Drop every exit except one target from an N-branch's exit list, when each
    other exit's post is absurd.  Collapses the 12-exit `taylor_round` branch at
    `excess = 0` to its single live QBACK exit. -/
private theorem cpsNBranchWithin_drop_all_absurd_except
    {nSteps : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {target : Word × Assertion} {exits : List (Word × Assertion)}
    (htarget : target ∈ exits)
    (hdead : ∀ ex : Word × Assertion, ex ∈ exits → ex ≠ target → ∀ h, ex.2 h → False)
    (h : cpsNBranchWithin nSteps entry cr P exits) :
    cpsNBranchWithin nSteps entry cr P [target] := by
  intro R hRfree s hcr hP hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hRfree s hcr hP hpc
  refine ⟨k, hk, s', hstep, target, ?_, ?_, ?_⟩
  · simp
  · by_cases heq : ex = target
    · subst heq
      exact hpc'
    · exfalso
      obtain ⟨h, hcompat, hsplit⟩ := hQR
      obtain ⟨h1, h2, hd, hu, hex, hR'⟩ := hsplit
      exact hdead ex hmem heq h1 hex
  · by_cases heq : ex = target
    · subst heq
      exact hQR
    · exfalso
      obtain ⟨h, hcompat, hsplit⟩ := hQR
      obtain ⟨h1, h2, hd, hu, hex, hR'⟩ := hsplit
      exact hdead ex hmem heq h1 hex

/-- Generic absurdity: `((X ** (A ** ⌜R⌝)) ** Y)` with `R` false.  The dead
    `taylor_round` exits at `excess = 0` all have this leading shape with a
    pure that reduces to `False`. -/
private theorem absurd_of_false_pure {X A Y : Assertion} {R : Prop} (hR : ¬ R) :
    ∀ h, ((X ** (A ** ⌜R⌝)) ** Y) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hlead, hY⟩ := hx
  obtain ⟨h3, h4, hd1, hu1, hX, hAp⟩ := hlead
  obtain ⟨h5, h6, hd2, hu2, hA, hRq⟩ := hAp
  exact hR hRq.2

/-- The `roundZero` (PriceK+804) exit at `excess = 0`, `acc = [D, 0, 0, 0, 0, 0]`
    is absurd: its `⌜or6 a0..a5 = 0⌝` pure is false since `or6 D 0 0 0 0 0 = D ≠ 0`. -/
private theorem roundZero_exit_absurd (D : Word) (Y : Assertion) (hD : D ≠ (0 : Word)) :
    ∀ h, ((((.x5 ↦ᵣ D) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜D = (0 : Word)⌝) ** Y)) h → False := by
  exact absurd_of_false_pure hD

/-- The terminal (PriceK+964) exit at `iVal = 1` is absurd: its `⌜¬ ult 1 496⌝`
    pure is false since `1 < 496`. -/
private theorem terminal_exit_absurd (iVal : Word) (Y : Assertion) (hlt : BitVec.ult iVal (496 : Word)) :
    ∀ h, ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) ** Y)) h → False := by
  exact absurd_of_false_pure (fun hnot => hnot hlt)

/-- The carry (PriceK+964) exit at `s = [0×6]` is absurd: its `⌜rCry-chain ≠ 0⌝`
    pure is false because the ripple-carry chain is all zeros. -/
private theorem carry_exit_absurd (rCryChain : Word) (Y : Assertion) (hzero : rCryChain = (0 : Word)) :
    ∀ h, ((((.x5 ↦ᵣ rCryChain) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜rCryChain ≠ (0 : Word)⌝) ** Y)) h → False := by
  exact absurd_of_false_pure (by intro hne; exact hne hzero)

/-- `rv64_mulhu a 0 = 0` for any `a`. -/
private theorem rv64_mulhu_zero_right (a : Word) : rv64_mulhu a (0 : Word) = (0 : Word) := by
  simp [rv64_mulhu]

/-- The `QOVFDIVP` (PriceK+964) exit at `iVal = 1` is absurd: its
    `⌜rv64_mulhu taylorDW iVal ≠ 0⌝` pure is false because `taylorDW · 1` has a
    zero high half. -/
private theorem qovfdivp_exit_absurd (Y : Assertion) :
    ∀ h, ((((.x6 ↦ᵣ (rv64_mulhu taylorDW (1 : Word))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜rv64_mulhu taylorDW (1 : Word) ≠ (0 : Word)⌝) ** Y)) h → False := by
  apply absurd_of_false_pure
  intro hne
  exact hne (by decide)

/-- The ripple-carry chain of `taylor_round`'s carry exit with
    `acc = [taylorDW, 0, 0, 0, 0, 0]`, `s = [0×6]` is zero. -/
private def carryChain : Word :=
  rCry (0 : Word) (0 : Word)
    (rCry (0 : Word) (0 : Word)
      (rCry (0 : Word) (0 : Word)
        (rCry (0 : Word) (0 : Word)
          (rCry (0 : Word) (0 : Word) (rCry taylorDW (0 : Word) (0 : Word))))))

private theorem carry_chain_zero : carryChain = (0 : Word) := by
  decide

/-- The six product limbs `(aN·excess + carry)` in the QBACK / QOVFDIVP exits
    at `excess = 0` — all zero.  (Kept as defs so the huge expressions are
    written once.) -/
private def qprod0 : Word := ((taylorDW * (0 : Word)) + (0 : Word))
private def qprod1 : Word :=
  ((0 * (0 : Word)) + ((rv64_mulhu taylorDW (0 : Word)) +
    (if BitVec.ult ((taylorDW * (0 : Word)) + (0 : Word)) (taylorDW * (0 : Word)) then (1 : Word) else (0 : Word))))
private def qprod2 : Word :=
  ((0 * (0 : Word)) + ((rv64_mulhu (0 : Word) (0 : Word)) +
    (if BitVec.ult ((0 * (0 : Word)) + qprod1) (0 * (0 : Word)) then (1 : Word) else (0 : Word))))
private def qprod3 : Word :=
  ((0 * (0 : Word)) + ((rv64_mulhu (0 : Word) (0 : Word)) +
    (if BitVec.ult ((0 * (0 : Word)) + qprod2) (0 * (0 : Word)) then (1 : Word) else (0 : Word))))
private def qprod4 : Word :=
  ((0 * (0 : Word)) + ((rv64_mulhu (0 : Word) (0 : Word)) +
    (if BitVec.ult ((0 * (0 : Word)) + qprod3) (0 * (0 : Word)) then (1 : Word) else (0 : Word))))
private def qprod5 : Word :=
  ((0 * (0 : Word)) + ((rv64_mulhu (0 : Word) (0 : Word)) +
    (if BitVec.ult ((0 * (0 : Word)) + qprod4) (0 * (0 : Word)) then (1 : Word) else (0 : Word))))

/-- The six sum limbs `(aN + sN) + rCry` in the QBACK / QOVFDIVP exits at
    `s = [0×6]`. -/
private def qsum0 : Word := ((taylorDW + (0 : Word)) + (0 : Word))
private def qsum1 : Word := ((0 + (0 : Word)) + (rCry taylorDW (0 : Word) (0 : Word)))
private def qsum2 : Word := ((0 + (0 : Word)) + (rCry (0 : Word) (0 : Word) (rCry taylorDW (0 : Word) (0 : Word))))
private def qsum3 : Word := ((0 + (0 : Word)) + (rCry (0 : Word) (0 : Word) (rCry (0 : Word) (0 : Word) (rCry taylorDW (0 : Word) (0 : Word)))))
private def qsum4 : Word := ((0 + (0 : Word)) + (rCry (0 : Word) (0 : Word) (rCry (0 : Word) (0 : Word) (rCry (0 : Word) (0 : Word) (rCry taylorDW (0 : Word) (0 : Word))))))
private def qsum5 : Word := ((0 + (0 : Word)) + (rCry (0 : Word) (0 : Word) (rCry (0 : Word) (0 : Word) (rCry (0 : Word) (0 : Word) (rCry (0 : Word) (0 : Word) (rCry taylorDW (0 : Word) (0 : Word)))))))

/-- `taylor_round`'s precondition at `excess = 0`, `iVal = 1`,
    `acc = [taylorDW, 0, 0, 0, 0, 0]`, `prod = sum = [0×6]`, on the concrete
    sample geometry. -/
private def roundPre (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
      ((.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
       (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ (1 : Word)) ** (.x19 ↦ᵣ (sampleStackA)) **
       (.x20 ↦ᵣ (sampleStackB)) ** (.x21 ↦ᵣ sampleOutPtr) **
       (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame sampleNewSp sampleSaved **
       (((sampleStackA) + signExtend12 (0 : BitVec 12)) ↦ₘ taylorDW) ** (((sampleStackA) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleStackA) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleStackA) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleStackB) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleStackB) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleStackB) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       FR)

/-- `taylor_round`'s QBACK exit post at the concrete instantiation. -/
private def roundQBACKPost (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  AmsterdamBlobGasPriceBody11Spec.QBACKP sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
    taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    qprod0 qprod1 qprod2 qprod3 qprod4 qprod5
    qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 v7 v28 v29 v30 v31 FR

/-- `taylor_round`'s full 12-exit list at the concrete instantiation.  Exits
    1..11 are dead at `excess = 0`; exit 12 (QBACK) is the live one. -/
private def roundExits (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : List (Word × Assertion) :=
  [(PriceK + 804,
      (((.x5 ↦ᵣ (((((((0 : Word) ||| taylorDW) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜(((((((0 : Word) ||| taylorDW) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) = (0 : Word)⌝) **
        (((.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
        (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ (1 : Word)) ** (.x19 ↦ᵣ (sampleStackA)) **
        (.x20 ↦ᵣ (sampleStackB)) ** (.x21 ↦ᵣ sampleOutPtr) **
        (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame sampleNewSp sampleSaved **
        (((sampleStackA) + signExtend12 (0 : BitVec 12)) ↦ₘ taylorDW) ** (((sampleStackA) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackA) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackA) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        FR)))),
    (PriceK + 964,
      (((.x18 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult (1 : Word) (496 : Word) = true⌝) **
        (((.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
        (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
        (.x19 ↦ᵣ (sampleStackA)) ** (.x20 ↦ᵣ (sampleStackB)) **
        (.x21 ↦ᵣ sampleOutPtr) ** (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) **
        (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame sampleNewSp sampleSaved **
        (((sampleStackA) + signExtend12 (0 : BitVec 12)) ↦ₘ taylorDW) ** (((sampleStackA) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackA) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackA) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        FR)))),
    (PriceK + 964,
      (((.x5 ↦ᵣ carryChain) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜carryChain ≠ (0 : Word)⌝) **
        (((.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
        (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ (1 : Word)) ** (.x19 ↦ᵣ (sampleStackA)) **
        (.x20 ↦ᵣ (sampleStackB)) ** (.x21 ↦ᵣ sampleOutPtr) **
        (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ carryChain) ** (.x30 ↦ᵣ qsum5) **
        (.x31 ↦ᵣ (if BitVec.ult qsum5 (0 : Word) = true then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame sampleNewSp sampleSaved **
        (((sampleStackA) + signExtend12 (0 : BitVec 12)) ↦ₘ taylorDW) ** (((sampleStackA) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackA) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackA) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackA) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackB) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) ** (((sampleStackB) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ qsum0) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ qsum1) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ qsum2) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ qsum3) **
        (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ qsum4) ** (((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ qsum5) **
        FR)))),
    (PriceK + 964, mul6PQOVF0 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR),
    (PriceK + 964, mul6PQOVF1 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR),
    (PriceK + 964, mul6PQOVF2 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR),
    (PriceK + 964, mul6PQOVF3 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR),
    (PriceK + 964, mul6PQOVF4 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR),
    (PriceK + 964, mul6PQOVF5 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR),
    (PriceK + 964, mul6PQOVFF sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR),
    (PriceK + 964, QOVFDIVP sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qprod0 qprod1 qprod2 qprod3 qprod4 qprod5
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR),
    (PriceK + 144, AmsterdamBlobGasPriceBody11Spec.QBACKP sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qprod0 qprod1 qprod2 qprod3 qprod4 qprod5
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 v7 v28 v29 v30 v31 FR)]

/-- A `mul6PQOVF0` exit at `excess = 0` is absurd: its `⌜ovf ≠ 0⌝` pure is
    false since every limb product and carry is zero. -/
private theorem mul6PQOVF0_excess0_absurd (FR : Assertion) :
    ∀ h, (mul6PQOVF0 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hq, hfr⟩ := hx
  unfold mul6PQOVF0 at hq
  exact absurd_of_false_pure (by intro hne; exact hne (by decide)) h1 hq

private theorem mul6PQOVF1_excess0_absurd (FR : Assertion) :
    ∀ h, (mul6PQOVF1 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hq, hfr⟩ := hx
  unfold mul6PQOVF1 at hq
  exact absurd_of_false_pure (by intro hne; exact hne (by decide)) h1 hq

private theorem mul6PQOVF2_excess0_absurd (FR : Assertion) :
    ∀ h, (mul6PQOVF2 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hq, hfr⟩ := hx
  unfold mul6PQOVF2 at hq
  exact absurd_of_false_pure (by intro hne; exact hne (by decide)) h1 hq

private theorem mul6PQOVF3_excess0_absurd (FR : Assertion) :
    ∀ h, (mul6PQOVF3 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hq, hfr⟩ := hx
  unfold mul6PQOVF3 at hq
  exact absurd_of_false_pure (by intro hne; exact hne (by decide)) h1 hq

private theorem mul6PQOVF4_excess0_absurd (FR : Assertion) :
    ∀ h, (mul6PQOVF4 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hq, hfr⟩ := hx
  unfold mul6PQOVF4 at hq
  exact absurd_of_false_pure (by intro hne; exact hne (by decide)) h1 hq

private theorem mul6PQOVF5_excess0_absurd (FR : Assertion) :
    ∀ h, (mul6PQOVF5 sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hq, hfr⟩ := hx
  unfold mul6PQOVF5 at hq
  exact absurd_of_false_pure (by intro hne; exact hne (by decide)) h1 hq

private theorem mul6PQOVFF_excess0_absurd (FR : Assertion) :
    ∀ h, (mul6PQOVFF sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hq, hfr⟩ := hx
  unfold mul6PQOVFF at hq
  exact absurd_of_false_pure (by intro hne; exact hne (by decide)) h1 hq

/-- The `QOVFDIVP` exit at `excess = 0` is absurd. -/
private theorem qovfdivp_excess0_absurd (v7 v28 v29 v30 v31 : Word) (FR : Assertion) :
    ∀ h, (QOVFDIVP sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        qprod0 qprod1 qprod2 qprod3 qprod4 qprod5
        qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 v7 v28 v29 v30 v31 FR) h → False := by
  intro h hq
  unfold QOVFDIVP at hq
  exact qovfdivp_exit_absurd _ h hq

/-- Collapse `taylor_round` at `excess = 0` to its single live exit: the QBACK
    backedge at `PriceK + 144`.  The eleven dead exits each carry a pure that
    reduces to `False` (verified per-exit by `decide`), so
    `cpsNBranchWithin_drop_all_absurd_except` drops them all in one step. -/
private theorem taylor_round_excess0_qback
    (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (roundPre v5 v6 v7 v28 v29 v30 v31 FR)
      [(PriceK + 144, roundQBACKPost v7 v28 v29 v30 v31 FR)] := by
  have hR0 := taylor_round sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleStackA sampleStackB sampleSaved
    taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    v5 v6 v7 v28 v29 v30 v31 FR hFR
  have hR : cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (roundPre v5 v6 v7 v28 v29 v30 v31 FR) (roundExits v7 v28 v29 v30 v31 FR) := by
    unfold roundPre roundExits qprod0 qprod1 qprod2 qprod3 qprod4 qprod5 qsum0 qsum1 qsum2 qsum3 qsum4 qsum5 carryChain
    exact hR0
  have hCollapsed : cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (roundPre v5 v6 v7 v28 v29 v30 v31 FR)
      [(PriceK + 144, roundQBACKPost v7 v28 v29 v30 v31 FR)] :=
    cpsNBranchWithin_drop_all_absurd_except
      (target := (PriceK + 144, roundQBACKPost v7 v28 v29 v30 v31 FR))
      (htarget := by simp [roundExits, roundQBACKPost])
      (hdead := by
        intro ex hmem hne h hq
        simp [roundExits] at hmem
        rcases hmem with heq0 | heq1 | heq2 | heq3 | heq4 | heq5 | heq6 | heq7 | heq8 | heq9 | heq10 | heq11
        · subst heq0
          exact absurd_of_false_pure
            (by decide : (((((((0 : Word) ||| taylorDW) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) ||| (0 : Word)) ≠ (0 : Word))
            h hq
        · subst heq1
          exact absurd_of_false_pure (by intro hf; exact hf) h hq
        · subst heq2
          exact absurd_of_false_pure
            (R := carryChain ≠ (0 : Word))
            (by intro hne'; exact hne' carry_chain_zero)
            h hq
        · subst heq3
          exact mul6PQOVF0_excess0_absurd FR h hq
        · subst heq4
          exact mul6PQOVF1_excess0_absurd FR h hq
        · subst heq5
          exact mul6PQOVF2_excess0_absurd FR h hq
        · subst heq6
          exact mul6PQOVF3_excess0_absurd FR h hq
        · subst heq7
          exact mul6PQOVF4_excess0_absurd FR h hq
        · subst heq8
          exact mul6PQOVF5_excess0_absurd FR h hq
        · subst heq9
          exact mul6PQOVFF_excess0_absurd FR h hq
        · subst heq10
          exact qovfdivp_excess0_absurd (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR h hq
        · subst heq11
          exact (hne rfl).elim)
      hR
  simpa [roundExits, roundQBACKPost] using hCollapsed

end EvmAsm.Codegen.AmsterdamBlobGasPricePriceContractWitness