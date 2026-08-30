import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody10Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody11Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14TerminalSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Composition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundQBackComposition
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceU256Sat
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceTaylorTie
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody8Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceDivisionBridge
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
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorTie
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceDivisionBridge

/-- Drop an exit whose post is absurd (`∀ h, Q h → False`) from an N-branch's
    exit list at an arbitrary position (`pre ++ [(m, Q)] ++ post`).  Used to
    eliminate the dead overflow exits of `taylor_round` at `excess = 0`, where
    each carries a pure that reduces to false. -/
private theorem cpsNBranchWithin_drop_absurd_exit
    {nSteps : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {pre post : List (Word × Assertion)} {m : Word} {Q : Assertion}
    (hQ : ∀ h, Q h → False)
    (h : cpsNBranchWithin nSteps entry cr P (pre ++ [(m, Q)] ++ post)) :
    cpsNBranchWithin nSteps entry cr P (pre ++ post) := by
  intro R hRfree s hcr hP hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hRfree s hcr hP hpc
  refine ⟨k, hk, s', hstep, ex, ?_, hpc', hQR⟩
  have hne : ex ≠ (m, Q) := by
    intro heq
    subst heq
    have hQl := holdsFor_sepConj_elim_left hQR
    obtain ⟨hq, _, hqw⟩ := hQl
    exact (hQ hq hqw).elim
  have hmem' : ex ∈ pre ++ post := by
    rw [List.mem_append] at hmem
    rcases hmem with hpre | hrest
    · rw [List.mem_append] at hpre
      rcases hpre with hpre' | hm
      · exact List.mem_append.mpr (Or.inl hpre')
      · exfalso
        exact hne (List.mem_singleton.mp hm)
    · exact List.mem_append.mpr (Or.inr hrest)
  exact hmem'

/-- The head form of `cpsNBranchWithin_drop_absurd_exit` (`pre = []`), derived
    so the two do not drift apart. -/
private theorem cpsNBranchWithin_drop_absurd_head
    {nSteps : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {m : Word} {Q : Assertion} {rest : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry cr P ((m, Q) :: rest))
    (hQ : ∀ h, Q h → False) :
    cpsNBranchWithin nSteps entry cr P rest := by
  simpa using
    cpsNBranchWithin_drop_absurd_exit (pre := []) (post := rest) hQ h

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

/-! ## The excess-0 body triple

   The whole machine route for `excess = 0`:
     setup 27 (+36 → +144), round 4028 (collapsed to the single QBACK exit),
     second loop-head pass 14 (or-chain 13 + beqz 1), exitdiv+tail 4183
     (+804 → +968).  Body total 8252 = 27 + 4028 + 14 + 4183.

   The caller residual `FR` (an arbitrary `pcFree` assertion) is threaded as
   the body's `scratch`/`scratchPost` throughout, alongside the caller-owned
   output cells and the output-geometry pure; the architectural `x0` rider
   (`(.x0 ↦ᵣ (0 : Word))`) rides in the body precondition and is preserved
   through the round (its QBACK exit owns it) into the exit-divide. -/

/-- The ABI-frame registers at the status-0 body exit for `excess = 0`:
    `x18 = 2` (one completed round), `x19`/`x20` exchanged once
    (`x19` at `+112`, `x20` at `+64`).  Registers outside the frame keep
    their entry values. -/
private def bodyVals : Reg → Word
  | .x1 => sampleSaved .x1
  | .x8 => (0 : Word)
  | .x9 => taylorDW
  | .x18 => (2 : Word)
  | .x19 => sampleStackB
  | .x20 => sampleStackA
  | .x21 => sampleOutPtr
  | .x22 => sampleNewSp + signExtend12 (160 : BitVec 12)
  | r => sampleSaved r

/-! ### The owned round pre

   `taylor_round_excess0_qback` pins the seven loop scratch registers.  For
   the body composition those registers are only owned (the setup leaves them
   untouched), so the round is lifted over them via
   `cpsNBranchWithin_of_forall_regIs_to_regOwn`, one register at a time.
   `roundPre` is factored so each lift peels one register atom. -/

@[reducible] private def roundPreHead : Assertion :=
  (.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
  (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
  (.x18 ↦ᵣ (1 : Word)) ** (.x19 ↦ᵣ sampleStackA) **
  (.x20 ↦ᵣ sampleStackB) ** (.x21 ↦ᵣ sampleOutPtr) **
  (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12)))

@[reducible] private def roundPreMem (FR : Assertion) : Assertion :=
  frameSlotsSaved priceFrame sampleNewSp sampleSaved **
  (((sampleStackA + signExtend12 (0 : BitVec 12)) ↦ₘ taylorDW) **
    (((sampleStackA + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      (((sampleStackA + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
        (((sampleStackA + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
          (((sampleStackA + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
            (((sampleStackA + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
              (((sampleStackB + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
                (((sampleStackB + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
                  (((sampleStackB + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
                    (((sampleStackB + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
                      (((sampleStackB + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
                        (((sampleStackB + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
                          ((((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
                            ((((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
                              ((((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
                                ((((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
                                  ((((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
                                    ((((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
                                      FR))))))))))))))))))

@[reducible] private def roundPreTemps (v5 v6 v7 v28 v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))

/-- The temp tail with the first `k` registers owned.  `tempsK` has the first
    `k` registers owned and the rest pinned; `tempsNoK` removes the `k`-th
    register entirely (for the forall-lift family). -/
@[reducible] private def temps0 (v5 v6 v7 v28 v29 v30 v31 : Word) : Assertion := roundPreTemps v5 v6 v7 v28 v29 v30 v31
@[reducible] private def temps1 (v6 v7 v28 v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))
@[reducible] private def temps2 (v7 v28 v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (.x7 ↦ᵣ v7) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))))
@[reducible] private def temps3 (v28 v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))))
@[reducible] private def temps4 (v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))))))
@[reducible] private def temps5 (v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 ** (regOwn .x29 **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))))))
@[reducible] private def temps6 (v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 ** (regOwn .x29 ** (regOwn .x30 **
    (.x31 ↦ᵣ v31))))))))
@[reducible] private def temps7 : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 ** (regOwn .x29 ** (regOwn .x30 ** regOwn .x31)))))))

@[reducible] private def tempsNo5 (v6 v7 v28 v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
@[reducible] private def tempsNo6 (v7 v28 v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (.x7 ↦ᵣ v7) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))
@[reducible] private def tempsNo7 (v28 v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))))
@[reducible] private def tempsNo28 (v29 v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))))
@[reducible] private def tempsNo29 (v30 v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))))))
@[reducible] private def tempsNo30 (v31 : Word) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 ** (regOwn .x29 **
    (.x31 ↦ᵣ v31)))))))
@[reducible] private def tempsNo31 : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 ** (regOwn .x29 ** regOwn .x30))))))

set_option linter.unusedSimpArgs false in
/-- The `taylor_round` collapse with the seven loop scratch registers owned
    (lifted from `taylor_round_excess0_qback`).  The QBACK post is constant
    in those registers (`QBACKP` drops them), so the exit list is fixed. -/
private theorem taylor_round_excess0_qback_owned (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (roundPreHead ** (temps7 ** roundPreMem FR))
      [(PriceK + 144, roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR)] := by
  let exits : List (Word × Assertion) :=
    [(PriceK + 144, roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR)]
  have hL5 : ∀ v6 v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (roundPreHead ** (temps1 v6 v7 v28 v29 v30 v31 ** roundPreMem FR)) exits := by
    intro v6 v7 v28 v29 v30 v31
    refine cpsNBranchWithin_weaken_pre ?_ (cpsNBranchWithin_of_forall_regIs_to_regOwn
      (P := roundPreHead ** (tempsNo5 v6 v7 v28 v29 v30 v31 ** roundPreMem FR))
      (r := .x5)
      (h := ?_))
    · intro h hx
      simp only [temps1, tempsNo5] at hx ⊢
      xperm_hyp hx
    · intro v5
      refine cpsNBranchWithin_weaken_pre ?_ (taylor_round_excess0_qback v5 v6 v7 v28 v29 v30 v31 FR hFR)
      intro h hx
      simp only [roundPre, roundPreHead, tempsNo5, roundPreMem, exits] at hx ⊢
      xperm_hyp hx
  have hL6 : ∀ v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (roundPreHead ** (temps2 v7 v28 v29 v30 v31 ** roundPreMem FR)) exits := by
    intro v7 v28 v29 v30 v31
    refine cpsNBranchWithin_weaken_pre ?_ (cpsNBranchWithin_of_forall_regIs_to_regOwn
      (P := roundPreHead ** (tempsNo6 v7 v28 v29 v30 v31 ** roundPreMem FR))
      (r := .x6)
      (h := ?_))
    · intro h hx
      simp only [temps2, tempsNo6] at hx ⊢
      xperm_hyp hx
    · intro v6
      refine cpsNBranchWithin_weaken_pre ?_ (hL5 v6 v7 v28 v29 v30 v31)
      intro h hx
      simp only [temps1, tempsNo6] at hx ⊢
      xperm_hyp hx
  have hL7 : ∀ v28 v29 v30 v31 : Word,
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (roundPreHead ** (temps3 v28 v29 v30 v31 ** roundPreMem FR)) exits := by
    intro v28 v29 v30 v31
    refine cpsNBranchWithin_weaken_pre ?_ (cpsNBranchWithin_of_forall_regIs_to_regOwn
      (P := roundPreHead ** (tempsNo7 v28 v29 v30 v31 ** roundPreMem FR))
      (r := .x7)
      (h := ?_))
    · intro h hx
      simp only [temps3, tempsNo7] at hx ⊢
      xperm_hyp hx
    · intro v7
      refine cpsNBranchWithin_weaken_pre ?_ (hL6 v7 v28 v29 v30 v31)
      intro h hx
      simp only [temps2, tempsNo7] at hx ⊢
      xperm_hyp hx
  have hL28 : ∀ v29 v30 v31 : Word,
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (roundPreHead ** (temps4 v29 v30 v31 ** roundPreMem FR)) exits := by
    intro v29 v30 v31
    refine cpsNBranchWithin_weaken_pre ?_ (cpsNBranchWithin_of_forall_regIs_to_regOwn
      (P := roundPreHead ** (tempsNo28 v29 v30 v31 ** roundPreMem FR))
      (r := .x28)
      (h := ?_))
    · intro h hx
      simp only [temps4, tempsNo28] at hx ⊢
      xperm_hyp hx
    · intro v28
      refine cpsNBranchWithin_weaken_pre ?_ (hL7 v28 v29 v30 v31)
      intro h hx
      simp only [temps3, tempsNo28] at hx ⊢
      xperm_hyp hx
  have hL29 : ∀ v30 v31 : Word,
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (roundPreHead ** (temps5 v30 v31 ** roundPreMem FR)) exits := by
    intro v30 v31
    refine cpsNBranchWithin_weaken_pre ?_ (cpsNBranchWithin_of_forall_regIs_to_regOwn
      (P := roundPreHead ** (tempsNo29 v30 v31 ** roundPreMem FR))
      (r := .x29)
      (h := ?_))
    · intro h hx
      simp only [temps5, tempsNo29] at hx ⊢
      xperm_hyp hx
    · intro v29
      refine cpsNBranchWithin_weaken_pre ?_ (hL28 v29 v30 v31)
      intro h hx
      simp only [temps4, tempsNo29] at hx ⊢
      xperm_hyp hx
  have hL30 : ∀ v31 : Word,
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (roundPreHead ** (temps6 v31 ** roundPreMem FR)) exits := by
    intro v31
    refine cpsNBranchWithin_weaken_pre ?_ (cpsNBranchWithin_of_forall_regIs_to_regOwn
      (P := roundPreHead ** (tempsNo30 v31 ** roundPreMem FR))
      (r := .x30)
      (h := ?_))
    · intro h hx
      simp only [temps6, tempsNo30] at hx ⊢
      xperm_hyp hx
    · intro v30
      refine cpsNBranchWithin_weaken_pre ?_ (hL29 v30 v31)
      intro h hx
      simp only [temps5, tempsNo30] at hx ⊢
      xperm_hyp hx
  have hL31 : cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (roundPreHead ** (temps7 ** roundPreMem FR)) exits := by
    refine cpsNBranchWithin_weaken_pre ?_ (cpsNBranchWithin_of_forall_regIs_to_regOwn
      (P := roundPreHead ** (tempsNo31 ** roundPreMem FR))
      (r := .x31)
      (h := ?_))
    · intro h hx
      simp only [temps7, tempsNo31] at hx ⊢
      xperm_hyp hx
    · intro v31
      refine cpsNBranchWithin_weaken_pre ?_ (hL30 v31)
      intro h hx
      simp only [temps6, tempsNo31] at hx ⊢
      xperm_hyp hx
  simpa [exits] using hL31

/-! ### The owned setup window

   `price_setup_spec` keeps the eighteen old dword values explicit (its
   precondition pins each workspace cell).  For the body composition those
   cells are only owned (`priceWorkspaceOwn`), so the spec is lifted over the
   eighteen cells with `cpsTripleWithin_of_forall_memIs_to_memOwn`, then the
   caller's residual frame (`setupFrame` = the `x0` rider, the caller-owned
   output cells, the output-geometry pure, and the caller's `FR`) is framed
   on both sides. -/

/-- The non-buffer part of the setup precondition (frame registers, saved
    slots, and the seven owned loop scratch registers). -/
@[reducible] private def setupBase : Assertion :=
  (.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
    (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
    (.x8 ↦ᵣ (sampleSaved .x8)) ** (.x9 ↦ᵣ (sampleSaved .x9)) **
    (.x18 ↦ᵣ (sampleSaved .x18)) ** (.x19 ↦ᵣ (sampleSaved .x19)) **
    (.x20 ↦ᵣ (sampleSaved .x20)) ** (.x21 ↦ᵣ (sampleSaved .x21)) **
    (.x22 ↦ᵣ (sampleSaved .x22)) **
    frameSlotsSaved priceFrame sampleNewSp sampleSaved **
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31)

/-- The caller residual threaded through the whole route: the architectural
    `x0` zero rider, the caller-owned output cells, the output-geometry pure,
    and the caller's `FR`. -/
@[reducible] private def setupFrame (FR : Assertion) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** priceOutputOwn sampleOutPtr **
    ⌜priceOutputGeometry sampleOutPtr⌝ ** FR

set_option linter.unusedSimpArgs false in
private theorem price_setup_spec_owned (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 27 (PriceK + 36) (PriceK + 144) priceCode
      (setupFrame FR ** setupBase ** priceWorkspaceOwn sampleNewSp)
      (setupFrame FR ** taylorLoopInv sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleSaved
        [(64, taylorDW), (72, 0), (80, 0), (88, 0), (96, 0), (104, 0)]
        [(112, 0), (120, 0), (128, 0), (136, 0), (144, 0), (152, 0)]
        [(160, 0), (168, 0), (176, 0), (184, 0), (192, 0), (200, 0)]) := by
  have hLift : cpsTripleWithin 27 (PriceK + 36) (PriceK + 144) priceCode
      (setupBase ** priceWorkspaceOwn sampleNewSp)
      (taylorLoopInv sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleSaved
        [(64, taylorDW), (72, 0), (80, 0), (88, 0), (96, 0), (104, 0)]
        [(112, 0), (120, 0), (128, 0), (136, 0), (144, 0), (152, 0)]
        [(160, 0), (168, 0), (176, 0), (184, 0), (192, 0), (200, 0)]) := by
    -- Peel the 18 workspace cells one at a time: each step replaces a
    -- pinned cell with its `memOwn` ownership token.  Cell 64 is peeled
    -- first (outermost); cell 200 last, whose family closes against
    -- `price_setup_spec` directly.
    refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
      (cpsTripleWithin_of_forall_memIs_to_memOwn
        (P := setupBase ** (memOwn (sampleNewSp + signExtend12 (72 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (80 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (88 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (96 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (104 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (64 : BitVec 12))) (fun v0 => ?_))
    · intro h hx
      simp only [setupBase, priceWorkspaceOwn, sepConj_emp_right'] at hx ⊢
      xperm_hyp hx
    · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
        (cpsTripleWithin_of_forall_memIs_to_memOwn
          (P := setupBase ** bufCells sampleNewSp [(64, v0)] ** (memOwn (sampleNewSp + signExtend12 (80 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (88 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (96 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (104 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (72 : BitVec 12))) (fun v1 => ?_))
      · intro h hx
        simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
        xperm_hyp hx
      · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
          (cpsTripleWithin_of_forall_memIs_to_memOwn
            (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1)] ** (memOwn (sampleNewSp + signExtend12 (88 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (96 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (104 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (80 : BitVec 12))) (fun v2 => ?_))
        · intro h hx
          simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
          xperm_hyp hx
        · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
            (cpsTripleWithin_of_forall_memIs_to_memOwn
              (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2)] ** (memOwn (sampleNewSp + signExtend12 (96 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (104 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (88 : BitVec 12))) (fun v3 => ?_))
          · intro h hx
            simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
            xperm_hyp hx
          · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
              (cpsTripleWithin_of_forall_memIs_to_memOwn
                (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3)] ** (memOwn (sampleNewSp + signExtend12 (104 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (96 : BitVec 12))) (fun v4 => ?_))
            · intro h hx
              simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
              xperm_hyp hx
            · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                (cpsTripleWithin_of_forall_memIs_to_memOwn
                  (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4)] ** (memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (104 : BitVec 12))) (fun v5 => ?_))
              · intro h hx
                simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                xperm_hyp hx
              · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                  (cpsTripleWithin_of_forall_memIs_to_memOwn
                    (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5)] ** (memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (112 : BitVec 12))) (fun v6 => ?_))
                · intro h hx
                  simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                  xperm_hyp hx
                · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                    (cpsTripleWithin_of_forall_memIs_to_memOwn
                      (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6)] ** (memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (120 : BitVec 12))) (fun v7 => ?_))
                  · intro h hx
                    simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                    xperm_hyp hx
                  · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                      (cpsTripleWithin_of_forall_memIs_to_memOwn
                        (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7)] ** (memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (128 : BitVec 12))) (fun v8 => ?_))
                    · intro h hx
                      simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                      xperm_hyp hx
                    · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                        (cpsTripleWithin_of_forall_memIs_to_memOwn
                          (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8)] ** (memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (136 : BitVec 12))) (fun v9 => ?_))
                      · intro h hx
                        simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                        xperm_hyp hx
                      · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                          (cpsTripleWithin_of_forall_memIs_to_memOwn
                            (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9)] ** (memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (144 : BitVec 12))) (fun v10 => ?_))
                        · intro h hx
                          simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                          xperm_hyp hx
                        · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                            (cpsTripleWithin_of_forall_memIs_to_memOwn
                              (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9), (144, v10)] ** (memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (152 : BitVec 12))) (fun v11 => ?_))
                          · intro h hx
                            simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                            xperm_hyp hx
                          · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                              (cpsTripleWithin_of_forall_memIs_to_memOwn
                                (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9), (144, v10), (152, v11)] ** (memOwn (sampleNewSp + signExtend12 (168 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (160 : BitVec 12))) (fun v12 => ?_))
                            · intro h hx
                              simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                              xperm_hyp hx
                            · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                                (cpsTripleWithin_of_forall_memIs_to_memOwn
                                  (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9), (144, v10), (152, v11), (160, v12)] ** (memOwn (sampleNewSp + signExtend12 (176 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (168 : BitVec 12))) (fun v13 => ?_))
                              · intro h hx
                                simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                                xperm_hyp hx
                              · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                                  (cpsTripleWithin_of_forall_memIs_to_memOwn
                                    (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9), (144, v10), (152, v11), (160, v12), (168, v13)] ** (memOwn (sampleNewSp + signExtend12 (184 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (176 : BitVec 12))) (fun v14 => ?_))
                                · intro h hx
                                  simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                                  xperm_hyp hx
                                · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                                    (cpsTripleWithin_of_forall_memIs_to_memOwn
                                      (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9), (144, v10), (152, v11), (160, v12), (168, v13), (176, v14)] ** (memOwn (sampleNewSp + signExtend12 (192 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (184 : BitVec 12))) (fun v15 => ?_))
                                  · intro h hx
                                    simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                                    xperm_hyp hx
                                  · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                                      (cpsTripleWithin_of_forall_memIs_to_memOwn
                                        (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9), (144, v10), (152, v11), (160, v12), (168, v13), (176, v14), (184, v15)] ** (memOwn (sampleNewSp + signExtend12 (200 : BitVec 12)))) (a := (sampleNewSp + signExtend12 (192 : BitVec 12))) (fun v16 => ?_))
                                    · intro h hx
                                      simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                                      xperm_hyp hx
                                    · refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
                                        (cpsTripleWithin_of_forall_memIs_to_memOwn
                                          (P := setupBase ** bufCells sampleNewSp [(64, v0), (72, v1), (80, v2), (88, v3), (96, v4), (104, v5), (112, v6), (120, v7), (128, v8), (136, v9), (144, v10), (152, v11), (160, v12), (168, v13), (176, v14), (184, v15), (192, v16)]) (a := (sampleNewSp + signExtend12 (200 : BitVec 12))) (fun v17 => ?_))
                                      · intro h hx
                                        simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                                        xperm_hyp hx
                                      · exact cpsTripleWithin_weaken (fun h hx => by
                                          simp only [setupBase, bufCells, sampleNewSp, sepConj_emp_right'] at hx ⊢
                                          xperm_hyp hx) (fun _ hq => hq)
                                            (price_setup_spec sampleSp0 (0 : Word) sampleOutPtr sampleSaved v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17)
  have hFramePC : (setupFrame FR).pcFree := by
    unfold setupFrame
    pcf
    exact hFR
  have hFrame := cpsTripleWithin_frameR (setupFrame FR) hFramePC hLift
  exact cpsTripleWithin_weaken
    (fun h hx => by simp only [sepConj_assoc', sepConj_comm', sepConj_emp_right'] at hx ⊢; xperm_hyp hx)
    (fun h hx => by simp only [sepConj_assoc', sepConj_comm', sepConj_emp_right'] at hx ⊢; xperm_hyp hx)
    hFrame

/-! ### The excess-0 parity-1 invariant and the loop-head/exit-divide route

   After the collapsed round (excess = 0) the QBACK backedge leaves the machine
   at `PriceK+144` with the parity-1 invariant: `x18 = 2`, `x19`/`x20`
   exchanged, the (all-zero) quotient at `sampleStackB`, the old accumulator at
   `sampleStackA`, the running sum at `newSp + 160`. -/

/-- The parity-1 loop-head invariant after the first round at `excess = 0`. -/
@[reducible] private def parity1 (FR0 : Assertion) : Assertion :=
  taylorLoopInvParityAt sampleNewSp (0 : Word) sampleOutPtr sampleSaved 1 (2 : Word)
    sampleStackA sampleStackB
    [(0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)]
    [taylorDW, (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)]
    [taylorDW, (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] FR0 **
    (.x0 ↦ᵣ (0 : Word))



set_option linter.unusedSimpArgs false in
/-- `roundPre`'s QBACK post at `excess = 0` is exactly the computed source QBACK
    consumed by the parity backedge adapter. -/
private theorem roundQBACKPost_to_sourceQBACK (FR0 : Assertion) :
    roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0 =
      taylorRoundSourceQBACKComputed sampleNewSp (0 : Word) sampleOutPtr (1 : Word)
        sampleStackA sampleStackB sampleSaved
        taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0 := by
  unfold roundQBACKPost taylorRoundSourceQBACKComputed taylorRoundSourceQBACK
  simp [qprod0, qprod1, qprod2, qprod3, qprod4, qprod5,
    qsum0, qsum1, qsum2, qsum3, qsum4, qsum5,
    roundP0, roundP1, roundP2, roundP3, roundP4, roundP5,
    roundS0, roundS1, roundS2, roundS3, roundS4, roundS5,
    rv64_mulhu_zero_right]

/-- The QBACK quotient at `excess = 0` is all-zero (division by the zero
    product limbs, so `taylorDW / 0 = 0`). -/
private theorem taylor_round_quotient_excess0 :
    taylorRoundBackedgeQuotient (1 : Word) (0 : Word)
      taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) =
      [(0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] := by
  unfold taylorRoundBackedgeQuotient
  have hP0 : roundP0 taylorDW (0 : Word) = (0 : Word) := by decide
  have hP1 : roundP1 taylorDW (0 : Word) (0 : Word) = (0 : Word) := by decide
  have hP2 : roundP2 taylorDW (0 : Word) (0 : Word) (0 : Word) = (0 : Word) := by decide
  have hP3 : roundP3 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) = (0 : Word) := by decide
  have hP4 : roundP4 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) = (0 : Word) := by decide
  have hP5 : roundP5 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) = (0 : Word) := by decide
  rw [hP0, hP1, hP2, hP3, hP4, hP5]
  rw [divstSix_eq_div384by64]
  have hq := div384by64_quot_to_natToLimbs
    taylorDW [(0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] 0
    (by decide) (by decide) (by simp)
    (by decide : limbsToNat [(0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] /
        taylorDW.toNat = 0)
  simpa [natToLimbs] using hq

/-- The QBACK sum at `excess = 0` is `[taylorDW, 0, 0, 0, 0, 0]` (the old
    accumulator added to the zero old sum). -/
private theorem taylor_round_sum_excess0 :
    taylorRoundBackedgeSum taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) =
      [taylorDW, (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] := by
  decide

/-- The collapsed round's QBACK post closes the parity-1 invariant. -/
private theorem roundQBACKPost_to_parity1 (FR0 : Assertion) :
    ∀ h, roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0 h →
      parity1 FR0 h := by
  intro h hp
  have hsrc : taylorRoundSourceQBACKComputed sampleNewSp (0 : Word) sampleOutPtr (1 : Word)
      sampleStackA sampleStackB sampleSaved
      taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0 h := by
    rw [← roundQBACKPost_to_sourceQBACK]
    exact hp
  have hpar := taylor_round_source_qback_computed_to_parity
    sampleNewSp (0 : Word) sampleOutPtr (1 : Word) sampleSaved 0
    sampleStackA sampleStackB
    taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0 h hsrc
  rw [taylor_round_quotient_excess0, taylor_round_sum_excess0] at hpar
  rw [show (1 : Word) + signExtend12 (1 : BitVec 12) = (2 : Word) from by decide] at hpar
  simpa [parity1, taylorLoopInvParityAt] using hpar

/-! ### The second loop-head pass and the exit-divide

   At parity 1 (`x19` = `sampleStackB`, `x20` = `sampleStackA`) the acc is
   all-zero, so the parametric or-chain (`or_chainP2`, cells at `PB+0..40`)
   computes `x5 = 0`, and the `beqz` at `PriceK+196` jumps to the exit-divide
   at `PriceK+804`.  The exit-divide is the swapped `round_zero_exitdiv_tail`
   with the seven scratch registers and the four output cells owned, and its
   tail (`tail_core`) is the linked status-0/status-1 pair.  The tail's exit
   posts are first weakened to an output- and scratch-register-independent
   form (`tailPost`), then the four output cells and the five scratch
   registers are lifted to ownership. -/

/-- The frame registers at parity 1 (temps and `x0` live in the temp block
    `temps0..7` reused from the round lift). -/
@[reducible] private def loopFrame : Assertion :=
  (.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
    (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
    (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ (2 : Word)) ** (.x19 ↦ᵣ sampleStackB) **
    (.x20 ↦ᵣ sampleStackA) ** (.x21 ↦ᵣ sampleOutPtr) **
    (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12)))

/-- The six cells shared by the parity-1 or-chain and the exit-divide. -/
@[reducible] private def loopCells : Assertion :=
  cellsOf sampleStackB [(0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] **
  cellsOf sampleStackA [taylorDW, (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] **
  cellsOf (sampleNewSp + signExtend12 (160 : BitVec 12))
    [taylorDW, (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)]

/-- The or-chain memory part (saved slots + loop cells). -/
@[reducible] private def orMem (FR0 : Assertion) : Assertion :=
  frameSlotsSaved priceFrame sampleNewSp sampleSaved ** loopCells ** FR0

/-- The parametric or-chain precondition at parity 1 (owned temps). -/
@[reducible] private def orPre (FR0 : Assertion) : Assertion :=
  loopFrame ** (temps7 ** orMem FR0)

/-- The parametric or-chain postcondition at parity 1: `x5 = or6(acc) = 0`,
    `x6 = a5 = 0`, remaining temps owned. -/
@[reducible] private def orPost (FR0 : Assertion) : Assertion :=
  loopFrame ** ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
    (regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) ** orMem FR0)

/-- The `beqz`-framed continuation: the or-chain post minus `x5` and `x0`. -/
@[reducible] private def beqzRest (FR0 : Assertion) : Assertion :=
  loopFrame ** ((.x6 ↦ᵣ (0 : Word)) **
    (regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) ** orMem FR0)

/-- The exit-divide precondition at `PriceK+804` with the seven scratch
    registers and the four output cells owned. -/
@[reducible] private def roundZeroLift (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ (2 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝ **
    loopFrame ** (.x6 ↦ᵣ (0 : Word)) **
    (regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
    orMem FR **
    (memOwn sampleOutPtr ** memOwn (sampleOutPtr + (8 : Word)) **
      memOwn (sampleOutPtr + (16 : Word)) ** memOwn (sampleOutPtr + (24 : Word))) **
    ⌜priceOutputGeometry sampleOutPtr⌝ ** FR

/-- The status-0 tail post at `excess = 0`, weakened to the
    `priceBodyPost`-shaped residual. -/
@[reducible] private def tailPost (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
    (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
    (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ (2 : Word)) ** (.x19 ↦ᵣ sampleStackB) **
    (.x20 ↦ᵣ sampleStackA) ** (.x21 ↦ᵣ sampleOutPtr) **
    (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) **
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31) **
    frameSlotsSaved priceFrame sampleNewSp sampleSaved **
    priceWorkspaceOwn sampleNewSp **
    bytesRegion sampleOutPtr
      (tailOutputBytes (exitdivQ0 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word))
        (exitdivQ1 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word))
        (exitdivQ2 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word))
        (exitdivQ3 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word))) **
    ⌜priceOutputGeometry sampleOutPtr⌝ ** FR

/-- The high quotient-or at `excess = 0` (used by the status-1 absurdity). -/
private def q4q5 : Word :=
  exitdivQ4 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) |||
    exitdivQ5 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)

/-- The status-1 tail post at `excess = 0` is absurd: its `⌜q4q5 ≠ 0⌝`
    pure is false since both high quotient limbs vanish. -/
private theorem tailStatus1_excess0_absurd (FR : Assertion) :
    ∀ h, ((((.x5 ↦ᵣ q4q5) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜q4q5 ≠ (0 : Word)⌝) ** FR) h → False := by
  intro h hx
  obtain ⟨h1, h2, hd, hu, hlead, hfr⟩ := hx
  obtain ⟨h3, h4, hd1, hu1, hx5x0, hpure⟩ := hlead
  exact (hpure.2 (by decide : q4q5 = (0 : Word))).elim

#print axioms taylor_round_excess0_qback_owned
#print axioms price_setup_spec_owned
#print axioms roundQBACKPost_to_parity1
#print axioms taylor_round_quotient_excess0

end EvmAsm.Codegen.AmsterdamBlobGasPricePriceContractWitness