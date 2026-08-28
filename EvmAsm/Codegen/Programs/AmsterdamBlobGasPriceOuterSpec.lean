/- Outer-loop assembly adapters for K70 (#12851).

   The first adapter below is deliberately small: it closes the terminal-index
   round before the recurrence fold is attempted.  The seven loop-scratch
   registers are owned by the parity invariant, while the linked terminal
   theorem consumes concrete values.  The existential exit posts retain those
   values for the subsequent exit-divide and outer-loop adapters.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundComposition

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
open EvmAsm.Codegen.AmsterdamBlobGasPrice

set_option maxRecDepth 8000

/- The library currently provides the N-branch bulk adapter for nine
   registers.  K70's round owns exactly these seven registers, so keep the
   smaller adapter local rather than manufacturing two unrelated resources. -/
private theorem nbranch_regOwn7
    {n : Nat} {entry : Word} {r1 r2 r3 r4 r5 r6 r7 : Reg}
    {P : Assertion} {exits : List (Word × Assertion)} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7, cpsNBranchWithin n entry cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) **
       (r7 ↦ᵣ v7)) exits) :
    cpsNBranchWithin n entry cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 **
       regOwn r4 ** regOwn r5 ** regOwn r6 ** regOwn r7) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact h v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

@[reducible] def terminalCore
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ vals .x1) **
  (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
  (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
  (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
  frameSlotsSaved priceFrame newSp vals **
  cellsOf AB [a0, a1, a2, a3, a4, a5] **
  cellsOf PB [p0, p1, p2, p3, p4, p5] **
  cellsOf (newSp + signExtend12 (160 : BitVec 12))
    [s0, s1, s2, s3, s4, s5] ** FR

@[reducible] def terminalZeroAny
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    roundZeroNoX0 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR h

@[reducible] def terminalStatus1Any
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    roundTerminalStatus1NoX0 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR h

/- The linked terminal round consumes concrete values for the seven owned
   scratch registers.  Package the five values which its posts retain; the
   subsequent exit-divide adapter destructures them before it continues. -/
theorem taylor_round_terminal_496_from_footprint
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree)
    (h_i : iVal = (496 : Word)) :
    cpsNBranchWithin 17 (PriceK + 144) priceCode
      (taylorRoundFootprint newSp excess outPtr iVal AB PB vals
        [a0, a1, a2, a3, a4, a5] [p0, p1, p2, p3, p4, p5]
        [s0, s1, s2, s3, s4, s5] FR)
      [ (PriceK + 804,
          terminalZeroAny newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
        (PriceK + 968,
          terminalStatus1Any newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) ] := by
  let core := terminalCore newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  let exits : List (Word × Assertion) := [
    (PriceK + 804,
      terminalZeroAny newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
    (PriceK + 968,
      terminalStatus1Any newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)]
  have hConcrete : ∀ v5 v6 v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin 17 (PriceK + 144) priceCode
        (core ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          (.x31 ↦ᵣ v31)) exits := by
    intro v5 v6 v7 v28 v29 v30 v31
    have hBranch := taylor_round_terminal_496_status1_drop_x0
      newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v5 v6 v7 v28 v29 v30 v31 FR hFR h_i
    have hN := cpsBranchWithin_as_cpsNBranchWithin hBranch
    have hN' := cpsNBranchWithin_weaken_pre (P' :=
        core ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          (.x31 ↦ᵣ v31)) (fun h hp => by
      simp only [core, terminalCore, roundEntryNoX0, roundFrame,
        EvmAsm.Rv64.AddrNorm.se12_0,
        EvmAsm.Rv64.AddrNorm.se12_8, EvmAsm.Rv64.AddrNorm.se12_16,
        EvmAsm.Rv64.AddrNorm.se12_24, EvmAsm.Rv64.AddrNorm.se12_32,
        EvmAsm.Rv64.AddrNorm.se12_40,
        EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
      rw [cellsOf_six, cellsOf_six, cellsOf_six] at hp
      xperm_hyp hp) hN
    refine cpsNBranchWithin_weaken_posts hN' ?_
    intro ex hex
    have hex' : ex =
        (PriceK + 804,
          roundZeroNoX0 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 v7 v28 v29 v30 v31 FR) ∨
      ex =
        (PriceK + 968,
          roundTerminalStatus1NoX0 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 v7 v28 v29 v30 v31 FR) := by
      simpa [hBranch] using hex
    rcases hex' with rfl | rfl
    · refine ⟨_, List.Mem.head _, rfl, ?_⟩
      intro h hh
      exact ⟨v7, v28, v29, v30, v31, hh⟩
    · refine ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, ?_⟩
      intro h hh
      exact ⟨v7, v28, v29, v30, v31, hh⟩
  have hOwned := nbranch_regOwn7 (P := core)
    (r1 := .x5) (r2 := .x6) (r3 := .x7) (r4 := .x28)
    (r5 := .x29) (r6 := .x30) (r7 := .x31) hConcrete
  have hFinal := cpsNBranchWithin_weaken_pre
    (P' := taylorRoundFootprint newSp excess outPtr iVal AB PB vals
      [a0, a1, a2, a3, a4, a5] [p0, p1, p2, p3, p4, p5]
      [s0, s1, s2, s3, s4, s5] FR)
    (fun h hp => by
      simp only [taylorRoundFootprint, regOwns, sepConj_emp_right', core,
        terminalCore] at hp ⊢
      xperm_hyp hp) hOwned
  simpa [exits] using hFinal

/- The terminal-index arm is reached from the actual parity invariant at the
   last loop index.  Keep this adapter separate from the value-packaging
   theorem above: its post is still the explicit terminal relation consumed
   by `round_zero_exitdiv_tail`, so the five scratch witnesses are available
   to that continuation rather than being treated as dead state. -/
theorem taylor_round_terminal_496_from_parity
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 17 (PriceK + 144) priceCode
      (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5] FR)
      [ (PriceK + 804,
          terminalZeroAny newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
        (PriceK + 968,
          terminalStatus1Any newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) ] := by
  let AB := parityBuffer 495 evenBase oddBase
  let PB := parityBuffer 495 oddBase evenBase
  have hRound := taylor_round_terminal_496_from_footprint
    newSp excess outPtr (496 : Word) AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR hFR
    (by decide)
  have hPre : ∀ h,
      taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5] FR h →
      taylorRoundFootprint newSp excess outPtr (496 : Word) AB PB vals
        [a0, a1, a2, a3, a4, a5] [p0, p1, p2, p3, p4, p5]
        [s0, s1, s2, s3, s4, s5] FR h := by
    intro h hh
    simpa [AB, PB] using
      (taylorLoopInvParityAt_to_taylorRoundFootprint
        newSp excess outPtr vals 495 (496 : Word) evenBase oddBase
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR h hh)
  have hFinal := cpsNBranchWithin_weaken_pre hPre hRound
  simpa [AB, PB] using hFinal

/- The zero arm is consumed immediately by `round_zero_exitdiv_tail`.  That
   continuation needs the five scratch values, so this adapter destructures
   `terminalZeroAny` and threads each value through the exit-divide proof. -/
private theorem outer_x0Free_sepConj {P Q : Assertion}
    (hP : x0FreeAssertion P) (hQ : x0FreeAssertion Q) :
    x0FreeAssertion (P ** Q) := by
  intro h hh
  obtain ⟨h1, h2, hd, hu, hp, hq⟩ := hh
  have h1x := hP h1 hp
  have h2x := hQ h2 hq
  rw [← hu]
  simp [PartialState.union, h1x, h2x]

private theorem outer_x0Free_regIs {r : Reg} {v : Word} (hr : r ≠ .x0) :
    x0FreeAssertion (regIs r v) := by
  intro h hh
  rw [hh]
  simp [PartialState.singletonReg, Ne.symm hr]

private theorem outer_x0Free_memIs {a v : Word} :
    x0FreeAssertion (memIs a v) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem outer_x0Free_frameSlotsSaved
    (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) :
    x0FreeAssertion (frameSlotsSaved frame newSp vals) := by
  induction frame with
  | nil =>
      intro h hh
      rw [hh]
      rfl
  | cons p rest ih =>
      simpa only [frameSlotsSaved_cons] using
        outer_x0Free_sepConj outer_x0Free_memIs ih

private theorem outer_x0Free_roundFrame :
    ∀ (newSp excess outPtr AB PB : Word) (vals : Reg → Word)
      (v6 v7 v28 v29 v30 v31 : Word)
      (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
      (FR : Assertion) (_hFR : x0FreeAssertion FR),
      x0FreeAssertion
      (roundFrame newSp excess outPtr AB PB vals v6 v7 v28 v29 v30 v31
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) := by
  intro newSp excess outPtr AB PB vals v6 v7 v28 v29 v30 v31
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR _hFR
  unfold roundFrame
  repeat' first
    | apply outer_x0Free_sepConj
    | exact outer_x0Free_regIs (by decide)
    | exact outer_x0Free_memIs
    | exact outer_x0Free_frameSlotsSaved _ _ _
    | assumption

private theorem outer_x0Free_pure {P : Prop} : x0FreeAssertion (⌜P⌝) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem outer_x0Free_roundZeroNoX0
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (hFR : x0FreeAssertion FR) :
    x0FreeAssertion (roundZeroNoX0 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR) := by
  unfold roundZeroNoX0
  repeat' first
    | apply outer_x0Free_sepConj
    | exact outer_x0Free_regIs (by decide)
    | exact outer_x0Free_memIs
    | exact outer_x0Free_frameSlotsSaved _ _ _
    | exact outer_x0Free_pure
    | exact outer_x0Free_roundFrame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    | assumption

private theorem outer_x0Free_exitdivOutputCells
    (outPtr o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : x0FreeAssertion FR) :
    x0FreeAssertion (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) := by
  unfold exitdivOutputCells
  repeat' first
    | apply outer_x0Free_sepConj
    | exact outer_x0Free_memIs
    | assumption

theorem terminal_zero_any_to_exitdiv
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hAB : AB = newSp + signExtend12 (64 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (112 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3 AB PB FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))) :
    cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (terminalZeroAny newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      exits := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0Free : x0FreeAssertion FR0 := by
    unfold FR0
    exact outer_x0Free_exitdivOutputCells outPtr o0 o1 o2 o3 FR hFRx0
  have hZero : ∀ v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin 4183 (PriceK + 804) priceCode
        (roundZeroNoX0 newSp excess outPtr iVal AB PB vals
          (roundAccum a0 a1 a2 a3 a4 a5)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
          s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0) exits := by
    intro v7 v28 v29 v30 v31
    have hZeroX := round_zero_exitdiv_tail
      newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB
      (exits := exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))
      hTail
    have hZeroX' :
        cpsNBranchWithin 4183 (PriceK + 804) priceCode
          ((roundZeroNoX0 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0) **
            regIs .x0 (0 : Word))
          (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word)))) := by
      refine cpsNBranchWithin_weaken_pre ?_ hZeroX
      intro h hp
      simp only [roundZeroNoX0, roundZero] at hp ⊢
      xperm_hyp hp
    have hZeroFree := outer_x0Free_roundZeroNoX0
      newSp excess outPtr iVal AB PB vals
      (roundAccum a0 a1 a2 a3 a4 a5)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0 hFR0Free
    have hDrop := cpsNBranchWithin_drop_x0
      (P := roundZeroNoX0 newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0)
      (exits := exits) hZeroFree hZeroX'
    simpa [FR0] using hDrop
  intro R hR s hcr hP hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hP
  obtain ⟨v7, v28, v29, v30, v31, hv⟩ := hPP
  exact hZero v7 v28 v29 v30 v31 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, hv, hRb⟩ hpc

/- The actual terminal BGEU arm carries the exit-divide output cells in the
   caller frame.  Frame those cells before invoking the parity adapter, then
   consume only the zero arm; the nonzero status arm stays as the second
   branch.  This is the first list-level composition that checks the five
   retained scratch values at their real consumer boundary. -/
theorem taylor_round_terminal_496_from_parity_exitdiv
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hAB : parityBuffer 495 evenBase oddBase =
      newSp + signExtend12 (64 : BitVec 12))
    (hPB : parityBuffer 495 oddBase evenBase =
      newSp + signExtend12 (112 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr (496 : Word) vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3
        (parityBuffer 495 evenBase oddBase)
        (parityBuffer 495 oddBase evenBase) FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))) :
    cpsNBranchWithin (17 + 4183) (PriceK + 144) priceCode
      (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5]
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      (exits ++
        [(PriceK + 968,
          terminalStatus1Any newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))]) := by
  let AB := parityBuffer 495 evenBase oddBase
  let PB := parityBuffer 495 oddBase evenBase
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  have hRound := taylor_round_terminal_496_from_parity
    newSp excess outPtr vals evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    FR0 hFR0
  have hZero := terminal_zero_any_to_exitdiv
    newSp excess outPtr (496 : Word) AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 FR hFR hFRx0 (by simpa [AB] using hAB)
    (by simpa [PB] using hPB) hTail
  have hAll := nb_extend_head_same_cr hRound hZero
  simpa [AB, PB, FR0] using hAll

#print axioms taylor_round_terminal_496_from_footprint
#print axioms taylor_round_terminal_496_from_parity
#print axioms terminal_zero_any_to_exitdiv
#print axioms taylor_round_terminal_496_from_parity_exitdiv

end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
