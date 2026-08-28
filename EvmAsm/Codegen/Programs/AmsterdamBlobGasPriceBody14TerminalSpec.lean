/- Terminal-index composition for the K70 outer-loop round (#12851). -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPrice

set_option maxRecDepth 8000

@[reducible] def roundAccum
    (a0 a1 a2 a3 a4 a5 : Word) : Word :=
  ((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5

/- The frame shared by the dispatch branches.  `v6` is explicit because the
   OR-chain has not yet loaded the final accumulator limb at its entry. -/
@[reducible] def roundFrame
    (newSp excess outPtr AB PB : Word) (vals : Reg → Word)
    (v6 v7 v28 v29 v30 v31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ vals .x1) **
  (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
  (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
  (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
  (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  frameSlotsSaved priceFrame newSp vals **
  ((AB + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
  ((AB + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
  ((AB + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
  ((AB + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
  ((AB + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
  ((AB + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
  ((PB + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
  ((PB + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
  ((PB + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
  ((PB + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
  ((PB + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
  ((PB + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR

@[reducible] def roundEntry
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
    roundFrame newSp excess outPtr AB PB vals v6 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR

@[reducible] def roundOr
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ w) **
  (.x0 ↦ᵣ (0 : Word)) **
    roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR

@[reducible] def roundZero
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ w) **
  (.x0 ↦ᵣ (0 : Word)) ** ⌜w = (0 : Word)⌝ **
    roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR

@[reducible] def roundNonzero
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ w) **
  (.x0 ↦ᵣ (0 : Word)) ** ⌜w ≠ (0 : Word)⌝ **
    roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR

@[reducible] def roundTerminal
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
  ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
  (.x0 ↦ᵣ (0 : Word)) ** ⌜w ≠ (0 : Word)⌝ **
    roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR

/- The status-1 tail overwrites `x10`, so its continuation frame is the
   terminal round with the old `x10 = excess` removed.  Keeping this assertion
   explicit prevents the LI proof from accidentally framing the register it
   writes. -/
@[reducible] def roundFrameNoX10
    (newSp excess outPtr AB PB : Word) (vals : Reg → Word)
    (v6 v7 v28 v29 v30 v31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ vals .x1) **
  (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
  (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
  (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
  (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  frameSlotsSaved priceFrame newSp vals **
  ((AB + signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
  ((AB + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
  ((AB + signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
  ((AB + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
  ((AB + signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
  ((AB + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
  ((PB + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
  ((PB + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
  ((PB + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
  ((PB + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
  ((PB + signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
  ((PB + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR

@[reducible] def roundTerminalRest
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
  ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
  (.x0 ↦ᵣ (0 : Word)) ** ⌜w ≠ (0 : Word)⌝ **
    roundFrameNoX10 newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR

@[reducible] def roundTerminalStatus1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    roundTerminalRest newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR

/- The terminal branch's final `li a0,1` is a separate one-instruction
   continuation.  Its source-level frame deliberately excludes `x10`, the
   destination of the instruction. -/
theorem round_terminal_status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (roundTerminal newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (roundTerminalStatus1 newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
  have hLi := li_spec_gen_within .x10 excess (1 : Word) (PriceK + 964) (by decide)
  have hRest : (roundTerminalRest newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR).pcFree := by
    unfold roundTerminalRest roundFrameNoX10
    pcFree
    exact hFR
  have hLiF := cpsTripleWithin_frameR
    (roundTerminalRest newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR) hRest hLi
  have hLiFP : cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      ((.x10 ↦ᵣ excess) **
        roundTerminalRest newSp excess outPtr iVal AB PB vals w
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v7 v28 v29 v30 v31 FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        roundTerminalRest newSp excess outPtr iVal AB PB vals w
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v7 v28 v29 v30 v31 FR) := by
    refine cpsTripleWithin_extend_code ?_ hLiF
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[241]'(by decide) =
        .LI .x10 (1 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 964)
      amsterdamBlobGasPriceU256_prog 241 (.LI .x10 (1 : Word))
      (by decide) (by decide) hins (by decide) a i hi
  refine cpsTripleWithin_weaken ?_ ?_ hLiFP
  · intro h hp
    simp only [roundTerminal, roundFrame, roundTerminalRest, roundFrameNoX10] at hp ⊢
    xperm_hyp hp
  · intro h hq
    simp only [roundTerminalStatus1, roundTerminalRest, roundFrameNoX10] at hq ⊢
    xperm_hyp hq

/-- The terminal-index round through the linked `li t0,496; bgeu s2,t0` arm.
    In the linked artifact
    `70ce14de6cd119437d05785633ec3f03b4b535fa73f4eb5c77d6f2f924b31959`,
    `li x5,496` is at `0x8000b414` (`PriceK+200`) and the taken `bgeu` is at
    `0x8000b418` (`PriceK+204`), targeting `0x8000b710` (`PriceK+964`). -/
theorem taylor_round_terminal_496
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (h_i : iVal = (496 : Word)) :
    cpsBranchWithin 16 (PriceK + 144) priceCode
      (roundEntry newSp excess outPtr iVal AB PB vals
        v5 v6 v7 v28 v29 v30 v31
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)
      (PriceK + 804)
      (roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 964)
      (roundTerminal newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
  let w : Word := roundAccum a0 a1 a2 a3 a4 a5
  have hOr := EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec.or_chainP2
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR hFR
  have hOr' : cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
      (roundEntry newSp excess outPtr iVal AB PB vals
        v5 v6 v7 v28 v29 v30 v31
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)
      (roundOr newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
    refine cpsTripleWithin_weaken
      (P' := roundEntry newSp excess outPtr iVal AB PB vals
        v5 v6 v7 v28 v29 v30 v31
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)
      (Q' := roundOr newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) ?_ ?_ hOr
    · intro h hp
      simp only [roundEntry, roundFrame] at hp ⊢
      xperm_hyp hp
    · intro h hq
      simp only [roundOr, roundFrame, w, roundAccum] at hq ⊢
      xperm_hyp hq

  let frameI : Assertion :=
    (.x18 ↦ᵣ iVal) **
      roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  have hFrameI_pc : frameI.pcFree := by
    unfold frameI roundFrame
    pcFree
    exact hFR
  have hBe0 := cpsBranchWithin_frameR frameI hFrameI_pc
    (EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec.loop_test_beqz_branch w)
  have hBe : cpsBranchWithin 1 (PriceK + 196) priceCode
      (roundOr newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 804)
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 200)
      (roundNonzero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
    refine cpsBranchWithin_weaken
      (P' := roundOr newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (Q_t' := roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (Q_f' := roundNonzero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) ?_ ?_ ?_ hBe0
    · intro h hp
      simp only [roundOr, roundFrame, frameI] at hp ⊢
      xperm_hyp hp
    · intro h hq
      simp only [roundZero, roundFrame, frameI] at hq ⊢
      xperm_hyp hq
    · intro h hq
      simp only [roundNonzero, roundFrame, frameI] at hq ⊢
      xperm_hyp hq

  let frameN : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** ⌜w ≠ (0 : Word)⌝ **
      roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  have hFrameN_pc : frameN.pcFree := by
    unfold frameN roundFrame
    pcFree
    exact hFR
  have hTerm0 :=
    EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec.loop_test_li_bgeu_terminal_496_drop_x0
      iVal w h_i frameN hFrameN_pc
  have hTerm : cpsTripleWithin 2 (PriceK + 200) (PriceK + 964) priceCode
      (roundNonzero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (roundTerminal newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
    refine cpsTripleWithin_weaken
      (P' := roundNonzero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (Q' := roundTerminal newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) ?_ ?_ hTerm0
    · intro h hp
      simp only [roundNonzero, roundFrame, frameN] at hp ⊢
      xperm_hyp hp
    · intro h hq
      simp only [roundTerminal, roundFrame, frameN] at hq ⊢
      xperm_hyp hq

  have hZero : cpsTripleWithin 2 (PriceK + 804) (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
    intro R hR s hcr hPR hpc
    exact ⟨0, by omega, s, by simp, hpc, hPR⟩
  have hZeroBr : cpsBranchWithin 2 (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 804)
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 964)
      (roundTerminal newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
    exact cpsTripleWithin_as_cpsBranchWithin_left
      (PriceK + 964)
      (roundTerminal newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) hZero
  have hTermBr : cpsBranchWithin 2 (PriceK + 200) priceCode
      (roundNonzero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 804)
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 964)
      (roundTerminal newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
    exact cpsTripleWithin_as_cpsBranchWithin_right
      (PriceK + 804)
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) hTerm

  have hDispatch := cpsBranchWithin_merge_branch_same_cr hBe hZeroBr hTermBr
  have hRound := cpsTripleWithin_seq_cpsBranchWithin_same_cr hOr' hDispatch
  simpa [w, roundAccum] using hRound

/- Complete the taken BGEU arm through the linked status-1 tail.  The zero
   accumulator arm remains an exit at `PriceK + 804`; the terminal arm now
   reaches the common body exit at `PriceK + 968`. -/
theorem taylor_round_terminal_496_status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (h_i : iVal = (496 : Word)) :
    cpsBranchWithin 17 (PriceK + 144) priceCode
      (roundEntry newSp excess outPtr iVal AB PB vals
        v5 v6 v7 v28 v29 v30 v31
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)
      (PriceK + 804)
      (roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (PriceK + 968)
      (roundTerminalStatus1 newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
  have hRound := taylor_round_terminal_496 newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR hFR h_i
  let w : Word := roundAccum a0 a1 a2 a3 a4 a5
  have hZero : cpsTripleWithin 0 (PriceK + 804) (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (roundZero newSp excess outPtr iVal AB PB vals w
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
    intro R hR s hcr hQR hpc
    exact ⟨0, by omega, s, by simp, hpc, hQR⟩
  have hZero1 := cpsTripleWithin_mono_nSteps (nSteps := 0) (nSteps' := 1)
    (by decide) hZero
  have hZeroBr := cpsTripleWithin_as_cpsBranchWithin_left
    (PriceK + 968)
    (roundTerminalStatus1 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR) hZero1
  have hTerm := round_terminal_status1 newSp excess outPtr iVal AB PB vals w
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR hFR
  have hTermBr := cpsTripleWithin_as_cpsBranchWithin_right
    (PriceK + 804)
    (roundZero newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR) hTerm
  simpa [w, roundAccum] using
    (cpsBranchWithin_merge_branch_same_cr hRound hZeroBr hTermBr)

#print axioms taylor_round_terminal_496
#print axioms round_terminal_status1
#print axioms taylor_round_terminal_496_status1

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
