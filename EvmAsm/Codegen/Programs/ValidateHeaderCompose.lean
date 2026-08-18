/-
  EvmAsm.Codegen.Programs.ValidateHeaderCompose

  Whole-routine composition for `validate_header` (GH #12346).

  The 35 merged results (5 call-arm adapters + 30 inline-arm theorems)
  cover the routine body from `H+56` onward but not the entry: this file
  adds the prologue spec (`H+0 → H+56`, stack allocation, callee-saved
  spills, ABI register moves) and, in later commits, the missing status
  exits, the post-merge dispatch chain, and the final composed
  `cpsTripleWithin` against `SpecRef.validate_header`.

  The prologue defines the whole-routine precondition, so its atoms are
  restricted to what the ABI and the machine demonstrably establish:
  the ABI argument registers `a0..a5` (`x10..x15`), the return address
  `x1`, the incoming stack pointer `x2`, and ownership of the seven
  frame cells the prologue itself writes.  Every further atom here would
  become an obligation on every caller (GH #12346 reviewer caution).
-/

import EvmAsm.Codegen.Programs.ValidateHeaderInlineArms

namespace EvmAsm.Codegen.ValidateHeaderCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderInlineArms

/-- `validate_header` prologue: 14 instructions from the routine entry
    `H` to the first check at `H + 56`.  `ADDI x2 x2 -56` allocates the
    frame; seven `SD`s spill `ra` and the six callee-saved registers the
    body repurposes; six `MV`s copy the ABI arguments `a0..a5` into
    `x8/x9/x18/x19/x20/x21` for the body.  The postcondition is the exact
    arm-entry state every conjunct theorem at `H + 56` consumes: `x2`
    pinned at the frame base, the saved values in frame cells, and the
    saved-register pins carrying the ABI values. -/
theorem validateHeader_prologue_spec
    (sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    cpsTripleWithin 14 H (H + 56) callerCode
      ((regIs .x1 raIn) ** (regIs .x2 sp0) **
        (regIs .x8 o8) ** (regIs .x9 o9) ** (regIs .x18 o18) **
        (regIs .x19 o19) ** (regIs .x20 o20) ** (regIs .x21 o21) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) **
        memOwn (spC + 24) ** memOwn (spC + 32) ** memOwn (spC + 40) **
        memOwn (spC + 48) ** G)
      ((regIs .x1 raIn) ** (regIs .x2 spC) **
        (regIs .x8 a0) ** (regIs .x9 a1) ** (regIs .x18 a2) **
        (regIs .x19 a3) ** (regIs .x20 a4) ** (regIs .x21 a5) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
        ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
        ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) ** G) := by
  subst hspC
  -- instruction 0: `ADDI x2 x2 -56`
  have s0 := addi_spec_gen_same_within .x2 sp0 (-56 : BitVec 12) H (by decide)
  -- instructions 1..7: `SD x2 {x1,x8,x9,x18,x19,x20,x21} {0,8,...,48}`
  have s1 := sd_spec_gen_own_within .x2 .x1 (sp0 + signExtend12 (-56 : BitVec 12))
    raIn (0 : BitVec 12) (H + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at s1
  have s2 := sd_spec_gen_own_within .x2 .x8 (sp0 + signExtend12 (-56 : BitVec 12))
    o8 (8 : BitVec 12) (H + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at s2
  have s3 := sd_spec_gen_own_within .x2 .x9 (sp0 + signExtend12 (-56 : BitVec 12))
    o9 (16 : BitVec 12) (H + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at s3
  have s4 := sd_spec_gen_own_within .x2 .x18 (sp0 + signExtend12 (-56 : BitVec 12))
    o18 (24 : BitVec 12) (H + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at s4
  have s5 := sd_spec_gen_own_within .x2 .x19 (sp0 + signExtend12 (-56 : BitVec 12))
    o19 (32 : BitVec 12) (H + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at s5
  have s6 := sd_spec_gen_own_within .x2 .x20 (sp0 + signExtend12 (-56 : BitVec 12))
    o20 (40 : BitVec 12) (H + 24)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at s6
  have s7 := sd_spec_gen_own_within .x2 .x21 (sp0 + signExtend12 (-56 : BitVec 12))
    o21 (48 : BitVec 12) (H + 28)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at s7
  -- instructions 8..13: `MV x8 x10 .. MV x21 x15`
  have s8 := mv_spec_gen_within .x8 .x10 a0 o8 (H + 32) (by decide)
  have s9 := mv_spec_gen_within .x9 .x11 a1 o9 (H + 36) (by decide)
  have s10 := mv_spec_gen_within .x18 .x12 a2 o18 (H + 40) (by decide)
  have s11 := mv_spec_gen_within .x19 .x13 a3 o19 (H + 44) (by decide)
  have s12 := mv_spec_gen_within .x20 .x14 a4 o20 (H + 48) (by decide)
  have s13 := mv_spec_gen_within .x21 .x15 a5 o21 (H + 52) (by decide)
  -- chain the block
  have hblock : cpsTripleWithin 14 H (H + 56) callerCode
      ((regIs .x1 raIn) ** (regIs .x2 sp0) **
        (regIs .x8 o8) ** (regIs .x9 o9) ** (regIs .x18 o18) **
        (regIs .x19 o19) ** (regIs .x20 o20) ** (regIs .x21 o21) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
        memOwn (sp0 + signExtend12 (-56 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-56 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-56 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-56 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-56 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-56 : BitVec 12) + 40) **
        memOwn (sp0 + signExtend12 (-56 : BitVec 12) + 48))
      ((regIs .x1 raIn) **
        (regIs .x2 (sp0 + signExtend12 (-56 : BitVec 12))) **
        (regIs .x8 a0) ** (regIs .x9 a1) ** (regIs .x18 a2) **
        (regIs .x19 a3) ** (regIs .x20 a4) ** (regIs .x21 a5) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ o8) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ o9) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ o18) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ o19) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ o20) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ o21)) := by
    runBlock s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13
  -- frame the ambient `G` around the block
  have hframed := cpsTripleWithin_frameR G hG hblock
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hframed

end EvmAsm.Codegen.ValidateHeaderCompose
