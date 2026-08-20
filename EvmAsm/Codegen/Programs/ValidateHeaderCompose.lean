/-
  EvmAsm.Codegen.Programs.ValidateHeaderCompose

  Route contracts for the SpecRef-shaped `validate_header` program (#12346).

  This file deliberately stops at the route seams.  The three expensive
  callees (excess-blob-gas, base-fee, and K67 post-merge) remain explicit
  premises in their adapter files; these lemmas prove the caller-side
  fall-through, K67 status mapping, and the common return tail around them.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderInlineArms
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen.ValidateHeaderCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderInlineArms

abbrev prog : Program := EvmAsm.Codegen.validateHeader_prog

theorem prog_length : prog.length = 97 := validateHeader_length

/-! ## Entry prologue - the concrete state handed to the first checker. -/

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
  have s0 := addi_spec_gen_same_within .x2 sp0 (-56 : BitVec 12) H (by decide)
  have s1 := sd_spec_gen_own_within .x2 .x1
    (sp0 + signExtend12 (-56 : BitVec 12)) raIn (0 : BitVec 12) (H + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word) =
      sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at s1
  have s2 := sd_spec_gen_own_within .x2 .x8
    (sp0 + signExtend12 (-56 : BitVec 12)) o8 (8 : BitVec 12) (H + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at s2
  have s3 := sd_spec_gen_own_within .x2 .x9
    (sp0 + signExtend12 (-56 : BitVec 12)) o9 (16 : BitVec 12) (H + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at s3
  have s4 := sd_spec_gen_own_within .x2 .x18
    (sp0 + signExtend12 (-56 : BitVec 12)) o18 (24 : BitVec 12) (H + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at s4
  have s5 := sd_spec_gen_own_within .x2 .x19
    (sp0 + signExtend12 (-56 : BitVec 12)) o19 (32 : BitVec 12) (H + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at s5
  have s6 := sd_spec_gen_own_within .x2 .x20
    (sp0 + signExtend12 (-56 : BitVec 12)) o20 (40 : BitVec 12) (H + 24)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at s6
  have s7 := sd_spec_gen_own_within .x2 .x21
    (sp0 + signExtend12 (-56 : BitVec 12)) o21 (48 : BitVec 12) (H + 28)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at s7
  have s8 := mv_spec_gen_within .x8 .x10 a0 o8 (H + 32) (by decide)
  have s9 := mv_spec_gen_within .x9 .x11 a1 o9 (H + 36) (by decide)
  have s10 := mv_spec_gen_within .x18 .x12 a2 o18 (H + 40) (by decide)
  have s11 := mv_spec_gen_within .x19 .x13 a3 o19 (H + 44) (by decide)
  have s12 := mv_spec_gen_within .x20 .x14 a4 o20 (H + 48) (by decide)
  have s13 := mv_spec_gen_within .x21 .x15 a5 o21 (H + 52) (by decide)
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
      ((regIs .x1 raIn) ** (regIs .x2 (sp0 + signExtend12 (-56 : BitVec 12))) **
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
  have hframed := cpsTripleWithin_frameR G hG hblock
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframed

/-! ## Common status tail for K67's 8/9/10 mapping. -/

theorem statusTailCore
    {entry : Word} {status oldStatus : Word} {jump : BitVec 21}
    (hLi : ∀ a i, CodeReq.singleton entry (.LI .x10 status) a = some i →
      callerCode a = some i)
    (hJal : ∀ a i, CodeReq.singleton (entry + 4) (.JAL .x0 jump) a = some i →
      callerCode a = some i)
    (htarget : entry + 4 + signExtend21 jump = H + 352) :
    cpsTripleWithin 2 entry (H + 352) callerCode
      ((.x10 ↦ᵣ oldStatus)) ((.x10 ↦ᵣ status)) := by
  have hli := li_spec_gen_within .x10 oldStatus status entry (by decide)
  have hjal := jal_x0_spec_gen_within jump (entry + 4)
  rw [htarget] at hjal
  have hliC := cpsTripleWithin_extend_code hLi hli
  have hjalC := cpsTripleWithin_extend_code hJal hjal
  runBlock hliC hjalC

set_option maxRecDepth 8000 in
theorem statusTailFrame
    {entry : Word} {status oldStatus : Word}
    (hcore : cpsTripleWithin 2 entry (H + 352) callerCode
      ((.x10 ↦ᵣ oldStatus)) ((.x10 ↦ᵣ status)))
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 entry raIn callerCode
      ((.x10 ↦ᵣ oldStatus) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  let hpre : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
  have hpreFree : hpre.pcFree := by
    dsimp [hpre]
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs |
      exact pcFree_memIs | exact hG
  have hcoreF := cpsTripleWithin_frameR hpre hpreFree hcore
  have hepi := vhEpi sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ status) ** G)
    (by refine pcFree_sepConj ?_ hG; exact pcFree_regIs) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hcoreF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hall

/-! Concrete mapped tails.  The remap is the monotone K67 order 1↦8,
    2↦9, 3↦10 (PR 12430). -/

theorem status8_tail
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 oldStatus : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 316) raIn callerCode
      ((.x10 ↦ᵣ oldStatus) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (8 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  refine statusTailFrame (status := (8 : Word)) (oldStatus := oldStatus) ?_ sp0 spC raIn
    cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 G hG hspC hret
  · apply statusTailCore
    · exact CodeReq.ofProg_mem_at H (H + 316) prog 79 _
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
    · exact CodeReq.ofProg_mem_at H (H + 320) prog 80 _
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
    · rw [show signExtend21 (32 : BitVec 21) = (32 : Word) from by decide]
      bv_omega

theorem status9_tail
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 oldStatus : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 324) raIn callerCode
      ((.x10 ↦ᵣ oldStatus) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (9 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  refine statusTailFrame (status := (9 : Word)) (oldStatus := oldStatus) ?_ sp0 spC raIn
    cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 G hG hspC hret
  · apply statusTailCore
    · exact CodeReq.ofProg_mem_at H (H + 324) prog 81 _
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
    · exact CodeReq.ofProg_mem_at H (H + 328) prog 82 _
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
    · rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by decide]
      bv_omega

theorem status10_tail
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 oldStatus : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 332) raIn callerCode
      ((.x10 ↦ᵣ oldStatus) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (10 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  refine statusTailFrame (status := (10 : Word)) (oldStatus := oldStatus) ?_ sp0 spC raIn
    cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 G hG hspC hret
  · apply statusTailCore
    · exact CodeReq.ofProg_mem_at H (H + 332) prog 83 _
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
    · exact CodeReq.ofProg_mem_at H (H + 336) prog 84 _
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
    · rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]
      bv_omega

/-! The two remaining concrete tails are the parent-hash result paths.  They
    are kept beside the K67 tails so the status dispatch has one named target
    contract for every edge: status `0` falls through to the parent-hash call's
    success continuation, while a nonzero parent-hash result lands at status
    `11`. -/

theorem status0_success_tail
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 252) raIn callerCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  refine statusTailFrame (status := (0 : Word)) (oldStatus := (0 : Word)) ?_
    sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 G hG hspC hret
  apply statusTailCore
  · exact CodeReq.ofProg_mem_at H (H + 252) prog 63 _
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
  · exact CodeReq.ofProg_mem_at H (H + 256) prog 64 _
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
  · exact by
      change H + 256 + signExtend21
        (jalOff (GuestAddrs.validate_header + 352)
          (GuestAddrs.validate_header + 256)) = H + 352
      change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 256 + _ =
        BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 352
      exact jalOff_correct_add (GuestAddrs.validate_header + 352)
        GuestAddrs.validate_header 256 (by decide) (by decide) (by decide) (by decide)

theorem status11_tail
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 oldStatus : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 340) raIn callerCode
      ((.x10 ↦ᵣ oldStatus) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (11 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  refine statusTailFrame (status := (11 : Word)) (oldStatus := oldStatus) ?_
    sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 G hG hspC hret
  apply statusTailCore
  · exact CodeReq.ofProg_mem_at H (H + 340) prog 85 _
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
  · exact CodeReq.ofProg_mem_at H (H + 344) prog 86 _
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)
  · rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
    bv_omega

theorem status12_tail
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 oldStatus : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 10 (H + 348) raIn callerCode
      ((.x10 ↦ᵣ oldStatus) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (12 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have hli := li_spec_gen_within .x10 oldStatus (12 : Word) (H + 348) (by decide)
  have hliC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 348) prog 87 (.LI .x10 (12 : Word))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)) hli
  let hrest : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
  have hrestFree : hrest.pcFree := by
    dsimp [hrest]
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs |
      exact pcFree_memIs | exact hG
  have hliF := cpsTripleWithin_frameR hrest hrestFree hliC
  have hepi := vhEpi sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (12 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; exact pcFree_regIs) hepi
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

/-! ## Parent-hash result dispatch

    `BNE a0,x0` at `H+248` is the last branch before the common return.  The
    branch itself preserves the callee's status; the selected tail then
    materialises either status `0` or status `11`.  Keeping the incoming
    status explicit is important: on the failing edge it is *not* already
    `11` when control reaches the `LI a0,11` at `H+340`. -/

abbrev parentHashFailureBrOff : BitVec 13 :=
  brOff (GuestAddrs.validate_header + 340) (GuestAddrs.validate_header + 248)

theorem parentHashFailure_taken_pc :
    (H + 248) + signExtend13 parentHashFailureBrOff = H + 340 := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 248 +
      signExtend13 (brOff (GuestAddrs.validate_header + 340)
        (GuestAddrs.validate_header + 248)) =
    BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 340
  exact brOff_correct_base_off GuestAddrs.validate_header 248 340
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8000 in
theorem parentHash_failure_to_status11
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 status : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hstatus : status ≠ 0) :
    cpsTripleWithin 12 (H + 248) raIn callerCode
      ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) ** (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) **
        ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
        ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (11 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have hbr := bne_spec_gen_within .x10 .x0 parentHashFailureBrOff
    status (0 : Word) (H + 248)
  rw [parentHashFailure_taken_pc] at hbr
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 248) prog 62
      (.BNE .x10 .x0 parentHashFailureBrOff)
      (by bv_omega) (by rw [prog_length]; decide) rfl
      (by rw [prog_length]; decide)) hbr
  have htaken := cpsBranchWithin_takenStripPure2 hbrC
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hstatus ((sepConj_pure_right _).1 hBP).2)
  let hrest : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
  have hrestFree : hrest.pcFree := by
    dsimp [hrest]
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs |
      exact pcFree_memIs | exact hG
  have hbranch := cpsTripleWithin_frameR hrest hrestFree htaken
  have hG' : ((.x0 ↦ᵣ (0 : Word)) ** G).pcFree := by
    exact pcFree_sepConj pcFree_regIs hG
  have htail := status11_tail sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 o20 o21 status ((.x0 ↦ᵣ (0 : Word)) ** G)
    hG' hspC hret
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (by xsimp) hbranch htail
  exact cpsTripleWithin_weaken (by xsimp) (by xsimp) hseq

set_option maxRecDepth 8000 in
theorem parentHash_success_to_common_return
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 status : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hstatus : status = 0) :
    cpsTripleWithin 12 (H + 248) raIn callerCode
      ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) ** (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) **
        ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
        ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have hbr := bne_spec_gen_within .x10 .x0 parentHashFailureBrOff
    status (0 : Word) (H + 248)
  rw [show (H + 248 : Word) + 4 = H + 252 from by bv_omega] at hbr
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 248) prog 62
      (.BNE .x10 .x0 parentHashFailureBrOff)
      (by bv_omega) (by rw [prog_length]; decide) rfl
      (by rw [prog_length]; decide)) hbr
  have hntaken := cpsBranchWithin_ntakenStripPure2 hbrC
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 hstatus)
  let hrest : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
      (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) ** (spC ↦ₘ raIn) **
      ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
      ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
      ((spC + 48) ↦ₘ cs5) ** G)
  have hrestFree : hrest.pcFree := by
    dsimp [hrest]
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs |
      exact pcFree_memIs | exact hG
  have hbranch := cpsTripleWithin_frameR hrest hrestFree hntaken
  have hG' : ((.x0 ↦ᵣ (0 : Word)) ** G).pcFree := by
    exact pcFree_sepConj pcFree_regIs hG
  have htail := status0_success_tail sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 o20 o21 ((.x0 ↦ᵣ (0 : Word)) ** G)
    hG' hspC hret
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [hstatus] at hp
      xperm_hyp hp) hbranch htail
  exact cpsTripleWithin_weaken (by xsimp) (by xsimp) hseq

/-! ## K67 status dispatch routes

    These contracts consume the three comparison branches after the K67 call;
    they are deliberately stated over the incoming status, not over the
    materialised 8/9/10 result.  The tail's `LI` is part of the route. -/

set_option maxRecDepth 8000 in
theorem postMerge_status1_to_status8
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 status x5Old : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hstatus : status = 1) :
    cpsTripleWithin 14 (H + 196) raIn callerCode
      ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ x5Old) ** (.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) ** (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) **
        ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
        ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (8 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have hneq : status ≠ 0 := by
    intro hz
    rw [hstatus] at hz
    exact (by decide : (1 : Word) ≠ 0) hz
  have hbeq0 := beq_spec_gen_within .x10 .x0 (32 : BitVec 13)
    status (0 : Word) (H + 196)
  rw [show (H + 196 : Word) + 4 = H + 200 from by bv_omega] at hbeq0
  have h0 := cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 196) prog 49
        (.BEQ .x10 .x0 (32 : BitVec 13))
        (by bv_omega) (by rw [prog_length]; decide) rfl
        (by rw [prog_length]; decide)) hbeq0)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hneq ((sepConj_pure_right _).1 hBP).2)
  have hli := li_spec_gen_within .x5 x5Old (1 : Word) (H + 200) (by decide)
  have hliC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 200) prog 50 (.LI .x5 (1 : Word))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide)) hli
  have h0F := cpsTripleWithin_frameR (.x5 ↦ᵣ x5Old)
    pcFree_regIs h0
  have hliF := cpsTripleWithin_frameR ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)))
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs) hliC
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F hliF
  have hbeq1 := beq_spec_gen_within .x10 .x5
    (brOff (GuestAddrs.validate_header + 316) (GuestAddrs.validate_header + 204))
    status (1 : Word) (H + 204)
  rw [show (H + 204 : Word) + signExtend13
      (brOff (GuestAddrs.validate_header + 316) (GuestAddrs.validate_header + 204)) =
      H + 316 by
    exact brOff_correct_base_off GuestAddrs.validate_header 204 316
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hbeq1
  have h1 := cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 204) prog 51 _
        (by bv_omega) (by rw [prog_length]; decide) rfl
        (by rw [prog_length]; decide)) hbeq1)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hstatus)
  have h1F := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; exact pcFree_regIs) h1
  have h01F := cpsTripleWithin_frameR G hG h01
  have hcore := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01F h1F
  let hrest : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5))
  have hrestFree : hrest.pcFree := by
    dsimp [hrest]
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs
  have hcoreF := cpsTripleWithin_frameR hrest hrestFree hcore
  have htail := status8_tail sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 o20 o21 status ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** G)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact hG)
    hspC hret
  have hseq := cpsTripleWithin_seq_perm_same_cr (by xsimp) hcoreF htail
  exact cpsTripleWithin_weaken (by xsimp) (by xsimp) hseq

/-! ## K67 status-0 fall-through to the parent-hash call. -/

theorem postMerge_status0_to_parent_hash_args
    (header headerLen s4 s5 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (H + 196) (H + 244) callerCode
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)) ** F)
      ((((.x21 ↦ᵣ s5) ** (.x13 ↦ᵣ s5)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ headerLen) **
        (.x12 ↦ᵣ s4) ** (.x20 ↦ᵣ s4)) ** F) := by
  have hbeq := beq_spec_gen_within .x10 .x0 (32 : BitVec 13)
    (0 : Word) (0 : Word) (H + 196)
  rw [show (H + 196) + signExtend13 (32 : BitVec 13) = H + 228 by decide] at hbeq
  have hbeqC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 196) prog 49
      (.BEQ .x10 .x0 (32 : BitVec 13))
      (by decide) (by rw [prog_length]; decide) rfl
      (by rw [prog_length]; decide)) hbeq
  have htaken := cpsBranchWithin_takenStripPure2 hbeqC
    (fun _ hp => by
      obtain ⟨_, _, _, _, _, hbad⟩ := hp
      exact ((sepConj_pure_right _).1 hbad).2 (by decide))
  have hbranch := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) ** (.x20 ↦ᵣ s4) **
      (.x21 ↦ᵣ s5) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) ** F) (by
        repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact hF) htaken
  have m0 := mv_spec_gen_within .x10 .x8 header (0 : Word) (H + 228) (by decide)
  have m1 := mv_spec_gen_within .x11 .x9 headerLen (0 : Word) (H + 232) (by decide)
  have m2 := mv_spec_gen_within .x12 .x20 s4 (0 : Word) (H + 236) (by decide)
  have m3 := mv_spec_gen_within .x13 .x21 s5 (0 : Word) (H + 240) (by decide)
  have htail : cpsTripleWithin 4 (H + 228) (H + 240 + 4) callerCode
      (((.x8 ↦ᵣ header) ** (.x10 ↦ᵣ (0 : Word))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ headerLen) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)))
      (((.x21 ↦ᵣ s5) ** (.x13 ↦ᵣ s5)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ headerLen) **
        (.x12 ↦ᵣ s4) ** (.x20 ↦ᵣ s4)) := by
    have m0C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 228) prog 57 _
        (by bv_omega) (by rw [prog_length]; decide) rfl
        (by rw [prog_length]; decide)) m0
    have m1C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 232) prog 58 _
        (by bv_omega) (by rw [prog_length]; decide) rfl
        (by rw [prog_length]; decide)) m1
    have m2C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 236) prog 59 _
        (by bv_omega) (by rw [prog_length]; decide) rfl
        (by rw [prog_length]; decide)) m2
    have m3C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 240) prog 60 _
        (by bv_omega) (by rw [prog_length]; decide) rfl
        (by rw [prog_length]; decide)) m3
    have m0F := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ headerLen) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)))
      (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs) m0C
    have m1F := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ header) ** (.x10 ↦ᵣ header) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)))
      (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs) m1C
    have m2F := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ headerLen) ** (.x21 ↦ᵣ s5) **
        (.x13 ↦ᵣ (0 : Word)))
      (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs) m2C
    have m3F := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ headerLen) ** (.x12 ↦ᵣ s4) **
        (.x20 ↦ᵣ s4))
      (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs) m3C
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) m0F m1F
    have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 m2F
    have h123 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) c2 m3F
    exact h123
  have htailF := cpsTripleWithin_frameR F hF htail
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hbranch htailF
  simpa [sepConj_assoc', show H + 240 + 4 = H + 244 by decide] using hseq

/-! The status-0 route's gate is genuinely inhabited: the K67 success status
    and the equality tested by the first dispatch branch are concrete, not an
    assumed postcondition disguised as a precondition. -/
theorem postMerge_status0_gate_inhabited :
    (0 : Word) = 0 ∧ ¬ ((0 : Word) ≠ 0) := by decide

/-! The explicit register precondition is inhabited as well.  The witness is
    deliberately boring: every owned register is zero and the frame is empty.
    Keeping this as a machine-state assertion prevents the route proof from
    relying only on a satisfiable branch predicate. -/
theorem postMerge_status0_route_precondition_inhabited :
    ∃ s : MachineState,
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
        (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)) ** empAssertion).holdsFor s := by
  let h13 := PartialState.singletonReg .x13 (0 : Word)
  let h12 := (PartialState.singletonReg .x12 (0 : Word)).union h13
  let h11 := (PartialState.singletonReg .x11 (0 : Word)).union h12
  let h21 := (PartialState.singletonReg .x21 (0 : Word)).union h11
  let h20 := (PartialState.singletonReg .x20 (0 : Word)).union h21
  let h9 := (PartialState.singletonReg .x9 (0 : Word)).union h20
  let h8 := (PartialState.singletonReg .x8 (0 : Word)).union h9
  let h10x0 := (PartialState.singletonReg .x10 (0 : Word)).union
    (PartialState.singletonReg .x0 (0 : Word))
  let h := h10x0.union h8
  let s : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := H + 196 }
  refine ⟨s, ?_⟩
  change ∃ h' : PartialState, h'.CompatibleWith s ∧
    (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
      (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ (0 : Word)) ** empAssertion) h'
  refine ⟨h, ?_, ?_⟩
  · unfold PartialState.CompatibleWith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r v hv
      cases r <;>
        simp [h, h10x0, h8, h9, h20, h21, h11, h12, h13,
          PartialState.union, PartialState.singletonReg, s, MachineState.getReg] at hv ⊢ <;>
        simpa using hv
    · intro a v hv
      simp [h, h10x0, h8, h9, h20, h21, h11, h12, h13,
        PartialState.union, PartialState.singletonReg] at hv
    · intro a i hv
      simp [h, h10x0, h8, h9, h20, h21, h11, h12, h13,
        PartialState.union, PartialState.singletonReg] at hv
    · intro v hv
      simp [h, h10x0, h8, h9, h20, h21, h11, h12, h13,
        PartialState.union, PartialState.singletonReg] at hv
    · intro v hv
      simp [h, h10x0, h8, h9, h20, h21, h11, h12, h13,
        PartialState.union, PartialState.singletonReg] at hv
    · intro v hv
      simp [h, h10x0, h8, h9, h20, h21, h11, h12, h13,
        PartialState.union, PartialState.singletonReg] at hv
    · intro v hv
      simp [h, h10x0, h8, h9, h20, h21, h11, h12, h13,
        PartialState.union, PartialState.singletonReg] at hv
  · have hd10x0 : (PartialState.singletonReg .x10 (0 : Word)).Disjoint
        (PartialState.singletonReg .x0 (0 : Word)) := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [PartialState.singletonReg]
    have hd12 : (PartialState.singletonReg .x12 (0 : Word)).Disjoint h13 := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [h13, PartialState.singletonReg]
    have hd11 : (PartialState.singletonReg .x11 (0 : Word)).Disjoint h12 := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [h12, h13, PartialState.union, PartialState.singletonReg]
    have hd21 : (PartialState.singletonReg .x21 (0 : Word)).Disjoint h11 := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [h11, h12, h13, PartialState.union, PartialState.singletonReg]
    have hd20 : (PartialState.singletonReg .x20 (0 : Word)).Disjoint h21 := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [h21, h11, h12, h13, PartialState.union, PartialState.singletonReg]
    have hd9 : (PartialState.singletonReg .x9 (0 : Word)).Disjoint h20 := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [h20, h21, h11, h12, h13, PartialState.union, PartialState.singletonReg]
    have hd8 : (PartialState.singletonReg .x8 (0 : Word)).Disjoint h9 := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [h9, h20, h21, h11, h12, h13, PartialState.union, PartialState.singletonReg]
    have htop : h10x0.Disjoint h8 := by
      refine ⟨?_, (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      intro r; cases r <;> simp [h10x0, h8, h9, h20, h21, h11, h12, h13,
        PartialState.union, PartialState.singletonReg]
    refine ⟨h10x0, h8, htop, rfl, ?_, ?_⟩
    · refine ⟨PartialState.singletonReg .x10 (0 : Word),
        PartialState.singletonReg .x0 (0 : Word), hd10x0, rfl, rfl, rfl⟩
    · refine ⟨PartialState.singletonReg .x8 (0 : Word), h9, hd8, rfl, rfl, ?_⟩
      refine ⟨PartialState.singletonReg .x9 (0 : Word), h20, hd9, rfl, rfl, ?_⟩
      refine ⟨PartialState.singletonReg .x20 (0 : Word), h21, hd20, rfl, rfl, ?_⟩
      refine ⟨PartialState.singletonReg .x21 (0 : Word), h11, hd21, rfl, rfl, ?_⟩
      refine ⟨PartialState.singletonReg .x11 (0 : Word), h12, hd11, rfl, rfl, ?_⟩
      refine ⟨PartialState.singletonReg .x12 (0 : Word), h13, hd12, rfl, rfl, ?_⟩
      exact ⟨h13, PartialState.empty, PartialState.Disjoint_empty_right,
        PartialState.union_empty_right, rfl, rfl⟩

end EvmAsm.Codegen.ValidateHeaderCompose
