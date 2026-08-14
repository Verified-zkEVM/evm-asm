/-
  EvmAsm.Codegen.Programs.ValidateHeaderInlineArms

  Inline scalar-comparison arms of SpecRef-shaped `validate_header` (#12346):
  conjuncts 1, 3, 5, 6.  No callee triple — each reject arm is proved against
  the linked exit (relative to `H`), carrying DISTINCT statuses 1 / 3 / 5 / 6.

  Reuses `H` / `callerCode` / `validateHeader_length` from
  `ValidateHeaderCorrespondence` — do not invent a second entry contract.

  Absolute PCs move with the link; proofs use `H + offset` only.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCorrespondence
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.ValidateHeaderInlineArms

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence

abbrev prog : Program := EvmAsm.Codegen.validateHeader_prog

theorem prog_length : prog.length = 97 := validateHeader_length

/-! ## Shared epilogue at `H + 352` (idx 88–96)

    Same 56-byte ABI-frame restore as `cvitEpilogue`. -/

set_option maxRecDepth 8000 in
theorem vhEpi
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (H + 352) raIn callerCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5)) := by
  subst hspC
  have l0 := ld_spec_gen_within .x1 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o1 raIn
    (0 : BitVec 12) (H + 352) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at l0
  have l1 := ld_spec_gen_within .x8 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o8 cs0
    (8 : BitVec 12) (H + 356) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at l1
  have l2 := ld_spec_gen_within .x9 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o9 cs1
    (16 : BitVec 12) (H + 360) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at l2
  have l3 := ld_spec_gen_within .x18 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o18 cs2
    (24 : BitVec 12) (H + 364) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at l3
  have l4 := ld_spec_gen_within .x19 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o19 cs3
    (32 : BitVec 12) (H + 368) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at l4
  have l5 := ld_spec_gen_within .x20 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o20 cs4
    (40 : BitVec 12) (H + 372) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at l5
  have l6 := ld_spec_gen_within .x21 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o21 cs5
    (48 : BitVec 12) (H + 376) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at l6
  have l7 := addi_spec_gen_same_within .x2 (sp0 + signExtend12 (-56 : BitVec 12))
    (56 : BitVec 12) (H + 380) (by decide)
  rw [show (sp0 + signExtend12 (-56 : BitVec 12)) + signExtend12 (56 : BitVec 12) = sp0
      from by rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
        show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at l7
  have hblock : cpsTripleWithin 8 (H + 352) (H + 384) callerCode
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-56 : BitVec 12))) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) **
        (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) := by
    runBlock l0 l1 l2 l3 l4 l5 l6 l7
  have hjalr := EvmAsm.Evm64.ret_spec_within' (H + 384) raIn
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 384) prog 96 (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    hjalr
  have hjalrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
      (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
      ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblock hjalrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Conjunct 1 status exit — `li a0, 1` @ `H+260` → `j` → epilogue

    Building block for the `number < 1` reject arm. Post carries **`a0 = 1`**.
    Pattern mirrors `cvpmfRetNonce` / `hfStatus1Return` (LI+JAL block then epi). -/

set_option maxRecDepth 8000 in
theorem status1Exit
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 260) raIn callerCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (1 : Word) (H + 260) (by decide)
  have s1 := jal_x0_spec_gen_within
    (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 264))
    (H + 264)
  rw [show (H + 264) + signExtend21
      (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 264)) =
      H + 352 from by
    change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 264 + _ =
      BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 352
    have hL : BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 264 =
        BitVec.ofNat 64 (GuestAddrs.validate_header + 264) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : GuestAddrs.validate_header + 264 < 2 ^ 64); omega
    have hR : BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 352 =
        BitVec.ofNat 64 (GuestAddrs.validate_header + 352) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : GuestAddrs.validate_header + 352 < 2 ^ 64); omega
    rw [hL, hR]
    exact jalOff_correct (GuestAddrs.validate_header + 352)
      (GuestAddrs.validate_header + 264) (by decide)] at s1
  have hblock : cpsTripleWithin 2 (H + 260) (H + 352) callerCode
      ((.x10 ↦ᵣ o10))
      ((.x10 ↦ᵣ (1 : Word))) := by
    have s0C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 260) prog 65 (.LI .x10 (1 : Word))
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      s0
    have s1C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 264) prog 66
        (.JAL .x0 (jalOff (GuestAddrs.validate_header + 352)
          (GuestAddrs.validate_header + 264)))
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      s1
    runBlock s0C s1C
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hblock
  have hepi := vhEpi sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (1 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Conjunct 1 — `number < 1` (beqz) → status 1

    `LD x5, 64(s2)` @ `H+56`, then `BEQ x5, x0` @ `H+60` taken → `status1Exit`.
    No `< 2^64` gate: the check is pure zero-test. -/

abbrev numberZeroBrOff : BitVec 13 :=
  brOff (GuestAddrs.validate_header + 260) (GuestAddrs.validate_header + 60)

theorem numberZeroBeq_taken_pc :
    (H + 60) + signExtend13 numberZeroBrOff = H + 260 := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 60 +
      signExtend13 (brOff (GuestAddrs.validate_header + 260)
        (GuestAddrs.validate_header + 60)) =
    BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 260
  exact brOff_correct_base_off GuestAddrs.validate_header 60 260
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem numberZeroBeq_taken (number : Word) (hnum : number = 0) :
    cpsTripleWithin 1 (H + 60) (H + 260) callerCode
      ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x5 .x0 numberZeroBrOff number (0 : Word) (H + 60)
  rw [numberZeroBeq_taken_pc] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 60) prog 15
        (.BEQ .x5 .x0 numberZeroBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbeq)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hnum)

/-- Fall-through when `number ≠ 0` (vacuous for the reject arm). -/
theorem numberZeroBeq_ntaken (number : Word) (hnum : number ≠ 0) :
    cpsTripleWithin 1 (H + 60) (H + 64) callerCode
      ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x5 .x0 numberZeroBrOff number (0 : Word) (H + 60)
  rw [show (H + 60 : Word) + 4 = H + 64 from by bv_omega] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 60) prog 15
        (.BEQ .x5 .x0 numberZeroBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbeq)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hnum ((sepConj_pure_right _).1 hBP).2)

theorem ldNumber (headerBase o5 number : Word) :
    cpsTripleWithin 1 (H + 56) (H + 60) callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ o5) ** ((headerBase + 64) ↦ₘ number))
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ number) ** ((headerBase + 64) ↦ₘ number)) := by
  have h := ld_spec_gen_within .x5 .x18 headerBase o5 number (64 : BitVec 12) (H + 56)
    (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 56) prog 14 (.LD .x5 .x18 (64 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

set_option maxRecDepth 8000 in
theorem numberLt1_reject
    (sp0 spC raIn headerBase number
      cs0 cs1 cs2 cs3 cs4 cs5 o10 o5 o1 o8 o9 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hnum : number = 0) :
    cpsTripleWithin 13 (H + 56) raIn callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ o5) ** ((headerBase + 64) ↦ₘ number) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)) **
        ((headerBase + 64) ↦ₘ number) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  -- Live `x18 = headerBase` for the LD; epilogue restores `x18` from `cs2`.
  -- Ambient framed over `status1Exit` must omit regs the epi clobbers.
  have hld := ldNumber headerBase o5 number
  have hldF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
      (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hld
  have hb := numberZeroBeq_taken number hnum
  have hbF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** ((headerBase + 64) ↦ₘ number) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
      (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hb
  have hex := status1Exit sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o10 o1 o8 o9 headerBase o19 o20 o21
    ((.x5 ↦ᵣ number) ** (.x0 ↦ᵣ (0 : Word)) **
      ((headerBase + 64) ↦ₘ number) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs)
    hspC hret
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hldF hbF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hex
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s2

end EvmAsm.Codegen.ValidateHeaderInlineArms
