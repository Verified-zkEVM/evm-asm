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


/-! ## Status 3 exit — `li a0, 3` @ `H+276` → `j` → epilogue -/

set_option maxRecDepth 8000 in
theorem status3Exit
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 276) raIn callerCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (3 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (3 : Word) (H + 276) (by decide)
  have s1 := jal_x0_spec_gen_within
    (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 280))
    (H + 280)
  rw [show (H + 280) + signExtend21
      (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 280)) =
      H + 352 from by
    change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 280 + _ =
      BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 352
    have hL : BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 280 =
        BitVec.ofNat 64 (GuestAddrs.validate_header + 280) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : GuestAddrs.validate_header + 280 < 2 ^ 64); omega
    have hR : BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 352 =
        BitVec.ofNat 64 (GuestAddrs.validate_header + 352) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : GuestAddrs.validate_header + 352 < 2 ^ 64); omega
    rw [hL, hR]
    exact jalOff_correct (GuestAddrs.validate_header + 352)
      (GuestAddrs.validate_header + 280) (by decide)] at s1
  have hblock : cpsTripleWithin 2 (H + 276) (H + 352) callerCode
      ((.x10 ↦ᵣ o10))
      ((.x10 ↦ᵣ (3 : Word))) := by
    have s0C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 276) prog 69 (.LI .x10 (3 : Word))
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      s0
    have s1C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 280) prog 70
        (.JAL .x0 (jalOff (GuestAddrs.validate_header + 352)
          (GuestAddrs.validate_header + 280)))
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
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (3 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Status 5 exit — `li a0, 5` @ `H+292` → `j` → epilogue -/

set_option maxRecDepth 8000 in
theorem status5Exit
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 292) raIn callerCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (5 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (5 : Word) (H + 292) (by decide)
  have s1 := jal_x0_spec_gen_within (56 : BitVec 21) (H + 296)
  rw [show (H + 296) + signExtend21 (56 : BitVec 21) = H + 352 from by
    rw [show signExtend21 (56 : BitVec 21) = (56 : Word) from by decide]
    bv_omega] at s1
  have hblock : cpsTripleWithin 2 (H + 292) (H + 352) callerCode
      ((.x10 ↦ᵣ o10))
      ((.x10 ↦ᵣ (5 : Word))) := by
    have s0C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 292) prog 73 (.LI .x10 (5 : Word))
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      s0
    have s1C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 296) prog 74
        (.JAL .x0 (56 : BitVec 21))
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
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (5 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Status 6 exit — `li a0, 6` @ `H+300` → `j` → epilogue -/

set_option maxRecDepth 8000 in
theorem status6Exit
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 11 (H + 300) raIn callerCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (6 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (6 : Word) (H + 300) (by decide)
  have s1 := jal_x0_spec_gen_within (48 : BitVec 21) (H + 304)
  rw [show (H + 304) + signExtend21 (48 : BitVec 21) = H + 352 from by
    rw [show signExtend21 (48 : BitVec 21) = (48 : Word) from by decide]
    bv_omega] at s1
  have hblock : cpsTripleWithin 2 (H + 300) (H + 352) callerCode
      ((.x10 ↦ᵣ o10))
      ((.x10 ↦ᵣ (6 : Word))) := by
    have s0C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 300) prog 75 (.LI .x10 (6 : Word))
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      s0
    have s1C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 304) prog 76
        (.JAL .x0 (48 : BitVec 21))
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
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (6 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## Conjunct 3 — `gasUsed > gasLimit` (bltu) → status 3

    `LD` used@88 / lim@80, then `BLTU lim, used` @ `H+96` taken → `status3Exit`. -/

abbrev gasUsedExceedsBrOff : BitVec 13 :=
  brOff (GuestAddrs.validate_header + 276) (GuestAddrs.validate_header + 96)

theorem gasUsedExceeds_taken_pc :
    (H + 96) + signExtend13 gasUsedExceedsBrOff = H + 276 := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 96 +
      signExtend13 (brOff (GuestAddrs.validate_header + 276)
        (GuestAddrs.validate_header + 96)) =
    BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 276
  exact brOff_correct_base_off GuestAddrs.validate_header 96 276
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem gasUsedExceeds_taken (gasLimit gasUsed : Word)
    (h_ult : BitVec.ult gasLimit gasUsed) :
    cpsTripleWithin 1 (H + 96) (H + 276) callerCode
      ((.x6 ↦ᵣ gasLimit) ** (.x5 ↦ᵣ gasUsed))
      ((.x6 ↦ᵣ gasLimit) ** (.x5 ↦ᵣ gasUsed)) := by
  have hbr := bltu_spec_gen_within .x6 .x5 gasUsedExceedsBrOff gasLimit gasUsed (H + 96)
  rw [gasUsedExceeds_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 96) prog 24
        (.BLTU .x6 .x5 gasUsedExceedsBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 h_ult)

theorem gasUsedExceeds_ntaken (gasLimit gasUsed : Word)
    (h_ok : ¬ BitVec.ult gasLimit gasUsed) :
    cpsTripleWithin 1 (H + 96) (H + 100) callerCode
      ((.x6 ↦ᵣ gasLimit) ** (.x5 ↦ᵣ gasUsed))
      ((.x6 ↦ᵣ gasLimit) ** (.x5 ↦ᵣ gasUsed)) := by
  have hbr := bltu_spec_gen_within .x6 .x5 gasUsedExceedsBrOff gasLimit gasUsed (H + 96)
  rw [show (H + 96 : Word) + 4 = H + 100 from by bv_omega] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 96) prog 24
        (.BLTU .x6 .x5 gasUsedExceedsBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact h_ok ((sepConj_pure_right _).1 hBP).2)

theorem ldGasUsed (headerBase o5 gasUsed : Word) :
    cpsTripleWithin 1 (H + 88) (H + 92) callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ o5) ** ((headerBase + 88) ↦ₘ gasUsed))
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ gasUsed) ** ((headerBase + 88) ↦ₘ gasUsed)) := by
  have h := ld_spec_gen_within .x5 .x18 headerBase o5 gasUsed (88 : BitVec 12) (H + 88)
    (by decide)
  rw [show signExtend12 (88 : BitVec 12) = (88 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 88) prog 22 (.LD .x5 .x18 (88 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

theorem ldGasLimit (headerBase o6 gasLimit : Word) :
    cpsTripleWithin 1 (H + 92) (H + 96) callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x6 ↦ᵣ o6) ** ((headerBase + 80) ↦ₘ gasLimit))
      ((.x18 ↦ᵣ headerBase) ** (.x6 ↦ᵣ gasLimit) ** ((headerBase + 80) ↦ₘ gasLimit)) := by
  have h := ld_spec_gen_within .x6 .x18 headerBase o6 gasLimit (80 : BitVec 12) (H + 92)
    (by decide)
  rw [show signExtend12 (80 : BitVec 12) = (80 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 92) prog 23 (.LD .x6 .x18 (80 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

set_option maxRecDepth 8000 in
theorem gasUsedExceeds_reject
    (sp0 spC raIn headerBase gasLimit gasUsed
      cs0 cs1 cs2 cs3 cs4 cs5 o10 o5 o6 o1 o8 o9 o19 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (h_ult : BitVec.ult gasLimit gasUsed) :
    cpsTripleWithin 14 (H + 88) raIn callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ o5) ** (.x6 ↦ᵣ o6) **
        ((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
        (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (3 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (.x5 ↦ᵣ gasUsed) ** (.x6 ↦ᵣ gasLimit) **
        ((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have h0 := ldGasUsed headerBase o5 gasUsed
  have h0F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ o6) ** ((headerBase + 80) ↦ₘ gasLimit) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
      (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h0
  have h1 := ldGasLimit headerBase o6 gasLimit
  have h1F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ gasUsed) ** ((headerBase + 88) ↦ₘ gasUsed) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
      (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h1
  have hb := gasUsedExceeds_taken gasLimit gasUsed h_ult
  have hbF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** ((headerBase + 88) ↦ₘ gasUsed) **
      ((headerBase + 80) ↦ₘ gasLimit) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
      (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hb
  have hex := status3Exit sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o10 o1 o8 o9 headerBase o19 o20 o21
    ((.x5 ↦ᵣ gasUsed) ** (.x6 ↦ᵣ gasLimit) **
      ((headerBase + 88) ↦ₘ gasUsed) ** ((headerBase + 80) ↦ₘ gasLimit) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs)
    hspC hret
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hbF
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 hex
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s3


/-! ## Conjunct 5 — `timestamp ≤ parent` (bgeu) → status 5

    `LD` header@72 / parent@72, then `BGEU parent, header` @ `H+148` taken
    → `status5Exit`. -/

abbrev timestampNotIncreasingBrOff : BitVec 13 :=
  brOff (GuestAddrs.validate_header + 292) (GuestAddrs.validate_header + 148)

theorem timestampNotIncreasing_taken_pc :
    (H + 148) + signExtend13 timestampNotIncreasingBrOff = H + 292 := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 148 +
      signExtend13 (brOff (GuestAddrs.validate_header + 292)
        (GuestAddrs.validate_header + 148)) =
    BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 292
  exact brOff_correct_base_off GuestAddrs.validate_header 148 292
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem timestampNotIncreasing_taken (parentTs headerTs : Word)
    (h_ge : ¬ BitVec.ult parentTs headerTs) :
    cpsTripleWithin 1 (H + 148) (H + 292) callerCode
      ((.x6 ↦ᵣ parentTs) ** (.x5 ↦ᵣ headerTs))
      ((.x6 ↦ᵣ parentTs) ** (.x5 ↦ᵣ headerTs)) := by
  have hbr := bgeu_spec_gen_within .x6 .x5 timestampNotIncreasingBrOff parentTs headerTs
    (H + 148)
  rw [timestampNotIncreasing_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 148) prog 37
        (.BGEU .x6 .x5 timestampNotIncreasingBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ge ((sepConj_pure_right _).1 hBP).2)

theorem timestampNotIncreasing_ntaken (parentTs headerTs : Word)
    (h_lt : BitVec.ult parentTs headerTs) :
    cpsTripleWithin 1 (H + 148) (H + 152) callerCode
      ((.x6 ↦ᵣ parentTs) ** (.x5 ↦ᵣ headerTs))
      ((.x6 ↦ᵣ parentTs) ** (.x5 ↦ᵣ headerTs)) := by
  have hbr := bgeu_spec_gen_within .x6 .x5 timestampNotIncreasingBrOff parentTs headerTs
    (H + 148)
  rw [show (H + 148 : Word) + 4 = H + 152 from by bv_omega] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 148) prog 37
        (.BGEU .x6 .x5 timestampNotIncreasingBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_lt)

theorem ldHeaderTimestamp (headerBase o5 headerTs : Word) :
    cpsTripleWithin 1 (H + 140) (H + 144) callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ o5) ** ((headerBase + 72) ↦ₘ headerTs))
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ headerTs) ** ((headerBase + 72) ↦ₘ headerTs)) := by
  have h := ld_spec_gen_within .x5 .x18 headerBase o5 headerTs (72 : BitVec 12) (H + 140)
    (by decide)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 140) prog 35 (.LD .x5 .x18 (72 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

theorem ldParentTimestamp (parentBase o6 parentTs : Word) :
    cpsTripleWithin 1 (H + 144) (H + 148) callerCode
      ((.x19 ↦ᵣ parentBase) ** (.x6 ↦ᵣ o6) ** ((parentBase + 72) ↦ₘ parentTs))
      ((.x19 ↦ᵣ parentBase) ** (.x6 ↦ᵣ parentTs) ** ((parentBase + 72) ↦ₘ parentTs)) := by
  have h := ld_spec_gen_within .x6 .x19 parentBase o6 parentTs (72 : BitVec 12) (H + 144)
    (by decide)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 144) prog 36 (.LD .x6 .x19 (72 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

set_option maxRecDepth 8000 in
theorem timestampNotIncreasing_reject
    (sp0 spC raIn headerBase parentBase headerTs parentTs
      cs0 cs1 cs2 cs3 cs4 cs5 o10 o5 o6 o1 o8 o9 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (h_ge : ¬ BitVec.ult parentTs headerTs) :
    cpsTripleWithin 14 (H + 140) raIn callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x19 ↦ᵣ parentBase) ** (.x5 ↦ᵣ o5) ** (.x6 ↦ᵣ o6) **
        ((headerBase + 72) ↦ₘ headerTs) ** ((parentBase + 72) ↦ₘ parentTs) **
        (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (5 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (.x5 ↦ᵣ headerTs) ** (.x6 ↦ᵣ parentTs) **
        ((headerBase + 72) ↦ₘ headerTs) ** ((parentBase + 72) ↦ₘ parentTs) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have h0 := ldHeaderTimestamp headerBase o5 headerTs
  have h0F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ parentBase) ** (.x6 ↦ᵣ o6) ** ((parentBase + 72) ↦ₘ parentTs) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h0
  have h1 := ldParentTimestamp parentBase o6 parentTs
  have h1F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ headerTs) ** ((headerBase + 72) ↦ₘ headerTs) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h1
  have hb := timestampNotIncreasing_taken parentTs headerTs h_ge
  have hbF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** (.x19 ↦ᵣ parentBase) **
      ((headerBase + 72) ↦ₘ headerTs) ** ((parentBase + 72) ↦ₘ parentTs) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hb
  have hex := status5Exit sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o10 o1 o8 o9 headerBase parentBase o20 o21
    ((.x5 ↦ᵣ headerTs) ** (.x6 ↦ᵣ parentTs) **
      ((headerBase + 72) ↦ₘ headerTs) ** ((parentBase + 72) ↦ₘ parentTs) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs)
    hspC hret
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hbF
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 hex
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s3


/-! ## Conjunct 6 — `number ≠ parent + 1` (addi+bne) → status 6

    BitVec `+ 1` is mod `2^64`. SpecRef correspondence for unbounded
    `parent.number + 1` needs a named no-wrap gate on the parent number
    (`parent ≠ ~~~0`); the reject arm itself is the RV64 comparison. -/

abbrev numberNotSuccBrOff : BitVec 13 :=
  brOff (GuestAddrs.validate_header + 300) (GuestAddrs.validate_header + 164)

theorem numberNotSucc_taken_pc :
    (H + 164) + signExtend13 numberNotSuccBrOff = H + 300 := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 164 +
      signExtend13 (brOff (GuestAddrs.validate_header + 300)
        (GuestAddrs.validate_header + 164)) =
    BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 300
  exact brOff_correct_base_off GuestAddrs.validate_header 164 300
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem numberNotSucc_taken (headerNum parentSucc : Word)
    (hne : headerNum ≠ parentSucc) :
    cpsTripleWithin 1 (H + 164) (H + 300) callerCode
      ((.x5 ↦ᵣ headerNum) ** (.x6 ↦ᵣ parentSucc))
      ((.x5 ↦ᵣ headerNum) ** (.x6 ↦ᵣ parentSucc)) := by
  have hbr := bne_spec_gen_within .x5 .x6 numberNotSuccBrOff headerNum parentSucc (H + 164)
  rw [numberNotSucc_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 164) prog 41
        (.BNE .x5 .x6 numberNotSuccBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hne ((sepConj_pure_right _).1 hBP).2)

theorem numberNotSucc_ntaken (headerNum parentSucc : Word)
    (heq : headerNum = parentSucc) :
    cpsTripleWithin 1 (H + 164) (H + 168) callerCode
      ((.x5 ↦ᵣ headerNum) ** (.x6 ↦ᵣ parentSucc))
      ((.x5 ↦ᵣ headerNum) ** (.x6 ↦ᵣ parentSucc)) := by
  have hbr := bne_spec_gen_within .x5 .x6 numberNotSuccBrOff headerNum parentSucc (H + 164)
  rw [show (H + 164 : Word) + 4 = H + 168 from by bv_omega] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 164) prog 41
        (.BNE .x5 .x6 numberNotSuccBrOff)
        (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
      hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 heq)

theorem ldHeaderNumber6 (headerBase o5 headerNum : Word) :
    cpsTripleWithin 1 (H + 152) (H + 156) callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ o5) ** ((headerBase + 64) ↦ₘ headerNum))
      ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ headerNum) ** ((headerBase + 64) ↦ₘ headerNum)) := by
  have h := ld_spec_gen_within .x5 .x18 headerBase o5 headerNum (64 : BitVec 12) (H + 152)
    (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 152) prog 38 (.LD .x5 .x18 (64 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

theorem ldParentNumber6 (parentBase o6 parentNum : Word) :
    cpsTripleWithin 1 (H + 156) (H + 160) callerCode
      ((.x19 ↦ᵣ parentBase) ** (.x6 ↦ᵣ o6) ** ((parentBase + 64) ↦ₘ parentNum))
      ((.x19 ↦ᵣ parentBase) ** (.x6 ↦ᵣ parentNum) ** ((parentBase + 64) ↦ₘ parentNum)) := by
  have h := ld_spec_gen_within .x6 .x19 parentBase o6 parentNum (64 : BitVec 12) (H + 156)
    (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 156) prog 39 (.LD .x6 .x19 (64 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

theorem addiParentSucc (parentNum : Word) :
    cpsTripleWithin 1 (H + 160) (H + 164) callerCode
      (.x6 ↦ᵣ parentNum)
      (.x6 ↦ᵣ (parentNum + 1)) := by
  have h := addi_spec_gen_same_within .x6 parentNum (1 : BitVec 12) (H + 160) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at h
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 160) prog 40 (.ADDI .x6 .x6 (1 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    h

set_option maxRecDepth 8000 in
theorem numberNotSucc_reject
    (sp0 spC raIn headerBase parentBase headerNum parentNum
      cs0 cs1 cs2 cs3 cs4 cs5 o10 o5 o6 o1 o8 o9 o20 o21 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hne : headerNum ≠ parentNum + 1) :
    cpsTripleWithin 15 (H + 152) raIn callerCode
      ((.x18 ↦ᵣ headerBase) ** (.x19 ↦ᵣ parentBase) ** (.x5 ↦ᵣ o5) ** (.x6 ↦ᵣ o6) **
        ((headerBase + 64) ↦ₘ headerNum) ** ((parentBase + 64) ↦ₘ parentNum) **
        (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (6 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (.x5 ↦ᵣ headerNum) ** (.x6 ↦ᵣ (parentNum + 1)) **
        ((headerBase + 64) ↦ₘ headerNum) ** ((parentBase + 64) ↦ₘ parentNum) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have h0 := ldHeaderNumber6 headerBase o5 headerNum
  have h0F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ parentBase) ** (.x6 ↦ᵣ o6) ** ((parentBase + 64) ↦ₘ parentNum) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h0
  have h1 := ldParentNumber6 parentBase o6 parentNum
  have h1F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** (.x5 ↦ᵣ headerNum) ** ((headerBase + 64) ↦ₘ headerNum) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h1
  have h2 := addiParentSucc parentNum
  have h2F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** (.x19 ↦ᵣ parentBase) ** (.x5 ↦ᵣ headerNum) **
      ((headerBase + 64) ↦ₘ headerNum) ** ((parentBase + 64) ↦ₘ parentNum) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) h2
  have hb := numberNotSucc_taken headerNum (parentNum + 1) hne
  have hbF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ headerBase) ** (.x19 ↦ᵣ parentBase) **
      ((headerBase + 64) ↦ₘ headerNum) ** ((parentBase + 64) ↦ₘ parentNum) **
      (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs) hb
  have hex := status6Exit sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o10 o1 o8 o9 headerBase parentBase o20 o21
    ((.x5 ↦ᵣ headerNum) ** (.x6 ↦ᵣ (parentNum + 1)) **
      ((headerBase + 64) ↦ₘ headerNum) ** ((parentBase + 64) ↦ₘ parentNum) ** G)
    (by repeat' first | exact hG | apply pcFree_sepConj | exact pcFree_regIs
                      | exact pcFree_memIs)
    hspC hret
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 h2F
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 hbF
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 hex
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) s4

end EvmAsm.Codegen.ValidateHeaderInlineArms
