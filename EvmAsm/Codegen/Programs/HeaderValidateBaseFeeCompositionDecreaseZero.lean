/-
  Zero-gas decrease route for K73 (#13164).

  The equality branch at K73 + 40 handles gasUsed = target.  Consequently
  the gasUsed = 0 shortcut below it is a genuine decrease route whenever the
  target is positive.  This file starts with the byte-image bridge for that
  route; the control-flow adapter is added only after this identity is
  kernel-checked.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseRouteB
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseRoute

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256SubBeSAsm
open EvmAsm.Stateless.SpecRef

/-- The zero-gas shortcut writes `parentFee - parentFee / 8`, which is the
    reference recurrence at `gasUsed = 0` when the parent target is positive.
    The proof is stated over the actual 32-byte machine buffers, not merely
    their numeric values, so it can be used to cast the subtractor's output
    region into the Route-B post. -/
theorem k73_zero_machine_bytes_eq_written
    {gasLimit : Word} {parentBytes : List (BitVec 8)}
    (htargetPos : 0 < (gasLimit >>> 1).toNat)
    (hlenP : parentBytes.length = 32) :
    u256SubBeBytes parentBytes
        (u256DivU64BeQuotBytes parentBytes parentBytes 8)
        (u256DivU64BeQuotBytes parentBytes parentBytes 8)
      = hvbfWrittenImage gasLimit 0 parentBytes := by
  have hqv : EvmAsm.Crypto.beBytesToNat
        (u256DivU64BeQuotBytes parentBytes parentBytes 8) =
      EvmAsm.Crypto.beBytesToNat parentBytes / 8 :=
    k73_decr_quot_val parentBytes 8 (by decide) (by decide) hlenP
  have hqlen : (u256DivU64BeQuotBytes parentBytes parentBytes 8).length = 32 := by
    have hq := k73_quot_bytes_natToBytesBE parentBytes parentBytes 8
      hlenP hlenP (by decide) (by decide)
    rw [hq]
    simp
  have hleSub : EvmAsm.Crypto.beBytesToNat
        (u256DivU64BeQuotBytes parentBytes parentBytes 8) ≤
      EvmAsm.Crypto.beBytesToNat parentBytes := by
    rw [hqv]
    exact Nat.div_le_self _ _
  have hsubmod := EvmAsm.Codegen.U256BeFlat.u256SubBe_mod_and_borrow
    parentBytes (u256DivU64BeQuotBytes parentBytes parentBytes 8)
      (u256DivU64BeQuotBytes parentBytes parentBytes 8)
      hlenP hqlen hqlen
  have hsubv : EvmAsm.Crypto.beBytesToNat
        (u256SubBeBytes parentBytes
          (u256DivU64BeQuotBytes parentBytes parentBytes 8)
          (u256DivU64BeQuotBytes parentBytes parentBytes 8)) =
    EvmAsm.Crypto.beBytesToNat parentBytes -
        EvmAsm.Crypto.beBytesToNat parentBytes / 8 := by
    obtain ⟨_, hmod⟩ := hsubmod
    rw [hmod]
    have hp := k73_fixed_bytes_bound parentBytes
    rw [k73_bytesBEtoNat_eq_beBytesToNat, hlenP] at hp
    have hp' : EvmAsm.Crypto.beBytesToNat parentBytes < 2 ^ 256 := by
      have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
      simpa [hpow] using hp
    rw [show 2 ^ 256 + EvmAsm.Crypto.beBytesToNat parentBytes -
        EvmAsm.Crypto.beBytesToNat
          (u256DivU64BeQuotBytes parentBytes parentBytes 8) =
        (EvmAsm.Crypto.beBytesToNat parentBytes -
          EvmAsm.Crypto.beBytesToNat
            (u256DivU64BeQuotBytes parentBytes parentBytes 8)) + 2 ^ 256 by
          omega]
    rw [Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt]
    rw [hqv]
    omega
  apply k73_bytes_inj_same_length
  · rw [EvmAsm.Codegen.U256BeFlat.u256SubBeBytes_length
      parentBytes
      (u256DivU64BeQuotBytes parentBytes parentBytes 8)
      (u256DivU64BeQuotBytes parentBytes parentBytes 8) hqlen]
    exact (hvbfWrittenImage_length gasLimit 0 parentBytes).symm
  · have hswap : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes =
        EvmAsm.Crypto.beBytesToNat parentBytes :=
      k73_bytesBEtoNat_eq_beBytesToNat parentBytes
    have htargetNat : (gasLimit >>> 1).toNat = gasLimit.toNat / 2 := rfl
    have htargetNatPos : 0 < gasLimit.toNat / 2 := by
      rw [← htargetNat]
      exact htargetPos
    have hneOuter : ¬ ((0 == gasLimit.toNat / 2) = true) := by
      intro h
      have hz := beq_iff_eq.mp h
      omega
    have hneInner : ¬ (0 > gasLimit.toNat / 2) := by omega
    have hp := k73_fixed_bytes_bound parentBytes
    rw [k73_bytesBEtoNat_eq_beBytesToNat, hlenP] at hp
    have hvv := k73_fixed_bytes_value 32
      (EvmAsm.Crypto.beBytesToNat parentBytes -
        EvmAsm.Crypto.beBytesToNat parentBytes / 8)
    have hvalExpected : EvmAsm.Crypto.beBytesToNat
        (hvbfWrittenImage gasLimit 0 parentBytes) =
        EvmAsm.Crypto.beBytesToNat parentBytes -
          EvmAsm.Crypto.beBytesToNat parentBytes / 8 := by
      show EvmAsm.Crypto.beBytesToNat
        (EvmAsm.Stateless.SpecRef.natToBytesBE 32
          (EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide 0
            (gasLimit.toNat / 2)
            (EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes))) = _
      rw [hswap, EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide,
        if_neg hneOuter, if_neg hneInner]
      rw [EvmAsm.Stateless.SpecRef.baseFeeDecreaseDelta_eq_reference]
      simp only [Nat.sub_zero]
      rw [Nat.mul_comm (EvmAsm.Crypto.beBytesToNat parentBytes)
        (gasLimit.toNat / 2)]
      rw [Nat.mul_div_cancel_left _ htargetNatPos]
      exact Eq.trans hvv (Nat.mod_eq_of_lt (by omega))
    rw [hsubv, hvalExpected]

/-! The zero route has no multiply scratch.  The K74 flat frame supplies only
    the four registers which the shared flat divider/subtractor contracts
    mention beyond K73's own footprint; all other atoms below are already in
    `k73PreRest`, so repeating them in this ambient would make the premise
    unsatisfiable. -/

def k73_zero_env (F : Assertion) : Assertion :=
  regOwns [.x14, .x15, .x16, .x17] ** F

def k73_zero_outj (F : Assertion) : Assertion :=
  k74FlatFrame F

def k73_zero_outj_tail (F : Assertion) : Assertion := F

theorem k73_zero_outj_out_eq (F : Assertion) :
    k73_zero_outj F = k74FlatFrame (k73_zero_outj_tail F) := by
  rfl

/-! The zero route's bound is kept separate from the nonzero-decrease bound:
    there is no multiply call, but it still performs the two flat divider and
    subtract calls before the shared borrow/status tails. -/

def k73_zero_route_steps (parentPtr : Word)
    (parentBytes expectedBytes : List (BitVec 8)) : Nat :=
  15 + 3 +
      (5 + (u256DivU64BeFn parentPtr Expected 8 parentBytes expectedBytes).body.steps) +
      1 + 3 +
      (5 + (u256SubBeInPlaceFn parentPtr Expected parentBytes
        (u256DivU64BeQuotBytes parentBytes expectedBytes 8)).body.steps) +
      20

/-! A branch whose two exits have already been reduced to one return point is
    useful for the zero route just as it is for Route-B's nonzero route. -/

private theorem k73_zero_branch_to_triple {n : Nat} {entry pt : Word}
    {cr : CodeReq} {P Qt Qf : Assertion}
    (h : cpsBranchWithin n entry cr P pt Qt pt Qf) :
    cpsTripleWithin n entry pt cr P (fun s => Qt s ∨ Qf s) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  rcases hbranch with ⟨hpc', hQR⟩ | ⟨hpc', hQR⟩
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    exact ⟨hpc', hst, hcomp, decr_or_left_lift _ hhold⟩
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    exact ⟨hpc', hst, hcomp, decr_or_right_lift _ hhold⟩

/-! After the subtract call, the six K73 frame pins and the three live
    pointer/value pins are converted to ownership/preserved form expected by
    the common return tails.  The ambient `P` contains only the tail-owned
    frame, header/base regions, and the caller's extra assertion. -/

private theorem k73_zero_exit_to_tail_pre
    (spK raIn basePtr outPtr headerPtr v9 old18 target v19 v20 : Word)
    (baseBytes subBytes : List (BitVec 8)) (P : Assertion) :
    ∀ u : PartialState,
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 224)) **
        (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20) **
        (.x2 ↦ᵣ spK) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch ** bytesRegion outPtr subBytes **
        bytesRegion basePtr baseBytes ** P ** regOwn .x10) u →
      ((.x2 ↦ᵣ spK) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20) **
        regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr subBytes ** bytesRegion basePtr baseBytes ** P) u := by
  intro u hu
  have c1 := decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
    (decr_sep_pin_lift (r := Reg.x1) (v := K73 + 224)) u hu
  have c2 := decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
    (decr_under_id (B := regOwn .x1)
      (decr_sep_pin_lift (r := Reg.x8) (v := basePtr))) u c1
  have c3 := decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
    (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
        (decr_sep_pin_lift (r := Reg.x9) (v := outPtr)))) u c2
  have c4 := decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
    (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
        (decr_under_id (B := regOwn .x9)
          (decr_sep_pin_lift (r := Reg.x18) (v := target))))) u c3
  have c5 := decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
    (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
        (decr_under_id (B := regOwn .x9)
          (decr_under_id (B := regOwn .x18)
            (decr_sep_pin_lift (r := Reg.x19) (v := v19)))))) u c4
  have c6 := decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
    (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
        (decr_under_id (B := regOwn .x9)
          (decr_under_id (B := regOwn .x18)
            (decr_under_id (B := regOwn .x19)
              (decr_sep_pin_lift (r := Reg.x20) (v := v20))))))) u c5
  have hEq :
      ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20) **
        (.x2 ↦ᵣ spK) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch ** bytesRegion outPtr subBytes **
        bytesRegion basePtr baseBytes ** P ** regOwn .x10) =
      ((.x2 ↦ᵣ spK) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20) **
        regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr subBytes ** bytesRegion basePtr baseBytes ** P) := by
    xperm_cert_eq
  exact hEq ▸ c6

/-! The four entry guards are the exact path conditions for the emitted
    `gasUsed = 0`, positive-target decrease shortcut.  This is deliberately a
    route theorem, not a stronger whole-entry precondition: the universal K73
    theorem obtains these facts from its branch guards. -/

theorem k73_zero_entry_to_div_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hgasZero : gasUsed = 0)
    (htargetPos : 0 < target.toNat)
    (hF : F.pcFree) :
    cpsTripleWithin 15 K73 (K73 + 160) wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outBytes F)
      (k73HeadPost spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 (0 : Word) v20 baseBytes outBytes F) := by
  have hhead := k73_head_spec_within
    sp0 spH raIn gasLimit gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes outBytes F hsp htarget hF
  let Rest : Assertion :=
    ((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x19 : Reg) ↦ᵣ v19) ** ((.x10 : Reg) ↦ᵣ gasLimit) **
      ((.x12 : Reg) ↦ᵣ basePtr) ** ((.x13 : Reg) ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    pcf
    exact hF
  have hbeq := beq_spec_gen_within .x11 .x18 (196 : BitVec 13)
    gasUsed target (K73 + 40)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 10 _ (K73 + 40) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (196 : BitVec 13) = (196 : Word) by decide,
    show (K73 + 40) + (196 : Word) = K73 + 236 by bv_omega,
    show (K73 + 40) + 4 = K73 + 44 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR
    (((.x20 : Reg) ↦ᵣ v20) ** Rest) (by pcf; exact hF) hbeqC
  have hneq := cpsBranchWithin_ntakenPath hbeqF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, -⟩ := hp
    exact hne h_eq)
  have hneq0 := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word))
    (by pcf) hneq
  have hneq' : cpsTripleWithin 1 (K73 + 40) (K73 + 44) wholeCode
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x18 : Reg) ↦ᵣ target) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x0 : Reg) ↦ᵣ 0) ** Rest)
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x18 : Reg) ↦ᵣ target) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x0 : Reg) ↦ᵣ 0) ** Rest) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) hneq0
  have h1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [k73HeadPost, Rest] at hp ⊢
      xperm_chunked hp) hhead hneq'
  have hli := li_spec_gen_within .x20 v20 (0 : Word) (K73 + 44) (by decide)
  have hliC := cpsTripleWithin_extend_code
    (k73_whole_mem 11 _ (K73 + 44) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hli
  have hliF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x18 : Reg) ↦ᵣ target) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest)
    (by pcf; exact hF) hliC
  have h2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Rest] at hp ⊢
      xperm_chunked hp) h1 hliF
  have htargetNZ : target ≠ (0 : Word) := by
    intro hz
    have hz' : (0 : Nat) < 0 := by simpa [hz] using htargetPos
    exact (by omega : ¬ ((0 : Nat) < 0)) hz'
  have hguard := beq_spec_gen_within .x18 .x0 (228 : BitVec 13)
    target (0 : Word) (K73 + 48)
  have hguardC := cpsBranchWithin_extend_code
    (k73_whole_mem 12 _ (K73 + 48) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hguard
  rw [show signExtend13 (228 : BitVec 13) = (228 : Word) by decide,
    show (K73 + 48) + (228 : Word) = K73 + 276 by bv_omega,
    show (K73 + 48) + 4 = K73 + 52 by bv_omega] at hguardC
  have hguardF := cpsBranchWithin_frameR
    (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      Rest) (by pcf; exact hF) hguardC
  have hguardnt := cpsBranchWithin_ntakenPath hguardF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, -⟩ := hp
    exact htargetNZ h_eq)
  have hguardnt' : cpsTripleWithin 1 (K73 + 48) (K73 + 52) wholeCode
      (((.x18 : Reg) ↦ᵣ target) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest)
      (((.x18 : Reg) ↦ᵣ target) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) hguardnt
  have h3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Rest] at hp ⊢
      xperm_chunked hp) h2 hguardnt'
  have hbltu := bltu_spec_gen_within .x18 .x11 (16 : BitVec 13)
    target gasUsed (K73 + 52)
  have hbltuC := cpsBranchWithin_extend_code
    (k73_whole_mem 13 _ (K73 + 52) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbltu
  rw [show signExtend13 (16 : BitVec 13) = (16 : Word) by decide,
    show (K73 + 52) + (16 : Word) = K73 + 68 by bv_omega,
    show (K73 + 52) + 4 = K73 + 56 by bv_omega] at hbltuC
  have hbltuF := cpsBranchWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      Rest) (by pcf; exact hF) hbltuC
  have hbltuNT := cpsBranchWithin_ntakenPath hbltuF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_lt, -⟩ := hp
    exact hnotlt ((BitVec.ult_iff_toNat_lt).1 h_lt))
  have hbltuNT' : cpsTripleWithin 1 (K73 + 52) (K73 + 56) wholeCode
      (((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ gasUsed) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest)
      (((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ gasUsed) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) hbltuNT
  have h4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Rest] at hp ⊢
      xperm_chunked hp) h3 hbltuNT'
  have hbeq0 := beq_spec_gen_within .x11 .x0 (104 : BitVec 13)
    gasUsed (0 : Word) (K73 + 56)
  have hbeq0C := cpsBranchWithin_extend_code
    (k73_whole_mem 14 _ (K73 + 56) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq0
  rw [show signExtend13 (104 : BitVec 13) = (104 : Word) by decide,
    show (K73 + 56) + (104 : Word) = K73 + 160 by bv_omega,
    show (K73 + 56) + 4 = K73 + 60 by bv_omega] at hbeq0C
  have hbeq0F := cpsBranchWithin_frameR
    (((.x18 : Reg) ↦ᵣ target) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      Rest) (by pcf; exact hF) hbeq0C
  have htaken := cpsBranchWithin_takenPath hbeq0F (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, -⟩ := hp
    exact h_eq hgasZero)
  have htaken' : cpsTripleWithin 1 (K73 + 56) (K73 + 160) wholeCode
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ target) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest)
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ target) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) htaken
  have h5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Rest] at hp ⊢
      xperm_chunked hp) h4 htaken'
  dsimp [k73HeadPost, Rest] at h5 ⊢
  exact cpsTripleWithin_mono_nSteps (nSteps' := 15) (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) h5)

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero
