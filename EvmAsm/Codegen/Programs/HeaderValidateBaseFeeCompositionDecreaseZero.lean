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
  k74FlatFrame F

def k73_zero_outj (F : Assertion) : Assertion :=
  k74FlatFrame F

def k73_zero_outj_tail (F : Assertion) : Assertion := F

theorem k73_zero_outj_out_eq (F : Assertion) :
    k73_zero_outj F = k74FlatFrame (k73_zero_outj_tail F) := by
  rfl

private theorem k73_zero_br_cast {le le' : List (BitVec 8)} {Z : Assertion}
    (heq : le = le') :
    ∀ q : PartialState, ((bytesRegion Expected le ** Z) q) →
      ((bytesRegion Expected le' ** Z) q) :=
  fun _ hp => heq ▸ hp

/-! The zero route's bound is kept separate from the nonzero-decrease bound:
    there is no multiply call, but it still performs the two flat divider and
    subtract calls before the shared borrow/status tails. -/

def k73_zero_route_steps (parentPtr : Word)
    (parentBytes expectedBytes : List (BitVec 8)) : Nat :=
  15 +
      (5 + (u256DivU64BeFn parentPtr Expected 8 parentBytes expectedBytes).body.steps) +
      1 +
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
    (spK raIn basePtr outPtr headerPtr v9 old18 target v19 v20Now v20Saved : Word)
    (baseBytes subBytes : List (BitVec 8)) (P : Assertion) :
    ∀ u : PartialState,
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 224)) **
        (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20Now) **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20Saved) **
        (.x2 ↦ᵣ spK) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch ** bytesRegion outPtr subBytes **
        bytesRegion basePtr baseBytes ** P ** regOwn .x10) u →
      ((.x2 ↦ᵣ spK) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20Saved) **
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
              (decr_sep_pin_lift (r := Reg.x20) (v := v20Now))))))) u c5
  have hEq :
      ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20Saved) **
        (.x2 ↦ᵣ spK) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch ** bytesRegion outPtr subBytes **
        bytesRegion basePtr baseBytes ** P ** regOwn .x10) =
      ((.x2 ↦ᵣ spK) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        frameSlotsSaved k73Frame spK
          (k73Saved raIn headerPtr v9 old18 v19 v20Saved) **
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
    simp [hz] at htargetPos
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

/-! The complete zero-gas decrease route.  The entry prefix establishes
    `x20 = 0`; the single divide writes the parent fee divided by eight, and
    the `x20` shortcut then reaches the in-place subtract.  The final borrow
    branch is shared with the nonzero decrease route, but the ambient has no
    multiply frame: only the K74 flat-frame registers ride through it. -/

theorem k73_zero_route_adapter {cr : CodeReq}
    (spH spK old8 headerPtr gasLimit gasUsed target parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hgasZero : gasUsed = 0)
    (htargetPos : 0 < target.toNat)
    (hret : ((H + 40 : Word) &&& ~~~(1 : Word)) = H + 40)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨Expected, 32⟩)
    (hroBase : Region.wf ⟨parentPtr, parentBytes⟩)
    (hlenP : parentBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hovBase : parentPtr.toNat + 32 < 2 ^ 64)
    (hovExpected : Expected.toNat + 32 < 2 ^ 64)
    (hdisj : parentPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ parentPtr.toNat)
    (hszDiv :
      4 * ((u256DivU64BeFn parentPtr Expected 8 parentBytes expectedBytes).body.size + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn parentPtr Expected parentBytes
        (u256DivU64BeQuotBytes parentBytes expectedBytes 8)).body.size + 1)
        ≤ 2 ^ 64)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i) :
    cpsTripleWithin (k73_zero_route_steps parentPtr parentBytes expectedBytes)
      K73 (H + 40) cr
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes (H + 40) old8
          (k73_zero_env F))
      ((.x1 ↦ᵣ (H + 40)) **
        k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18 target v19 v20
          gasUsed gasLimit parentPtr parentBytes headerBytes
          (k73_zero_outj F)) := by
  let Ftail0 : Assertion :=
    frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
      bytesRegion headerPtr headerBytes ** F
  let Fenv : Assertion := k73_zero_env Ftail0
  let Fdiv : Assertion :=
    ((.x2 : Reg) ↦ᵣ spK) **
      ((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ v19) **
      frameSlotsSaved k73Frame spK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** Ftail0
  let FdivFull : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Fdiv
  let q1 : List (BitVec 8) :=
    u256DivU64BeQuotBytes parentBytes expectedBytes 8
  let sBytes : List (BitVec 8) := u256SubBeBytes parentBytes q1 q1
  let nDiv : Nat :=
    5 + (u256DivU64BeFn parentPtr Expected 8 parentBytes expectedBytes).body.steps
  let nSub : Nat :=
    5 + (u256SubBeInPlaceFn parentPtr Expected parentBytes q1).body.steps
  have hFtail0 : Ftail0.pcFree := by
    dsimp [Ftail0]
    pcf
    exact hF
  have hFenv : Fenv.pcFree := by
    dsimp [Fenv]
    pcf
    exact hF
  have hFdiv : Fdiv.pcFree := by
    dsimp [Fdiv, Ftail0]
    pcf
    exact hF
  have hq1Len : q1.length = 32 := by
    have hq := k73_quot_bytes_natToBytesBE parentBytes expectedBytes (8 : Word)
      hlenP hExpectedLen (by decide) (by decide)
    simpa [q1] using congrArg List.length hq
  have hqOrig : q1 =
      u256DivU64BeQuotBytes parentBytes parentBytes 8 := by
    calc
      q1 = EvmAsm.Stateless.SpecRef.natToBytesBE 32
          (EvmAsm.Crypto.beBytesToNat parentBytes / (8 : Word).toNat) := by
        dsimp [q1]
        exact k73_quot_bytes_natToBytesBE parentBytes expectedBytes (8 : Word)
          hlenP hExpectedLen (by decide) (by decide)
      _ = u256DivU64BeQuotBytes parentBytes parentBytes 8 := by
        symm
        exact k73_quot_bytes_natToBytesBE parentBytes parentBytes (8 : Word)
          hlenP hlenP (by decide) (by decide)
  have hcast : u256SubBeBytes parentBytes q1 q1 =
      hvbfWrittenImage gasLimit 0 parentBytes := by
    rw [hqOrig]
    exact k73_zero_machine_bytes_eq_written (by simpa [htarget] using htargetPos) hlenP
  have hprefix := k73_zero_entry_to_div_spec_within
    spH spK (H + 40) gasLimit gasUsed target parentPtr Expected
    headerPtr v9 old18 v19 v20 parentBytes expectedBytes Fenv
    hspK htarget hne hnotlt hgasZero htargetPos hFenv
  have hprefixC := cpsTripleWithin_extend_code hk73Mono hprefix
  let DPreRest : Assertion :=
    ((.x1 : Reg) ↦ᵣ (H + 40)) ** ((.x8 : Reg) ↦ᵣ parentPtr) **
      ((.x9 : Reg) ↦ᵣ Expected) ** ((.x10 : Reg) ↦ᵣ gasLimit) **
      ((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x12 : Reg) ↦ᵣ parentPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      bytesRegion Expected expectedBytes ** bytesRegion parentPtr parentBytes ** FdivFull
  let DPre : Assertion :=
    ((.x1 : Reg) ↦ᵣ (H + 40)) ** ((.x8 : Reg) ↦ᵣ parentPtr) **
      ((.x9 : Reg) ↦ᵣ Expected) ** ((.x10 : Reg) ↦ᵣ gasLimit) **
      ((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x12 : Reg) ↦ᵣ parentPtr) **
      regOwns u256DivU64BeScratch ** bytesRegion Expected expectedBytes **
      bytesRegion parentPtr parentBytes ** FdivFull
  have hheadDiv : ∀ s : PartialState,
      k73HeadPost spK (H + 40) gasLimit gasUsed parentPtr Expected target
        headerPtr v9 old18 v19 (0 : Word) v20 parentBytes expectedBytes Fenv s →
      (((.x13 : Reg) ↦ᵣ Expected) ** DPreRest) s := by
    intro s hs
    have heq :
        (k73HeadPost spK (H + 40) gasLimit gasUsed parentPtr Expected target
            headerPtr v9 old18 v19 (0 : Word) v20 parentBytes expectedBytes Fenv) =
          (((.x13 : Reg) ↦ᵣ Expected) ** DPreRest) := by
      dsimp only [DPreRest, FdivFull, Fdiv, Fenv, Ftail0, k73_zero_env,
        k74FlatFrame, k73HeadPost]
      simp only [regOwns_cons, regOwns_nil,
        sepConj_emp_right']
      xperm
    exact heq ▸ hs
  have hheadDivOwn : ∀ s : PartialState,
      k73HeadPost spK (H + 40) gasLimit gasUsed parentPtr Expected target
        headerPtr v9 old18 v19 (0 : Word) v20 parentBytes expectedBytes Fenv s →
      ((regOwn .x13 ** DPreRest) s) := by
    intro s hs
    exact decr_sep_pin_lift (r := Reg.x13) (v := Expected) s (hheadDiv s hs)
  have hprefixDiv : cpsTripleWithin 15 K73 (K73 + 160) cr
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes (H + 40) old8 (k73_zero_env F))
      DPre := by
    have hpreEq :
        ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
            parentBytes expectedBytes headerBytes (H + 40) old8 (k73_zero_env F)) =
        k73HeadPre spH spK (H + 40) gasLimit gasUsed parentPtr Expected
          headerPtr v9 old18 v19 v20 parentBytes expectedBytes Fenv := by
      dsimp only [k73HeadPre, k73PreRest, Fenv, Ftail0, k73_zero_env,
        k74FlatFrame]
      simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
      xperm
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun s hq => ?_) hprefixC
    · exact hpreEq ▸ hp
    · have hq' := hheadDivOwn s hq
      dsimp [DPre, DPreRest, Fdiv, Fenv, Ftail0, k73_zero_env]
        at hq' ⊢
      simp only [u256DivU64BeScratch, regOwns_cons, regOwns_nil,
        sepConj_emp_right'] at hq' ⊢
      xperm_chunked hq'
  have hdiv0 := k73_disjoint_div_spec_within
    parentPtr Expected (H + 40) gasLimit gasUsed parentPtr
    parentBytes expectedBytes FdivFull (by
      dsimp [FdivFull, Fdiv]
      pcf
      exact hF) hrw hroBase hlenP hExpectedLen
    hovBase hovExpected hdisj hszDiv (by decide)
  have hdiv1 := cpsTripleWithin_extend_code full_whole_mono hdiv0
  have hdiv2 := cpsTripleWithin_extend_code hk73Mono hdiv1
  have hdivSeq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => hp)
    hprefixDiv hdiv2
  let RestDiv : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 176)) **
      ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder parentBytes expectedBytes 8) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ Expected) **
      regOwns u256DivU64BeScratch ** bytesRegion Expected q1 **
      bytesRegion parentPtr parentBytes ** ((.x8 : Reg) ↦ᵣ parentPtr) **
      ((.x9 : Reg) ↦ᵣ Expected) ** Fdiv
  have hRestDiv : RestDiv.pcFree := by
    dsimp [RestDiv, Fdiv, Ftail0]
    pcf
    exact hF
  have hguard0 := beq_spec_gen_within .x20 .x0 (32 : BitVec 13)
    (0 : Word) (0 : Word) (K73 + 176)
  have hguard1 := cpsBranchWithin_extend_code
    (k73_whole_mem 44 _ (K73 + 176) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hguard0
  rw [show signExtend13 (32 : BitVec 13) = (32 : Word) by decide,
    show (K73 + 176) + (32 : Word) = K73 + 208 by bv_omega,
    show (K73 + 176) + 4 = K73 + 180 by bv_omega] at hguard1
  have hguard2 := cpsBranchWithin_extend_code hk73Mono hguard1
  have hguardF := cpsBranchWithin_frameR RestDiv hRestDiv hguard2
  have hguardSeq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      simp only [RestDiv, Fdiv, FdivFull, u256DivU64BeScratch,
        regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp ⊢
      xperm_chunked hp)
    hdivSeq hguardF
  have hguardTaken := cpsBranchWithin_takenPath hguardSeq (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact h_ne rfl)
  let Fsub : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      ((.x2 : Reg) ↦ᵣ spK) ** ((.x18 : Reg) ↦ᵣ target) **
      ((.x19 : Reg) ↦ᵣ v19) **
      frameSlotsSaved k73Frame spK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** Ftail0
  have hFsub : Fsub.pcFree := by
    dsimp [Fsub, Ftail0]
    pcf
    exact hF
  have hsub0 := k73_in_place_sub_spec_within
    parentPtr Expected (K73 + 176)
    (u256DivU64BeRemainder parentBytes expectedBytes 8) (8 : Word) Expected
    parentBytes q1 Fsub hFsub hrw hroBase hlenP hq1Len hovBase hovExpected hdisj
    hszSub (by decide)
  have hsub1 := cpsTripleWithin_extend_code hk73Mono hsub0
  let SubPre : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 176)) ** ((.x8 : Reg) ↦ᵣ parentPtr) **
      ((.x9 : Reg) ↦ᵣ Expected) **
      ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder parentBytes expectedBytes 8) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ Expected) **
      regOwns u256SubBeInPlaceScratch ** bytesRegion Expected q1 **
      bytesRegion parentPtr parentBytes ** Fsub
  have hguardSub := cpsTripleWithin_weaken
    (P' := ((.x1 : Reg) ↦ᵣ (H + 40)) **
      k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
        parentBytes expectedBytes headerBytes (H + 40) old8 (k73_zero_env F))
    (Q' := SubPre)
    (fun _ hp => hp)
    (fun _ hq => by
      extract_pure_deep hq
      obtain ⟨_, hq⟩ := hq
      dsimp [SubPre, Fsub, RestDiv, Fdiv, FdivFull, Ftail0] at hq ⊢
      simp only [u256DivU64BeScratch, u256SubBeInPlaceScratch,
        regOwns_cons, regOwns_nil, sepConj_emp_right'] at hq ⊢
      xperm_hyp hq) hguardTaken
  have hsubSeq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [SubPre, Fsub, RestDiv, Fdiv, Ftail0] at hp ⊢
      simp only [u256SubBeInPlaceScratch,
        regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp) hguardSub hsub1
  rw [show (HeaderBaseFeeSpec.K73 : Word) = K73 from rfl] at hsubSeq
  let RestBorrow : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 224)) ** ((.x8 : Reg) ↦ᵣ parentPtr) **
      ((.x9 : Reg) ↦ᵣ Expected) ** ((.x18 : Reg) ↦ᵣ target) **
      ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
      ((.x2 : Reg) ↦ᵣ spK) ** ((.x11 : Reg) ↦ᵣ Expected) **
      ((.x12 : Reg) ↦ᵣ Expected) ** regOwns u256SubBeInPlaceScratch **
      bytesRegion Expected sBytes ** bytesRegion parentPtr parentBytes ** Ftail0
  have hRestBorrow : RestBorrow.pcFree := by
    dsimp [RestBorrow, Ftail0]
    pcf
    exact hF
  have hborrow0 := k73_decrease_sub_borrow_branch_pinned_spec_within
    RestBorrow hRestBorrow
    (u256SubBeBorrow parentBytes q1 q1)
  have hborrow1 := cpsBranchWithin_extend_code hk73Mono hborrow0
  have hborrowSeq :
      cpsBranchWithin
        (15 + (5 + (u256DivU64BeFn parentPtr Expected 8 parentBytes expectedBytes).body.steps) + 1 +
          (5 + (u256SubBeInPlaceFn parentPtr Expected parentBytes q1).body.steps) + 1)
        K73 cr
        (((.x1 : Reg) ↦ᵣ (H + 40)) **
          k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
            parentBytes expectedBytes headerBytes (H + 40) old8 (k73_zero_env F))
        (K73 + 276) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** RestBorrow ** regOwn .x10)
        (K73 + 228) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** RestBorrow ** regOwn .x10) := by
    exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (Q2 := (((.x0 : Reg) ↦ᵣ (0 : Word)) ** RestBorrow) **
        ((.x10 : Reg) ↦ᵣ u256SubBeBorrow parentBytes q1 q1))
      (fun _ hp => by
      dsimp [RestBorrow, Fsub, Ftail0, sBytes, q1] at hp ⊢
      xperm_chunked hp) hsubSeq hborrow1
  let Ptail : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ Expected) **
      ((.x12 : Reg) ↦ᵣ Expected) ** regOwns u256SubBeInPlaceScratch **
      bytesRegion Expected sBytes ** bytesRegion parentPtr parentBytes ** Ftail0
  let TailPre : Assertion :=
    ((.x2 : Reg) ↦ᵣ spK) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
      regOwn .x10 ** Ptail
  have hPtail : Ptail.pcFree := by
    dsimp [Ptail, Ftail0]
    pcf
    exact hF
  have hTailPre : TailPre.pcFree := by
    dsimp [TailPre]
    pcf
    exact hF
  have hbrT : cpsBranchWithin
      (15 + nDiv + 1 + nSub + 1) K73 cr
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes (H + 40) old8 (k73_zero_env F))
      (K73 + 276) TailPre (K73 + 228) TailPre := by
    refine cpsBranchWithin_weaken (fun _ hp => hp)
      (fun s hp => ?_) (fun s hp => ?_) hborrowSeq
    · have htail := k73_zero_exit_to_tail_pre spK (H + 40) parentPtr Expected
        headerPtr v9 old18 target v19 (0 : Word) v20 parentBytes sBytes Ftail0 s (by
          dsimp [RestBorrow, Fsub, Ftail0, sBytes, q1] at hp ⊢
          sep_perm hp)
      dsimp [TailPre, Ptail, Ftail0, regsOwnAt, k73Frame] at htail ⊢
      simp only [sepConj_emp_right'] at htail ⊢
      xperm_hyp htail
    · have htail := k73_zero_exit_to_tail_pre spK (H + 40) parentPtr Expected
        headerPtr v9 old18 target v19 (0 : Word) v20 parentBytes sBytes Ftail0 s (by
          dsimp [RestBorrow, Fsub, Ftail0, sBytes, q1] at hp ⊢
          sep_perm hp)
      dsimp [TailPre, Ptail, Ftail0, regsOwnAt, k73Frame] at htail ⊢
      simp only [sepConj_emp_right'] at htail ⊢
      xperm_hyp htail

  have hspTail : spK + signExtend12 (56 : BitVec 12) = spH := by
    rw [hspK]
    rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
      show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]
    bv_omega
  let saved : Reg → Word :=
    k73Saved (H + 40) headerPtr v9 old18 v19 v20
  have hfailT := k73_failure_tail_spec_within
    spH spK (H + 40) saved Ptail hspTail hret (by rfl) hPtail
  have hsuccT := k73_decrease_success_tail_spec_within
    spH spK (H + 40) saved Ptail hspTail hret (by rfl) hPtail
  have hfailTC := cpsTripleWithin_extend_code hk73Mono hfailT
  have hsuccTC := cpsTripleWithin_extend_code hk73Mono hsuccT
  have hfext := cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr hbrT hfailTC
  have hall := cpsBranchWithin_seq_cpsTripleWithin_notTaken_same_cr hfext hsuccTC
  have hall' : cpsBranchWithin
      (15 + nDiv + 1 + nSub + 1 + 9 + 10) K73 cr
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes (H + 40) old8 (k73_zero_env F))
      (H + 40)
        ((.x1 ↦ᵣ (H + 40)) **
          k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18 target
            v19 v20 gasUsed gasLimit parentPtr parentBytes headerBytes
            (k73_zero_outj F))
      (H + 40)
        ((.x1 ↦ᵣ (H + 40)) **
          k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18 target
            v19 v20 gasUsed gasLimit parentPtr parentBytes headerBytes
            (k73_zero_outj F)) := by
    let SuccessArm : Assertion :=
      k73PostOwn spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr
        parentBytes (hvbfWrittenImage gasLimit 0 parentBytes) headerBytes
        (H + 40) old8 (k73_zero_outj F)
    let FailureArm : Assertion := fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)),
        status ≠ (0 : Word) ∧
        k73FailurePost spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr
          status parentBytes scratchBytes headerBytes (H + 40) old8
          (k73_zero_outj F) u
    refine cpsBranchWithin_weaken (fun _ hp => hp)
      (fun s hq => ?_) (fun s hq => ?_) hall
    · -- status-1 failure tail: expose its nonzero status and written image.
      dsimp [TailPre, Ptail, Ftail0, saved] at hq
      have hEq1 :
          (((.x2 : Reg) ↦ᵣ spH) ** regsAt k73Frame
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x11 : Reg) ↦ᵣ Expected) ** ((.x12 : Reg) ↦ᵣ Expected) **
            regOwns u256SubBeInPlaceScratch ** bytesRegion Expected sBytes **
            bytesRegion parentPtr parentBytes **
            frameSlotsSaved hvbfFrame spH
              (hvbfSaved (H + 40) old8) ** bytesRegion headerPtr headerBytes ** F) =
          (((.x2 : Reg) ↦ᵣ spH) ** ((.x11 : Reg) ↦ᵣ Expected) **
            ((.x12 : Reg) ↦ᵣ Expected) ** bytesRegion Expected sBytes **
            ((.x1 : Reg) ↦ᵣ (H + 40)) ** ((.x8 : Reg) ↦ᵣ headerPtr) **
            ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ old18) **
            ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
            frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwns u256SubBeInPlaceScratch ** bytesRegion parentPtr parentBytes **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) := by
        simp only [k73Frame, regsAt_cons, regsAt_nil, k73Saved,
          sepConj_emp_right']
        xperm_cert_eq
      have hp1 := hEq1 ▸ hq
      have hc11 := decr_under_id (B := (.x2 ↦ᵣ spH))
        (decr_sep_pin_lift (r := Reg.x11) (v := Expected)) s hp1
      have hc12 := decr_under_id (B := (.x2 ↦ᵣ spH))
        (decr_under_id (B := regOwn .x11)
          (decr_sep_pin_lift (r := Reg.x12) (v := Expected))) s hc11
      have hEq2 :
          (((.x2 : Reg) ↦ᵣ spH) ** regOwn .x11 ** regOwn .x12 **
            bytesRegion Expected sBytes ** ((.x1 : Reg) ↦ᵣ (H + 40)) **
            ((.x8 : Reg) ↦ᵣ headerPtr) ** ((.x9 : Reg) ↦ᵣ v9) **
            ((.x18 : Reg) ↦ᵣ old18) ** ((.x19 : Reg) ↦ᵣ v19) **
            ((.x20 : Reg) ↦ᵣ v20) ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwns u256SubBeInPlaceScratch ** bytesRegion parentPtr parentBytes **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) =
          (((.x1 : Reg) ↦ᵣ (H + 40)) **
            k73FailurePost spH spK headerPtr v9 old18 target v19 v20 gasUsed
              parentPtr (1 : Word) parentBytes sBytes headerBytes (H + 40) old8
              (k73_zero_outj F)) := by
        dsimp only [k73FailurePost, tailRestScratch, tailRestCore,
          k73_zero_outj, k74FlatFrame]
        simp only [u256SubBeInPlaceScratch, regOwns_cons, regOwns_nil,
          sepConj_emp_right']
        xperm_cert_eq
      have htmp :
          (((.x1 : Reg) ↦ᵣ (H + 40)) ** FailureArm) s := by
        exact decr_sep_pair_congr
          (A := ((.x1 : Reg) ↦ᵣ (H + 40)))
          (A' := ((.x1 : Reg) ↦ᵣ (H + 40)))
          (B := k73FailurePost spH spK headerPtr v9 old18 target v19 v20 gasUsed
            parentPtr (1 : Word) parentBytes sBytes headerBytes (H + 40) old8
            (k73_zero_outj F))
          (B' := FailureArm)
          (fun _ h => h)
          (fun _ h => ⟨1, sBytes, by decide, h⟩)
          s (hEq2 ▸ hc12)
      have hBR : (FailureArm ** ((.x1 : Reg) ↦ᵣ (H + 40))) s := by
        xperm_hyp htmp
      have hor := decr_or_right_lift (A := SuccessArm) (B := FailureArm)
        (R := ((.x1 : Reg) ↦ᵣ (H + 40))) s hBR
      rw [sepConj_comm'
        (fun u => SuccessArm u ∨ FailureArm u)
        ((.x1 : Reg) ↦ᵣ (H + 40))] at hor
      have hroute :
          k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18 target
              v19 v20 gasUsed gasLimit parentPtr parentBytes headerBytes
              (k73_zero_outj F) =
            (fun u => SuccessArm u ∨ FailureArm u) := by
        funext u
        simp only [k73RouteBCallPost, SuccessArm, FailureArm]
        rw [hgasZero]
      rw [hroute]
      exact hor
    · -- status-0 success tail: cast the subtract image to the recurrence.
      dsimp [TailPre, Ptail, Ftail0, saved] at hq
      have hEq1 :
          (((.x2 : Reg) ↦ᵣ spH) ** regsAt k73Frame
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x11 : Reg) ↦ᵣ Expected) ** ((.x12 : Reg) ↦ᵣ Expected) **
            regOwns u256SubBeInPlaceScratch ** bytesRegion Expected sBytes **
            bytesRegion parentPtr parentBytes **
            frameSlotsSaved hvbfFrame spH
              (hvbfSaved (H + 40) old8) ** bytesRegion headerPtr headerBytes ** F) =
          (((.x2 : Reg) ↦ᵣ spH) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
            ((.x11 : Reg) ↦ᵣ Expected) ** ((.x12 : Reg) ↦ᵣ Expected) **
            bytesRegion Expected sBytes ** ((.x1 : Reg) ↦ᵣ (H + 40)) **
            ((.x8 : Reg) ↦ᵣ headerPtr) ** ((.x9 : Reg) ↦ᵣ v9) **
            ((.x18 : Reg) ↦ᵣ old18) ** ((.x19 : Reg) ↦ᵣ v19) **
            ((.x20 : Reg) ↦ᵣ v20) ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwns u256SubBeInPlaceScratch ** bytesRegion parentPtr parentBytes **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) := by
        simp only [k73Frame, regsAt_cons, regsAt_nil, k73Saved,
          sepConj_emp_right']
        xperm_cert_eq
      have hp1 := hEq1 ▸ hq
      have hc10 := decr_under_id (B := (.x2 ↦ᵣ spH))
        (decr_sep_pin_lift (r := Reg.x10) (v := (0 : Word))) s hp1
      have hc11 := decr_under_id (B := (.x2 ↦ᵣ spH))
        (decr_under_id (B := regOwn .x10)
          (decr_sep_pin_lift (r := Reg.x11) (v := Expected))) s hc10
      have hc12 := decr_under_id (B := (.x2 ↦ᵣ spH))
        (decr_under_id (B := regOwn .x10)
          (decr_under_id (B := regOwn .x11)
            (decr_sep_pin_lift (r := Reg.x12) (v := Expected)))) s hc11
      have hcbr := decr_under_id (B := (.x2 ↦ᵣ spH))
        (decr_under_id (B := regOwn .x10)
          (decr_under_id (B := regOwn .x11)
            (decr_under_id (B := regOwn .x12)
              (k73_zero_br_cast hcast)))) s hc12
      have hEq2 :
          (((.x2 : Reg) ↦ᵣ spH) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
            bytesRegion Expected (hvbfWrittenImage gasLimit 0 parentBytes) **
            ((.x1 : Reg) ↦ᵣ (H + 40)) ** ((.x8 : Reg) ↦ᵣ headerPtr) **
            ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ old18) **
            ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
            frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwns u256SubBeInPlaceScratch ** bytesRegion parentPtr parentBytes **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) =
          (((.x1 : Reg) ↦ᵣ (H + 40)) **
            k73PostOwn spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr
              parentBytes (hvbfWrittenImage gasLimit 0 parentBytes) headerBytes
              (H + 40) old8 (k73_zero_outj F)) := by
        dsimp only [k73PostOwn, tailRest, tailRestCore,
          k73_zero_outj, k74FlatFrame]
        simp only [u256SubBeInPlaceScratch, regOwns_cons, regOwns_nil,
          sepConj_emp_right']
        xperm_cert_eq
      have hRS : (SuccessArm ** ((.x1 : Reg) ↦ᵣ (H + 40))) s := by
        have h := hEq2 ▸ hcbr
        rw [sepConj_comm'
          ((.x1 : Reg) ↦ᵣ (H + 40))
          (k73PostOwn spH spK headerPtr v9 old18 target v19 v20 gasUsed
            parentPtr parentBytes (hvbfWrittenImage gasLimit 0 parentBytes)
            headerBytes (H + 40) old8 (k73_zero_outj F))] at h
        simpa only [SuccessArm] using h
      have hor := decr_or_left_lift (A := SuccessArm) (B := FailureArm)
        (R := ((.x1 : Reg) ↦ᵣ (H + 40))) s hRS
      rw [sepConj_comm'
        (fun u => SuccessArm u ∨ FailureArm u)
        ((.x1 : Reg) ↦ᵣ (H + 40))] at hor
      have hroute :
          k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18 target
              v19 v20 gasUsed gasLimit parentPtr parentBytes headerBytes
              (k73_zero_outj F) =
            (fun u => SuccessArm u ∨ FailureArm u) := by
        funext u
        simp only [k73RouteBCallPost, SuccessArm, FailureArm]
        rw [hgasZero]
      rw [hroute]
      exact hor
  have htriple := k73_zero_branch_to_triple hall'
  have hbound : 15 + nDiv + 1 + nSub + 1 + 9 + 10 ≤
      k73_zero_route_steps parentPtr parentBytes expectedBytes := by
    dsimp [k73_zero_route_steps, nDiv, nSub, q1, Expected]
    omega
  have htriple' := cpsTripleWithin_mono_nSteps hbound htriple
  simpa [Fenv, Ftail0, k73_zero_env] using htriple'

/-! A closed, non-degenerate witness for the zero-gas route.  The three
    32-byte regions are real separated regions; the ambient is empty only
    after those regions and the saved frame have been supplied.  In
    particular this checks the complete adapter premise set, rather than
    counting the conditional theorem from an arbitrary callee premise. -/

theorem k73_zero_route_adapter_inhabited :
    cpsTripleWithin
      (k73_zero_route_steps (0x200100 : Word)
        (List.replicate 32 0) (List.replicate 32 0))
      K73 (H + 40) wholeCode
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest (0xa0050038 : Word) (0xa0050000 : Word) (0x200000 : Word)
          (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          (10000 : Word) (0 : Word) (0x200100 : Word)
          (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
          (H + 40) (0 : Word) (k73_zero_env empAssertion))
      ((.x1 ↦ᵣ (H + 40)) **
        k73RouteBCallPost (0xa0050038 : Word) (0xa0050000 : Word) (H + 40)
          (0 : Word) (0x200000 : Word) (0 : Word) (0 : Word)
          ((10000 : Word) >>> 1) (0 : Word) (0 : Word) (0 : Word) (10000 : Word)
          (0x200100 : Word) (List.replicate 32 0) (List.replicate 32 0)
          (k73_zero_outj empAssertion)) :=
  k73_zero_route_adapter (cr := wholeCode)
    (0xa0050038 : Word) (0xa0050000 : Word) (0 : Word) (0x200000 : Word)
    (10000 : Word) (0 : Word) ((10000 : Word) >>> 1) (0x200100 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
    empAssertion
    (hspK := by decide)
    (htarget := rfl)
    (hne := by decide)
    (hnotlt := by decide)
    (hgasZero := by decide)
    (htargetPos := by decide)
    (hret := by unfold H; rfl)
    (hF := by pcf)
    (hrw := by decide)
    (hroBase := by
      refine ⟨?_, ?_, ?_⟩
      · decide
      · decide
      · intro k hk
        have hk32 : k < 32 := by simpa using hk
        interval_cases k <;> decide)
    (hlenP := by simp)
    (hExpectedLen := by simp)
    (hovBase := by decide)
    (hovExpected := by decide)
    (hdisj := by decide)
    (hszDiv := by
      simp only [u256DivU64BeFn]
      decide)
    (hszSub := by
      simp only [u256SubBeInPlaceFn]
      decide)
    (fun _ _ h => h)

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero
