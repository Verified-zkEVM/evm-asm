/-
  Generic K73 entry composition.

  This file exposes the already-composed increasing route without the old
  concrete `5000/2500` specialization.  The equal and decrease dispatch
  compositions are kept below this seam so the entry theorem can carry an
  arm-indexed post without baking one historical gas pair into the contract.

  IMPORTANT SCOPE: the current arm seams inherit `regOwns [.x14, .x15, .x16,
  .x17]` from the shared flat mul/div/sub contracts.  Linked K73's exact
  footprint is [x5, x6, x7, x28, x29, x30, x31], plus genuine x13 clobber;
  ELF sha256 is 06cd10315b05beda7fc5dc43839ffc3a9e809f6e031d0b58d207a1633b351c4f.
  Thus the pre below is intentionally over-approximated, not exact Route-B;
  Item 12 is the shared frame-cancellation blocker.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeRoutes
import EvmAsm.Codegen.Programs.K73Arithmetic

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256SubBeSAsm
open EvmAsm.Codegen.U256AddBeBInPlaceSAsm
open EvmAsm.Codegen.U256FromU64BeSAsm

private theorem k73_entry_div_quot_length
    (a orig : List (BitVec 8)) (b : Word) (hlen : orig.length = 32) :
    (u256DivU64BeQuotBytes a orig b).length = 32 := by
  have h : ∀ k : Nat, (divState a orig b k).1.length = orig.length := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [divState, ih]
  simpa [u256DivU64BeQuotBytes, hlen] using h 32

/-! The decrease arm reaches the multiply call through the fall-through path
    after the zero-gas special case.  This seam keeps that path independent of
    the increase-only carry/status packaging below. -/
theorem k73_decrease_nonzero_entry_to_mul_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hF : F.pcFree) :
    cpsTripleWithin 19 K73 (K73 + 84) wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed
        basePtr outPtr v8 v9 v18 v19 v20 baseBytes outBytes F)
      (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ target) **
      ((.x19 : Reg) ↦ᵣ (target - gasUsed)) ** ((.x20 : Reg) ↦ᵣ 0) **
      ((.x10 : Reg) ↦ᵣ basePtr) ** ((.x11 : Reg) ↦ᵣ (target - gasUsed)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x13 : Reg) ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ 0) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F) := by
  let Rest : Assertion :=
    ((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x19 : Reg) ↦ᵣ v19) ** ((.x10 : Reg) ↦ᵣ gasLimit) **
      ((.x12 : Reg) ↦ᵣ basePtr) ** ((.x13 : Reg) ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ 0) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    pcf
    exact hF
  let RestNoX0 : Assertion :=
    ((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x19 : Reg) ↦ᵣ v19) ** ((.x10 : Reg) ↦ᵣ gasLimit) **
      ((.x12 : Reg) ↦ᵣ basePtr) ** ((.x13 : Reg) ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F
  have hRestNoX0 : RestNoX0.pcFree := by
    dsimp [RestNoX0]
    pcf
    exact hF
  have hhead := k73_head_spec_within
    sp0 spH raIn gasLimit gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes outBytes F hsp htarget hF
  have hbeq := beq_spec_gen_within .x11 .x18 (192 : BitVec 13)
    gasUsed target (K73 + 40)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 10 _ (K73 + 40) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (192 : BitVec 13) = (192 : Word) by decide,
    show (K73 + 40) + (192 : Word) = K73 + 232 by bv_omega,
    show (K73 + 40) + 4 = K73 + 44 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR
    (((.x20 : Reg) ↦ᵣ v20) ** Rest)
    (by dsimp [Rest]; pcf; exact hF) hbeqC
  have hneq := cpsBranchWithin_ntakenPath hbeqF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, -⟩ := hp
    exact hne h_eq)
  have hneq' : cpsTripleWithin 1 (K73 + 40) (K73 + 44) wholeCode
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x18 : Reg) ↦ᵣ target) **
        ((.x20 : Reg) ↦ᵣ v20) ** Rest)
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x18 : Reg) ↦ᵣ target) **
        ((.x20 : Reg) ↦ᵣ v20) ** Rest) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) hneq
  have hheadneq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [k73HeadPost, Rest] at hp ⊢
      xperm_chunked hp) hhead hneq'
  have hli := li_spec_gen_within .x20 v20 (0 : Word) (K73 + 44)
    (by decide)
  have hliC := cpsTripleWithin_extend_code
    (k73_whole_mem 11 _ (K73 + 44) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hli
  let Fli : Assertion :=
    ((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x18 : Reg) ↦ᵣ target) ** Rest
  have hFli : Fli.pcFree := by
    dsimp [Fli, Rest]
    pcf
    exact hF
  have hliF := cpsTripleWithin_frameR Fli hFli hliC
  have hmid := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [k73HeadPost, Fli, Rest] at hp ⊢
      xperm_chunked hp) hheadneq hliF
  have hbltu := bltu_spec_gen_within .x18 .x11 (16 : BitVec 13)
    target gasUsed (K73 + 48)
  have hbltuC := cpsBranchWithin_extend_code
    (k73_whole_mem 12 _ (K73 + 48) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbltu
  rw [show signExtend13 (16 : BitVec 13) = (16 : Word) by decide,
    show (K73 + 48) + (16 : Word) = K73 + 64 by bv_omega,
    show (K73 + 48) + 4 = K73 + 52 by bv_omega] at hbltuC
  have hbltuF := cpsBranchWithin_frameR
    (((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest)
    (by dsimp [Rest]; pcf; exact hF) hbltuC
  have hntaken := cpsBranchWithin_ntakenPath hbltuF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_lt, -⟩ := hp
    exact hnotlt ((BitVec.ult_iff_toNat_lt).1 h_lt))
  have hntaken' : cpsTripleWithin 1 (K73 + 48) (K73 + 52) wholeCode
      (((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ gasUsed) **
        ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest)
      (((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ gasUsed) **
        ((.x20 : Reg) ↦ᵣ (0 : Word)) ** Rest) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) hntaken
  have hmid' := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Fli, Rest] at hp ⊢
      xperm_chunked hp) hmid hntaken'
  have hbeq0 := beq_spec_gen_within .x11 .x0 (104 : BitVec 13)
    gasUsed (0 : Word) (K73 + 52)
  have hbeq0C := cpsBranchWithin_extend_code
    (k73_whole_mem 13 _ (K73 + 52) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq0
  rw [show signExtend13 (104 : BitVec 13) = (104 : Word) by decide,
    show (K73 + 52) + (104 : Word) = K73 + 156 by bv_omega,
    show (K73 + 52) + 4 = K73 + 56 by bv_omega] at hbeq0C
  have hbeq0F := cpsBranchWithin_frameR
    (((.x18 : Reg) ↦ᵣ target) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** RestNoX0)
    (by dsimp [RestNoX0]; pcf; exact hF) hbeq0C
  have hbeq0nt := cpsBranchWithin_ntakenPath hbeq0F (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, -⟩ := hp
    exact hnonzero h_eq)
  have hbeq0nt' : cpsTripleWithin 1 (K73 + 52) (K73 + 56) wholeCode
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ target) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** RestNoX0)
      (((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ target) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) ** RestNoX0) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) hbeq0nt
  have hmid'' := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Rest, RestNoX0] at hp ⊢
      xperm_chunked hp) hmid' hbeq0nt'
  have hsub := sub_spec_gen_within .x19 .x18 .x11 target gasUsed v19
    (K73 + 56) (by decide)
  have hsubC := cpsTripleWithin_extend_code
    (k73_whole_mem 14 _ (K73 + 56) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hsub
  have hsubF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x12 : Reg) ↦ᵣ basePtr) **
      ((.x13 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ 0) **
      ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hsubC
  have hsub' : cpsTripleWithin 1 (K73 + 56) (K73 + 60) wholeCode
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x18 : Reg) ↦ᵣ target) **
        ((.x11 : Reg) ↦ᵣ gasUsed) **
        ((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x12 : Reg) ↦ᵣ basePtr) **
        ((.x13 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ 0) **
        ((.x20 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
      (((.x19 : Reg) ↦ᵣ (target - gasUsed)) **
        ((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ gasUsed) **
        ((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x12 : Reg) ↦ᵣ basePtr) **
        ((.x13 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ 0) **
        ((.x20 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hsubF
  have hj := jal_x0_spec_gen_within (12 : BitVec 21) (K73 + 60)
  have hjC := cpsTripleWithin_extend_code
    (k73_whole_mem 15 _ (K73 + 60) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hj
  rw [show signExtend21 (12 : BitVec 21) = (12 : Word) by decide,
    show (K73 + 60) + (12 : Word) = K73 + 72 by bv_omega] at hjC
  have hjF := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (target - gasUsed)) **
      ((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ gasUsed) **
      ((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x12 : Reg) ↦ᵣ basePtr) **
        ((.x13 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ 0) **
        ((.x20 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hjC
  have hmv10 := mv_spec_gen_within .x10 .x8 basePtr gasLimit (K73 + 72)
    (by decide)
  have hmv10C := cpsTripleWithin_extend_code
    (k73_whole_mem 18 _ (K73 + 72) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv10
  have hmv10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
      ((.x19 : Reg) ↦ᵣ (target - gasUsed)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ gasUsed) ** ((.x12 : Reg) ↦ᵣ basePtr) **
      ((.x13 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ 0) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hmv10C
  have hmv11 := mv_spec_gen_within .x11 .x19 (target - gasUsed) gasUsed
    (K73 + 76) (by decide)
  have hmv11C := cpsTripleWithin_extend_code
    (k73_whole_mem 19 _ (K73 + 76) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv11
  have hmv11F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ target) **
      ((.x20 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ basePtr) **
      ((.x12 : Reg) ↦ᵣ basePtr) ** ((.x13 : Reg) ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ 0) ** frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) ** bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hmv11C
  have hmv12 := mv_spec_gen_within .x12 .x9 outPtr basePtr (K73 + 80)
    (by decide)
  have hmv12C := cpsTripleWithin_extend_code
    (k73_whole_mem 20 _ (K73 + 80) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv12
  have hmv12F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x8 : Reg) ↦ᵣ basePtr) **
      ((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ (target - gasUsed)) **
      ((.x20 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ basePtr) **
      ((.x11 : Reg) ↦ᵣ (target - gasUsed)) ** ((.x13 : Reg) ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ 0) ** frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) ** bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hmv12C
  have hseq0 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Rest, RestNoX0] at hp ⊢
      sep_perm hp)
    hmid'' hsub'
  rw [sepConj_emp_left'] at hjF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by sep_perm hp) hseq0 hjF
  have hseq1' := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by sep_perm hp) hseq1 hmv10F
  have hseq2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by sep_perm hp) hseq1' hmv11F
  have hseq3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by sep_perm hp) hseq2 hmv12F
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hseq3

/-! The decrease arm uses the same linked multiply entry as the increasing arm,
    but the carry flag is zero and the multiplier is `target - gasUsed`.
    Keep this seam separate from the later overflow-status packaging: it is the
    call-site contract itself, with no increase-only arithmetic hidden in it. -/
theorem k73_decrease_mul_call_spec_within
    (spH raIn delta basePtr outPtr v8 v9 v18 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre F spH (K73 + 88)
        v8 v9 v18 delta v20 basePtr delta outPtr outPtr
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        v8 v9 v18 delta v20 basePtr delta outPtr baseBytes accBytes outBytes ** F))
    (htarget : (K73 + 84) + signExtend21
        (jalOff GuestAddrs.u256_mul_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 84)) =
      (GuestAddrs.u256_mul_u64_be : Word))
    (hmem : ∀ a i, CodeReq.singleton (K73 + 84)
      (.JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 84))) a = some i →
      wholeCode a = some i) :
    cpsTripleWithin 3851 (K73 + 84) (K73 + 88) wholeCode
      (((.x1 : Reg) ↦ᵣ raIn) **
        k73MulPreNoRa spH v8 v9 v18 delta v20 basePtr delta outPtr outPtr
          f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F)
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        k73MulBodyPostNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) v8 v9 v18 delta v20 basePtr delta outPtr
          baseBytes accBytes outBytes ** F) := by
  have hcalleeMem : ∀ a i, mulCode a = some i → wholeCode a = some i :=
    mul_whole_mono
  exact k73_mul_call_spec_within
    (cr := wholeCode) (n := 3850)
    (K73 + 84) (GuestAddrs.u256_mul_u64_be : Word) raIn spH
    (spH + signExtend12 (-48 : BitVec 12)) v8 v9 v18 delta v20
    basePtr delta outPtr outPtr
    (jalOff GuestAddrs.u256_mul_u64_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 84)) F hF
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
    hcallee htarget hmem hcalleeMem

/-! The status branch itself is independent of the arithmetic relation.  This
    small helper is shared by the increasing and decreasing multiply routes;
    the route-specific theorem only has to turn the callee's overflow post
    into the corresponding `Rest`. -/
theorem k73_mul_status_branch_spec_within
    (Rest : Assertion) (hRest : Rest.pcFree) :
    cpsBranchWithin 1 (K73 + 88) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
  have hraw : ∀ old10, cpsBranchWithin 1 (K73 + 88) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) **
        ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 272) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 92) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
    intro old10
    have hbne := bne_spec_gen_within .x10 .x0 (184 : BitVec 13)
      old10 (0 : Word) (K73 + 88)
    have hbneC := cpsBranchWithin_extend_code
      (k73_whole_mem 22 _ (K73 + 88) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hbne
    have hbneF := cpsBranchWithin_frameR Rest hRest hbneC
    refine cpsBranchWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => ?_) (fun h hq => ?_) hbneF
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      sep_perm hq1
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      sep_perm hq1
  have hbr := cpsBranchWithin_of_forall_regIs_to_regOwn
    (r := .x10) (P := ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) hraw
  exact cpsBranchWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) (fun _ hq => by sep_perm hq) hbr

def k73DecreaseMulCarryRest
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (K73 + 88)) **
    frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
    (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
      (fun s => ∃ k, (k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word) **
        bytesRegion outPtr outBytes **
        k73MulOverflowCoreNoStatus accBytes k) s)) ** G

def k73DecreaseMulPost
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (K73 + 88)) **
    k73MulBodyPostNoRa (spH + signExtend12 (-48 : BitVec 12))
      (K73 + 88) basePtr outPtr target delta (0 : Word)
      basePtr delta outPtr baseBytes accBytes outBytes **
    (frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** G)

theorem k73_decrease_mul_post_factor
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion) : ∀ s,
      k73DecreaseMulPost spH raIn basePtr outPtr target delta v8 v9 v18
        v19Saved v20Saved baseBytes accBytes outBytes G s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta v8 v9 v18
          v19Saved v20Saved baseBytes accBytes outBytes G) s := by
  intro s hs
  dsimp [k73DecreaseMulPost, k73MulBodyPostNoRa,
    k73DecreaseMulCarryRest] at hs ⊢
  have hstatus := k73_mul_overflow_status_factor
    (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
    basePtr outPtr target delta (0 : Word) outPtr accBytes outBytes
  let newOverflow : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
      (fun s => ∃ k, (k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word) **
        bytesRegion outPtr outBytes **
        k73MulOverflowCoreNoStatus accBytes k) s)
  have h_over : ∀ h,
      k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) basePtr outPtr target delta (0 : Word)
          outPtr accBytes outBytes h → newOverflow h := by
    intro h hh
    exact hstatus h hh
  have hbody0 : ∀ h,
      (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
        k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) basePtr outPtr target delta (0 : Word)
          outPtr accBytes outBytes) h →
      (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
        newOverflow) h := by
    intro h hh
    exact sepConj_mono_right h_over h hh
  have hbody : ∀ h,
      ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
        k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
          (K73 + 88) basePtr outPtr target delta (0 : Word)
          outPtr accBytes outBytes) ** G) h →
      ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
        newOverflow) ** G) h := by
    intro h hh
    exact sepConj_mono_left hbody0 h hh
  have hframe : ∀ h,
      (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
          k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
            (K73 + 88) basePtr outPtr target delta (0 : Word)
            outPtr accBytes outBytes) ** G)) h →
      (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
          newOverflow) ** G)) h := by
    intro h hh
    exact sepConj_mono_right hbody h hh
  have houter : ∀ h,
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
          k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
            (K73 + 88) basePtr outPtr target delta (0 : Word)
            outPtr accBytes outBytes) ** G)) h →
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
          newOverflow) ** G)) h := by
    intro h hh
    exact sepConj_mono_right hframe h hh
  have hs' :
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
        ((EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr baseBytes **
          k73MulOverflowNoRa (spH + signExtend12 (-48 : BitVec 12))
            (K73 + 88) basePtr outPtr target delta (0 : Word)
            outPtr accBytes outBytes) ** G)) s := by
    sep_perm hs
  have hmapped := houter s hs'
  dsimp [newOverflow] at hmapped ⊢
  sep_perm hmapped

theorem k73_decrease_mul_status_branch_spec_within
    (spH raIn target delta basePtr outPtr v8 v9 v18 v19Saved v20Saved : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** G)
        spH (K73 + 88) basePtr outPtr target delta (0 : Word)
        basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word)
        basePtr delta outPtr baseBytes accBytes outBytes **
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** G))) :
    cpsBranchWithin 3852 (K73 + 84) wholeCode
      (((.x1 : Reg) ↦ᵣ raIn) **
        k73MulPreNoRa spH basePtr outPtr target delta (0 : Word)
          basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
          baseBytes accBytes outBytes
          (frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** G))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
            v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes G **
          regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
            v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes G **
          regOwn .x10) := by
  let Fframe : Assertion :=
    frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19Saved v20Saved)
  have hFframe : Fframe.pcFree := by
    dsimp [Fframe]
    exact pcFree_frameSlotsSaved _ _ _
  let Fcall : Assertion := Fframe ** G
  have hFcall : Fcall.pcFree := by
    dsimp [Fcall]
    exact pcFree_sepConj hFframe hG
  have htarget :
      (K73 + 84) + signExtend21
        (jalOff GuestAddrs.u256_mul_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 84)) =
      (GuestAddrs.u256_mul_u64_be : Word) := by
    change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 84 + _ = BitVec.ofNat 64 GuestAddrs.u256_mul_u64_be
    exact jalOff_correct_add GuestAddrs.u256_mul_u64_be
      GuestAddrs.eip1559_calc_base_fee_per_gas 84
      (by decide) (by decide) (by decide) (by decide)
  have hmem : ∀ a i, CodeReq.singleton (K73 + 84)
      (.JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 84))) a = some i →
      wholeCode a = some i := by
    intro a i hi
    exact k73_whole_mono a i (k73_mem 21 _ (K73 + 84) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi)
  have hcalleeMem : ∀ a i, mulCode a = some i → wholeCode a = some i :=
    mul_whole_mono
  have hcall := k73_decrease_mul_call_spec_within
    spH raIn delta basePtr outPtr basePtr outPtr target (0 : Word)
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes Fcall hFcall
    (by
      simpa only [Fcall, Fframe] using hcallee)
    htarget hmem
  have hmul : cpsTripleWithin 3851 (K73 + 84) (K73 + 88) wholeCode
      (((.x1 : Reg) ↦ᵣ raIn) **
        k73MulPreNoRa spH basePtr outPtr target delta (0 : Word)
          basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
          baseBytes accBytes outBytes Fcall)
      (k73DecreaseMulPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes G) := by
    exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
      (fun _ hq => by
        dsimp [k73DecreaseMulPost, Fcall, Fframe, K73] at hq ⊢
        exact hq) hcall
  have hRest :
      (k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes G).pcFree := by
    have hExists : Assertion.pcFree (fun s => ∃ k, (k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word) **
        bytesRegion outPtr outBytes **
        k73MulOverflowCoreNoStatus accBytes k) s) := by
      apply pcFree_exists
      intro k
      pcf
    dsimp [k73DecreaseMulCarryRest]
    pcf
    exact hExists
    exact hG
  have hmul' : cpsTripleWithin 3851 (K73 + 84) (K73 + 88) wholeCode
      (((.x1 : Reg) ↦ᵣ raIn) **
        k73MulPreNoRa spH basePtr outPtr target delta (0 : Word)
          basePtr delta outPtr outPtr f0 f1 f2 f3 f4 f5
          baseBytes accBytes outBytes Fcall)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
          v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes G **
        regOwn .x10) := by
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun s hq => by
        have hq' := k73_decrease_mul_post_factor
          spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved
          baseBytes accBytes outBytes G s hq
        sep_perm hq') hmul
  have hstatus := k73_mul_status_branch_spec_within
    (k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
      v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes G) hRest
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by sep_perm hp) hmul' hstatus
  simpa only [show 3851 + 1 = 3852 by decide] using hseq

def k73DecreaseDivPairFrame
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes : List (BitVec 8)) (H : Assertion) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spH) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x19 : Reg) ↦ᵣ delta) **
    ((.x20 : Reg) ↦ᵣ (0 : Word)) **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
      basePtr outPtr target delta (0 : Word) **
    bytesRegion basePtr baseBytes **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
    frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** H

def k73DecreaseDivPairPre
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (H : Assertion) : Assertion :=
  (((.x1 : Reg) ↦ᵣ (K73 + 88)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ delta) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
    bytesRegion outPtr outBytes **
    k73DecreaseDivPairFrame spH raIn basePtr outPtr target delta
      v8 v9 v18 v19Saved v20Saved baseBytes accBytes H) ** regOwn .x10

def k73DecreaseDivPairPost
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (H : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x18 : Reg) ↦ᵣ target) **
    ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
      (u256DivU64BeQuotBytes outBytes outBytes target)
      (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
    ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
    regOwns u256DivU64BeScratch **
    bytesRegion outPtr
      (u256DivU64BeQuotBytes
        (u256DivU64BeQuotBytes outBytes outBytes target)
        (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
    k73DecreaseDivPairFrame spH raIn basePtr outPtr target delta
      v8 v9 v18 v19Saved v20Saved baseBytes accBytes H

/-! The decrease carry contains the divider ABI after exposing the multiply
    overflow core.  The four extra divider scratch registers are supplied by
    the caller's `H`; the rest of the divider frame is recovered from the
    multiply epilogue and tail.  This is deliberately the flat-contract
    over-approximation blocked on Item 12: exact linked K73 footprint is
    [x5, x6, x7, x28, x29, x30, x31] plus genuine x13 clobber.  `H` is not
    evidence that K73 writes x14--x17, and this seam is not exact Route-B. -/
theorem k73_decrease_mul_carry_to_div_pre
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (H : Assertion) : ∀ s,
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target delta
          v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes
          (regOwns [.x14, .x15, .x16, .x17] ** H) ** regOwn .x10) s →
      k73DecreaseDivPairPre spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H s := by
  intro s hs
  let Core : Nat → Assertion := fun k =>
    k73MulEpilogueNoRa
      (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
      basePtr outPtr target delta (0 : Word) **
      bytesRegion outPtr outBytes ** k73MulOverflowCoreNoStatus accBytes k
  let C : Assertion := regOwns [.x14, .x15, .x16, .x17] ** H
  let A : Assertion :=
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
          EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr
            baseBytes))) ** regOwn .x10
  have hsource : (A ** ((fun u => ∃ k, Core k u) ** C)) s := by
    dsimp [k73DecreaseMulCarryRest] at hs
    dsimp [A, C, Core, k73DecreaseMulCarryRest]
    xperm_hyp hs
  have hoverOwn : ∀ k h,
      k73MulOverflowCoreNoStatus accBytes k h →
      (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes) h := by
    intro k h hh
    dsimp [k73MulOverflowCoreNoStatus] at hh ⊢
    have h5 := sepConj_mono_left
      (regIs_to_regOwn .x5
        (EvmAsm.Codegen.U256MulU64Be.accBase +
          BitVec.ofNat 64 (32 + k))) h hh
    have h56 := sepConj_mono_right
      (fun h' hq => sepConj_mono_left
        (regIs_to_regOwn .x6 (BitVec.ofNat 64 (8 - k))) h' hq) h h5
    exact h56
  have hcoreOwn : ∀ k h, Core k h →
      (k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target delta (0 : Word) **
        bytesRegion outPtr outBytes **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes)) h := by
    intro k h hh
    dsimp [Core] at hh
    exact sepConj_mono_right
      (fun h' hq => sepConj_mono_right (hoverOwn k) h' hq) h hh
  have pull_nested : ∀ (A : Assertion) (B : Nat → Assertion)
      (C : Assertion) h,
      (A ** ((fun u => ∃ k, B k u) ** C)) h →
      ∃ k, (A ** (B k ** C)) h := by
    intro A B C h hh
    have hh' : (A ** (fun u => ∃ k, (B k ** C) u)) h := by
      exact sepConj_mono_right
        (fun h' hq => (sepConj_exists_left h').mp hq) h hh
    exact sepConj_exists_right h hh'
  obtain ⟨k, hk⟩ := pull_nested A Core C s hsource
  have hk' : (A ** (Core k ** C)) s := hk
  have hkOwn : (A **
      ((k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target delta (0 : Word) **
        bytesRegion outPtr outBytes **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes)) ** C)) s := by
    apply sepConj_mono_right
      (fun h' hq => sepConj_mono_left (hcoreOwn k) h' hq) s hk'
  let MulOwned : Assertion :=
    bytesRegion basePtr baseBytes ** regOwn .x7 **
      ((.x11 : Reg) ↦ᵣ delta) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have hMulOwn : ∀ h,
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr
        baseBytes h → MulOwned h := by
    intro h hh
    dsimp [MulOwned, EvmAsm.Codegen.U256MulU64Be.mulTailExtra] at hh ⊢
    apply sepConj_mono_right
      (fun h' hq => sepConj_mono_left
        (regIs_to_regOwn .x7 (0 : Word)) h' hq) h hh
  let AOwned : Assertion :=
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** MulOwned))) **
      regOwn .x10
  have hAmap : ∀ h, A h → AOwned h := by
    intro h hh
    have hframe : ∀ h',
        (frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
          EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr
            baseBytes) h' →
        (frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** MulOwned) h' := by
      intro h' hh'
      exact sepConj_mono_right hMulOwn h' hh'
    have h1 : ∀ h',
        (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
            (frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
              EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr
                baseBytes)) h' →
        (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
            (frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** MulOwned)) h' := by
      intro h' hh'
      exact sepConj_mono_right hframe h' hh'
    have h2 : ∀ h',
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
              (frameSlotsSaved k73Frame spH
                (k73Saved raIn v8 v9 v18 v19Saved v20Saved) **
                EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr delta outPtr
                  baseBytes))) h' →
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
              (frameSlotsSaved k73Frame spH
                (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** MulOwned))) h' := by
      intro h' hh'
      exact sepConj_mono_right h1 h' hh'
    dsimp [A, AOwned]
    apply sepConj_mono_left h2 h
    exact hh
  have hkOwnedA : (AOwned **
      ((k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target delta (0 : Word) **
        bytesRegion outPtr outBytes **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes)) ** C)) s := by
    exact sepConj_mono_left hAmap s hkOwn
  have hsp :
      (spH + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (48 : BitVec 12) = spH := by
    have hneg : signExtend12 (-48 : BitVec 12) =
        (18446744073709551568 : Word) := by decide
    rw [hneg, signExtend12_48]
    bv_omega
  have hregx2 :
      ((.x2 : Reg) ↦ᵣ
          ((spH + signExtend12 (-48 : BitVec 12)) +
            signExtend12 (48 : BitVec 12))) = ((.x2 : Reg) ↦ᵣ spH) :=
    congrArg (fun v => (.x2 : Reg) ↦ᵣ v) hsp
  have hepi :
      k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target delta (0 : Word) =
        (((.x2 : Reg) ↦ᵣ spH) ** ((.x8 : Reg) ↦ᵣ basePtr) **
          ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
          ((.x19 : Reg) ↦ᵣ delta) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            basePtr outPtr target delta (0 : Word)) := by
    unfold k73MulEpilogueNoRa
    rw [hregx2]
  rw [hepi] at hkOwnedA
  dsimp [k73DecreaseDivPairPre, k73DecreaseDivPairFrame,
    k73MulOverflowCoreNoStatus,
    EvmAsm.Codegen.U256MulU64Be.mulTailExtra, u256DivU64BeScratch,
    regOwns, A, AOwned, MulOwned, C, Core] at hkOwnedA ⊢
  xperm_hyp hkOwnedA

/-! The two in-place divisions are common to both fee directions.  This
    decrease-facing wrapper keeps the multiply carry/frame resources in `F`
    and exposes only the divider ABI at the call boundary. -/
theorem k73_decrease_div_pair_spec_within
    (outPtr target delta : Word) (oldRa : Word)
    (outBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4) :
    cpsTripleWithin
      (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps)
      (K73 + 92) (K73 + 124) wholeCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ delta) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
        bytesRegion outPtr outBytes ** F ** regOwn .x10)
      (((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x18 : Reg) ↦ᵣ target) **
        ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns u256DivU64BeScratch **
        bytesRegion outPtr
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8) ** F) := by
  have hown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
    (P := ((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ target) ** ((.x11 : Reg) ↦ᵣ delta) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr outBytes ** F)
    (Q := ((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ target) **
      ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
        (u256DivU64BeQuotBytes outBytes outBytes target)
        (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256DivU64BeScratch **
      bytesRegion outPtr
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8) ** F)
    (fun old10 => by
      have hpair0 := k73_in_place_div_pair_spec_within
        outPtr target oldRa old10 delta outPtr outBytes
        empAssertion (by pcf) hrw hlenOut hoverOut htargetPos
        hsz1 hsz2 hret1 hret2
      have hpairF := cpsTripleWithin_frameR F hF hpair0
      have hpairFW := cpsTripleWithin_extend_code full_whole_mono hpairF
      refine cpsTripleWithin_weaken
        (P := (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x18 : Reg) ↦ᵣ target) ** ((.x10 : Reg) ↦ᵣ old10) **
          ((.x11 : Reg) ↦ᵣ delta) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes **
          empAssertion) ** F)
        (P' := (((.x1 : Reg) ↦ᵣ oldRa) **
          ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
          ((.x11 : Reg) ↦ᵣ delta) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256DivU64BeScratch ** bytesRegion outPtr outBytes ** F) **
          ((.x10 : Reg) ↦ᵣ old10))
        (Q := (((.x1 : Reg) ↦ᵣ (K73 + 124)) **
          ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
          ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
          ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256DivU64BeScratch **
          bytesRegion outPtr
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
          empAssertion) ** F)
        (Q' := ((.x1 : Reg) ↦ᵣ (K73 + 124)) **
          ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
          ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
          ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256DivU64BeScratch **
          bytesRegion outPtr
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8) ** F)
        (fun _ hp => by
          simp only [sepConj_emp_right'] at hp ⊢
          xperm_hyp hp)
        (fun _ hq => by
          simp only [sepConj_emp_right'] at hq ⊢
          xperm_hyp hq) hpairFW)
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hown

/-! The decrease route has `x20 = 0` after the multiply, so the branch at
    `+124` is taken directly to the shared subtraction arm. -/
theorem k73_decrease_div_to_sub_branch_spec_within
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (H : Assertion)
    (hH : H.pcFree) :
    cpsTripleWithin 1 (K73 + 124) (K73 + 172) wholeCode
      (k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
      (k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H) := by
  let q2 : List (BitVec 8) :=
    u256DivU64BeQuotBytes
      (u256DivU64BeQuotBytes outBytes outBytes target)
      (u256DivU64BeQuotBytes outBytes outBytes target) 8
  let Rest : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ target) **
      ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
        (u256DivU64BeQuotBytes outBytes outBytes target)
        (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256DivU64BeScratch ** bytesRegion outPtr q2 **
      ((.x2 : Reg) ↦ᵣ spH) ** ((.x8 : Reg) ↦ᵣ basePtr) **
      ((.x19 : Reg) ↦ᵣ delta) **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word) **
      bytesRegion basePtr baseBytes **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** H
  have hRest : Rest.pcFree := by
    dsimp [Rest, q2]
    pcf
    exact hH
  have hbeq := beq_spec_gen_within .x20 .x0 (48 : BitVec 13)
    (0 : Word) (0 : Word) (K73 + 124)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 31 _ (K73 + 124) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (48 : BitVec 13) = (48 : Word) by decide,
    show (K73 + 124) + (48 : Word) = K73 + 172 by bv_omega,
    show (K73 + 124) + 4 = K73 + 128 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR
    Rest hRest
    hbeqC
  have htaken := cpsBranchWithin_takenPath hbeqF
    (fun _ hq => by
      extract_pure_deep hq
      obtain ⟨h_ne, -⟩ := hq
      exact (by decide : ¬ ((0 : Word) ≠ (0 : Word))) h_ne)
  refine cpsTripleWithin_weaken
    (P' := k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
      v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
    (Q' := k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
      v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
    (fun _ hp => by
      dsimp [k73DecreaseDivPairPost, k73DecreaseDivPairFrame, Rest, q2]
        at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      extract_pure_deep hq
      obtain ⟨-, hq⟩ := hq
      dsimp [k73DecreaseDivPairPost, k73DecreaseDivPairFrame, Rest, q2]
        at hq ⊢
      xperm_hyp hq) htaken

/-! The second zero test is also taken on the decrease route.  After it, the
    three moves at `+204` establish the in-place subtraction ABI. -/
theorem k73_decrease_div_to_sub_spec_within
    (spH raIn basePtr outPtr target delta v8 v9 v18 v19Saved v20Saved : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (H : Assertion)
    (hH : H.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hsz : 4 * ((u256SubBeInPlaceFn basePtr outPtr baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8)).body.size + 1)
      ≤ 2 ^ 64)
    (hret : ((K73 + 216) + 4) &&& ~~~(1 : Word) = K73 + 216 + 4) :
    cpsTripleWithin
      (1 + (5 + (u256SubBeInPlaceFn basePtr outPtr baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8)).body.steps))
      (K73 + 172) (K73 + 220) wholeCode
      (k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
      (((.x1 : Reg) ↦ᵣ (K73 + 220)) **
        ((.x10 : Reg) ↦ᵣ u256SubBeBorrow baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr
          (u256SubBeBytes baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        bytesRegion basePtr baseBytes ** ((.x8 : Reg) ↦ᵣ basePtr) **
        ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spH) **
        ((.x19 : Reg) ↦ᵣ delta) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target delta (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** H) := by
  let q2 : List (BitVec 8) :=
    u256DivU64BeQuotBytes
      (u256DivU64BeQuotBytes outBytes outBytes target)
      (u256DivU64BeQuotBytes outBytes outBytes target) 8
  let Fsub : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spH) **
      ((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ delta) **
      ((.x20 : Reg) ↦ᵣ (0 : Word)) **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** H
  have hFsub : Fsub.pcFree := by
    dsimp [Fsub]
    pcf
    exact hH
  have hq1Len :
      (u256DivU64BeQuotBytes outBytes outBytes target).length = 32 :=
    k73_entry_div_quot_length outBytes outBytes target hlenOut
  have hq2Len : q2.length = 32 := by
    dsimp [q2]
    exact k73_entry_div_quot_length
      (u256DivU64BeQuotBytes outBytes outBytes target)
      (u256DivU64BeQuotBytes outBytes outBytes target) 8 hq1Len
  have hsub := k73_in_place_sub_spec_within
    basePtr outPtr (K73 + 124)
    (u256DivU64BeRemainder
      (u256DivU64BeQuotBytes outBytes outBytes target)
      (u256DivU64BeQuotBytes outBytes outBytes target) 8)
    (8 : Word) outPtr baseBytes q2 Fsub hFsub hrw hroBase hlenBase
    hq2Len
    hovBase hovOut hdisj hsz hret
  have hscratch : u256DivU64BeScratch = u256SubBeInPlaceScratch := by
    rfl
  let SubPost : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 220)) **
      ((.x10 : Reg) ↦ᵣ u256SubBeBorrow baseBytes q2 q2) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr (u256SubBeBytes baseBytes q2 q2) **
      bytesRegion basePtr baseBytes ** ((.x8 : Reg) ↦ᵣ basePtr) **
      ((.x9 : Reg) ↦ᵣ outPtr) ** Fsub
  let Rest : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ target) **
      ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
        (u256DivU64BeQuotBytes outBytes outBytes target)
        (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256DivU64BeScratch ** bytesRegion outPtr q2 **
      ((.x2 : Reg) ↦ᵣ spH) ** ((.x8 : Reg) ↦ᵣ basePtr) **
      ((.x19 : Reg) ↦ᵣ delta) **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target delta (0 : Word) **
      bytesRegion basePtr baseBytes **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19Saved v20Saved) ** H
  have hRest : Rest.pcFree := by
    dsimp [Rest, q2]
    pcf
    exact hH
  have hbeq := beq_spec_gen_within .x20 .x0 (32 : BitVec 13)
    (0 : Word) (0 : Word) (K73 + 172)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 43 _ (K73 + 172) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (32 : BitVec 13) = (32 : Word) by decide,
    show (K73 + 172) + (32 : Word) = K73 + 204 by bv_omega,
    show (K73 + 172) + 4 = K73 + 176 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR Rest hRest hbeqC
  have htaken := cpsBranchWithin_takenPath hbeqF
    (fun _ hq => by
      extract_pure_deep hq
      obtain ⟨h_ne, -⟩ := hq
      exact (by decide : ¬ ((0 : Word) ≠ (0 : Word))) h_ne)
  have hbranch : cpsTripleWithin 1 (K73 + 172) (K73 + 204) wholeCode
      (k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
      (k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H) := by
    refine cpsTripleWithin_weaken
      (P' := k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
      (Q' := k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
      (fun _ hp => by
        dsimp [k73DecreaseDivPairPost, k73DecreaseDivPairFrame, Rest, q2]
          at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨-, hq⟩ := hq
        dsimp [k73DecreaseDivPairPost, k73DecreaseDivPairFrame, Rest, q2]
          at hq ⊢
        xperm_hyp hq) htaken
  have hsub' : cpsTripleWithin
      (5 + (u256SubBeInPlaceFn basePtr outPtr baseBytes q2).body.steps)
      (K73 + 204) (K73 + 220) wholeCode
      (k73DecreaseDivPairPost spH raIn basePtr outPtr target delta
        v8 v9 v18 v19Saved v20Saved baseBytes accBytes outBytes H)
      SubPost := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [k73DecreaseDivPairPost, k73DecreaseDivPairFrame, Fsub, q2]
          at hp ⊢
        rw [hscratch] at hp
        xperm_hyp hp)
      (fun _ hq => by
        dsimp [SubPost, Fsub, q2] at hq ⊢
        xperm_hyp hq) hsub
  have hseq := cpsTripleWithin_seq_same_cr hbranch hsub'
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    dsimp [SubPost, Fsub, q2] at hq ⊢
    xperm_hyp hq) hseq

/-! The nonzero decrease arm subtracts at `+204`, then branches on the
    in-place subtract borrow at `+220`.  Its successful fallthrough starts at
    `+224`, so it needs its own tail rather than the increase tail at `+196`.
    The subtract may have partially overwritten the output before reporting a
    borrow; the caller therefore keeps the actual output bytes existential in
    the nonzero arm and only this status tail pins `a0`. -/
theorem k73_decrease_success_tail_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn) (hP : P.pcFree) :
    cpsTripleWithin 10 (K73 + 224) raIn wholeCode
      ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 0) ** P) := by
  let Rest : Assertion :=
    (.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved ** P
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    exact pcFree_sepConj (pcFree_regIs (r := .x2) (v := spH))
      (pcFree_sepConj (pcFree_regsOwnAt k73Frame)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hP))
  have hliAny : ∀ old10, cpsTripleWithin 1 (K73 + 224) (K73 + 228)
      wholeCode (Rest ** (.x10 ↦ᵣ old10))
      (Rest ** (.x10 ↦ᵣ (0 : Word))) := by
    intro old10
    have hli := li_spec_gen_within .x10 old10 (0 : Word) (K73 + 224)
      (by decide)
    have hliC := cpsTripleWithin_extend_code
      (k73_whole_mem 56 _ (K73 + 224) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hli
    have hliF := cpsTripleWithin_frameR Rest hRest hliC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hli' := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
    (P := Rest) (Q := Rest ** (.x10 ↦ᵣ (0 : Word))) hliAny
  have hj := jal_x0_spec_gen_within (48 : BitVec 21) (K73 + 228)
  rw [show (K73 + 228) + signExtend21 (48 : BitVec 21) = K73 + 276 by
    rw [show signExtend21 (48 : BitVec 21) = (48 : Word) from by decide]
    bv_omega] at hj
  have hjC := cpsTripleWithin_extend_code
    (k73_whole_mem 57 _ (K73 + 228) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hj
  let P0 : Assertion := (.x10 ↦ᵣ (0 : Word)) ** P
  have hP0 : P0.pcFree := by
    dsimp [P0]
    exact pcFree_sepConj (pcFree_regIs (r := .x10) (v := 0)) hP
  have hjF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved) ** P0)
    (by dsimp [P0]; pcf; exact hP) hjC
  have hjump : cpsTripleWithin 1 (K73 + 228) (K73 + 276) wholeCode
      (Rest ** (.x10 ↦ᵣ (0 : Word)))
      (Rest ** (.x10 ↦ᵣ (0 : Word))) := by
    simpa [Rest, P0, sepConj_assoc', sepConj_comm', sepConj_left_comm',
      sepConj_emp_left', sepConj_emp_right'] using hjF
  have hepi := k73_epilogue_spec_within sp0 spH raIn saved P0
    hsp hret hsaved hP0
  have hepi' : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (Rest ** (.x10 ↦ᵣ (0 : Word)))
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 0) ** P) := by
    simpa [Rest, P0, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hepi
  have hseq := cpsTripleWithin_seq_same_cr hli' hjump
  have hseq' := cpsTripleWithin_seq_same_cr hseq hepi'
  dsimp [Rest] at hseq' ⊢
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hseq'

theorem k73_increase_entry_status_div_zero_to_return_general_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (F : Assertion)
    (Nstatus Ntail : Nat)
    (hG : F.pcFree)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hlt : target.toNat < gasUsed.toNat)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F))
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F)))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hq1 : q1 = u256DivU64BeQuotBytes outBytes outBytes target)
    (hq2 : q2 = u256DivU64BeQuotBytes q1 q1 8)
    (hlen1 : q1.length = 32) (hlen2 : q2.length = 32)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAddQ2 : k73AddBSize basePtr outPtr baseBytes q2 ≤ 2 ^ 64)
    (hszAddOne : k73AddBSize basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4)
    (hNstatus : Nstatus =
      3857 + (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps
            + 1)) + 1)))))
    (hNq2 : 1 + k73AddBTailSteps basePtr outPtr baseBytes q2 ≤ Ntail)
    (hNq1 : 1 + k73AddBTailSteps basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ Ntail)
    (hNcarry : 9 ≤ Ntail) :
    cpsBranchWithin (13 + Nstatus + Ntail) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes **
          (regOwns [.x14, .x15, .x16, .x17] ** F)))
      (K73 + 204) (fun _ => False) raIn
      (k73IncreaseStatusFinalPost sp0 spH raIn gasUsed
        basePtr outPtr target v8 v9 v18 v19 v20
        baseBytes accBytes outBytes q2 F) := by
  let Fstatus : Assertion := regOwns [.x14, .x15, .x16, .x17] ** F
  have hFstatus : Fstatus.pcFree := by
    dsimp [Fstatus]
    pcf
    exact hG
  have hspEntry : spH = sp0 + signExtend12 (-56 : BitVec 12) := by
    have hplus : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
    have hminus : signExtend12 (-56 : BitVec 12) =
        (18446744073709551560 : Word) := by decide
    rw [hplus] at hsp
    rw [hminus]
    bv_omega
  have hprefix := k73_increase_entry_to_mul_spec_within
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes Fstatus hspEntry htarget hne hlt hFstatus
  have hroute := k73_increase_status_div_zero_to_return_general
    (sp0 := sp0) (spH := spH) (raIn := raIn)
    (gasLimit := gasLimit) (gasUsed := gasUsed) (basePtr := basePtr)
    (outPtr := outPtr) (target := target)
    (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (v20 := v20)
    (f0 := f0) (f1 := f1) (f2 := f2) (f3 := f3) (f4 := f4) (f5 := f5)
    (baseBytes := baseBytes) (accBytes := accBytes) (outBytes := outBytes)
    (q1 := q1) (q2 := q2) (G := F)
    (Nstatus := Nstatus) (Ntail := Ntail)
    (hG := hG) (hsp := hsp) (hret := hret) (hsaved := hsaved)
    (hcallee := hcallee) (hrw := hrw) (hlenOut := hlenOut)
    (hq1 := hq1) (hq2 := hq2) (hlen1 := hlen1) (hlen2 := hlen2)
    (hoverOut := hovOut) (htargetPos := htargetPos)
    (hovOut := hovOut)
    (hsz1 := hsz1) (hsz2 := hsz2) (hret1 := hret1) (hret2 := hret2)
    (hroBase := hroBase) (hlenBase := hlenBase) (hlenQ2 := hlen2)
    (hovBase := hovBase) (hdisj := hdisj) (hszAddQ2 := hszAddQ2)
    (hszAddOne := hszAddOne) (hcallRet := hcallRet)
    (hNstatus := hNstatus) (hNq2 := hNq2) (hNq1 := hNq1)
    (hNcarry := hNcarry)
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      unfold k73IncreaseMulPre at ⊢
      dsimp [Fstatus] at hp ⊢
      xperm_chunked hp) hprefix hroute
  simpa only [Nat.add_assoc] using hseq

end EvmAsm.Codegen.HeaderBaseFeeSpec
