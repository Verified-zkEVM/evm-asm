/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeTop

  K73's increasing-base-fee entry composition.  The lower-level adapters are
  split between HeaderBaseFeeWholeSpec and HeaderBaseFeeWholeBranches.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeBranches

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256AddBeSAsm
open EvmAsm.Codegen.U256AddBeBInPlaceSAsm

/-! The entry prefix selects the increasing arm.  The saved `x20` value is
    deliberately kept separate from the live flag written by the prefix. -/
theorem k73_increase_entry_to_mul_spec_within
    (sp0 spH raIn basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (hF : F.pcFree) :
    cpsTripleWithin 13 K73 (K73 + 64) wholeCode
      (k73HeadPre sp0 spH raIn (5000 : Word) (5000 : Word)
        basePtr outPtr v8 v9 v18 v19 v20 baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes ** F))
      (k73HeadPost spH raIn (5000 : Word) (5000 : Word)
        basePtr outPtr (2500 : Word) v8 v9 v18 v19 (0 : Word) v20
        baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes ** F)) := by
  let Fmul : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
      bytesRegion U256MulU64Be.accBase accBytes ** F
  let Frest : Assertion :=
    (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
      (.x9 ↦ᵣ outPtr) ** (.x19 ↦ᵣ v19) ** (.x10 ↦ᵣ (5000 : Word)) **
      (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** Fmul
  have hFrest : Frest.pcFree := by
    dsimp [Frest, Fmul]
    pcf
    exact hF
  have hhead := k73_head_spec_within
    sp0 spH raIn (5000 : Word) (5000 : Word) basePtr outPtr (2500 : Word)
    v8 v9 v18 v19 v20 baseBytes outBytes Fmul hsp (by decide) (by
      dsimp [Fmul]
      pcf
      exact hF)
  have hbeq := beq_spec_gen_within .x11 .x18 (192 : BitVec 13)
    (5000 : Word) (2500 : Word) (K73 + 40)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 10 _ (K73 + 40) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (192 : BitVec 13) = (192 : Word) by decide,
    show (K73 + 40) + (192 : Word) = K73 + 232 by bv_omega,
    show (K73 + 40) + 4 = K73 + 44 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR
    ((.x20 ↦ᵣ v20) ** Frest) (by
        dsimp [Frest]
        pcf
        exact hF) hbeqC
  have hneq := cpsBranchWithin_ntakenPath hbeqF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact (by decide : ¬ ((5000 : Word) = 2500)) h_ne)
  have hneq' : cpsTripleWithin 1 (K73 + 40) (K73 + 44) wholeCode
      (((.x11 ↦ᵣ (5000 : Word)) ** (.x18 ↦ᵣ (2500 : Word))) **
        ((.x20 ↦ᵣ v20) ** Frest))
      (((.x11 ↦ᵣ (5000 : Word)) ** (.x18 ↦ᵣ (2500 : Word))) **
        ((.x20 ↦ᵣ v20) ** Frest)) := by
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        extract_pure_deep hq
        obtain ⟨_, hq⟩ := hq
        xperm_chunked hq) hneq
  have hheadneq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [k73HeadPost, Frest, Fmul] at hp ⊢
      xperm_chunked hp) hhead hneq'
  have hli := li_spec_gen_within .x20 v20 (0 : Word) (K73 + 44)
    (by decide)
  have hliC := cpsTripleWithin_extend_code
    (k73_whole_mem 11 _ (K73 + 44) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hli
  let Fli : Assertion :=
    ((.x11 ↦ᵣ (5000 : Word)) ** (.x18 ↦ᵣ (2500 : Word))) ** Frest
  have hFli : Fli.pcFree := by
    dsimp [Fli, Frest, Fmul]
    pcf
    exact hF
  have hliF := cpsTripleWithin_frameR Fli hFli hliC
  have hmid := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [k73HeadPost, Fli, Frest, Fmul] at hp ⊢
      xperm_chunked hp) hheadneq hliF
  have hbltu := bltu_spec_gen_within .x18 .x11 (16 : BitVec 13)
    (2500 : Word) (5000 : Word) (K73 + 48)
  have hbltuC := cpsBranchWithin_extend_code
    (k73_whole_mem 12 _ (K73 + 48) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbltu
  rw [show signExtend13 (16 : BitVec 13) = (16 : Word) by decide,
    show (K73 + 48) + (16 : Word) = K73 + 64 by bv_omega,
    show (K73 + 48) + 4 = K73 + 52 by bv_omega] at hbltuC
  have hbltuF := cpsBranchWithin_frameR
    ((.x20 ↦ᵣ (0 : Word)) ** Frest) (by
      dsimp [Frest]
      pcf
      exact hF) hbltuC
  have htaken := cpsBranchWithin_takenPath hbltuF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact h_ne (by decide))
  have hfinal := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Fli, Frest, Fmul] at hp ⊢
      xperm_chunked hp) hmid htaken
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      extract_pure_deep hq
      obtain ⟨_, hq⟩ := hq
      dsimp [k73HeadPost, Frest, Fmul] at hq ⊢
      xperm_chunked hq) hfinal

/-! The prefix above now feeds the multiply/status adapter. -/
theorem k73_increase_entry_status_branch_spec_within
    (sp0 spH raIn basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (hF : F.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr (2500 : Word) (5000 : Word)
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F)
      (k73IncreaseMulCalleePost spH basePtr outPtr (2500 : Word) (5000 : Word)
        baseBytes accBytes outBytes F)) :
    cpsBranchWithin (13 + 3857) K73 wholeCode
      (k73HeadPre sp0 spH raIn (5000 : Word) (5000 : Word)
        basePtr outPtr v8 v9 v18 v19 v20 baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes ** F))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn (5000 : Word) basePtr outPtr
            (2500 : Word) v8 v9 v18 v19 v20 baseBytes accBytes outBytes F **
          regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn (5000 : Word) basePtr outPtr
            (2500 : Word) v8 v9 v18 v19 v20 baseBytes accBytes outBytes F **
          regOwn .x10) := by
  let Fmul : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
      bytesRegion U256MulU64Be.accBase accBytes ** F
  have hprefix := k73_increase_entry_to_mul_spec_within
    sp0 spH raIn basePtr outPtr v8 v9 v18 v19 v20
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F hsp hF
  have hstatus := k73_increase_mul_status_branch_spec_within
    spH raIn (5000 : Word) (5000 : Word) basePtr outPtr (2500 : Word)
    v8 v9 v18 v19 (0 : Word) v20 f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes F hF hcallee
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      unfold k73IncreaseMulPre at ⊢
      dsimp [Fmul] at hp ⊢
      xperm_chunked hp) hprefix hstatus
  simpa only [show 13 + 3857 = 3870 by decide] using hseq

private theorem k73_increase_status_to_div_spec_within
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))) :
    cpsBranchWithin 3857 (K73 + 64) wholeCode
      (k73IncreaseMulPre spH raIn (5000 : Word) gasUsed basePtr outPtr target
        v8 v9 v18 v19 (0 : Word) v20 f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes
            (regOwns [.x14, .x15, .x16, .x17] ** G) ** regOwn .x10)
      (K73 + 92)
        (fun s => ∃ k, k73IncreaseDivPairPre spH gasUsed basePtr outPtr target
          baseBytes accBytes outBytes
          (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G)
          k s) := by
  let Fstatus : Assertion := regOwns [.x14, .x15, .x16, .x17] ** G
  have hFstatus : Fstatus.pcFree := by
    dsimp [Fstatus]
    pcf
    exact hG
  have hstatus := k73_increase_mul_status_branch_spec_within
    spH raIn (5000 : Word) gasUsed basePtr outPtr target
    v8 v9 v18 v19 (0 : Word) v20 f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes Fstatus hFstatus hcallee
  have hcarry := k73_increase_mul_carry_to_div_pre
    spH raIn gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    baseBytes accBytes outBytes G
  refine cpsBranchWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => hq)
    (fun s hq => hcarry s hq) hstatus

@[irreducible] def k73IncreaseDivZeroPost
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) :
    Assertion := fun s =>
  ∃ k : Nat,
    (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
      k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes
        (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k) s ∨
    (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      regOwns exposedRegs **
      bytesRegion outPtr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) **
      ((.x18 : Reg) ↦ᵣ target) **
      k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes
        (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k) s

private theorem k73_increase_status_div_zero_spec_within
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G)))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hq1 : q1 = u256DivU64BeQuotBytes outBytes outBytes target)
    (hq2 : q2 = u256DivU64BeQuotBytes q1 q1 8)
    (hlen1 : q1.length = 32) (hlen2 : q2.length = 32)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (htargetBound : target.toNat ≤ 2 ^ 56)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4) :
    cpsBranchWithin
      (3857 + (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps + 1)) + 1)))))
      (K73 + 64) wholeCode
      (k73IncreaseMulPre spH raIn (5000 : Word) gasUsed basePtr outPtr target
        v8 v9 v18 v19 (0 : Word) v20 f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes
            (regOwns [.x14, .x15, .x16, .x17] ** G) ** regOwn .x10)
      (K73 + 172)
        (k73IncreaseDivZeroPost spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G) := by
  let Fstatus : Assertion := regOwns [.x14, .x15, .x16, .x17] ** G
  have hFstatus : Fstatus.pcFree := by
    dsimp [Fstatus]
    pcf
    exact hG
  have hstatus := k73_increase_status_to_div_spec_within
    spH raIn gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes G hG hcallee
  have hGdiv : (frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19 v20) ** G).pcFree := by
    pcf
    exact hG
  have hzero := k73_increase_div_zero_branch_spec_within
    spH gasUsed basePtr outPtr target baseBytes accBytes outBytes q1 q2
    (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G)
    hGdiv hrw hlenOut hq1 hq2 hlen1 hlen2 hoverOut htargetPos htargetBound
    hsz1 hsz2 hret1 hret2
  have hseq := cpsBranchWithin_seq_cpsTripleWithin_same_cr hstatus hzero
    (fun _ hq => hq)
  unfold k73IncreaseDivZeroPost
  exact hseq

private theorem k73_increase_nonzero_exit_branch
    (P : Assertion) (hP : P.pcFree) :
    cpsBranchWithin 1 (K73 + 172) wholeCode
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)
      (K73 + 204) (fun _ => False)
      (K73 + 176)
        (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P) := by
  have hbeq := beq_spec_gen_within .x20 .x0 (32 : BitVec 13)
    (1 : Word) (0 : Word) (K73 + 172)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 43 _ (K73 + 172) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (32 : BitVec 13) = (32 : Word) by decide,
    show (K73 + 172) + (32 : Word) = K73 + 204 by bv_omega,
    show (K73 + 172) + 4 = K73 + 176 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR P hP hbeqC
  refine cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      extract_pure_deep hq
      obtain ⟨h_eq, _⟩ := hq
      exact (by decide : ¬ ((1 : Word) = 0)) h_eq)
    (fun _ hq => by
      extract_pure_deep hq
      obtain ⟨_, hq⟩ := hq
      xperm_hyp hq) hbeqF

@[irreducible] def k73IncreaseAddTailP
    (_spH basePtr outPtr : Word)
    (baseBytes q2 : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
    (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
    bytesRegion outPtr (u256AddBeBytes baseBytes q2 q2) **
    bytesRegion basePtr baseBytes ** F

@[irreducible] def k73IncreaseFirstAddPre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) : Assertion :=
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
    bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G))

private theorem k73_increase_first_add_branch
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenQ2 : q2.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAdd : k73AddBSize basePtr outPtr baseBytes q2 ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes q2)
      (K73 + 176) wholeCode
      (k73IncreaseFirstAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G)
      (K73 + 272)
        (k73AddBTailPost spH (k73Saved raIn v8 v9 v18 v19 v20)
          (k73IncreaseAddTailP spH basePtr outPtr baseBytes q2
            (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
              (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
              bytesRegion U256MulU64Be.accBase accBytes ** G)))
      (K73 + 196)
        (k73AddBTailPost spH (k73Saved raIn v8 v9 v18 v19 v20)
          (k73IncreaseAddTailP spH basePtr outPtr baseBytes q2
            (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
              (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
              bytesRegion U256MulU64Be.accBase accBytes ** G))) := by
  let F : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G
  let FrameRest : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20)
  let Fadd : Assertion := FrameRest ** F
  let TailP : Assertion := k73IncreaseAddTailP
    spH basePtr outPtr baseBytes q2 F
  have hF : F.pcFree := by
    dsimp [F]
    pcf
    exact hG
  have hFrameRest : FrameRest.pcFree := by
    dsimp [FrameRest]
    pcf
  have hFadd : Fadd.pcFree := by
    dsimp [Fadd]
    exact pcFree_sepConj hFrameRest hF
  have hTailP : TailP.pcFree := by
    unfold TailP k73IncreaseAddTailP
    pcf
    exact hG
  have hbranch := k73_in_place_add_tail_branch_spec_within
    spH (k73Saved raIn v8 v9 v18 v19 v20) basePtr outPtr
    (K73 + 136) (0 : Word) (8 : Word) outPtr baseBytes q2 F Fadd TailP
    (by simp [Fadd, FrameRest, F, sepConj_assoc'])
    (by simp [TailP, k73IncreaseAddTailP, F]) hFadd hrw hroBase
    hlenBase hlenQ2 hovBase hovOut hdisj hszAdd hcallRet
  simpa only [k73IncreaseFirstAddPre, k73IncreaseAddTailP, k73AddBTailPost,
    Fadd, FrameRest, TailP, F, sepConj_assoc'] using hbranch

@[irreducible] def k73IncreaseSecondAddPre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion) : Assertion :=
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    regOwns exposedRegs ** bytesRegion outPtr orig **
    bytesRegion basePtr baseBytes ** ((.x2 : Reg) ↦ᵣ spH) **
    regsOwnAt k73FrameRest3 **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G))

private theorem k73_increase_second_add_branch
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAdd : k73AddBSize basePtr outPtr baseBytes orig ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 176) wholeCode
      (k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G)
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 **
          k73IncreaseAddTailP spH basePtr outPtr baseBytes orig
            (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
              (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
              bytesRegion U256MulU64Be.accBase accBytes ** G))
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 **
          k73IncreaseAddTailP spH basePtr outPtr baseBytes orig
            (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
              (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
              bytesRegion U256MulU64Be.accBase accBytes ** G)) := by
  let F : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G
  let FrameRest : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20)
  let Fadd : Assertion := FrameRest ** F
  let TailP : Assertion := k73IncreaseAddTailP
    spH basePtr outPtr baseBytes orig F
  have hF : F.pcFree := by
    dsimp [F]
    pcf
    exact hG
  have hFrameRest : FrameRest.pcFree := by
    dsimp [FrameRest]
    pcf
  have hFadd : Fadd.pcFree := by
    dsimp [Fadd]
    exact pcFree_sepConj hFrameRest hF
  have hTailP : TailP.pcFree := by
    unfold TailP k73IncreaseAddTailP
    pcf
    exact hG
  have hraw : ∀ v10 v11 v12, cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 176) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion basePtr baseBytes ** Fadd) ** ((.x12 : Reg) ↦ᵣ v12)))
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** TailP)
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** TailP) := by
    intro v10 v11 v12
    have hbranch := k73_in_place_add_tail_branch_spec_within
      spH (k73Saved raIn v8 v9 v18 v19 v20) basePtr outPtr
      (K73 + 152) v10 v11 v12 baseBytes orig F Fadd TailP
      (by simp [Fadd, FrameRest, F, sepConj_assoc'])
      (by simp [TailP, k73IncreaseAddTailP, F]) hFadd hrw hroBase
      hlenBase hlenOrig hovBase hovOut hdisj hszAdd hcallRet
    refine cpsBranchWithin_weaken
      (P :=
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
          ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
          ((.x12 : Reg) ↦ᵣ v12) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr orig ** bytesRegion basePtr baseBytes ** Fadd))
      (P' :=
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
          ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
            regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
            bytesRegion basePtr baseBytes ** Fadd) ** ((.x12 : Reg) ↦ᵣ v12)))
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hbranch
  have h12 : ∀ v10 v11, cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 176) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion basePtr baseBytes ** Fadd) ** regOwn .x12))
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** TailP)
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** TailP) := by
    intro v10 v11
    simpa only [sepConj_assoc'] using
      (cpsBranchWithin_of_forall_regIs_to_regOwn
        (r := .x12)
        (P :=
          (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
            ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
            ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
            regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
            bytesRegion basePtr baseBytes ** Fadd))
        (fun v12 => hraw v10 v11 v12))
  have h11 : ∀ v10, cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 176) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr orig ** bytesRegion basePtr baseBytes ** Fadd **
        regOwn .x12) ** regOwn .x11))
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** TailP)
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** TailP) := by
    intro v10
    refine cpsBranchWithin_of_forall_regIs_to_regOwn
      (r := .x11)
      (P :=
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
          ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x10 : Reg) ↦ᵣ v10) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr orig ** bytesRegion basePtr baseBytes ** Fadd **
          regOwn .x12)) ?_
    intro v11
    simpa only [sepConj_assoc'] using (cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) (fun _ hq => by xperm_hyp hq)
      (h12 v10 v11))
  have h10 := cpsBranchWithin_of_forall_regIs_to_regOwn
    (r := .x10)
    (P :=
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion basePtr baseBytes ** Fadd ** regOwn .x11 ** regOwn .x12))
    (fun v10 => cpsBranchWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) (fun _ hq => by xperm_hyp hq)
      (h11 v10))
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      simp only [k73IncreaseSecondAddPre, Fadd, FrameRest, F,
        exposedRegs, u256AddBeBInPlaceScratch, regOwns,
        regAtomsOf_cons, regAtomsOf_nil, sepConj_assoc', sepConj_comm',
        sepConj_left_comm'] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq) h10

@[irreducible] def k73IncreaseFirstDivPost
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) :
    Assertion :=
  (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
    bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
    k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)

private theorem k73_increase_reg_frame_rearrange
    (target delta : Word) (R : Assertion) :
    ∀ s,
      (((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ delta) **
        ((.x20 : Reg) ↦ᵣ (1 : Word)) ** R) s →
      (regsOwnAt k73FrameRest3 ** R) s := by
  intro s hs
  let vals : Reg → Word := fun r => match r with
    | .x18 => target
    | .x19 => delta
    | .x20 => 1
    | _ => 0
  have hreg := regsAt_implies_regsOwnAt k73FrameRest3 vals
  have hreg' :
      ((regsAt k73FrameRest3 vals) ** R) s := by
    simpa [regsAt, k73FrameRest3, vals, sepConj_emp_left',
      sepConj_emp_right', sepConj_assoc'] using hs
  exact sepConj_mono_left hreg s hreg'

/- obsolete expanded first-branch adapter; generic ownership lemma above is the
   reusable seam, and the full continuation will consume it after the branch
   shape is assembled.
private theorem k73_increase_first_div_to_add_pre_clean
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) :
    ∀ s, k73IncreaseFirstDivPost spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s →
      k73IncreaseFirstAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G s := by
  intro s hs
  unfold k73IncreaseFirstDivPost at hs
  unfold k73IncreaseFirstAddPre at ⊢
  let R : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
      ((.x2 : Reg) ↦ᵣ spH) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G
  have hsplit :
      (((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
        ((.x20 : Reg) ↦ᵣ (1 : Word)) ** R) s := by
    dsimp [R, k73IncreaseDivPairFrame, k73IncreaseDivPairCoreFrame] at hs ⊢
    xperm_hyp hs
  have hown := k73_increase_reg_frame_rearrange
    target (gasUsed - target) R s hsplit
  dsimp [R] at hown ⊢
  simp [u256DivU64BeScratch, u256AddBeBInPlaceScratch,
    sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hown ⊢
  xperm_hyp hown

/- old expanded first-branch helper kept only as a scratch note
private theorem k73_increase_first_div_to_add_pre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) :
    ∀ s, k73IncreaseFirstDivPost spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s →
      k73IncreaseFirstAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G s := by
/- old expanded type:
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
        bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
        k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
          baseBytes accBytes
          (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k) s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
        ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
          (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
          bytesRegion U256MulU64Be.accBase accBytes ** G)) s := by
-/
  intro s hs
  let vals : Reg → Word := fun r => match r with
    | .x18 => target
    | .x19 => gasUsed - target
    | .x20 => 1
    | _ => 0
  let R : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
      ((.x2 : Reg) ↦ᵣ spH) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G
  have hsplit :
      (((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
        ((.x20 : Reg) ↦ᵣ (1 : Word)) ** R) s := by
    unfold k73IncreaseFirstDivPost at hs
    dsimp [k73IncreaseFirstDivPost, R, k73IncreaseDivPairFrame,
      k73IncreaseDivPairCoreFrame] at hs ⊢
    xperm_hyp hs
  have hown :
      ((regsOwnAt k73FrameRest3) ** R) s := by
    have hreg := regsAt_implies_regsOwnAt k73FrameRest3 vals
    have hreg' :
        ((regsAt k73FrameRest3 vals) ** R) s := by
      simpa [regsAt, k73FrameRest3, vals, sepConj_emp_left',
        sepConj_emp_right', sepConj_assoc'] using hsplit
    exact sepConj_mono_left hreg s hreg'
  dsimp [k73IncreaseFirstAddPre, R] at hown ⊢
  simp [u256DivU64BeScratch, u256AddBeBInPlaceScratch,
    sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hown ⊢
  xperm_hyp hown

/- scratch helper removed
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
        bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
        k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
          baseBytes accBytes
          (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G0) k) s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
        ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
          (fun | .x5 => 0 | .x6 => 0 | .x7 => 0 | .x28 => 0 | .x29 => 0 | .x30 => 0 | .x31 => 0 | _ => 0) .x5
          0 0 0 0 0 ** bytesRegion U256MulU64Be.accBase accBytes ** G0)) s := by
  intro s hs
-/
-/
-/

end EvmAsm.Codegen.HeaderBaseFeeSpec
