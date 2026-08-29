/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeTop

  K73's increasing-base-fee entry composition.  The lower-level adapters are
  split between HeaderBaseFeeWholeSpec and HeaderBaseFeeWholeBranches.
  The x14--x17 ownership is inherited from generic contracts, not a claim that
  K73 writes them; exact footprint is [x5, x6, x7, x28, x29, x30, x31]
  plus genuine x13 clobber; ELF sha256 is 06cd10315b05beda7fc5dc43839ffc3a9e809f6e031d0b58d207a1633b351c4f; Item 12
  owns cancellation, so this banks an over-approximation, not exact Route-B.
-/
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeBranches
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeInPlaceAdd
import EvmAsm.Rv64.Tactics.XCancelStruct

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256AddBeSAsm
open EvmAsm.Codegen.U256AddBeBInPlaceSAsm

/-! The entry prefix selects the increasing arm.  The saved `x20` value is
    deliberately kept separate from the live flag written by the prefix. -/
theorem k73_increase_entry_to_mul_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hlt : target.toNat < gasUsed.toNat)
    (hF : F.pcFree) :
    cpsTripleWithin 13 K73 (K73 + 68) wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed
        basePtr outPtr v8 v9 v18 v19 v20 baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes ** F))
      (k73HeadPost spH raIn gasLimit gasUsed
        basePtr outPtr target v8 v9 v18 v19 (0 : Word) v20
        baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes ** F)) := by
  let Fmul : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
      bytesRegion U256MulU64Be.accBase accBytes ** F
  let Frest : Assertion :=
    (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
      (.x9 ↦ᵣ outPtr) ** (.x19 ↦ᵣ v19) ** (.x10 ↦ᵣ gasLimit) **
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
    sp0 spH raIn gasLimit gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes outBytes Fmul hsp htarget (by
      dsimp [Fmul]
      pcf
      exact hF)
  have hbeq := beq_spec_gen_within .x11 .x18 (196 : BitVec 13)
    gasUsed target (K73 + 40)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 10 _ (K73 + 40) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (196 : BitVec 13) = (196 : Word) by decide,
    show (K73 + 40) + (196 : Word) = K73 + 236 by bv_omega,
    show (K73 + 40) + 4 = K73 + 44 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR
    ((.x20 ↦ᵣ v20) ** Frest) (by
        dsimp [Frest]
        pcf
        exact hF) hbeqC
  have hneq := cpsBranchWithin_ntakenPath hbeqF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact hne h_ne)
  have hneq' : cpsTripleWithin 1 (K73 + 40) (K73 + 44) wholeCode
      (((.x11 ↦ᵣ gasUsed) ** (.x18 ↦ᵣ target)) **
        ((.x20 ↦ᵣ v20) ** Frest))
      (((.x11 ↦ᵣ gasUsed) ** (.x18 ↦ᵣ target)) **
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
    ((.x11 ↦ᵣ gasUsed) ** (.x18 ↦ᵣ target)) ** Frest
  have hFli : Fli.pcFree := by
    dsimp [Fli, Frest, Fmul]
    pcf
    exact hF
  have hliF := cpsTripleWithin_frameR Fli hFli hliC
  have hmid := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [k73HeadPost, Fli, Frest, Fmul] at hp ⊢
      xperm_chunked hp) hheadneq hliF
  have hbltu := bltu_spec_gen_within .x18 .x11 (20 : BitVec 13)
    target gasUsed (K73 + 48)
  have hbltuC := cpsBranchWithin_extend_code
    (k73_whole_mem 12 _ (K73 + 48) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbltu
  rw [show signExtend13 (20 : BitVec 13) = (20 : Word) by decide,
    show (K73 + 48) + (20 : Word) = K73 + 68 by bv_omega,
    show (K73 + 48) + 4 = K73 + 52 by bv_omega] at hbltuC
  have hbltuF := cpsBranchWithin_frameR
    ((.x20 ↦ᵣ (0 : Word)) ** Frest) (by
      dsimp [Frest]
      pcf
      exact hF) hbltuC
  have htaken := cpsBranchWithin_takenPath hbltuF (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact h_ne ((BitVec.ult_iff_toNat_lt).2 hlt))
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

private theorem k73_increase_status_to_div_spec_within
    (spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 92) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))) :
    cpsBranchWithin 3857 (K73 + 68) wholeCode
      (k73IncreaseMulPre spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 (0 : Word) v20 f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (K73 + 276)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes
            (regOwns [.x14, .x15, .x16, .x17] ** G) ** regOwn .x10)
      (K73 + 96)
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
    spH raIn gasLimit gasUsed basePtr outPtr target
    v8 v9 v18 v19 (0 : Word) v20 f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes Fstatus hFstatus hcallee
  have hcarry := k73_increase_mul_carry_to_div_pre
    spH raIn gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    baseBytes accBytes outBytes G
  refine cpsBranchWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => hq)
    (fun s hq => hcarry s hq) hstatus

/-- The keep/replace disjuncts carry the window-value pures
`beBytesToNat q2 ≠ 0` / `= 0`: the zero-test controls WHICH BYTES the window
holds (keep window = `AddBe p q2 q2` vs replace image = `AddBe p 1 1`), so
without the pures the post is PATH-BLIND, and a path-blind post admits
countermodel states that no local window algebra can kill, because the
implication quantifies over all states satisfying the post rather than the
reachable ones. Do not weaken the pures back out. -/
@[irreducible] def k73IncreaseDivZeroPost
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) :
    Assertion := fun s =>
  ∃ k : Nat,
    ((((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
      k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes
        (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k) ** ⌜EvmAsm.Crypto.beBytesToNat q2 ≠ 0⌝) s ∨
    ((((.x1 : Reg) ↦ᵣ (K73 + 156)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      regOwns exposedRegs **
      bytesRegion outPtr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) **
      ((.x18 : Reg) ↦ᵣ target) **
      k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes
        (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k) ** ⌜EvmAsm.Crypto.beBytesToNat q2 = 0⌝) s

theorem k73_increase_status_div_zero_spec_within
    (spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 92) mulCode
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
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 108) + 4) &&& ~~~(1 : Word) = (K73 + 108) + 4)
    (hret2 : ((K73 + 124) + 4) &&& ~~~(1 : Word) = (K73 + 124) + 4) :
    cpsBranchWithin
      (3857 + (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps + 1)) + 1)))))
      (K73 + 68) wholeCode
      (k73IncreaseMulPre spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 (0 : Word) v20 f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (K73 + 276)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes
            (regOwns [.x14, .x15, .x16, .x17] ** G) ** regOwn .x10)
      (K73 + 176)
        (k73IncreaseDivZeroPost spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G) := by
  let Fstatus : Assertion := regOwns [.x14, .x15, .x16, .x17] ** G
  have hFstatus : Fstatus.pcFree := by
    dsimp [Fstatus]
    pcf
    exact hG
  have hstatus := k73_increase_status_to_div_spec_within
    spH raIn gasLimit gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes G hG hcallee
  have hGdiv : (frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19 v20) ** G).pcFree := by
    pcf
    exact hG
  have hzero := k73_increase_div_zero_branch_spec_within
    spH gasUsed basePtr outPtr target baseBytes accBytes outBytes q1 q2
    (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G)
    hGdiv hrw hlenOut hq1 hq2 hlen1 hlen2 hoverOut htargetPos
    hsz1 hsz2 hret1 hret2
  have hseq := cpsBranchWithin_seq_cpsTripleWithin_same_cr hstatus hzero
    (fun _ hq => hq)
  unfold k73IncreaseDivZeroPost
  exact hseq

private theorem k73_increase_nonzero_exit_branch
    (P : Assertion) (hP : P.pcFree) :
    cpsBranchWithin 1 (K73 + 176) wholeCode
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)
      (K73 + 208) (fun _ => False)
      (K73 + 180)
        (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P) := by
  have hbeq := beq_spec_gen_within .x20 .x0 (32 : BitVec 13)
    (1 : Word) (0 : Word) (K73 + 176)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 44 _ (K73 + 176) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (32 : BitVec 13) = (32 : Word) by decide,
    show (K73 + 176) + (32 : Word) = K73 + 208 by bv_omega,
    show (K73 + 176) + 4 = K73 + 180 by bv_omega] at hbeqC
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
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
    bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
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
    (hcallRet : ((K73 + 192) + 4) &&& ~~~(1 : Word) = (K73 + 192) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes q2)
      (K73 + 180) wholeCode
      (k73IncreaseFirstAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G)
      (K73 + 276)
        (k73AddBTailPost spH (k73Saved raIn v8 v9 v18 v19 v20)
          (k73IncreaseAddTailP spH basePtr outPtr baseBytes q2
            (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
              (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
              bytesRegion U256MulU64Be.accBase accBytes ** G)))
      (K73 + 200)
        (k73AddBTailPost spH (k73Saved raIn v8 v9 v18 v19 v20)
          (k73IncreaseAddTailP spH basePtr outPtr baseBytes q2
            (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
              (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
              bytesRegion U256MulU64Be.accBase accBytes ** G))) := by
  let F : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
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
    (K73 + 140) (0 : Word) (8 : Word) outPtr baseBytes q2 F Fadd TailP
    (by simp [Fadd, FrameRest, F, sepConj_assoc'])
    (by simp [TailP, k73IncreaseAddTailP, F]) hFadd hrw hroBase
    hlenBase hlenQ2 hovBase hovOut hdisj hszAdd hcallRet
  simpa only [k73IncreaseFirstAddPre, k73IncreaseAddTailP, k73AddBTailPost,
    Fadd, FrameRest, TailP, F, sepConj_assoc'] using hbranch

@[irreducible] def k73IncreaseSecondAddPre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion) : Assertion :=
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    regOwns exposedRegs ** bytesRegion outPtr orig **
    bytesRegion basePtr baseBytes ** ((.x2 : Reg) ↦ᵣ spH) **
    regsOwnAt k73FrameRest3 **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G))

@[irreducible] def k73IncreaseAddTailPost
    (spH raIn basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes _accBytes orig : List (BitVec 8)) (F : Assertion) : Assertion :=
  k73AddBTailPost spH (k73Saved raIn v8 v9 v18 v19 v20)
    (k73IncreaseAddTailP spH basePtr outPtr baseBytes orig F)

private theorem k73_increase_add_tail_raw
    (spH : Word) (saved : Reg → Word)
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F Fadd TailP : Assertion)
    (hFaddShape : Fadd =
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F))
    (hTailPShape : TailP =
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** F))
    (hFadd : Fadd.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hcallRet : ((K73 + 192) + 4) &&& ~~~(1 : Word) = (K73 + 192) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 180) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd) ** ((.x12 : Reg) ↦ᵣ v12)))
      (K73 + 276) (k73AddBTailPost spH saved TailP)
      (K73 + 200) (k73AddBTailPost spH saved TailP) := by
  have hbranch := k73_in_place_add_tail_branch_spec_within
    spH saved srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F Fadd TailP
    hFaddShape hTailPShape hFadd hrw hroSrc hlenSrc hlenOrig hovSrc hovOut
    hdisj hsz hcallRet
  refine cpsBranchWithin_weaken
    (P := (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
      ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
      ((.x12 : Reg) ↦ᵣ v12) ** regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr orig ** bytesRegion srcPtr srcBytes ** Fadd))
    (P' := (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
      ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
      regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
      bytesRegion srcPtr srcBytes ** Fadd) ** ((.x12 : Reg) ↦ᵣ v12))))
    ?_ ?_ ?_ hbranch
  · intro _ hp
    xperm_hyp hp
  · intro _ hq
    simpa only [k73AddBTailPost] using hq
  · intro _ hq
    simpa only [k73AddBTailPost] using hq

private theorem k73_increase_add_tail_own_regs
    (srcPtr outPtr oldRa : Word)
    (srcBytes orig : List (BitVec 8)) (Fadd Qt Qf : Assertion)
    (hraw : ∀ v10 v11 v12, cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 180) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd) ** ((.x12 : Reg) ↦ᵣ v12)))
      (K73 + 276) Qt (K73 + 200) Qf) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 180) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns exposedRegs ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd)
      (K73 + 276) Qt (K73 + 200) Qf := by
  have h12 : ∀ v10 v11, cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 180) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd) ** regOwn .x12))
      (K73 + 276) Qt (K73 + 200) Qf := by
    intro v10 v11
    simpa only [sepConj_assoc'] using
      (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x12)
        (P :=
          (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
            ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
            ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
            regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
            bytesRegion srcPtr srcBytes ** Fadd))
        (fun v12 => hraw v10 v11 v12))
  have h11 : ∀ v10, cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 180) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr orig ** bytesRegion srcPtr srcBytes ** Fadd **
        regOwn .x12) ** regOwn .x11))
      (K73 + 276) Qt (K73 + 200) Qf := by
    intro v10
    refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x11)
      (P :=
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
          ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x10 : Reg) ↦ᵣ v10) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr orig ** bytesRegion srcPtr srcBytes ** Fadd **
          regOwn .x12)) ?_
    intro v11
    simpa only [sepConj_assoc'] using (cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) (h12 v10 v11))
  have h10 := cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x10)
    (P :=
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd ** regOwn .x11 ** regOwn .x12))
    (fun v10 => cpsBranchWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) (h11 v10))
  refine cpsBranchWithin_weaken
    (P :=
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd ** regOwn .x11 ** regOwn .x12) **
        regOwn .x10)
    (P' :=
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x8 : Reg) ↦ᵣ srcPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns exposedRegs ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd))
    (fun _ hp => by
      simp only [exposedRegs, u256AddBeBInPlaceScratch, regOwns,
        sepConj_comm', sepConj_left_comm'] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq) h10

@[irreducible] def k73IncreaseSecondAddOwnPre
    (_spH _raIn basePtr outPtr : Word) (Fadd : Assertion)
    (baseBytes orig : List (BitVec 8)) : Assertion :=
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    regOwns exposedRegs ** bytesRegion outPtr orig **
    bytesRegion basePtr baseBytes ** Fadd)

theorem k73_increase_second_add_branch
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
    (hcallRet : ((K73 + 192) + 4) &&& ~~~(1 : Word) = (K73 + 192) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 180) wholeCode
      (k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G)
      (K73 + 276)
        (k73IncreaseAddTailPost spH raIn basePtr outPtr
          v8 v9 v18 v19 v20 baseBytes accBytes orig
          (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
            (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
            bytesRegion U256MulU64Be.accBase accBytes ** G))
      (K73 + 200)
        (k73IncreaseAddTailPost spH raIn basePtr outPtr
          v8 v9 v18 v19 v20 baseBytes accBytes orig
          (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
            (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
            bytesRegion U256MulU64Be.accBase accBytes ** G)) := by
  let F : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G
  let FrameRest : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20)
  let Fadd : Assertion := FrameRest ** F
  let TailP : Assertion := k73IncreaseAddTailP
    spH basePtr outPtr baseBytes orig F
  let Post : Assertion :=
    (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x10 ** TailP)
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
      (K73 + 180) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion basePtr baseBytes ** Fadd) ** ((.x12 : Reg) ↦ᵣ v12)))
      (K73 + 276) Post
      (K73 + 200) Post := by
    intro v10 v11 v12
    simpa only [Post, k73AddBTailPost] using
      (k73_increase_add_tail_raw
        spH (k73Saved raIn v8 v9 v18 v19 v20) basePtr outPtr
        (K73 + 156) v10 v11 v12 baseBytes orig F Fadd TailP
        (by simp [Fadd, FrameRest, F, sepConj_assoc'])
        (by simp [TailP, k73IncreaseAddTailP, F]) hFadd hrw hroBase
        hlenBase hlenOrig hovBase hovOut hdisj hszAdd hcallRet)
  /-
  have h12 : ∀ v10 v11, cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 180) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion basePtr baseBytes ** Fadd) ** regOwn .x12))
      (K73 + 276) Post
      (K73 + 200) Post := by
    intro v10 v11
    simpa only [sepConj_assoc'] using
      (cpsBranchWithin_of_forall_regIs_to_regOwn
        (r := .x12)
        (P :=
          (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
            ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
            ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
            regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
            bytesRegion basePtr baseBytes ** Fadd))
        (fun v12 => hraw v10 v11 v12))
  have h11 : ∀ v10, cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 180) wholeCode
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr orig ** bytesRegion basePtr baseBytes ** Fadd **
        regOwn .x12) ** regOwn .x11))
      (K73 + 276) Post
      (K73 + 200) Post := by
    intro v10
    refine cpsBranchWithin_of_forall_regIs_to_regOwn
      (r := .x11)
      (P :=
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
          ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x10 : Reg) ↦ᵣ v10) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr orig ** bytesRegion basePtr baseBytes ** Fadd **
          regOwn .x12)) ?_
    intro v11
    simpa only [sepConj_assoc'] using (cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq)
      (h12 v10 v11))
  have h10 := cpsBranchWithin_of_forall_regIs_to_regOwn
    (r := .x10)
    (P :=
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion basePtr baseBytes ** Fadd ** regOwn .x11 ** regOwn .x12))
    (fun v10 => cpsBranchWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq)
      (h11 v10))
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      simp only [k73IncreaseSecondAddPre, Fadd, FrameRest, F,
        exposedRegs, u256AddBeBInPlaceScratch, regOwns,
        regAtomsOf_cons, regAtomsOf_nil, sepConj_assoc', sepConj_comm',
        sepConj_left_comm'] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq) h10
  -/
  have hown := k73_increase_add_tail_own_regs
    basePtr outPtr (K73 + 156) baseBytes orig Fadd Post Post hraw
  have hown' : cpsBranchWithin
      (k73AddBBranchSteps basePtr outPtr baseBytes orig)
      (K73 + 180) wholeCode
      (k73IncreaseSecondAddOwnPre spH raIn basePtr outPtr Fadd baseBytes orig)
      (K73 + 276) Post (K73 + 200) Post := by
    simpa only [k73IncreaseSecondAddOwnPre] using hown
  /-
  refine cpsBranchWithin_weaken
    (P :=
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns exposedRegs ** bytesRegion outPtr orig **
        bytesRegion basePtr baseBytes ** Fadd))
    (P' := k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes orig G)
    (fun _ hp => by
      simp only [k73IncreaseSecondAddPre, Fadd, FrameRest, F,
        exposedRegs, u256AddBeBInPlaceScratch, regOwns,
        regAtomsOf_cons, regAtomsOf_nil, sepConj_assoc', sepConj_comm',
        sepConj_left_comm'] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by simpa only [Post, k73AddBTailPost] using hq)
    (fun _ hq => by simpa only [Post, k73AddBTailPost] using hq) hown
  -/
  refine cpsBranchWithin_weaken
    (fun s hp => by
      unfold k73IncreaseSecondAddPre at hp
      unfold k73IncreaseSecondAddOwnPre
      have hFShape : F =
          (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
            (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
            bytesRegion U256MulU64Be.accBase accBytes ** G) := by
        simp [F]
      have hFaddShape : Fadd = (FrameRest ** F) := by
        simp only [Fadd, FrameRest]
      rw [hFaddShape, hFShape]
      xperm_hyp hp)
    (fun _ hq => by
      simpa only [Post, k73IncreaseAddTailPost, k73AddBTailPost, TailP,
        k73IncreaseAddTailP, F] using hq)
    (fun _ hq => by
      simpa only [Post, k73IncreaseAddTailPost, k73AddBTailPost, TailP,
        k73IncreaseAddTailP, F] using hq) hown'

@[irreducible] def k73IncreaseFirstDivPost
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) :
    Assertion :=
  (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
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

/-! The divider posts expose the same live values that the add arms need.  The
    opaque aliases keep this ownership seam from re-elaborating the large
    branch posts at every use site. -/
@[irreducible] def k73IncreaseFirstDivToAddSource
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) : Assertion :=
  (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
    bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
    k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)

@[irreducible] def k73IncreaseFirstDivToAddTarget
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) : Assertion :=
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
    bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G))

/-
/-! The branch at `K73 + 176` owns `x0` and `x20` itself.  Keep those two
    atoms out of the divider core passed to that branch; the full divider
    source above is the postcondition shape used after the branch.  Passing
    the full shape as `P` to `k73_increase_nonzero_exit_branch` would supply
    both atoms twice and make the composed precondition unsatisfiable. -/
@[irreducible] def k73IncreaseFirstDivCoreSource
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) : Assertion :=
  (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
    ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
    bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
    k73IncreaseDivPairCoreFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)

theorem k73_increase_first_div_source_branch
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree) (k : Nat) :
    cpsBranchWithin 1 (K73 + 176) wholeCode
      (k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G k)
      (K73 + 208) (fun _ => False)
      (K73 + 180)
        (k73IncreaseFirstAddPre spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G) := by
  let Core : Assertion :=
    ((regIs .x1 (K73 + 140) ** regIs .x9 outPtr) **
      regIs .x10 (0 : Word) ** regIs .x11 (8 : Word) **
      regIs .x12 outPtr ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** regIs .x18 target **
      k73IncreaseDivPairCoreFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes
        (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)
  have hCore : Core.pcFree := by
    dsimp [Core, k73IncreaseFirstDivCoreSource]
    pcf
    exact hG
  have hbranch := k73_increase_nonzero_exit_branch Core hCore
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      dsimp [Core, k73IncreaseFirstDivToAddSource,
        k73IncreaseDivPairFrame, k73IncreaseDivPairCoreFrame] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by exact hq)
    (fun s hq => by
      have hq' :
          k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s := by
        dsimp [Core, k73IncreaseFirstDivToAddSource,
          k73IncreaseDivPairFrame, k73IncreaseDivPairCoreFrame] at hq ⊢
        xperm_hyp hq
      exact k73_increase_first_div_to_add_pre_live
        spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s hq') hbranch
-/

private theorem k73_increase_first_div_to_add_pre_live
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) :
    ∀ s, k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s →
      k73IncreaseFirstDivToAddTarget spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G s := by
  intro s hs
  unfold k73IncreaseFirstDivToAddSource at hs
  let R : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
      ((.x2 : Reg) ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G
  have hsplit :
      (((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
        ((.x20 : Reg) ↦ᵣ (1 : Word)) ** R) s := by
    dsimp only [R] at hs ⊢
    unfold k73IncreaseDivPairFrame k73IncreaseDivPairCoreFrame at hs
    xperm_hyp hs
  have hown := k73_increase_reg_frame_rearrange
    target (gasUsed - target) R s hsplit
  dsimp [R] at hown
  have hscratch : u256DivU64BeScratch = u256AddBeBInPlaceScratch := by
    rfl
  rw [hscratch] at hown
  let T0 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes
  let T1 : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (U256MulU64Be.frameSlots (spH + signExtend12 (4048 : BitVec 12))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion U256MulU64Be.accBase accBytes ** G)
  have hgroup : ((regsOwnAt k73FrameRest3 ** T0) ** T1) s := by
    simp only [T0, T1, sepConj_assoc'] at hown ⊢
    exact hown
  have hswapPrefix : ∀ h,
      (regsOwnAt k73FrameRest3 ** T0) h →
        (T0 ** regsOwnAt k73FrameRest3) h := by
    intro h hp
    xperm_hyp hp
  have hswap := sepConj_mono_left hswapPrefix s hgroup
  let T2 : Assertion := ((.x2 : Reg) ↦ᵣ spH)
  let T3 : Assertion :=
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (U256MulU64Be.frameSlots (spH + signExtend12 (4048 : BitVec 12))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion U256MulU64Be.accBase accBytes ** G)
  have hgroup2 : (T0 ** ((regsOwnAt k73FrameRest3 ** T2) ** T3)) s := by
    simpa only [T0, T1, T2, T3, sepConj_assoc'] using hswap
  have hswapAtom : ∀ h,
      (regsOwnAt k73FrameRest3 ** T2) h →
        (T2 ** regsOwnAt k73FrameRest3) h := by
    intro h hp
    xperm_hyp hp
  have hswapInner : ∀ h,
      ((regsOwnAt k73FrameRest3 ** T2) ** T3) h →
        ((T2 ** regsOwnAt k73FrameRest3) ** T3) h := by
    intro h hp
    exact sepConj_mono_left hswapAtom h hp
  have hswap2 := sepConj_mono_right hswapInner s hgroup2
  unfold k73IncreaseFirstDivToAddTarget
  simp only [T0, T2, T3, sepConj_assoc'] at hswap2 ⊢
  exact hswap2

/-! `x0` and `x20` belong to the branch at `K73 + 176`; they are removed
    from this core before that branch is composed with the divider post. -/
@[irreducible] def k73IncreaseFirstDivCoreSource
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) : Assertion :=
  ((regIs .x1 (K73 + 140) ** regIs .x9 outPtr) **
    regIs .x10 (0 : Word) ** regIs .x11 (8 : Word) **
    regIs .x12 outPtr ** regOwns u256DivU64BeScratch **
    bytesRegion outPtr q2 ** regIs .x18 target **
    k73IncreaseDivPairCoreFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)

theorem k73_increase_first_div_source_branch
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree) (k : Nat) :
    cpsBranchWithin 1 (K73 + 176) wholeCode
      (k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G k)
      (K73 + 208) (fun _ => False)
      (K73 + 180)
        (k73IncreaseFirstAddPre spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G) := by
  let Core : Assertion :=
    ((regIs .x1 (K73 + 140) ** regIs .x9 outPtr) **
      regIs .x10 (0 : Word) ** regIs .x11 (8 : Word) **
      regIs .x12 outPtr ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** regIs .x18 target **
      k73IncreaseDivPairCoreFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes
        (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)
  have hCore : Core.pcFree := by
    unfold Core
    pcf
    exact hG
  have hbranch := k73_increase_nonzero_exit_branch Core hCore
  have hsource :
      k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G k =
        (regIs .x20 (1 : Word) ** regIs .x0 (0 : Word) ** Core) := by
    funext s
    apply propext
    constructor
    · intro hp
      unfold k73IncreaseFirstDivToAddSource at hp
      unfold k73IncreaseDivPairFrame at hp
      simp only [Core]
      xperm_hyp hp
    · intro hp
      unfold Core at hp
      unfold k73IncreaseFirstDivToAddSource
      unfold k73IncreaseDivPairFrame
      xperm_hyp hp
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      rw [hsource] at hp
      exact hp)
    (fun _ hq => False.elim hq)
    (fun s hq => by
      have hq' :
          k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s := by
        rw [hsource]
        exact hq
      have htarget := k73_increase_first_div_to_add_pre_live
        spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s hq'
      unfold k73IncreaseFirstDivToAddTarget at htarget
      unfold k73IncreaseFirstAddPre
      xperm_hyp htarget) hbranch

@[irreducible] def k73IncreaseSecondDivToAddSource
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion) (k : Nat) : Assertion :=
  (((.x1 : Reg) ↦ᵣ (K73 + 156)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    regOwns exposedRegs ** bytesRegion outPtr orig **
    ((.x18 : Reg) ↦ᵣ target) **
    k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
      baseBytes accBytes
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)

@[irreducible] def k73IncreaseSecondDivToAddTarget
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion) : Assertion :=
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
    ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
    regOwns exposedRegs ** bytesRegion outPtr orig **
    bytesRegion basePtr baseBytes ** ((.x2 : Reg) ↦ᵣ spH) **
    regsOwnAt k73FrameRest3 **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G))

private theorem k73_increase_second_div_to_add_pre_live
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion) (k : Nat) :
    ∀ s,
      k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G k s →
      k73IncreaseSecondDivToAddTarget spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G s := by
  intro s hs
  unfold k73IncreaseSecondDivToAddSource at hs
  let R : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      regOwns exposedRegs ** bytesRegion outPtr orig **
      bytesRegion basePtr baseBytes **
      ((.x2 : Reg) ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G
  have hsplit :
      (((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
        ((.x20 : Reg) ↦ᵣ (1 : Word)) ** R) s := by
    dsimp only [R] at hs ⊢
    unfold k73IncreaseDivPairFrame k73IncreaseDivPairCoreFrame at hs
    xperm_hyp hs
  have hown := k73_increase_reg_frame_rearrange
    target (gasUsed - target) R s hsplit
  dsimp [R] at hown
  let T0 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      regOwns exposedRegs ** bytesRegion outPtr orig **
      bytesRegion basePtr baseBytes
  let T1 : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (U256MulU64Be.frameSlots (spH + signExtend12 (4048 : BitVec 12))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion U256MulU64Be.accBase accBytes ** G)
  have hgroup : ((regsOwnAt k73FrameRest3 ** T0) ** T1) s := by
    simp only [T0, T1, sepConj_assoc'] at hown ⊢
    exact hown
  have hswapPrefix : ∀ h,
      (regsOwnAt k73FrameRest3 ** T0) h →
        (T0 ** regsOwnAt k73FrameRest3) h := by
    intro h hp
    xperm_hyp hp
  have hswap := sepConj_mono_left hswapPrefix s hgroup
  let T2 : Assertion := ((.x2 : Reg) ↦ᵣ spH)
  let T3 : Assertion :=
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (U256MulU64Be.frameSlots (spH + signExtend12 (4048 : BitVec 12))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion U256MulU64Be.accBase accBytes ** G)
  have hgroup2 : (T0 ** ((regsOwnAt k73FrameRest3 ** T2) ** T3)) s := by
    simpa only [T0, T1, T2, T3, sepConj_assoc'] using hswap
  have hswapAtom : ∀ h,
      (regsOwnAt k73FrameRest3 ** T2) h →
        (T2 ** regsOwnAt k73FrameRest3) h := by
    intro h hp
    xperm_hyp hp
  have hswapInner : ∀ h,
      ((regsOwnAt k73FrameRest3 ** T2) ** T3) h →
        ((T2 ** regsOwnAt k73FrameRest3) ** T3) h := by
    intro h hp
    exact sepConj_mono_left hswapAtom h hp
  have hswap2 := sepConj_mono_right hswapInner s hgroup2
  unfold k73IncreaseSecondDivToAddTarget
  simp only [T0, T2, T3, sepConj_assoc'] at hswap2 ⊢
  exact hswap2

theorem k73_increase_second_div_source_branch
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree) (k : Nat) :
    cpsBranchWithin 1 (K73 + 176) wholeCode
      (k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G k)
      (K73 + 208) (fun _ => False)
      (K73 + 180)
        (k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes orig G) := by
  let Core : Assertion :=
    ((regIs .x1 (K73 + 156) ** regIs .x9 outPtr) **
      regOwns exposedRegs ** bytesRegion outPtr orig ** regIs .x18 target **
      k73IncreaseDivPairCoreFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes
        (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k)
  have hCore : Core.pcFree := by
    unfold Core
    pcf
    exact hG
  have hbranch := k73_increase_nonzero_exit_branch Core hCore
  have hsource :
      k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes orig G k =
        (regIs .x20 (1 : Word) ** regIs .x0 (0 : Word) ** Core) := by
    funext s
    apply propext
    constructor
    · intro hp
      unfold k73IncreaseSecondDivToAddSource at hp
      unfold k73IncreaseDivPairFrame at hp
      simp only [Core]
      xperm_hyp hp
    · intro hp
      unfold Core at hp
      unfold k73IncreaseSecondDivToAddSource
      unfold k73IncreaseDivPairFrame
      xperm_hyp hp
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      rw [hsource] at hp
      exact hp)
    (fun _ hq => False.elim hq)
    (fun s hq => by
      have hq' :
          k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes orig G k s := by
        rw [hsource]
        exact hq
      have htarget := k73_increase_second_div_to_add_pre_live
        spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G k s hq'
      unfold k73IncreaseSecondDivToAddTarget at htarget
      unfold k73IncreaseSecondAddPre
      xperm_hyp htarget) hbranch

/- local divider-to-add conversions are kept at the final composition seam;
   elaborating them as standalone theorems unfolds the large post too early.
private theorem k73_increase_first_div_to_add_pre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) :
    ∀ s, k73IncreaseFirstDivPost spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes q2 G k s →
      k73IncreaseFirstAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G s := by
  intro s hs
  let vals : Reg → Word := fun r => match r with
    | .x18 => target
    | .x19 => gasUsed - target
    | .x20 => 1
    | _ => 0
  let R : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
      ((.x2 : Reg) ↦ᵣ spH) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G
  have hsplit :
      (((.x18 : Reg) ↦ᵣ target) ** ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
        ((.x20 : Reg) ↦ᵣ (1 : Word)) ** R) s := by
    unfold k73IncreaseFirstDivPost at hs
    dsimp [R, k73IncreaseDivPairFrame, k73IncreaseDivPairCoreFrame] at hs ⊢
    xperm_hyp hs
  have hreg := regsAt_implies_regsOwnAt k73FrameRest3 vals
  have hreg' : ((regsAt k73FrameRest3 vals) ** R) s := by
    simpa [regsAt, k73FrameRest3, vals, sepConj_emp_left',
      sepConj_emp_right', sepConj_assoc'] using hsplit
  have hown := sepConj_mono_left hreg s hreg'
  dsimp [k73IncreaseFirstAddPre, R] at hown ⊢
  simp [u256DivU64BeScratch, u256AddBeBInPlaceScratch,
    sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hown ⊢
  xperm_hyp hown

private theorem k73_increase_second_div_to_add_pre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) (k : Nat) :
    ∀ s,
      (((.x1 : Reg) ↦ᵣ (K73 + 156)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        regOwns exposedRegs **
        bytesRegion outPtr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) **
        ((.x18 : Reg) ↦ᵣ target) **
        k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
          baseBytes accBytes
          (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k) s →
      k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G s := by
  intro s hs
  let R : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      regOwns exposedRegs **
      bytesRegion outPtr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) **
      ((.x2 : Reg) ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase baseBytes ** G
  have hsplit :
      (((.x18 : Reg) ↦ᵣ target) **
        ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
        ((.x20 : Reg) ↦ᵣ (1 : Word)) ** R) s := by
    dsimp [R, k73IncreaseDivPairFrame, k73IncreaseDivPairCoreFrame] at hs ⊢
    xperm_hyp hs
  have hown := k73_increase_reg_frame_rearrange
    target (gasUsed - target) R s hsplit
  dsimp [k73IncreaseSecondAddPre, R] at hown ⊢
  simp [u256DivU64BeScratch, u256AddBeBInPlaceScratch,
    sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hown ⊢
  xperm_hyp hown
-/

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
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
      ((.x2 : Reg) ↦ᵣ spH) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
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
      (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
        bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
        k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
          baseBytes accBytes
          (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G) k) s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
        ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
          (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
          bytesRegion U256MulU64Be.accBase accBytes ** G)) s := by
-/
  intro s hs
  let vals : Reg → Word := fun r => match r with
    | .x18 => target
    | .x19 => gasUsed - target
    | .x20 => 1
    | _ => 0
  let R : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
      ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
      ((.x2 : Reg) ↦ᵣ spH) **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 92) basePtr outPtr target (gasUsed - target) (1 : Word) **
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
      (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
        bytesRegion outPtr q2 ** ((.x18 : Reg) ↦ᵣ target) **
        k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
          baseBytes accBytes
          (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G0) k) s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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

@[irreducible] def k73IncreaseCarryTail
    (spH gasUsed basePtr outPtr target : Word)
    (_v8 _v9 _v18 _v19 _v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
      (gasUsed - target) outPtr baseBytes **
    (fun s => ∃ k,
      (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion outPtr outBytes ** k73MulOverflowCoreNoStatus accBytes k) s) ** F

end EvmAsm.Codegen.HeaderBaseFeeSpec
