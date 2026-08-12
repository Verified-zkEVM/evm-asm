/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedOneHit

  One-record hit path for `witness_lookup_by_hash_indexed` (coverHit domain).

  Domain: widx_count = 1, arena holds one record whose hash equals target.
  Straight-line: BGEU ntaken → mid=0 → record_ptr(0) → cmp32 eq → hit stores → a0=0.

  **Depends on PR #12169.** NEW file only.
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedCallees
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve
import EvmAsm.Evm64.WitnessAssertions
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.U256MinSAsm

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Evm64
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty
open EvmAsm.Codegen.WitnessLookupByHashIndexedCallees
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256MinSAsm
open EvmAsm.Crypto
open EvmAsm.Codegen (laHi laLo)

private abbrev B : Word := (IndexedB : Word)
private abbrev Prog : List Instr := witnessLookupByHashIndexed_prog
private abbrev CR : CodeReq := fullCode

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < 50)
    (hins : Prog[k]'(by rw [indexed_prog_length]; exact hk) = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → CR a = some i := by
  intro a i h
  apply wrapper_in_fullCode
  exact CodeReq.ofProg_mem_at B A Prog k ins hA
    (by rw [indexed_prog_length]; exact hk) hins
    (by rw [indexed_prog_length]; decide) a i h

/-! ## Ambients with count = 1 -/

def hitMvAmb (spC : Word) (s : IndexedSaved)
    (v5 v10 v20 s5 s6 : Word) : Assertion :=
  ((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ v10) ** ((.x20 : Reg) ↦ᵣ v20) **
  ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (1 : Word))

private theorem hitMvAmb_pcFree (spC : Word) (s : IndexedSaved)
    (v5 v10 v20 s5 s6 : Word) :
    (hitMvAmb spC s v5 v10 v20 s5 s6).pcFree := by
  dsimp [hitMvAmb]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) pcFree_memIs)))))

def hitAfterLaAmb (spC : Word) (s : IndexedSaved)
    (v10 v20 s5 s6 : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ v10) ** ((.x20 : Reg) ↦ᵣ v20) **
  ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (1 : Word))

private theorem hitAfterLaAmb_pcFree (spC : Word) (s : IndexedSaved)
    (v10 v20 s5 s6 : Word) :
    (hitAfterLaAmb spC s v10 v20 s5 s6).pcFree := by
  dsimp [hitAfterLaAmb]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) pcFree_memIs))))

/-- LoopHdr ambient after ld hi=1 (same frame temps as empty). -/
def hitLoopHdrAmb (spC : Word) (s : IndexedSaved)
    (v10 s5 s6 : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s)

private theorem hitLoopHdrAmb_pcFree (spC : Word) (s : IndexedSaved)
    (v10 s5 s6 : Word) :
    (hitLoopHdrAmb spC s v10 s5 s6).pcFree := by
  dsimp [hitLoopHdrAmb]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_frameSlotsSaved _ _ _)))

/-! ## Setup bodyEntry → loopHdr (count=1) -/

/-- bodyEntry → B+52: MVs + LI (count cell preserved as 1 in amb). Fuel 4. -/
theorem hit_mvs_li
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v8 v9 v18 v19 v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 4 bodyEntryPc (B + 52) CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitMvAmb spC s v5 v10 v20 s5 s6))
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitMvAmb spC s v5 v10 v20 s5 s6)) := by
  have hspEq : sp0 - 64 = spC := by
    rw [hspC]
    rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide]
    bv_omega
  have hm0 := empty_mv_s0 hashPtr v8 raMid sp0
  have hm1 := empty_mv_s1 outOff v9 hashPtr raMid sp0
  have hm2 := empty_mv_s2 outLen v18 hashPtr outOff raMid sp0
  have hli := empty_li_lo v19 hashPtr outOff outLen raMid sp0
  have hm0' : cpsTripleWithin 1 bodyEntryPc (bodyEntryPc + 4) CR
      (((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC))
      (((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) := by
    convert hm0 using 1 <;> try rw [hspEq]
  have hm1' : cpsTripleWithin 1 (B + 40) (B + 44) CR
      (((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x1 : Reg) ↦ᵣ raMid) **
       ((.x2 : Reg) ↦ᵣ spC))
      (((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x1 : Reg) ↦ᵣ raMid) **
       ((.x2 : Reg) ↦ᵣ spC)) := by
    convert hm1 using 1 <;> try rw [hspEq]
  have hm2' : cpsTripleWithin 1 (B + 44) (B + 48) CR
      (((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC))
      (((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) := by
    convert hm2 using 1 <;> try rw [hspEq]
  have hli' : cpsTripleWithin 1 (B + 48) (B + 52) CR
      (((.x19 : Reg) ↦ᵣ v19) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x1 : Reg) ↦ᵣ raMid) **
       ((.x2 : Reg) ↦ᵣ spC))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x1 : Reg) ↦ᵣ raMid) **
       ((.x2 : Reg) ↦ᵣ spC)) := by
    convert hli using 1 <;> try rw [hspEq]
  let F0 : Assertion :=
    ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
    ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
    ((.x19 : Reg) ↦ᵣ v19) ** hitMvAmb spC s v5 v10 v20 s5 s6
  have hF0 : F0.pcFree := by
    dsimp [F0]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (hitMvAmb_pcFree _ _ _ _ _ _ _)))))
  have c0 := cpsTripleWithin_frameR F0 hF0 hm0'
  let F1 : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) **
    ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
    ((.x19 : Reg) ↦ᵣ v19) ** hitMvAmb spC s v5 v10 v20 s5 s6
  have hF1 : F1.pcFree := by
    dsimp [F1]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (hitMvAmb_pcFree _ _ _ _ _ _ _))))
  have c1 := cpsTripleWithin_frameR F1 hF1 hm1'
  have s01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [F0, F1] at hp ⊢; xperm_chunked hp) c0 c1
  let F2 : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x19 : Reg) ↦ᵣ v19) ** hitMvAmb spC s v5 v10 v20 s5 s6
  have hF2 : F2.pcFree := by
    dsimp [F2]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (hitMvAmb_pcFree _ _ _ _ _ _ _)))
  have c2 := cpsTripleWithin_frameR F2 hF2 hm2'
  have s012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [F1, F2] at hp ⊢; xperm_chunked hp) s01 c2
  let F3 : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) ** hitMvAmb spC s v5 v10 v20 s5 s6
  have hF3 : F3.pcFree := by
    dsimp [F3]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (hitMvAmb_pcFree _ _ _ _ _ _ _)))
  have c3 := cpsTripleWithin_frameR F3 hF3 hli'
  have s0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [F2, F3] at hp ⊢; xperm_chunked hp) s012 c3
  have hn : 1 + 1 + 1 + 1 = 4 := rfl
  rw [hn] at s0123
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F0, hitMvAmb] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by dsimp [F3, hitMvAmb] at hq ⊢; xperm_chunked hq) s0123

/-- B+52 → B+60: la t0,widx_count. Fuel 2. -/
theorem hit_la_at
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 2 (B + 52) (B + 60) CR
      (((( (.x5 : Reg) ↦ᵣ v5) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitAfterLaAmb spC s v10 v20 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitAfterLaAmb spC s v10 v20 s5 s6)) := by
  have hspEq : sp0 - 64 = spC := by
    rw [hspC]
    rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide]
    bv_omega
  have h0 := empty_la_count v5 hashPtr outOff outLen raMid sp0
  have h : cpsTripleWithin 2 (B + 52) (B + 60) CR
      (((.x5 : Reg) ↦ᵣ v5) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC))
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) := by
    convert h0 using 1 <;> try rw [hspEq]
  let F : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) ** hitAfterLaAmb spC s v10 v20 s5 s6
  have hF : F.pcFree := by
    dsimp [F]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (hitAfterLaAmb_pcFree _ _ _ _ _ _)))
  have hf := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F, hitAfterLaAmb] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by dsimp [F, hitAfterLaAmb] at hq ⊢; xperm_chunked hq) hf

/-- LD s4,*widx_count (=1) @ B+60. -/
theorem hit_ld_count
    (v20 hashPtr outOff outLen ret sp0 : Word) :
    cpsTripleWithin 1 (B + 60) (B + 64) CR
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
       (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have hld := ld_spec_gen_within .x20 .x5 WidxCountLoc v20 (1 : Word)
    (0 : BitVec 12) (B + 60) (by decide)
  rw [signExtend12_0,
      show (WidxCountLoc + 0 : Word) = WidxCountLoc from by bv_omega,
      show (B + 60 : Word) + 4 = B + 64 from by unfold B IndexedB; decide] at hld
  have l := cpsTripleWithin_extend_code
    (mem_at 15 (.LD .x20 .x5 (0 : BitVec 12)) (B + 60)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hld
  have hF :
      (((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs pcFree_regIs))))
  have lf := cpsTripleWithin_frameR _ hF l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

theorem hit_ld_at
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 1 (B + 60) loopHdrPc CR
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
         (WidxCountLoc ↦ₘ (1 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitLoopHdrAmb spC s v10 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
         (WidxCountLoc ↦ₘ (1 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitLoopHdrAmb spC s v10 s5 s6)) := by
  have hspEq : sp0 - 64 = spC := by
    rw [hspC]
    rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide]
    bv_omega
  have h0 := hit_ld_count v20 hashPtr outOff outLen raMid sp0
  have h : cpsTripleWithin 1 (B + 60) (B + 64) CR
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
       (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC))
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) := by
    convert h0 using 1 <;> try rw [hspEq]
  let F : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) ** hitLoopHdrAmb spC s v10 s5 s6
  have hF : F.pcFree := by
    dsimp [F]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (hitLoopHdrAmb_pcFree _ _ _ _ _)))
  have hf := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F, hitLoopHdrAmb] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by dsimp [F, hitLoopHdrAmb] at hq ⊢; xperm_chunked hq) hf

theorem hit_la_ld
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 3 (B + 52) loopHdrPc CR
      (((( (.x5 : Reg) ↦ᵣ v5) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
         hitLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (1 : Word))))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
         (WidxCountLoc ↦ₘ (1 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitLoopHdrAmb spC s v10 s5 s6)) := by
  have hla := hit_la_at sp0 spC s hashPtr outOff outLen raMid v5 v10 v20 s5 s6 hspC
  have hld := hit_ld_at sp0 spC s hashPtr outOff outLen raMid v10 v20 s5 s6 hspC
  have hla' : cpsTripleWithin 2 (B + 52) (B + 60) CR
      (((( (.x5 : Reg) ↦ᵣ v5) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
         hitLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (1 : Word))))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
         hitLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (1 : Word)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [hitAfterLaAmb, hitLoopHdrAmb] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        dsimp [hitAfterLaAmb, hitLoopHdrAmb] at hq ⊢; xperm_chunked hq) hla
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [hitLoopHdrAmb] at hp ⊢; xperm_chunked hp) hla' hld
  have hn : 2 + 1 = 3 := rfl
  rw [hn] at c
  exact c

/-- bodyEntry → loopHdr with count=1. Fuel 7. -/
theorem hit_bodyEntry_to_loopHdr
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v8 v9 v18 v19 v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 7 bodyEntryPc loopHdrPc CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitMvAmb spC s v5 v10 v20 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
         (WidxCountLoc ↦ₘ (1 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitLoopHdrAmb spC s v10 s5 s6)) := by
  have hmvs := hit_mvs_li sp0 spC s hashPtr outOff outLen raMid
    v8 v9 v18 v19 v5 v10 v20 s5 s6 hspC
  have hla := hit_la_ld sp0 spC s hashPtr outOff outLen raMid
    v5 v10 v20 s5 s6 hspC
  have hmvs' : cpsTripleWithin 4 bodyEntryPc (B + 52) CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitMvAmb spC s v5 v10 v20 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ v5) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
         hitLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (1 : Word)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by
        dsimp [hitMvAmb, hitLoopHdrAmb] at hq ⊢; xperm_chunked hq) hmvs
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [hitLoopHdrAmb] at hp ⊢; xperm_chunked hp) hmvs' hla
  have hn : 4 + 3 = 7 := rfl
  rw [hn] at c
  exact c

/-! ## BGEU ntaken (lo=0, hi=1) + mid = 0 -/

private def bgeuMissOff : BitVec 13 :=
  brOff (GuestAddrs.witness_lookup_by_hash_indexed + 156)
    (GuestAddrs.witness_lookup_by_hash_indexed + 64)

private theorem bgeu_miss_target :
    (B + 64 : Word) + signExtend13 bgeuMissOff = B + 156 := by
  unfold B IndexedB bgeuMissOff
  decide

/-- BGEU lo,hi ntaken when lo=0, hi=1 → fall through B+68. Fuel 1. -/
theorem hit_bgeu_ntaken
    (hashPtr outOff outLen ret sp0 : Word) (v5 : Word) :
    cpsTripleWithin 1 (B + 64) (B + 68) CR
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x5 : Reg) ↦ᵣ v5) ** (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x5 : Reg) ↦ᵣ v5) ** (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have hb := bgeu_spec_gen_within .x19 .x20 bgeuMissOff
    (0 : Word) (1 : Word) (B + 64)
  rw [bgeu_miss_target,
      show (B + 64 : Word) + 4 = B + 68 from by unfold B IndexedB; decide] at hb
  have hbe := cpsBranchWithin_extend_code
    (mem_at 16 (.BGEU .x19 .x20 bgeuMissOff) (B + 64)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hb
  -- ntaken: taken pure is ⌜¬ult 0 1⌝ = false
  have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hF :
      (((.x5 : Reg) ↦ᵣ v5) ** (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs pcFree_regIs)))))
  have lf := cpsTripleWithin_frameR _ hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-- ADD s5,s3,s4 @ B+68. -/
theorem hit_mid_add (v21 : Word) :
    cpsTripleWithin 1 (B + 68) (B + 72) CR
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x21 : Reg) ↦ᵣ v21))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x21 : Reg) ↦ᵣ ((0 : Word) + (1 : Word)))) := by
  have h := add_spec_gen_within .x21 .x19 .x20 (0 : Word) (1 : Word) v21
    (B + 68) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 17 (.ADD .x21 .x19 .x20) (B + 68)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 68 : Word) + 4 = B + 72 from by unfold B IndexedB; decide] at l
  exact l

/-- SRLI s5,s5,1 @ B+72: (0+1)>>1 = 0. -/
theorem hit_mid_srli :
    cpsTripleWithin 1 (B + 72) (B + 76) CR
      (((.x21 : Reg) ↦ᵣ ((0 : Word) + (1 : Word))))
      (((.x21 : Reg) ↦ᵣ (0 : Word))) := by
  have h := srli_spec_gen_same_within .x21 ((0 : Word) + (1 : Word))
    (1 : BitVec 6) (B + 72) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 18 (.SRLI .x21 .x21 (1 : BitVec 6)) (B + 72)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 72 : Word) + 4 = B + 76 from by unfold B IndexedB; decide] at l
  have hshift :
      (((0 : Word) + (1 : Word)) >>> (1 : BitVec 6).toNat) = (0 : Word) := by
    decide
  simpa [hshift] using l

/-- mid = (0+1)>>1 = 0. Fuel 2. -/
theorem hit_mid_zero (v21 : Word) :
    cpsTripleWithin 2 (B + 68) (B + 76) CR
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x21 : Reg) ↦ᵣ v21))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x21 : Reg) ↦ᵣ (0 : Word))) := by
  have ha := hit_mid_add v21
  have hs := hit_mid_srli
  have hs' : cpsTripleWithin 1 (B + 72) (B + 76) CR
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x21 : Reg) ↦ᵣ ((0 : Word) + (1 : Word))))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x21 : Reg) ↦ᵣ (0 : Word))) := by
    have hF :
        (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word))).pcFree :=
      pcFree_sepConj pcFree_regIs pcFree_regIs
    have hf := cpsTripleWithin_frameR _ hF hs
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hf
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) ha hs'
  have hn : 1 + 1 = 2 := rfl
  rw [hn] at c
  exact c

/-! ## MV a0,s5 @ B+76 then JAL widx_record_ptr @ B+80 -/

private def recordPtrJalOff : BitVec 21 :=
  jalOff GuestAddrs.widx_record_ptr
    (GuestAddrs.witness_lookup_by_hash_indexed + 80)

private theorem record_ptr_jal_target :
    (B + 80 : Word) + signExtend21 recordPtrJalOff = (RecordPtrB : Word) := by
  unfold B IndexedB recordPtrJalOff RecordPtrB
  change BitVec.ofNat 64 _ + signExtend21 (jalOff _ _) = BitVec.ofNat 64 _
  exact jalOff_correct_add GuestAddrs.widx_record_ptr
    GuestAddrs.witness_lookup_by_hash_indexed 80
    (by decide) (by decide) (by decide) (by decide)

private theorem record_ptr_ret_even :
    ((B + 80 : Word) + 4) &&& ~~~(1 : Word) = (B + 80 : Word) + 4 := by
  unfold B IndexedB; decide

/-- MV a0, s5 @ B+76 with mid=0. -/
theorem hit_mv_a0_mid (v10 : Word) :
    cpsTripleWithin 1 (B + 76) (B + 80) CR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x21 : Reg) ↦ᵣ (0 : Word))) := by
  have h := mv_spec_gen_within .x10 .x21 (0 : Word) v10 (B + 76) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 19 (.MV .x10 .x21) (B + 76)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 76 : Word) + 4 = B + 80 from by unfold B IndexedB; decide] at l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) l

/-- Non-exposed ambient through record_ptr (callee owns only exposed + ra). -/
def hitRecordPtrF (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
  ((.x18 : Reg) ↦ᵣ outLen) **
  ((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
  ((.x21 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spC) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (1 : Word))

private theorem hitRecordPtrF_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    (hitRecordPtrF spC s hashPtr outOff outLen).pcFree := by
  dsimp [hitRecordPtrF]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) pcFree_memIs)))))))

/-- callWithin `widx_record_ptr` at B+80, a0=0. Fuel 8.
    Post uses opaque `widxRecordPtrZeroPostAtoms` (a0 = WidxRecordsBase via Callees). -/
theorem hit_record_ptr_call
    (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raOld : Word) :
    cpsTripleWithin 8 (B + 80) (B + 84) CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       widxRecordPtrZeroPreAtoms **
       hitRecordPtrF spC s hashPtr outOff outLen)
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
       widxRecordPtrZeroPostAtoms **
       hitRecordPtrF spC s hashPtr outOff outLen) := by
  have hmem : ∀ a i,
      CodeReq.singleton (B + 80) (.JAL .x1 recordPtrJalOff) a = some i →
        CR a = some i :=
    mem_at 20 (.JAL .x1 recordPtrJalOff) (B + 80)
      (by unfold B IndexedB; decide) (by decide) (by rfl)
  have h := widx_record_ptr_zero_callWithin (B + 80) raOld recordPtrJalOff
    (hitRecordPtrF spC s hashPtr outOff outLen)
    (hitRecordPtrF_pcFree spC s hashPtr outOff outLen)
    record_ptr_jal_target hmem record_ptr_ret_even
  have hpc : (B + 80 : Word) + 4 = B + 84 := by unfold B IndexedB; decide
  simpa [hpc] using h

/-- MV s6, a0 @ B+84 — needs a0 already concrete (from post regAtoms peel later). -/
theorem hit_mv_s6_a0 (v22 : Word) :
    cpsTripleWithin 1 (B + 84) (B + 88) CR
      (((.x22 : Reg) ↦ᵣ v22) ** ((.x10 : Reg) ↦ᵣ WidxRecordsBase))
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x10 : Reg) ↦ᵣ WidxRecordsBase)) := by
  have h := mv_spec_gen_within .x22 .x10 WidxRecordsBase v22 (B + 84) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 21 (.MV .x22 .x10) (B + 84)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 84 : Word) + 4 = B + 88 from by unfold B IndexedB; decide] at l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) l

/-- MV a0, s6 @ B+88. -/
theorem hit_mv_a0_s6 (v10 : Word) :
    cpsTripleWithin 1 (B + 88) (B + 92) CR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x22 : Reg) ↦ᵣ WidxRecordsBase))
      (((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x22 : Reg) ↦ᵣ WidxRecordsBase)) := by
  have h := mv_spec_gen_within .x10 .x22 WidxRecordsBase v10 (B + 88) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 22 (.MV .x10 .x22) (B + 88)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 88 : Word) + 4 = B + 92 from by unfold B IndexedB; decide] at l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) l

/-- MV a1, s0 @ B+92. -/
theorem hit_mv_a1_s0 (v11 hashPtr : Word) :
    cpsTripleWithin 1 (B + 92) (B + 96) CR
      (((.x11 : Reg) ↦ᵣ v11) ** ((.x8 : Reg) ↦ᵣ hashPtr))
      (((.x11 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr)) := by
  have h := mv_spec_gen_within .x11 .x8 hashPtr v11 (B + 92) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 23 (.MV .x11 .x8) (B + 92)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 92 : Word) + 4 = B + 96 from by unfold B IndexedB; decide] at l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) l

/-! ## Simple peel + cmp32 equal path -/

/-- coverHit hash bytes (32 × 0x01). -/
def coverHitHash : List (BitVec 8) := List.replicate 32 (1 : BitVec 8)

theorem coverHitHash_length : coverHitHash.length = 32 := by decide

theorem coverHitHash_eq_record :
    coverHitHash = coverHitRecord.hash := rfl

/-- callWithin record_ptr with simplified post (a0 concrete). -/
theorem hit_record_ptr_call_simple
    (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raOld : Word) :
    cpsTripleWithin 8 (B + 80) (B + 84) CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       widxRecordPtrZeroPreAtoms **
       hitRecordPtrF spC s hashPtr outOff outLen)
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
       widxRecordPtrZeroPostSimple **
       hitRecordPtrF spC s hashPtr outOff outLen) := by
  have hmem : ∀ a i,
      CodeReq.singleton (B + 80) (.JAL .x1 recordPtrJalOff) a = some i →
        CR a = some i :=
    mem_at 20 (.JAL .x1 recordPtrJalOff) (B + 80)
      (by unfold B IndexedB; decide) (by decide) (by rfl)
  have h := widx_record_ptr_zero_callWithin_simple (B + 80) raOld recordPtrJalOff
    (hitRecordPtrF spC s hashPtr outOff outLen)
    (hitRecordPtrF_pcFree spC s hashPtr outOff outLen)
    record_ptr_jal_target hmem record_ptr_ret_even
  have hpc : (B + 80 : Word) + 4 = B + 84 := by unfold B IndexedB; decide
  simpa [hpc] using h

/-- Ambient after record_ptr simple: non-exposed + a0=Base + owns exposed\{x10}. -/
def hitAfterRecordSimple (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (B + 84)) **
  ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
  regOwns exposedWithoutX10 **
  hitRecordPtrF spC s hashPtr outOff outLen

private theorem hitAfterRecordSimple_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    (hitAfterRecordSimple spC s hashPtr outOff outLen).pcFree := by
  dsimp [hitAfterRecordSimple]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regOwns _)
        (hitRecordPtrF_pcFree spC s hashPtr outOff outLen)))

/-! ## ABI MVs after record_ptr (split steps) -/

/-- Frame through MV s6,a0 (everything except x10/x22). -/
def hitMvS6F (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (B + 84)) **
  regOwns exposedWithoutX10 **
  hitRecordPtrF spC s hashPtr outOff outLen

theorem hitMvS6F_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    (hitMvS6F spC s hashPtr outOff outLen).pcFree := by
  dsimp [hitMvS6F]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj (pcFree_regOwns _)
      (hitRecordPtrF_pcFree spC s hashPtr outOff outLen))

/-- After record_ptr: MV s6,a0. x22 free ambient. -/
theorem hit_mv_s6_framed (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen v22 : Word) :
    cpsTripleWithin 1 (B + 84) (B + 88) CR
      (hitAfterRecordSimple spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22))
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
       ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
       regOwns exposedWithoutX10 **
       hitRecordPtrF spC s hashPtr outOff outLen) := by
  have hcore := hit_mv_s6_a0 v22
  have hf := cpsTripleWithin_frameR
    (hitMvS6F spC s hashPtr outOff outLen)
    (hitMvS6F_pcFree spC s hashPtr outOff outLen) hcore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [hitAfterRecordSimple, hitMvS6F] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      dsimp [hitMvS6F] at hq ⊢
      xperm_chunked hq) hf

/-- Frame through MV a0,s6 (except x10/x22). -/
def hitMvA0F (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (B + 84)) **
  regOwns exposedWithoutX10 **
  hitRecordPtrF spC s hashPtr outOff outLen

theorem hitMvA0F_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    (hitMvA0F spC s hashPtr outOff outLen).pcFree :=
  hitMvS6F_pcFree spC s hashPtr outOff outLen

/-- MV a0,s6 (both Base). Focus is x10+x22 — frame omits both. -/
theorem hit_mv_a0_s6_framed (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    cpsTripleWithin 1 (B + 88) (B + 92) CR
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
       ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
       regOwns exposedWithoutX10 **
       hitRecordPtrF spC s hashPtr outOff outLen)
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
       ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
       regOwns exposedWithoutX10 **
       hitRecordPtrF spC s hashPtr outOff outLen) := by
  have hcore := hit_mv_a0_s6 WidxRecordsBase
  -- Core focus = x10 ** x22; frame omits both
  have hF :
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
        regOwns exposedWithoutX10 **
        hitRecordPtrF spC s hashPtr outOff outLen).pcFree :=
    hitMvS6F_pcFree spC s hashPtr outOff outLen
  have hf := cpsTripleWithin_frameR _ hF hcore
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hf

/-- exposedWithoutX10 owns rearranged with x11 trailing. -/
private theorem exposedWithoutX10_split_x11 :
    ∀ h, regOwns exposedWithoutX10 h →
      (regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
                .x12, .x13, .x14, .x15, .x16, .x17] **
       regOwn (Reg.x11)) h := by
  intro h hp
  dsimp [exposedWithoutX10, regOwns] at hp ⊢
  xperm_chunked hp

/-- Post-shape after ABI MVs (cmp32 entry regs). -/
def hitAfterCmpAbi (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (B + 84)) **
  ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
  ((.x11 : Reg) ↦ᵣ hashPtr) **
  ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
  ((.x8 : Reg) ↦ᵣ hashPtr) **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
           .x12, .x13, .x14, .x15, .x16, .x17] **
  ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
  ((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
  ((.x21 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spC) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (1 : Word))

theorem hitAfterCmpAbi_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    (hitAfterCmpAbi spC s hashPtr outOff outLen).pcFree := by
  unfold hitAfterCmpAbi
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_regOwns _)
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj pcFree_regIs
                      (pcFree_sepConj pcFree_regIs
                        (pcFree_sepConj pcFree_regIs
                          (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _)
                            pcFree_memIs))))))))))))

/-! ## a1 MV via named ambients (avoid paren hell) -/

/-- Rest of ambient without x11 (for of_forall trailing own). -/
def hitA1Rest (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (B + 84)) **
  ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
  ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
           .x12, .x13, .x14, .x15, .x16, .x17] **
  ((.x8 : Reg) ↦ᵣ hashPtr) **
  ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
  ((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
  ((.x21 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spC) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (1 : Word))

theorem hitA1Rest_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    (hitA1Rest spC s hashPtr outOff outLen).pcFree := by
  unfold hitA1Rest
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj pcFree_regIs
                      (pcFree_sepConj pcFree_regIs
                        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _)
                          pcFree_memIs)))))))))))

/-- Frame for MV a1 (everything except x11 and x8). -/
def hitA1Frame (spC : Word) (s : IndexedSaved)
    (outOff outLen : Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (B + 84)) **
  ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
  ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
           .x12, .x13, .x14, .x15, .x16, .x17] **
  ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
  ((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
  ((.x21 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spC) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (1 : Word))

theorem hitA1Frame_pcFree (spC : Word) (s : IndexedSaved)
    (outOff outLen : Word) :
    (hitA1Frame spC s outOff outLen).pcFree := by
  unfold hitA1Frame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj pcFree_regIs
                      (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _)
                        pcFree_memIs))))))))))

/-- Reshape: after-record → hitA1Rest ** own x11. -/
private theorem hit_pre_a1_reshape (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    ∀ h,
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
       ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
       regOwns exposedWithoutX10 **
       hitRecordPtrF spC s hashPtr outOff outLen) h →
      (hitA1Rest spC s hashPtr outOff outLen ** regOwn (Reg.x11)) h := by
  intro h hp
  -- Split owns first (while still folded as regOwns exposedWithoutX10)
  have hp1 := sepConj_mono_right
    (fun h hq =>
      sepConj_mono_right
        (fun h hq =>
          sepConj_mono_right
            (fun h hq => sepConj_mono_left exposedWithoutX10_split_x11 h hq)
            h hq)
        h hq)
    h hp
  -- Now unfold targets and permute own x11 to trailing
  dsimp [hitA1Rest, hitRecordPtrF] at hp1 ⊢
  xperm_chunked hp1

/-- MV a1,s0 after peeling x11 from owns. -/
theorem hit_mv_a1_framed (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    cpsTripleWithin 1 (B + 92) (B + 96) CR
      (((.x1 : Reg) ↦ᵣ (B + 84)) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) **
       ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
       regOwns exposedWithoutX10 **
       hitRecordPtrF spC s hashPtr outOff outLen)
      (hitAfterCmpAbi spC s hashPtr outOff outLen) := by
  have hP : ∀ v11 : Word,
      cpsTripleWithin 1 (B + 92) (B + 96) CR
        (hitA1Rest spC s hashPtr outOff outLen ** ((.x11 : Reg) ↦ᵣ v11))
        (hitAfterCmpAbi spC s hashPtr outOff outLen) := by
    intro v11
    have h := hit_mv_a1_s0 v11 hashPtr
    have hf := cpsTripleWithin_frameR
      (hitA1Frame spC s outOff outLen)
      (hitA1Frame_pcFree spC s outOff outLen) h
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [hitA1Rest, hitA1Frame] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp [hitAfterCmpAbi, hitA1Frame] at hq ⊢
        xperm_chunked hq) hf
  have hforall := cpsTripleWithin_of_forall_regIs_to_regOwn (r := Reg.x11) hP
  exact cpsTripleWithin_weaken
    (hit_pre_a1_reshape spC s hashPtr outOff outLen)
    (fun _ hq => hq)
    hforall

/-- Compose three ABI MVs: fuel 3. -/
theorem hit_cmp_abi_mvs (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen v22 : Word) :
    cpsTripleWithin 3 (B + 84) (B + 96) CR
      (hitAfterRecordSimple spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22))
      (hitAfterCmpAbi spC s hashPtr outOff outLen) := by
  have h1 := hit_mv_s6_framed spC s hashPtr outOff outLen v22
  have h2 := hit_mv_a0_s6_framed spC s hashPtr outOff outLen
  have h3 := hit_mv_a1_framed spC s hashPtr outOff outLen
  have c12 := cpsTripleWithin_seq_same_cr h1 h2
  exact cpsTripleWithin_seq_same_cr c12 h3

private def cmp32JalOff : BitVec 21 :=
  jalOff GuestAddrs.widx_cmp32
    (GuestAddrs.witness_lookup_by_hash_indexed + 96)

private theorem cmp32_jal_target :
    (B + 96 : Word) + signExtend21 cmp32JalOff = (Cmp32B : Word) := by
  unfold B IndexedB cmp32JalOff Cmp32B
  change BitVec.ofNat 64 _ + signExtend21 (jalOff _ _) = BitVec.ofNat 64 _
  exact jalOff_correct_add GuestAddrs.widx_cmp32
    GuestAddrs.witness_lookup_by_hash_indexed 96
    (by decide) (by decide) (by decide) (by decide)

private theorem cmp32_ret_even :
    ((B + 96 : Word) + 4) &&& ~~~(1 : Word) = (B + 96 : Word) + 4 := by
  unfold B IndexedB; decide

theorem widx_records_base_aligned :
    WidxRecordsBase.toNat % 8 = 0 := by
  unfold WidxRecordsBase; decide

theorem widx_records_base_fit :
    WidxRecordsBase.toNat + 32 < 2 ^ 64 := by
  unfold WidxRecordsBase; decide

/-- Frame for cmp32 outside EqPre focus. -/
def hitCmp32F (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
  ((.x8 : Reg) ↦ᵣ hashPtr) **
  regOwns [.x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17] **
  ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
  ((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
  ((.x21 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spC) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (1 : Word))

theorem hitCmp32F_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) :
    (hitCmp32F spC s hashPtr outOff outLen).pcFree := by
  unfold hitCmp32F
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regOwns _)
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _)
                      pcFree_memIs)))))))))

/-- cmp32 equal at B+96. -/
theorem hit_cmp32_eq_call
    (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raOld : Word)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 294 (B + 96) (B + 100) CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       widxCmp32EqPre WidxRecordsBase hashPtr coverHitHash **
       hitCmp32F spC s hashPtr outOff outLen)
      (((.x1 : Reg) ↦ᵣ (B + 100)) **
       widxCmp32EqPost WidxRecordsBase hashPtr coverHitHash **
       hitCmp32F spC s hashPtr outOff outLen) := by
  have hmem : ∀ a i,
      CodeReq.singleton (B + 96) (.JAL .x1 cmp32JalOff) a = some i →
        CR a = some i :=
    mem_at 24 (.JAL .x1 cmp32JalOff) (B + 96)
      (by unfold B IndexedB; decide) (by decide) (by rfl)
  have h := widx_cmp32_eq_callWithin (B + 96) raOld WidxRecordsBase hashPtr
    coverHitHash cmp32JalOff
    (hitCmp32F spC s hashPtr outOff outLen)
    (hitCmp32F_pcFree spC s hashPtr outOff outLen)
    coverHitHash_length
    widx_records_base_aligned halignH
    widx_records_base_fit hovH
    hvalidR hvalidH
    cmp32_jal_target hmem cmp32_ret_even
  have hpc : (B + 96 : Word) + 4 = B + 100 := by unfold B IndexedB; decide
  simpa [hpc] using h

/-! ## After cmp32 eq: LI 1, BEQ hit, stores, LI 0, JAL epi -/

private theorem beq_hit_off :
    (B + 104 : Word) + signExtend13 (28 : BitVec 13) = B + 132 := by
  unfold B IndexedB; decide

/-- LI x5,1 @ B+100. -/
theorem hit_li1 (v5 : Word) :
    cpsTripleWithin 1 (B + 100) (B + 104) CR
      ((.x5 : Reg) ↦ᵣ v5)
      ((.x5 : Reg) ↦ᵣ (1 : Word)) := by
  have h := li_spec_gen_within .x5 v5 (1 : Word) (B + 100) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 25 (.LI .x5 (1 : Word)) (B + 100)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 100 : Word) + 4 = B + 104 from by unfold B IndexedB; decide] at l
  exact l

/-- BEQ a0,x5 taken when a0=1 (equal hash) → hitPc B+132.
    Focuses x10+x5 only. -/
theorem hit_beq_taken :
    cpsTripleWithin 1 (B + 104) (B + 132) CR
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x5 : Reg) ↦ᵣ (1 : Word)))
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x5 : Reg) ↦ᵣ (1 : Word))) := by
  have hb := beq_spec_gen_within .x10 .x5 (28 : BitVec 13)
    (1 : Word) (1 : Word) (B + 104)
  rw [beq_hit_off,
      show (B + 104 : Word) + 4 = B + 108 from by unfold B IndexedB; decide] at hb
  have hbe := cpsBranchWithin_extend_code
    (mem_at 26 (.BEQ .x10 .x5 (28 : BitVec 13)) (B + 104)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hb
  -- fallthrough pure is ⌜1 ≠ 1⌝ false
  have htk := cpsBranchWithin_takenStripPure2 hbe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) htk

/-- LI 1 + BEQ hit: fuel 2, B+100 → hitPc B+132. -/
theorem hit_li1_beq (v5 : Word) :
    cpsTripleWithin 2 (B + 100) (B + 132) CR
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ (1 : Word)))
      (((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))) := by
  have hli := hit_li1 v5
  have hliF := cpsTripleWithin_frameR
    ((.x10 : Reg) ↦ᵣ (1 : Word)) pcFree_regIs hli
  -- hliF post is (x5**x10); reorder beq to match
  have hbeq' : cpsTripleWithin 1 (B + 104) (B + 132) CR
      (((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)))
      (((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hit_beq_taken
  have c := cpsTripleWithin_seq_same_cr hliF hbeq'
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) c

/-! ## Hit stores @ B+132: LD/SD off+len, LI a0=0, JAL epi

coverHitRecord: offset=0 @ base+32, len=32 @ base+40 (LE u64 dwords).
x22 = WidxRecordsBase; x9 = outOff ptr; x18 = outLen ptr. -/

private abbrev hitOffAddr : Word := WidxRecordsBase + (32 : Word)
private abbrev hitLenAddr : Word := WidxRecordsBase + (40 : Word)
private abbrev hitOffW : Word := (0 : Word)
private abbrev hitLenW : Word := (32 : Word)

private theorem hit_off_addr_eq :
    WidxRecordsBase + signExtend12 (32 : BitVec 12) = hitOffAddr := by
  unfold hitOffAddr
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]

private theorem hit_len_addr_eq :
    WidxRecordsBase + signExtend12 (40 : BitVec 12) = hitLenAddr := by
  unfold hitLenAddr
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]

private theorem hit_out_addr0 (p : Word) :
    p + signExtend12 (0 : BitVec 12) = p := by
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  bv_omega

/-- LD x5, 32(x22) @ B+132 — load coverHit offset (=0). -/
theorem hit_ld_off (v5 : Word) :
    cpsTripleWithin 1 (B + 132) (B + 136) CR
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ v5) **
       (hitOffAddr ↦ₘ hitOffW))
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ hitOffW) **
       (hitOffAddr ↦ₘ hitOffW)) := by
  have hld := ld_spec_gen_within .x5 .x22 WidxRecordsBase v5 hitOffW
    (32 : BitVec 12) (B + 132) (by decide)
  rw [hit_off_addr_eq,
      show (B + 132 : Word) + 4 = B + 136 from by unfold B IndexedB; decide] at hld
  have l := cpsTripleWithin_extend_code
    (mem_at 33 (.LD .x5 .x22 (32 : BitVec 12)) (B + 132)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hld
  exact l

/-- SD x9, x5, 0 @ B+136 — *outOff := offset. -/
theorem hit_sd_off (outOff offOld : Word) :
    cpsTripleWithin 1 (B + 136) (B + 140) CR
      (((.x9 : Reg) ↦ᵣ outOff) ** ((.x5 : Reg) ↦ᵣ hitOffW) **
       (outOff ↦ₘ offOld))
      (((.x9 : Reg) ↦ᵣ outOff) ** ((.x5 : Reg) ↦ᵣ hitOffW) **
       (outOff ↦ₘ hitOffW)) := by
  have hsd := sd_spec_gen_within .x9 .x5 outOff hitOffW offOld
    (0 : BitVec 12) (B + 136)
  rw [hit_out_addr0 outOff,
      show (B + 136 : Word) + 4 = B + 140 from by unfold B IndexedB; decide] at hsd
  exact cpsTripleWithin_extend_code
    (mem_at 34 (.SD .x9 .x5 (0 : BitVec 12)) (B + 136)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hsd

/-- LD x5, 40(x22) @ B+140 — load coverHit len (=32). -/
theorem hit_ld_len (v5 : Word) :
    cpsTripleWithin 1 (B + 140) (B + 144) CR
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ v5) **
       (hitLenAddr ↦ₘ hitLenW))
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ hitLenW) **
       (hitLenAddr ↦ₘ hitLenW)) := by
  have hld := ld_spec_gen_within .x5 .x22 WidxRecordsBase v5 hitLenW
    (40 : BitVec 12) (B + 140) (by decide)
  rw [hit_len_addr_eq,
      show (B + 140 : Word) + 4 = B + 144 from by unfold B IndexedB; decide] at hld
  exact cpsTripleWithin_extend_code
    (mem_at 35 (.LD .x5 .x22 (40 : BitVec 12)) (B + 140)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hld

/-- SD x18, x5, 0 @ B+144 — *outLen := len. -/
theorem hit_sd_len (outLen lenOld : Word) :
    cpsTripleWithin 1 (B + 144) (B + 148) CR
      (((.x18 : Reg) ↦ᵣ outLen) ** ((.x5 : Reg) ↦ᵣ hitLenW) **
       (outLen ↦ₘ lenOld))
      (((.x18 : Reg) ↦ᵣ outLen) ** ((.x5 : Reg) ↦ᵣ hitLenW) **
       (outLen ↦ₘ hitLenW)) := by
  have hsd := sd_spec_gen_within .x18 .x5 outLen hitLenW lenOld
    (0 : BitVec 12) (B + 144)
  rw [hit_out_addr0 outLen,
      show (B + 144 : Word) + 4 = B + 148 from by unfold B IndexedB; decide] at hsd
  exact cpsTripleWithin_extend_code
    (mem_at 36 (.SD .x18 .x5 (0 : BitVec 12)) (B + 144)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hsd

/-- LI a0,0 @ B+148. -/
theorem hit_li0 (v10 : Word) :
    cpsTripleWithin 1 (B + 148) (B + 152) CR
      ((.x10 : Reg) ↦ᵣ v10)
      ((.x10 : Reg) ↦ᵣ (0 : Word)) := by
  have h := li_spec_gen_within .x10 v10 (0 : Word) (B + 148) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 37 (.LI .x10 (0 : Word)) (B + 148)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 148 : Word) + 4 = B + 152 from by unfold B IndexedB; decide] at l
  exact l

private theorem jal_epi_off :
    (B + 152 : Word) + signExtend21 (8 : BitVec 21) = B + 160 := by
  unfold B IndexedB
  rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
  decide

/-- JAL x0,+8 @ B+152 → epiPc B+160. emp/emp. -/
theorem hit_jal_epi :
    cpsTripleWithin 1 (B + 152) epiPc CR empAssertion empAssertion := by
  have h := jal_x0_spec_gen_within (8 : BitVec 21) (B + 152)
  have l := cpsTripleWithin_extend_code
    (mem_at 38 (.JAL .x0 (8 : BitVec 21)) (B + 152)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [jal_epi_off] at l
  -- epiPc = B+160 definitionally via IndexedB
  simpa [epiPc, IndexedB, B] using l

/-- Hit path stores + LI0 + JAL epi. Fuel 6, hitPc → epiPc.
    Pre: x22=base, x9=outOff, x18=outLen, dword cells at base+32/+40 and *out*.
    Post: *outOff=0, *outLen=32, a0=0, temps/x5 updated. -/
theorem hit_stores_to_epi
    (v5 v10 outOff outLen offOld lenOld : Word) :
    cpsTripleWithin 6 hitPc epiPc CR
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x10 : Reg) ↦ᵣ v10) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ offOld) ** (outLen ↦ₘ lenOld))
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ hitLenW) **
       ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW)) := by
  -- LD off
  have h0 := hit_ld_off v5
  have h0F := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
     ((.x10 : Reg) ↦ᵣ v10) ** (hitLenAddr ↦ₘ hitLenW) **
     (outOff ↦ₘ offOld) ** (outLen ↦ₘ lenOld))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_memIs
              (pcFree_sepConj pcFree_memIs pcFree_memIs))))) h0
  -- SD off
  have h1 := hit_sd_off outOff offOld
  have h1F := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x18 : Reg) ↦ᵣ outLen) **
     ((.x10 : Reg) ↦ᵣ v10) ** (hitOffAddr ↦ₘ hitOffW) **
     (hitLenAddr ↦ₘ hitLenW) ** (outLen ↦ₘ lenOld))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_memIs
              (pcFree_sepConj pcFree_memIs pcFree_memIs))))) h1
  -- LD len (x5 currently hitOffW)
  have h2 := hit_ld_len hitOffW
  have h2F := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
     ((.x10 : Reg) ↦ᵣ v10) ** (hitOffAddr ↦ₘ hitOffW) **
     (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ lenOld))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_memIs
              (pcFree_sepConj pcFree_memIs pcFree_memIs))))) h2
  -- SD len
  have h3 := hit_sd_len outLen lenOld
  have h3F := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x9 : Reg) ↦ᵣ outOff) **
     ((.x10 : Reg) ↦ᵣ v10) ** (hitOffAddr ↦ₘ hitOffW) **
     (hitLenAddr ↦ₘ hitLenW) ** (outOff ↦ₘ hitOffW))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_memIs
              (pcFree_sepConj pcFree_memIs pcFree_memIs))))) h3
  -- LI a0,0
  have h4 := hit_li0 v10
  have h4F := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ hitLenW) **
     ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
     (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
     (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_memIs
                (pcFree_sepConj pcFree_memIs
                  (pcFree_sepConj pcFree_memIs pcFree_memIs))))))) h4
  -- JAL epi
  have h5 := hit_jal_epi
  have h5F := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ hitLenW) **
     ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
     ((.x10 : Reg) ↦ᵣ (0 : Word)) **
     (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
     (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_memIs
                  (pcFree_sepConj pcFree_memIs
                    (pcFree_sepConj pcFree_memIs pcFree_memIs)))))))) h5
  -- seq compose
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h0F h1F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c01 h2F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c02 h3F
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c03 h4F
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      -- strip emp from jal pre
      refine (sepConj_emp_left _).2 ?_
      xperm_chunked hp) c04 h5F
  have hn : 1 + 1 + 1 + 1 + 1 + 1 = 6 := rfl
  rw [hn] at c05
  -- post has emp ** rest from jal; strip
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      have hq1 := (sepConj_emp_left _).1 hq
      xperm_chunked hq1) c05

/-- Frame around stores: non-focus callee-saved + sp + frame slots.
    Omits x9/x18/x22 (stores focus) to avoid double-own with regsAt. -/
def hitStoresF (spC : Word) (s cur : IndexedSaved) : Assertion :=
  ((.x2 : Reg) ↦ᵣ spC) **
  ((.x1 : Reg) ↦ᵣ cur.ra) ** ((.x8 : Reg) ↦ᵣ cur.s0) **
  ((.x19 : Reg) ↦ᵣ cur.s3) ** ((.x20 : Reg) ↦ᵣ cur.s4) **
  ((.x21 : Reg) ↦ᵣ cur.s5) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s)

private theorem hitStoresF_pcFree (spC : Word) (s cur : IndexedSaved) :
    (hitStoresF spC s cur).pcFree := by
  unfold hitStoresF
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_frameSlotsSaved _ _ _))))))

/-- Hit stores framed through hitStoresF. Fuel 6, hitPc → epiPc. -/
theorem hit_stores_to_epi_framed
    (spC : Word) (s cur : IndexedSaved)
    (v5 v10 outOff outLen offOld lenOld : Word) :
    cpsTripleWithin 6 hitPc epiPc CR
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x10 : Reg) ↦ᵣ v10) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ offOld) ** (outLen ↦ₘ lenOld) **
       hitStoresF spC s cur)
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ hitLenW) **
       ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       hitStoresF spC s cur) := by
  have hs := hit_stores_to_epi v5 v10 outOff outLen offOld lenOld
  -- frameR yields left-pair (P)**F; flatten to right-assoc P**F
  have hsF := cpsTripleWithin_frameR (hitStoresF spC s cur)
    (hitStoresF_pcFree spC s cur) hs
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hsF

/-- Hit stores + epi restore. Fuel 16, hitPc → s.ra, a0=0, outs written.
    Requires cur.s1/s2/s6 match live outOff/outLen/base (saved through body). -/
theorem hit_stores_li0_epi
    (sp0 spC : Word) (s cur : IndexedSaved)
    (v5 v10 outOff outLen offOld lenOld : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hs1 : cur.s1 = outOff) (hs2 : cur.s2 = outLen)
    (hs6 : cur.s6 = WidxRecordsBase) :
    cpsTripleWithin 16 hitPc s.ra CR
      (((.x22 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x10 : Reg) ↦ᵣ v10) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ offOld) ** (outLen ↦ₘ lenOld) **
       hitStoresF spC s cur)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW)) := by
  have hs := hit_stores_to_epi_framed spC s cur v5 v10 outOff outLen offOld lenOld
  -- epi restore under a0=0 + mem cells + x5
  have hrest0 := empty_epi_restore sp0 spC s cur hspC hret
  have hrest := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) **
     (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
     (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
     ((.x5 : Reg) ↦ᵣ hitLenW))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_memIs
          (pcFree_sepConj pcFree_memIs
            (pcFree_sepConj pcFree_memIs
              (pcFree_sepConj pcFree_memIs pcFree_regIs))))) hrest0
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    -- stores post ** hitStoresF → epi pre (x2 ** regsAt cur ** frame) ** cells
    -- hrest frameR left-pairs: ((x2**regsAt**frame)**cells)
    simp only [hitStoresF, regsAt_indexedFrame, hs1, hs2, hs6] at hp ⊢
    xperm_chunked hp) hs hrest
  have hn : 6 + 10 = 16 := rfl
  rw [hn] at c
  -- hrest post is left-pair ((restored)**cells); flatten
  exact cpsTripleWithin_weaken
    (fun _ hp => by simp only [hitStoresF] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by
      -- strip frameR left-pair on post
      have hq1 := hq
      simp only [] at hq1
      xperm_chunked hq1) c

/-! ## B+100 → ret: LI1+BEQ framed into stores+epi -/

/-- Frame for LI1+BEQ: stores ambient without x5/x10. -/
def hitBeqStoresF (spC : Word) (s cur : IndexedSaved)
    (outOff outLen offOld lenOld : Word) : Assertion :=
  ((.x22 : Reg) ↦ᵣ WidxRecordsBase) **
  ((.x9 : Reg) ↦ᵣ outOff) ** ((.x18 : Reg) ↦ᵣ outLen) **
  (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
  (outOff ↦ₘ offOld) ** (outLen ↦ₘ lenOld) **
  hitStoresF spC s cur

private theorem hitBeqStoresF_pcFree (spC : Word) (s cur : IndexedSaved)
    (outOff outLen offOld lenOld : Word) :
    (hitBeqStoresF spC s cur outOff outLen offOld lenOld).pcFree := by
  unfold hitBeqStoresF
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_memIs
          (pcFree_sepConj pcFree_memIs
            (pcFree_sepConj pcFree_memIs
              (pcFree_sepConj pcFree_memIs
                (hitStoresF_pcFree spC s cur)))))))

/-- After cmp32 (a0=1) at B+100: LI1+BEQ+stores+epi → ret a0=0.
    Fuel 18. cur.s1/s2/s6 = outOff/outLen/base. -/
theorem hit_from_a0eq_to_ret
    (sp0 spC : Word) (s cur : IndexedSaved)
    (v5 outOff outLen offOld lenOld : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hs1 : cur.s1 = outOff) (hs2 : cur.s2 = outLen)
    (hs6 : cur.s6 = WidxRecordsBase) :
    cpsTripleWithin 18 (B + 100) s.ra CR
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
       hitBeqStoresF spC s cur outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW)) := by
  have hbeq := hit_li1_beq v5
  have hbeqF := cpsTripleWithin_frameR
    (hitBeqStoresF spC s cur outOff outLen offOld lenOld)
    (hitBeqStoresF_pcFree spC s cur outOff outLen offOld lenOld) hbeq
  have hst := hit_stores_li0_epi sp0 spC s cur (1 : Word) (1 : Word)
    outOff outLen offOld lenOld hspC hret hs1 hs2 hs6
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [hitBeqStoresF] at hp ⊢
    xperm_chunked hp) hbeqF hst
  have hn : 2 + 16 = 18 := rfl
  rw [hn] at c
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [hitBeqStoresF] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) c

end EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
