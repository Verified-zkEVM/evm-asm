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

end EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
