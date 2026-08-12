/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty

  Empty-index miss path for `witness_lookup_by_hash_indexed`
  (`widx_count = 0` → BGEU taken → a0 = 1).

  Checkpoint: first machine path on the production-reachable indexed domain
  (count may be zero after a successful build of an empty section).

  Depends on #12169. NEW file only. No sorry.
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Evm64
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
open EvmAsm.Codegen.Proofs

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

/-! ## Setup MVs + LI lo=0
MV focuses BOTH rd and rs — frame must omit both. -/

/-- MV s0,a2 @ bodyEntry (idx 9). -/
theorem empty_mv_s0
    (hashPtr v8 ret sp0 : Word) :
    cpsTripleWithin 1 bodyEntryPc (bodyEntryPc + 4) CR
      (((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have h := mv_spec_gen_within .x8 .x12 hashPtr v8 bodyEntryPc (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 9 (.MV .x8 .x12) bodyEntryPc (by unfold bodyEntryPc B IndexedB; decide)
      (by decide) (by rfl)) h
  -- frame omits x8 (rd) and x12 (rs)
  have hF :
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs pcFree_regIs
  have lf := cpsTripleWithin_frameR _ hF l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-- MV s1,a3 @ B+40 (idx 10). -/
theorem empty_mv_s1
    (outOff v9 hashPtr ret sp0 : Word) :
    cpsTripleWithin 1 (B + 40) (B + 44) CR
      (((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have h := mv_spec_gen_within .x9 .x13 outOff v9 (B + 40) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 10 (.MV .x9 .x13) (B + 40) (by unfold B IndexedB; decide)
      (by decide) (by rfl)) h
  rw [show (B + 40 : Word) + 4 = B + 44 from by unfold B IndexedB; decide] at l
  -- frame omits x9 (rd) and x13 (rs)
  have hF :
      (((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_regIs)
  have lf := cpsTripleWithin_frameR _ hF l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-- MV s2,a4 @ B+44 (idx 11). -/
theorem empty_mv_s2
    (outLen v18 hashPtr outOff ret sp0 : Word) :
    cpsTripleWithin 1 (B + 44) (B + 48) CR
      (((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have h := mv_spec_gen_within .x18 .x14 outLen v18 (B + 44) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 11 (.MV .x18 .x14) (B + 44) (by unfold B IndexedB; decide)
      (by decide) (by rfl)) h
  rw [show (B + 44 : Word) + 4 = B + 48 from by unfold B IndexedB; decide] at l
  -- frame omits x18 (rd) and x14 (rs)
  have hF :
      (((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs pcFree_regIs))
  have lf := cpsTripleWithin_frameR _ hF l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-- LI s3,0 @ B+48 (idx 12). -/
theorem empty_li_lo
    (v19 hashPtr outOff outLen ret sp0 : Word) :
    cpsTripleWithin 1 (B + 48) (B + 52) CR
      (((.x19 : Reg) ↦ᵣ v19) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have h := li_spec_gen_within .x19 v19 (0 : Word) (B + 48) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 12 (.LI .x19 (0 : Word)) (B + 48) (by unfold B IndexedB; decide)
      (by decide) (by rfl)) h
  rw [show (B + 48 : Word) + 4 = B + 52 from by unfold B IndexedB; decide] at l
  have hF :
      (((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs pcFree_regIs)))
  have lf := cpsTripleWithin_frameR _ hF l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-! ## la widx_count @ B+52 (idx 13-14) -/

private theorem la_count_range :
    laInRange (B + 52) WidxCountLoc := by
  unfold laInRange B WidxCountLoc IndexedB GuestAddrs.widx_count
  decide

set_option maxRecDepth 8000 in
private theorem la_count_hi :
    Rv64.laHi (B + 52) WidxCountLoc =
      Codegen.laHi GuestAddrs.widx_count (IndexedB + 52) := by
  unfold B WidxCountLoc IndexedB
  decide

set_option maxRecDepth 8000 in
private theorem la_count_lo :
    Rv64.laLo (B + 52) WidxCountLoc =
      Codegen.laLo GuestAddrs.widx_count (IndexedB + 52) := by
  unfold B WidxCountLoc IndexedB
  decide

private theorem prog_auipc_count :
    Prog[13]'(by rw [indexed_prog_length]; decide) =
      .AUIPC .x5 (Codegen.laHi GuestAddrs.widx_count (IndexedB + 52)) := by
  rfl

private theorem prog_addi_count :
    Prog[14]'(by rw [indexed_prog_length]; decide) =
      .ADDI .x5 .x5 (Codegen.laLo GuestAddrs.widx_count (IndexedB + 52)) := by
  rfl

private theorem hpc_la_mid : (B + 52 : Word) + 4 = B + 56 := by
  unfold B IndexedB; decide

private theorem hpc_la_exit : (B + 52 : Word) + 8 = B + 60 := by
  unfold B IndexedB; decide

/-- la t0, widx_count @ B+52 (idx 13-14). -/
theorem empty_la_count
    (v5 hashPtr outOff outLen ret sp0 : Word) :
    cpsTripleWithin 2 (B + 52) (B + 60) CR
      (((.x5 : Reg) ↦ᵣ v5) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have hla := la_materialize_within (cr := CR) .x5 v5 (B + 52) WidxCountLoc
    (by decide) la_count_range
    (by
      intro a i hs
      have hs' : CodeReq.singleton (B + 52)
          (.AUIPC .x5 (Codegen.laHi GuestAddrs.widx_count (IndexedB + 52)))
          a = some i := by
        simpa [la_count_hi] using hs
      exact mem_at 13 _ (B + 52) (by unfold B IndexedB; decide) (by decide)
        prog_auipc_count a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (B + 56)
          (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.widx_count (IndexedB + 52)))
          a = some i := by
        simpa [hpc_la_mid, la_count_lo] using hs
      exact mem_at 14 _ (B + 56) (by unfold B IndexedB; decide) (by decide)
        prog_addi_count a i hs')
  rw [hpc_la_exit] at hla
  have hF :
      (((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs pcFree_regIs))))
  have lf := cpsTripleWithin_frameR _ hF hla
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-! ## LD hi=*widx_count (=0) @ B+60 (idx 15) -/

/-- LD s4, 0(t0) with *widx_count = 0. Focuses x20+x5+mem. -/
theorem empty_ld_count
    (v20 hashPtr outOff outLen ret sp0 : Word) :
    cpsTripleWithin 1 (B + 60) (B + 64) CR
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
       (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have hld := ld_spec_gen_within .x20 .x5 WidxCountLoc v20 (0 : Word)
    (0 : BitVec 12) (B + 60) (by decide)
  rw [signExtend12_0,
      show (WidxCountLoc + 0 : Word) = WidxCountLoc from by bv_omega,
      show (B + 60 : Word) + 4 = B + 64 from by unfold B IndexedB; decide] at hld
  have l := cpsTripleWithin_extend_code
    (mem_at 15 (.LD .x20 .x5 (0 : BitVec 12)) (B + 60)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hld
  -- frame omits x20 (rd), x5 (rs1), and mem cell
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

/-! ## BGEU lo,hi taken → miss (lo=hi=0) @ B+64 (idx 16) -/

private def bgeuMissOff : BitVec 13 :=
  brOff (GuestAddrs.witness_lookup_by_hash_indexed + 156)
    (GuestAddrs.witness_lookup_by_hash_indexed + 64)

private theorem bgeu_miss_taken :
    (B + 64 : Word) + signExtend13 bgeuMissOff = B + 156 := by
  unfold B IndexedB bgeuMissOff
  change BitVec.ofNat 64 GuestAddrs.witness_lookup_by_hash_indexed +
      BitVec.ofNat 64 64 +
      signExtend13 (brOff (GuestAddrs.witness_lookup_by_hash_indexed + 156)
        (GuestAddrs.witness_lookup_by_hash_indexed + 64)) =
    BitVec.ofNat 64 GuestAddrs.witness_lookup_by_hash_indexed + BitVec.ofNat 64 156
  exact brOff_correct_base_off GuestAddrs.witness_lookup_by_hash_indexed 64 156
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- BGEU s3,s4 with both 0 → taken to miss entry B+156.
    Focuses x19+x20; frame carries the rest. -/
theorem empty_bgeu_miss
    (hashPtr outOff outLen ret sp0 : Word) :
    cpsTripleWithin 1 (B + 64) (B + 156) CR
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have hb := bgeu_spec_gen_within .x19 .x20 bgeuMissOff
    (0 : Word) (0 : Word) (B + 64)
  rw [bgeu_miss_taken,
      show (B + 64 : Word) + 4 = B + 68 from by unfold B IndexedB; decide] at hb
  have hbe := cpsBranchWithin_extend_code
    (mem_at 16 (.BGEU .x19 .x20 bgeuMissOff) (B + 64)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hb
  -- taken strip: fallthrough pure is ⌜ult 0 0⌝ which is false;
  -- takenStripPure2 also drops the taken-side pure
  have htk := cpsBranchWithin_takenStripPure2 hbe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hF :
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs pcFree_regIs)))))
  have lf := cpsTripleWithin_frameR _ hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-! ## LI a0,1 @ miss entry B+156 (idx 39) -/

/-- LI a0, 1 at miss join. -/
theorem empty_li_a0_1
    (v10 hashPtr outOff outLen ret sp0 : Word) :
    cpsTripleWithin 1 (B + 156) (B + 160) CR
      (((.x10 : Reg) ↦ᵣ v10) **
       ((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64)))
      (((.x10 : Reg) ↦ᵣ (1 : Word)) **
       ((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))) := by
  have h := li_spec_gen_within .x10 v10 (1 : Word) (B + 156) (by decide)
  have l := cpsTripleWithin_extend_code
    (mem_at 39 (.LI .x10 (1 : Word)) (B + 156)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) h
  rw [show (B + 156 : Word) + 4 = B + 160 from by unfold B IndexedB; decide] at l
  have hF :
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ (sp0 - 64))).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_memIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs pcFree_regIs)))))))
  have lf := cpsTripleWithin_frameR _ hF l
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) lf

/-! ## Epilogue restore @ B+160 (idx 40–49): 8×LD + ADDI+64 + JALR -/

structure IndexedSaved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word

def indexedSavedVals (s : IndexedSaved) : Reg → Word
  | .x1  => s.ra
  | .x8  => s.s0
  | .x9  => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | _ => 0

theorem regsAt_indexedFrame (s : IndexedSaved) :
    regsAt indexedFrame (indexedSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6)) := by
  simp [indexedFrame, regsAt, indexedSavedVals, sepConj_emp_right']

private theorem indexedFrame_hne : ∀ p ∈ indexedFrame, p.1 ≠ .x0 := by decide

/-- loadSeq + ADDI sp,+64 + JALR from epiPc → s.ra. Fuel 8+1+1 = 10.
    Pattern: ExecutionRequestsHashEpi.erhEpilogueRestore. -/
theorem empty_epi_restore
    (sp0 spC : Word) (s cur : IndexedSaved)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 10 epiPc s.ra CR
      ((.x2 ↦ᵣ spC) ** regsAt indexedFrame (indexedSavedVals cur) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s)) := by
  have hs0 := loadSeq_spec indexedFrame spC (indexedSavedVals s) (indexedSavedVals cur)
    epiPc (by decide) indexedFrame_hne
  have h_loadMono : ∀ a i,
      CodeReq.ofProg epiPc (loadProg indexedFrame) a = some i →
        CR a = some i := by
    intro a i h_mem
    apply wrapper_in_fullCode
    exact CodeReq.ofProg_mono_sub B epiPc Prog (loadProg indexedFrame) 40
      (by unfold B IndexedB epiPc; decide) (by rfl)
      (by rw [indexed_prog_length]; simp [indexedFrame, loadProg])
      (by rw [indexed_prog_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  rw [show epiPc + BitVec.ofNat 64 (4 * indexedFrame.length) = B + 192 from by
    simp [epiPc, indexedFrame, B, IndexedB]; decide] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (64 : BitVec 12) (B + 192) (by decide)
  have hsp : spC + signExtend12 (64 : BitVec 12) = sp0 := by
    rw [hspC]
    rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
      show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha := cpsTripleWithin_extend_code
    (mem_at 48 (.ADDI .x2 .x2 (64 : BitVec 12)) (B + 192)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt indexedFrame (indexedSavedVals s) **
      frameSlotsSaved indexedFrame spC (indexedSavedVals s))
    (by exact pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _)) ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hs haF
  rw [show (B + 192 : Word) + 4 = B + 196 from by unfold B IndexedB; decide]
    at hload_addi
  have hjalr0 := ret_spec_within' (B + 196) s.ra
  rw [hret] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (mem_at 49 (.JALR .x0 .x1 (0 : BitVec 12)) (B + 196)
      (by unfold B IndexedB; decide) (by decide) (by rfl)) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      frameSlotsSaved indexedFrame spC (indexedSavedVals s))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj pcFree_regIs
                      (pcFree_frameSlotsSaved _ _ _))))))))) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_indexedFrame] at hp
    xperm_hyp hp) hload_addi hjalrF
  have hn : indexedFrame.length + 1 + 1 = 10 := by simp [indexedFrame]
  rw [hn] at hall
  change cpsTripleWithin 10 epiPc s.ra CR _ _
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-- Miss LI a0,1 + epi restore. Fuel 11. Pattern: erh_fail_join. -/
theorem empty_miss_li_epi
    (sp0 spC : Word) (s cur : IndexedSaved) (v10old : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 11 missPc s.ra CR
      ((.x10 ↦ᵣ v10old) ** (.x2 ↦ᵣ spC) **
        regsAt indexedFrame (indexedSavedVals cur) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s)) := by
  let F : Assertion :=
    (.x2 ↦ᵣ spC) ** regsAt indexedFrame (indexedSavedVals cur) **
      frameSlotsSaved indexedFrame spC (indexedSavedVals s)
  have hF : F.pcFree := by
    dsimp [F]
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regsAt _ _) (pcFree_frameSlotsSaved _ _ _))
  have hli0 := li_spec_gen_within .x10 v10old (1 : Word) missPc (by decide)
  have hliC := cpsTripleWithin_extend_code
    (mem_at 39 (.LI .x10 (1 : Word)) missPc
      (by simp only [missPc, B, IndexedB]; decide) (by decide) (by rfl)) hli0
  rw [show missPc + (4 : Word) = epiPc from by
    simp only [missPc, epiPc, IndexedB]; decide] at hliC
  have hliF := cpsTripleWithin_frameR F hF hliC
  have hrest := empty_epi_restore sp0 spC s cur hspC hret
  have hrestF := cpsTripleWithin_frameR (.x10 ↦ᵣ (1 : Word))
    (by exact pcFree_regIs) hrest
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hrestF
  have hn : 1 + 10 = 11 := rfl
  rw [hn] at hall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-- Frame empty_miss_li_epi with count cell — exact frameR shape (P ** Fc). -/
theorem empty_miss_li_epi_count
    (sp0 spC : Word) (s cur : IndexedSaved) (v10old : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 11 missPc s.ra CR
      (((.x10 ↦ᵣ v10old) ** (.x2 ↦ᵣ spC) **
        regsAt indexedFrame (indexedSavedVals cur) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s)) **
       (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word))))
      (((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s)) **
       (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)))) :=
  cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)))
    (pcFree_sepConj pcFree_regIs pcFree_memIs)
    (empty_miss_li_epi sp0 spC s cur v10old hspC hret)

/-- loopHdr lo=hi=0 → return a0=1. Fuel 12.
    Pre is frameR shape (bgeu_core ** Fextra).
    Fextra carries ABI copies x12/x13/x14 + temps x10/x21/x22 + frame. -/
theorem empty_loopHdr_to_ret
    (sp0 spC : Word) (s : IndexedSaved) (v10 : Word)
    (hashPtr outOff outLen raMid s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 12 loopHdrPc s.ra CR
      (((( (.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
         ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
         ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       (((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s))))
      ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s)) **
       (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen)))) := by
  have hspEq : sp0 - 64 = spC := by
    rw [hspC]
    rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide]
    bv_omega
  have hb0 := empty_bgeu_miss hashPtr outOff outLen raMid sp0
  have hb : cpsTripleWithin 1 loopHdrPc missPc CR
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) := by
    convert hb0 using 1 <;> try rw [hspEq]
  let Fextra : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) **
    ((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
    frameSlotsSaved indexedFrame spC (indexedSavedVals s)
  have hFx : Fextra.pcFree := by
    dsimp [Fextra]
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs (pcFree_frameSlotsSaved _ _ _))))))
  have hbF := cpsTripleWithin_frameR Fextra hFx hb
  let cur : IndexedSaved :=
    { ra := raMid, s0 := hashPtr, s1 := outOff, s2 := outLen
    , s3 := 0, s4 := 0, s5 := s5, s6 := s6 }
  -- miss_li_epi_count frames only count; also frame ABI copies x12-14
  have hli0 := empty_miss_li_epi_count sp0 spC s cur v10 hspC hret
  let Fabi : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen)
  have hFabi : Fabi.pcFree := by
    dsimp [Fabi]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_regIs)
  have hli := cpsTripleWithin_frameR Fabi hFabi hli0
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Fextra, Fabi] at hp
      simp only [regsAt_indexedFrame] at hp ⊢
      dsimp [cur, indexedSavedVals] at hp ⊢
      xperm_chunked hp) hbF hli
  have hn : 1 + 11 = 12 := rfl
  rw [hn] at c
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by dsimp [Fabi] at hq ⊢; xperm_chunked hq) c

/-! ## bodyEntry → B+52: 3×MV + LI lo (fuel 4) -/

/-- Ambient through MVs: unused temps + frame slots + count cell. -/
def emptyMvAmb (spC : Word) (s : IndexedSaved)
    (v5 v10 v20 s5 s6 : Word) : Assertion :=
  ((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ v10) ** ((.x20 : Reg) ↦ᵣ v20) **
  ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (0 : Word))

private theorem emptyMvAmb_pcFree (spC : Word) (s : IndexedSaved)
    (v5 v10 v20 s5 s6 : Word) :
    (emptyMvAmb spC s v5 v10 v20 s5 s6).pcFree := by
  dsimp [emptyMvAmb]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) pcFree_memIs)))))

/-- Ambient after la (x5 = WidxCountLoc); still has v20 and count. -/
def emptyAfterLaAmb (spC : Word) (s : IndexedSaved)
    (v10 v20 s5 s6 : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ v10) ** ((.x20 : Reg) ↦ᵣ v20) **
  ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
  (WidxCountLoc ↦ₘ (0 : Word))

private theorem emptyAfterLaAmb_pcFree (spC : Word) (s : IndexedSaved)
    (v10 v20 s5 s6 : Word) :
    (emptyAfterLaAmb spC s v10 v20 s5 s6).pcFree := by
  dsimp [emptyAfterLaAmb]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) pcFree_memIs))))

/-- Ambient at loopHdr after ld (hi=0): temps + frame (count still present). -/
def emptyLoopHdrAmb (spC : Word) (s : IndexedSaved)
    (v10 s5 s6 : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s)

private theorem emptyLoopHdrAmb_pcFree (spC : Word) (s : IndexedSaved)
    (v10 s5 s6 : Word) :
    (emptyLoopHdrAmb spC s v10 s5 s6).pcFree := by
  dsimp [emptyLoopHdrAmb]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_frameSlotsSaved _ _ _)))

/-- bodyEntry → B+52: s0=hash, s1=outOff, s2=outLen, s3=0. Fuel 4. -/
theorem empty_mvs_li
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v8 v9 v18 v19 v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 4 bodyEntryPc (B + 52) CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyMvAmb spC s v5 v10 v20 s5 s6))
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyMvAmb spC s v5 v10 v20 s5 s6)) := by
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
    ((.x19 : Reg) ↦ᵣ v19) ** emptyMvAmb spC s v5 v10 v20 s5 s6
  have hF0 : F0.pcFree := by
    dsimp [F0]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (emptyMvAmb_pcFree _ _ _ _ _ _ _)))))
  have c0 := cpsTripleWithin_frameR F0 hF0 hm0'
  let F1 : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) **
    ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
    ((.x19 : Reg) ↦ᵣ v19) ** emptyMvAmb spC s v5 v10 v20 s5 s6
  have hF1 : F1.pcFree := by
    dsimp [F1]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (emptyMvAmb_pcFree _ _ _ _ _ _ _))))
  have c1 := cpsTripleWithin_frameR F1 hF1 hm1'
  have s01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [F0, F1] at hp ⊢; xperm_chunked hp) c0 c1
  let F2 : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x19 : Reg) ↦ᵣ v19) ** emptyMvAmb spC s v5 v10 v20 s5 s6
  have hF2 : F2.pcFree := by
    dsimp [F2]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (emptyMvAmb_pcFree _ _ _ _ _ _ _)))
  have c2 := cpsTripleWithin_frameR F2 hF2 hm2'
  have s012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [F1, F2] at hp ⊢; xperm_chunked hp) s01 c2
  let F3 : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) ** emptyMvAmb spC s v5 v10 v20 s5 s6
  have hF3 : F3.pcFree := by
    dsimp [F3]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (emptyMvAmb_pcFree _ _ _ _ _ _ _)))
  have c3 := cpsTripleWithin_frameR F3 hF3 hli'
  have s0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [F2, F3] at hp ⊢; xperm_chunked hp) s012 c3
  have hn : 1 + 1 + 1 + 1 = 4 := rfl
  rw [hn] at s0123
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F0, emptyMvAmb] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by dsimp [F3, emptyMvAmb] at hq ⊢; xperm_chunked hq) s0123

/-- B+52 → B+60: la t0,widx_count. Fuel 2. -/
theorem empty_la_at
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
       emptyAfterLaAmb spC s v10 v20 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyAfterLaAmb spC s v10 v20 s5 s6)) := by
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
  -- la focuses x5 only; frame = x12,x13,x14 + afterLaAmb
  let F : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) ** emptyAfterLaAmb spC s v10 v20 s5 s6
  have hF : F.pcFree := by
    dsimp [F]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (emptyAfterLaAmb_pcFree _ _ _ _ _ _)))
  have hf := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F, emptyAfterLaAmb] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by dsimp [F, emptyAfterLaAmb] at hq ⊢; xperm_chunked hq) hf

/-- B+60 → loopHdr: LD s4,*widx_count (=0). Fuel 1. -/
theorem empty_ld_at
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 1 (B + 60) loopHdrPc CR
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
         (WidxCountLoc ↦ₘ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyLoopHdrAmb spC s v10 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
         (WidxCountLoc ↦ₘ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyLoopHdrAmb spC s v10 s5 s6)) := by
  have hspEq : sp0 - 64 = spC := by
    rw [hspC]
    rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide]
    bv_omega
  have h0 := empty_ld_count v20 hashPtr outOff outLen raMid sp0
  have h : cpsTripleWithin 1 (B + 60) (B + 64) CR
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
       (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC))
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
       (WidxCountLoc ↦ₘ (0 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) ** ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) := by
    convert h0 using 1 <;> try rw [hspEq]
  -- B+64 = loopHdrPc definitionally
  -- ld focuses x5+x20+mem; frame = x12,x13,x14 + loopHdrAmb
  let F : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) ** emptyLoopHdrAmb spC s v10 s5 s6
  have hF : F.pcFree := by
    dsimp [F]; exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (emptyLoopHdrAmb_pcFree _ _ _ _ _)))
  have hf := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp [F, emptyLoopHdrAmb] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by dsimp [F, emptyLoopHdrAmb] at hq ⊢; xperm_chunked hq) hf

/-- B+52 → loopHdr: la + ld count=0. Fuel 3. -/
theorem empty_la_ld
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
         emptyLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (0 : Word))))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
         (WidxCountLoc ↦ₘ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyLoopHdrAmb spC s v10 s5 s6)) := by
  have hla := empty_la_at sp0 spC s hashPtr outOff outLen raMid v5 v10 v20 s5 s6 hspC
  have hld := empty_ld_at sp0 spC s hashPtr outOff outLen raMid v10 v20 s5 s6 hspC
  -- reshape la pre/post: emptyAfterLaAmb = x20 ** loopHdrAmb ** count
  have hla' : cpsTripleWithin 2 (B + 52) (B + 60) CR
      (((( (.x5 : Reg) ↦ᵣ v5) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
         emptyLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (0 : Word))))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
         emptyLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (0 : Word)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [emptyAfterLaAmb, emptyLoopHdrAmb] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        dsimp [emptyAfterLaAmb, emptyLoopHdrAmb] at hq ⊢; xperm_chunked hq) hla
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [emptyLoopHdrAmb] at hp ⊢; xperm_chunked hp) hla' hld
  have hn : 2 + 1 = 3 := rfl
  rw [hn] at c
  exact c

/-- bodyEntry → loopHdr: MVs + LI + la + ld. Fuel 7. -/
theorem empty_bodyEntry_to_loopHdr
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v8 v9 v18 v19 v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 7 bodyEntryPc loopHdrPc CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyMvAmb spC s v5 v10 v20 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
         (WidxCountLoc ↦ₘ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyLoopHdrAmb spC s v10 s5 s6)) := by
  have hmvs := empty_mvs_li sp0 spC s hashPtr outOff outLen raMid
    v8 v9 v18 v19 v5 v10 v20 s5 s6 hspC
  have hla := empty_la_ld sp0 spC s hashPtr outOff outLen raMid
    v5 v10 v20 s5 s6 hspC
  -- reshape mvs post → la pre: emptyMvAmb = x5**x20**loopHdrAmb**count
  have hmvs' : cpsTripleWithin 4 bodyEntryPc (B + 52) CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyMvAmb spC s v5 v10 v20 s5 s6))
      (((( (.x5 : Reg) ↦ᵣ v5) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x19 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
         emptyLoopHdrAmb spC s v10 s5 s6) **
       (WidxCountLoc ↦ₘ (0 : Word)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by
        dsimp [emptyMvAmb, emptyLoopHdrAmb] at hq ⊢; xperm_chunked hq) hmvs
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [emptyLoopHdrAmb] at hp ⊢; xperm_chunked hp) hmvs' hla
  have hn : 4 + 3 = 7 := rfl
  rw [hn] at c
  exact c

/-- bodyEntry → ret: empty miss a0=1. Fuel 19. -/
theorem empty_bodyEntry_to_ret
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v8 v9 v18 v19 v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 19 bodyEntryPc s.ra CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyMvAmb spC s v5 v10 v20 s5 s6))
      ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s)) **
       (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen)))) := by
  have hsetup := empty_bodyEntry_to_loopHdr sp0 spC s hashPtr outOff outLen raMid
    v8 v9 v18 v19 v5 v10 v20 s5 s6 hspC
  have hloop := empty_loopHdr_to_ret sp0 spC s v10 hashPtr outOff outLen raMid
    s5 s6 hspC hret
  -- reshape setup post → loop pre (frameR shape with x12-14 in Fextra)
  have hsetup' : cpsTripleWithin 7 bodyEntryPc loopHdrPc CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       emptyMvAmb spC s v5 v10 v20 s5 s6))
      (((( (.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (0 : Word)) **
         ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
         ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
         ((.x18 : Reg) ↦ᵣ outLen) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       (((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x22 : Reg) ↦ᵣ s6) **
        frameSlotsSaved indexedFrame spC (indexedSavedVals s)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by
        dsimp [emptyLoopHdrAmb] at hq ⊢; xperm_chunked hq) hsetup
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp [emptyLoopHdrAmb] at hp ⊢; xperm_chunked hp)
    hsetup' hloop
  have hn : 7 + 12 = 19 := rfl
  rw [hn] at c
  exact c

/-! ## Prologue + empty-miss top triple
    Manual frame (not abiFrame_spec): body path already includes miss epi→ret.
    Pattern: ExecutionRequestsHashWrap.erh_prologue. -/

/-- ADDI sp,-64 + storeSeq. Fuel 1+8 = 9. Entry B → bodyEntry. -/
theorem empty_prologue
    (sp0 : Word) (s : IndexedSaved)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 9 B bodyEntryPc CR
      ((.x2 ↦ᵣ sp0) ** regsAt indexedFrame (indexedSavedVals s) **
        frameSlotsOwn indexedFrame (sp0 + signExtend12 (-64 : BitVec 12)) ** A)
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-64 : BitVec 12))) **
        regsAt indexedFrame (indexedSavedVals s) **
        frameSlotsSaved indexedFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (indexedSavedVals s) ** A) := by
  set newSp := sp0 + signExtend12 (-64 : BitVec 12) with hNS
  have hbound : 4 * indexedFrame.length < 2 ^ 64 := by
    simp only [indexedFrame, List.length_cons, List.length_nil]; norm_num
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-64 : BitVec 12) B (by decide)
  rw [← hNS] at ha0
  have haC := cpsTripleWithin_extend_code
    (mem_at 0 (.ADDI .x2 .x2 (-64 : BitVec 12)) B
      (by unfold B IndexedB; decide) (by decide) (by rfl)) ha0
  have hFpc : (regsAt indexedFrame (indexedSavedVals s) **
      frameSlotsOwn indexedFrame newSp ** A).pcFree := by
    exact pcFree_sepConj (pcFree_regsAt _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _) hA)
  have haF := cpsTripleWithin_frameR
    (regsAt indexedFrame (indexedSavedVals s) **
      frameSlotsOwn indexedFrame newSp ** A) hFpc haC
  -- frameR yields (x2 ** (regs**own**A)); right-assoc ** matches goal shape
  have ha : cpsTripleWithin 1 B (B + 4) CR
      ((.x2 ↦ᵣ sp0) ** regsAt indexedFrame (indexedSavedVals s) **
        frameSlotsOwn indexedFrame newSp ** A)
      ((.x2 ↦ᵣ newSp) ** regsAt indexedFrame (indexedSavedVals s) **
        frameSlotsOwn indexedFrame newSp ** A) := haF
  have hs0 := storeSeq_spec indexedFrame newSp (indexedSavedVals s) (B + 4) hbound
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg indexedFrame) a = some i →
        CR a = some i := by
    intro a i h_mem
    apply wrapper_in_fullCode
    exact CodeReq.ofProg_mono_sub B (B + 4) Prog (storeProg indexedFrame) 1
      (by unfold B IndexedB; decide) (by rfl)
      (by rw [indexed_prog_length]; simp [indexedFrame, storeProg])
      (by rw [indexed_prog_length]; decide) a i h_mem
  have hs1 := cpsTripleWithin_extend_code h_storeMono hs0
  have hsF := cpsTripleWithin_frameR A hA hs1
  rw [show (B + 4 : Word) + BitVec.ofNat 64 (4 * indexedFrame.length) = bodyEntryPc
      from by simp [bodyEntryPc, indexedFrame, B, IndexedB]; decide] at hsF
  -- store frameR: ((x2**regs**slots)**A) → flatten with sepConj_assoc'
  have hs : cpsTripleWithin indexedFrame.length (B + 4) bodyEntryPc CR
      ((.x2 ↦ᵣ newSp) ** regsAt indexedFrame (indexedSavedVals s) **
        frameSlotsOwn indexedFrame newSp ** A)
      ((.x2 ↦ᵣ newSp) ** regsAt indexedFrame (indexedSavedVals s) **
        frameSlotsSaved indexedFrame newSp (indexedSavedVals s) ** A) := by
    -- hsF: ((x2**regs**slots)**A); flatten with sepConj_assoc' (Assertion eq)
    convert hsF using 1
    · rw [sepConj_assoc' (.x2 ↦ᵣ newSp)
        (regsAt indexedFrame (indexedSavedVals s) **
          frameSlotsOwn indexedFrame newSp) A]
      rw [sepConj_assoc' (regsAt indexedFrame (indexedSavedVals s))
        (frameSlotsOwn indexedFrame newSp) A]
    · rw [sepConj_assoc' (.x2 ↦ᵣ newSp)
        (regsAt indexedFrame (indexedSavedVals s) **
          frameSlotsSaved indexedFrame newSp (indexedSavedVals s)) A]
      rw [sepConj_assoc' (regsAt indexedFrame (indexedSavedVals s))
        (frameSlotsSaved indexedFrame newSp (indexedSavedVals s)) A]
  have hall := cpsTripleWithin_seq_same_cr ha hs
  have hn : 1 + indexedFrame.length = 9 := by
    simp only [indexedFrame, List.length_cons, List.length_nil]
  rw [hn] at hall
  exact hall

/-- Whole-routine empty-miss top: prologue + bodyEntry_to_ret.
    Fuel 28. Domain: widx_count=0 (production-reachable with enable=1). -/
theorem witness_lookup_by_hash_indexed_spec_within_empty
    (sp0 ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen v5 v10 : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 28 B ret CR
      ((.x2 ↦ᵣ sp0) ** regsAt indexedFrame (indexedSavedVals { s with ra := ret }) **
        (.x12 ↦ᵣ hashPtr) ** (.x13 ↦ᵣ outOff) ** (.x14 ↦ᵣ outLen) **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        frameSlotsOwn indexedFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        (WidxCountLoc ↦ₘ (0 : Word)))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved indexedFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (indexedSavedVals { s with ra := ret }) **
        ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
        ((.x14 : Reg) ↦ᵣ outLen)) := by
  set newSp := sp0 + signExtend12 (-64 : BitVec 12) with hNS
  -- Force saved ra = ret so entry x1 matches exit PC
  let sRet : IndexedSaved := { s with ra := ret }
  have hsRet_ra : sRet.ra = ret := rfl
  let Apro : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) **
    ((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ v10) **
    (WidxCountLoc ↦ₘ (0 : Word))
  have hApro : Apro.pcFree := by
    dsimp [Apro]
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs pcFree_memIs))))
  have hpro := empty_prologue sp0 sRet Apro hApro
  have hbody := empty_bodyEntry_to_ret sp0 newSp sRet
    hashPtr outOff outLen ret
    s.s0 s.s1 s.s2 s.s3 v5 v10 s.s4 s.s5 s.s6
    (by exact hNS) (by simpa [hsRet_ra] using halignRet)
  -- Seq: reshape prologue post ↔ body pre
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [← hNS, sRet, Apro, emptyMvAmb, regsAt_indexedFrame] at hp ⊢
      xperm_chunked hp) hpro hbody
  have hn : 9 + 19 = 28 := rfl
  rw [hn] at c
  -- Exit PC: sRet.ra = ret
  have c' : cpsTripleWithin 28 B ret CR
      ((.x2 ↦ᵣ sp0) **
        regsAt indexedFrame (indexedSavedVals sRet) **
          frameSlotsOwn indexedFrame (sp0 + signExtend12 (-64 : BitVec 12)) ** Apro)
      (((( .x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ sRet.ra) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ sRet.s0) ** (.x9 ↦ᵣ sRet.s1) **
          (.x18 ↦ᵣ sRet.s2) ** (.x19 ↦ᵣ sRet.s3) **
          (.x20 ↦ᵣ sRet.s4) ** (.x21 ↦ᵣ sRet.s5) **
          (.x22 ↦ᵣ sRet.s6) ** frameSlotsSaved indexedFrame newSp (indexedSavedVals sRet)) **
        ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
          ((.x14 : Reg) ↦ᵣ outLen))) := by
    simpa [hsRet_ra] using c
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [sRet, Apro, regsAt_indexedFrame] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      simp only [sRet] at hq ⊢
      xperm_chunked hq) c'

end EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty



