/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedOneHitStores

  Hit arm after cmp32 eq: LI1+BEQ → hitPc, LD/SD off+len, LI0, epi restore.
  Split from OneHit.lean for the 1500-line file-size gate.

  **Depends on PR #12169.** NEW file only.
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedOneHit
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedCallees
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Evm64
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty
open EvmAsm.Codegen.WitnessLookupByHashIndexedCallees
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

abbrev hitOffAddr : Word := WidxRecordsBase + (32 : Word)
abbrev hitLenAddr : Word := WidxRecordsBase + (40 : Word)
abbrev hitOffW : Word := (0 : Word)
abbrev hitLenW : Word := (32 : Word)

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

/-! ## Bridge cmp32 post → hit_from_a0eq → ret

Live `cur` after coverHit cmp32: ra = B+100, s0 = hashPtr (x8), s1/s2 = outs,
s3=0 s4=1 s5=0 (loop temps), s6 = WidxRecordsBase. -/

/-- Live frame-reg map at B+100 after equal cmp32 on coverHit. -/
def hitLiveCur (hashPtr outOff outLen : Word) : IndexedSaved where
  ra := B + 100
  s0 := hashPtr
  s1 := outOff
  s2 := outLen
  s3 := (0 : Word)
  s4 := (1 : Word)
  s5 := (0 : Word)
  s6 := WidxRecordsBase

/-- Out + record dword cells carried ambient through cmp32. -/
def hitCells (outOff outLen offOld lenOld : Word) : Assertion :=
  (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
  (outOff ↦ₘ offOld) ** (outLen ↦ₘ lenOld)

private theorem hitCells_pcFree (outOff outLen offOld lenOld : Word) :
    (hitCells outOff outLen offOld lenOld).pcFree := by
  unfold hitCells
  exact pcFree_sepConj pcFree_memIs
    (pcFree_sepConj pcFree_memIs
      (pcFree_sepConj pcFree_memIs pcFree_memIs))

/-- Extras on cmp32 post not needed by hit stores (bytes + clobber owns + x0 + count). -/
def hitCmp32Extra (hashPtr : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  regOwns [.x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17] **
  bytesRegion WidxRecordsBase coverHitHash **
  bytesRegion hashPtr coverHitHash **
  (WidxCountLoc ↦ₘ (1 : Word))

private theorem hitCmp32Extra_pcFree (hashPtr : Word) :
    (hitCmp32Extra hashPtr).pcFree := by
  unfold hitCmp32Extra
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj pcFree_regOwn
          (pcFree_sepConj (pcFree_regOwns _)
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_memIs))))))

/-- After cmp32 eq at B+100: reshape into hit_from_a0eq pre ** extras, then ret.
    Fuel 18. Requires cur = hitLiveCur (live s-regs). -/
theorem hit_cmp32_post_to_ret
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 18 (B + 100) s.ra CR
      (((.x1 : Reg) ↦ᵣ (B + 100)) **
       widxCmp32EqPost WidxRecordsBase hashPtr coverHitHash **
       hitCmp32F spC s hashPtr outOff outLen **
       hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW) **
       hitCmp32Extra hashPtr) := by
  set cur := hitLiveCur hashPtr outOff outLen with hcur
  -- hit_from_a0eq with live cur; peel x5 own via of_forall
  have hcore0 : ∀ v5 : Word,
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
    intro v5
    exact hit_from_a0eq_to_ret sp0 spC s cur v5 outOff outLen offOld lenOld
      hspC hret (by simp [cur, hitLiveCur]) (by simp [cur, hitLiveCur])
      (by simp [cur, hitLiveCur])
  have hcoreOwn : cpsTripleWithin 18 (B + 100) s.ra CR
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
       hitBeqStoresF spC s cur outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW)) := by
    -- of_forall peels trailing own; reassoc x5 to trailing first
    have htrail : ∀ v5 : Word,
        cpsTripleWithin 18 (B + 100) s.ra CR
          (((( .x10 : Reg) ↦ᵣ (1 : Word)) **
            hitBeqStoresF spC s cur outOff outLen offOld lenOld) **
           ((.x5 : Reg) ↦ᵣ v5))
          (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
           (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
           (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
           (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
           frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
           (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
           (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
           ((.x5 : Reg) ↦ᵣ hitLenW)) := by
      intro v5
      exact cpsTripleWithin_weaken
        (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by xperm_chunked hq) (hcore0 v5)
    have hown := cpsTripleWithin_of_forall_regIs_to_regOwn htrail
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hown
  -- Frame extras through core
  have hcoreF := cpsTripleWithin_frameR (hitCmp32Extra hashPtr)
    (hitCmp32Extra_pcFree hashPtr) hcoreOwn
  -- Reshape cmp32 post+cells → core pre ** extras
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      -- Goal pre: x1 ** EqPost ** hitCmp32F ** cells
      -- Core pre framed: ((own x5 ** x10=1 ** hitBeqStoresF) ** Extra)
      simp only [widxCmp32EqPost, hitCmp32F, hitBeqStoresF, hitStoresF,
        hitCells, hitCmp32Extra, cur, hitLiveCur] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      -- frameR left-pair post; flatten
      simp only [hitCmp32Extra] at hq ⊢
      xperm_chunked hq) hcoreF

/-! ## cmp32 call + post→ret (fuel 294+18 = 312) -/

/-- Bytes ambient for equal-hash cmp32 (both sides coverHitHash). -/
def hitHashBytes (hashPtr : Word) : Assertion :=
  bytesRegion WidxRecordsBase coverHitHash **
  bytesRegion hashPtr coverHitHash

private theorem hitHashBytes_pcFree (hashPtr : Word) :
    (hitHashBytes hashPtr).pcFree := by
  unfold hitHashBytes
  exact pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)

/-- After ABI MVs at B+96: cmp32 eq + stores/epi → ret. Fuel 312.
    Ambient carries x0=0, hash bytes, and out/record cells. -/
theorem hit_cmp32_call_to_ret
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld raOld : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 312 (B + 96) s.ra CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x11 : Reg) ↦ᵣ hashPtr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       hitHashBytes hashPtr **
       hitCmp32F spC s hashPtr outOff outLen **
       hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW) **
       hitCmp32Extra hashPtr) := by
  -- cmp32 call framed with cells
  have hcall0 := hit_cmp32_eq_call spC s hashPtr outOff outLen raOld
    halignH hovH hvalidR hvalidH
  have hcallF := cpsTripleWithin_frameR
    (hitCells outOff outLen offOld lenOld)
    (hitCells_pcFree outOff outLen offOld lenOld) hcall0
  -- reshape call pre: left-pair → flat with EqPre unfolded
  have hcall : cpsTripleWithin 294 (B + 96) (B + 100) CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       ((.x10 : Reg) ↦ᵣ WidxRecordsBase) ** ((.x11 : Reg) ↦ᵣ hashPtr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       hitHashBytes hashPtr **
       hitCmp32F spC s hashPtr outOff outLen **
       hitCells outOff outLen offOld lenOld)
      (((.x1 : Reg) ↦ᵣ (B + 100)) **
       widxCmp32EqPost WidxRecordsBase hashPtr coverHitHash **
       hitCmp32F spC s hashPtr outOff outLen **
       hitCells outOff outLen offOld lenOld) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [widxCmp32EqPre, hitHashBytes] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hcallF
  have hpost := hit_cmp32_post_to_ret sp0 spC s hashPtr outOff outLen
    offOld lenOld hspC hret
  have c := cpsTripleWithin_seq_same_cr hcall hpost
  have hn : 294 + 18 = 312 := rfl
  rw [hn] at c
  exact c

/-- After record_ptr simple at B+84: ABI MVs + cmp32 + ret. Fuel 3+312 = 315. -/
theorem hit_after_record_to_ret
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld v22 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 315 (B + 84) s.ra CR
      (hitAfterRecordSimple spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW) **
       hitCmp32Extra hashPtr) := by
  have habi := hit_cmp_abi_mvs spC s hashPtr outOff outLen v22
  -- frame abi with x0 + bytes + cells
  have habiF := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** hitHashBytes hashPtr **
     hitCells outOff outLen offOld lenOld)
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (hitHashBytes_pcFree hashPtr)
          (hitCells_pcFree outOff outLen offOld lenOld))) habi
  have hcmp := hit_cmp32_call_to_ret sp0 spC s hashPtr outOff outLen
    offOld lenOld (B + 84) hspC hret
    halignH hovH hvalidR hvalidH
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    -- abi post ** (x0**bytes**cells) → cmp pre
    -- expand regOwns [x5,x6,x7,…] → own x5 ** own x6 ** own x7 ** …
    simp only [hitAfterCmpAbi, hitCmp32F, hitHashBytes, regOwns_cons,
      regOwns_nil] at hp ⊢
    xperm_chunked hp) habiF hcmp
  have hn : 3 + 312 = 315 := rfl
  rw [hn] at c
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) c

/-- At B+80 (a0=0 mid): record_ptr + ABI + cmp32 + ret. Fuel 8+315 = 323. -/
theorem hit_record_to_ret
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld raOld v22 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 323 (B + 80) s.ra CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       widxRecordPtrZeroPreAtoms **
       hitRecordPtrF spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW) **
       hitCmp32Extra hashPtr) := by
  -- record_ptr: PreAtoms already pins x10=0 via zeroIdxRf
  have hrp0 := hit_record_ptr_call_simple spC s hashPtr outOff outLen raOld
  have hrpF := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ v22) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     hitHashBytes hashPtr ** hitCells outOff outLen offOld lenOld)
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (hitHashBytes_pcFree hashPtr)
            (hitCells_pcFree outOff outLen offOld lenOld)))) hrp0
  have hrp : cpsTripleWithin 8 (B + 80) (B + 84) CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       widxRecordPtrZeroPreAtoms **
       hitRecordPtrF spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld)
      (hitAfterRecordSimple spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [hitAfterRecordSimple, widxRecordPtrZeroPostSimple] at hq ⊢
        xperm_chunked hq) hrpF
  have hrest := hit_after_record_to_ret sp0 spC s hashPtr outOff outLen
    offOld lenOld v22 hspC hret halignH hovH hvalidR hvalidH
  have c := cpsTripleWithin_seq_same_cr hrp hrest
  have hn : 8 + 315 = 323 := rfl
  rw [hn] at c
  exact c

/-! ## Live-ambient record_ptr (a0=0 only; preserves ABI x12-14) -/

/-- RegFile at B+80 for one-hit: a0=0, a2/a3/a4 = ABI copies, x5=count loc; other exposed 0. -/
def hitLiveRf (hashPtr outOff outLen : Word) : RegFile :=
  RegFile.set
    (RegFile.set
      (RegFile.set
        (RegFile.set
          (RegFile.set (fun _ : Reg => (0 : Word)) .x10 (0 : Word))
          .x5 WidxCountLoc)
        .x12 hashPtr)
      .x13 outOff)
    .x14 outLen

private theorem hitLiveRf_get_x5 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x5 = WidxCountLoc := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x6 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x6 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x7 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x7 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x28 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x28 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x29 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x29 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x30 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x30 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x31 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x31 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
theorem hitLiveRf_x10 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x10 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x11 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x11 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x12 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x12 = hashPtr := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x13 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x13 = outOff := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x14 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x14 = outLen := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x15 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x15 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x16 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x16 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]
private theorem hitLiveRf_get_x17 (hashPtr outOff outLen : Word) :
    (hitLiveRf hashPtr outOff outLen).get .x17 = (0 : Word) := by
  simp [hitLiveRf, RegFile.get, RegFile.set]

/-- callWithin record_ptr under live ABI temps (only a0 must be 0). Fuel 8.
    Post = `hitAfterRecordSimple` (matches a0zero flat post). -/
theorem hit_record_ptr_call_live
    (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raOld : Word) :
    cpsTripleWithin 8 (B + 80) (B + 84) CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       regAtoms (hitLiveRf hashPtr outOff outLen) exposedRegs **
       hitRecordPtrF spC s hashPtr outOff outLen)
      (hitAfterRecordSimple spC s hashPtr outOff outLen) := by
  have hmem : ∀ a i,
      CodeReq.singleton (B + 80) (.JAL .x1 recordPtrJalOff) a = some i →
        CR a = some i :=
    mem_at 20 (.JAL .x1 recordPtrJalOff) (B + 80)
      (by unfold B IndexedB; decide) (by decide) (by rfl)
  have h := widx_record_ptr_a0zero_callWithin_simple (B + 80) raOld
    (hitLiveRf hashPtr outOff outLen) recordPtrJalOff
    (hitRecordPtrF spC s hashPtr outOff outLen)
    (hitRecordPtrF_pcFree spC s hashPtr outOff outLen)
    (hitLiveRf_x10 hashPtr outOff outLen)
    record_ptr_jal_target hmem record_ptr_ret_even
  have hpc : (B + 80 : Word) + 4 = B + 84 := by unfold B IndexedB; decide
  -- a0zero post = x1 ** x10 ** owns ** F  ≡ hitAfterRecordSimple
  simpa [hpc, hitAfterRecordSimple] using h

/-- B+80 live → ret. Fuel 323. -/
theorem hit_record_to_ret_live
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld raOld v22 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 323 (B + 80) s.ra CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       regAtoms (hitLiveRf hashPtr outOff outLen) exposedRegs **
       hitRecordPtrF spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW) **
       hitCmp32Extra hashPtr) := by
  have hrp0 := hit_record_ptr_call_live spC s hashPtr outOff outLen raOld
  have hrpF := cpsTripleWithin_frameR
    (((.x22 : Reg) ↦ᵣ v22) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     hitHashBytes hashPtr ** hitCells outOff outLen offOld lenOld)
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (hitHashBytes_pcFree hashPtr)
            (hitCells_pcFree outOff outLen offOld lenOld)))) hrp0
  have hrp : cpsTripleWithin 8 (B + 80) (B + 84) CR
      (((.x1 : Reg) ↦ᵣ raOld) **
       regAtoms (hitLiveRf hashPtr outOff outLen) exposedRegs **
       hitRecordPtrF spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld)
      (hitAfterRecordSimple spC s hashPtr outOff outLen **
       ((.x22 : Reg) ↦ᵣ v22) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [hitAfterRecordSimple] at hq ⊢
        xperm_chunked hq) hrpF
  have hrest := hit_after_record_to_ret sp0 spC s hashPtr outOff outLen
    offOld lenOld v22 hspC hret halignH hovH hvalidR hvalidH
  have c := cpsTripleWithin_seq_same_cr hrp hrest
  have hn : 8 + 315 = 323 := rfl
  rw [hn] at c
  exact c

/-! ## loopHdr → B+80 → ret (count=1, mid=0) -/

/-- Exposed free temps zero at loopHdr (domain for live rf). -/
def hitExposedZeros : Assertion :=
  ((.x6 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ (0 : Word)) **
  ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ (0 : Word)) **
  ((.x16 : Reg) ↦ᵣ (0 : Word)) ** ((.x17 : Reg) ↦ᵣ (0 : Word)) **
  ((.x28 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
  ((.x30 : Reg) ↦ᵣ (0 : Word)) ** ((.x31 : Reg) ↦ᵣ (0 : Word))

private theorem hitExposedZeros_pcFree : hitExposedZeros.pcFree := by
  dsimp [hitExposedZeros]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs pcFree_regIs))))))))

/-- Shared ABI+count ambient at loopHdr (count=1). -/
def hitLoopCore (spC : Word) (_s : IndexedSaved)
    (hashPtr outOff outLen raMid : Word) : Assertion :=
  ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
  (WidxCountLoc ↦ₘ (1 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
  ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
  ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
  ((.x19 : Reg) ↦ᵣ (0 : Word)) **
  ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)

private theorem hitLoopCore_pcFree (spC : Word) (_s : IndexedSaved)
    (hashPtr outOff outLen raMid : Word) :
    (hitLoopCore spC _s hashPtr outOff outLen raMid).pcFree := by
  dsimp [hitLoopCore]
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj pcFree_regIs
                      (pcFree_sepConj pcFree_regIs pcFree_regIs))))))))))

/-- After mid+mv: core + a0=0 mid=0 + s6 + frame. -/
def hitAtRecord (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid s6 : Word) : Assertion :=
  hitLoopCore spC s hashPtr outOff outLen raMid **
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x21 : Reg) ↦ᵣ (0 : Word)) **
  ((.x22 : Reg) ↦ᵣ s6) **
  frameSlotsSaved indexedFrame spC (indexedSavedVals s)

/-- Expand `regAtoms (hitLiveRf …) exposedRegs` to concrete regIs chain.
    RHS parenthesized so `=` does not bind tighter than `**`. -/
theorem hitLiveRf_atoms (hashPtr outOff outLen : Word) :
    regAtoms (hitLiveRf hashPtr outOff outLen) exposedRegs =
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (0 : Word)) **
       ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ (0 : Word)) **
       ((.x31 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
       ((.x13 : Reg) ↦ᵣ outOff) ** ((.x14 : Reg) ↦ᵣ outLen) **
       ((.x15 : Reg) ↦ᵣ (0 : Word)) ** ((.x16 : Reg) ↦ᵣ (0 : Word)) **
       ((.x17 : Reg) ↦ᵣ (0 : Word)) ** empAssertion) := by
  simp only [exposedRegs, regAtoms_cons, regAtoms_nil]
  simp only [
    hitLiveRf_get_x5 hashPtr outOff outLen,
    hitLiveRf_get_x6 hashPtr outOff outLen,
    hitLiveRf_get_x7 hashPtr outOff outLen,
    hitLiveRf_get_x28 hashPtr outOff outLen,
    hitLiveRf_get_x29 hashPtr outOff outLen,
    hitLiveRf_get_x30 hashPtr outOff outLen,
    hitLiveRf_get_x31 hashPtr outOff outLen,
    hitLiveRf_x10 hashPtr outOff outLen,
    hitLiveRf_get_x11 hashPtr outOff outLen,
    hitLiveRf_get_x12 hashPtr outOff outLen,
    hitLiveRf_get_x13 hashPtr outOff outLen,
    hitLiveRf_get_x14 hashPtr outOff outLen,
    hitLiveRf_get_x15 hashPtr outOff outLen,
    hitLiveRf_get_x16 hashPtr outOff outLen,
    hitLiveRf_get_x17 hashPtr outOff outLen]

/-- BGEU ntaken + mid=0 + MV a0. Fuel 4. Leaves a0=0 mid=0 at B+80. -/
theorem hit_loopHdr_to_record
    (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen raMid v10 s5 s6 : Word) :
    cpsTripleWithin 4 loopHdrPc (B + 80) CR
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       hitLoopHdrAmb spC s v10 s5 s6)
      (hitAtRecord spC s hashPtr outOff outLen raMid s6) := by
  have hsp_sub : ((spC + 64 : Word) - 64) = spC := by
    have h : (64 : Word) + (-64 : Word) = (0 : Word) := by decide
    calc
      (spC + 64) - 64 = (spC + 64) + (-64) := by
        simp only [BitVec.sub_eq_add_neg]
      _ = spC + (64 + (-64)) := by ac_rfl
      _ = spC + 0 := by rw [h]
      _ = spC := by simp
  have hb0 := hit_bgeu_ntaken hashPtr outOff outLen raMid (spC + 64) WidxCountLoc
  have hb : cpsTripleWithin 1 (B + 64) (B + 68) CR
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC))
      (((.x19 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x8 : Reg) ↦ᵣ hashPtr) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) := by
    -- rewrite goal spC → (spC+64)-64 so it matches hb0
    rw [← hsp_sub]; exact hb0
  have hFb :
      (((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
       ((.x14 : Reg) ↦ᵣ outLen) ** hitLoopHdrAmb spC s v10 s5 s6).pcFree := by
    dsimp [hitLoopHdrAmb]
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs (pcFree_frameSlotsSaved _ _ _))))))
  have hbF := cpsTripleWithin_frameR _ hFb hb
  have hb' : cpsTripleWithin 1 (B + 64) (B + 68) CR
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       hitLoopHdrAmb spC s v10 s5 s6)
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       hitLoopHdrAmb spC s v10 s5 s6) :=
    cpsTripleWithin_weaken
      (fun _ hp => by dsimp [hitLoopCore, hitLoopHdrAmb] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by dsimp [hitLoopCore, hitLoopHdrAmb] at hq ⊢; xperm_chunked hq) hbF
  have hm0 := hit_mid_zero s5
  have hFm :
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x22 : Reg) ↦ᵣ s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s)).pcFree := by
    exact pcFree_sepConj (hitLoopCore_pcFree _ _ _ _ _ _)
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (pcFree_frameSlotsSaved _ _ _)))
  -- mid focuses x19 x20 x21; strip those from core for frame
  have hFm' :
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
       ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x22 : Reg) ↦ᵣ s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s)).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj pcFree_regIs
                      (pcFree_sepConj pcFree_regIs
                        (pcFree_sepConj pcFree_regIs
                          (pcFree_sepConj pcFree_regIs
                            (pcFree_frameSlotsSaved _ _ _))))))))))))
  have hmF := cpsTripleWithin_frameR _ hFm' hm0
  have hm' : cpsTripleWithin 2 (B + 68) (B + 76) CR
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       hitLoopHdrAmb spC s v10 s5 s6)
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ (0 : Word)) **
       ((.x22 : Reg) ↦ᵣ s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by dsimp [hitLoopCore, hitLoopHdrAmb] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by dsimp [hitLoopCore] at hq ⊢; xperm_chunked hq) hmF
  have ha0 := hit_mv_a0_mid v10
  have hFa' :
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       ((.x22 : Reg) ↦ᵣ s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s)).pcFree := by
    exact pcFree_sepConj (hitLoopCore_pcFree _ _ _ _ _ _)
      (pcFree_sepConj pcFree_regIs (pcFree_frameSlotsSaved _ _ _))
  -- MV focuses x10+x21; frame without those
  have hFa :
      (((.x5 : Reg) ↦ᵣ WidxCountLoc) ** ((.x20 : Reg) ↦ᵣ (1 : Word)) **
       (WidxCountLoc ↦ₘ (1 : Word)) **
       ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ hashPtr) **
       ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ outOff) **
       ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ outLen) **
       ((.x19 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC) **
       ((.x22 : Reg) ↦ᵣ s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s)).pcFree := by
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_memIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs
                (pcFree_sepConj pcFree_regIs
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj pcFree_regIs
                      (pcFree_sepConj pcFree_regIs
                        (pcFree_sepConj pcFree_regIs
                          (pcFree_sepConj pcFree_regIs
                            (pcFree_sepConj pcFree_regIs
                              (pcFree_frameSlotsSaved _ _ _)))))))))))))
  have haF := cpsTripleWithin_frameR _ hFa ha0
  have ha' : cpsTripleWithin 1 (B + 76) (B + 80) CR
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x21 : Reg) ↦ᵣ (0 : Word)) **
       ((.x22 : Reg) ↦ᵣ s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s))
      (hitAtRecord spC s hashPtr outOff outLen raMid s6) :=
    cpsTripleWithin_weaken
      (fun _ hp => by dsimp [hitLoopCore] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by dsimp [hitAtRecord, hitLoopCore] at hq ⊢; xperm_chunked hq) haF
  have c1 := cpsTripleWithin_seq_same_cr hb' hm'
  have hn1 : 1 + 2 = 3 := rfl
  rw [hn1] at c1
  have c2 := cpsTripleWithin_seq_same_cr c1 ha'
  have hn2 : 3 + 1 = 4 := rfl
  rw [hn2] at c2
  exact c2

/-- loopHdr → ret under live rf + exposed zeros. Fuel 4+323 = 327. -/
theorem hit_loopHdr_to_ret
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld raMid v10 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 327 loopHdrPc s.ra CR
      (hitLoopCore spC s hashPtr outOff outLen raMid **
       hitLoopHdrAmb spC s v10 s5 s6 **
       hitExposedZeros **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW) **
       hitCmp32Extra hashPtr) := by
  have hsetup := hit_loopHdr_to_record spC s hashPtr outOff outLen raMid v10 s5 s6
  have hsetupF := cpsTripleWithin_frameR
    (hitExposedZeros ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     hitHashBytes hashPtr ** hitCells outOff outLen offOld lenOld)
    (by
      exact pcFree_sepConj hitExposedZeros_pcFree
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (hitHashBytes_pcFree hashPtr)
            (hitCells_pcFree outOff outLen offOld lenOld)))) hsetup
  have hrec := hit_record_to_ret_live sp0 spC s hashPtr outOff outLen
    offOld lenOld raMid s6 hspC hret halignH hovH hvalidR hvalidH
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    -- setup post: hitAtRecord ** zeros ** x0 ** hash ** cells
    -- record pre: x1 ** liveAtoms ** hitRecordPtrF ** x22 ** x0 ** hash ** cells
    simp only [hitAtRecord, hitLoopCore, hitLiveRf_atoms, hitRecordPtrF,
      hitExposedZeros, hitHashBytes, hitCells, sepConj_emp_right'] at hp ⊢
    xperm_chunked hp) hsetupF hrec
  have hn : 4 + 323 = 327 := rfl
  rw [hn] at c
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) c

/-! ## bodyEntry → ret (setup + loopHdr path). Fuel 7+327 = 334. -/

/-- bodyEntry → ret under coverHit + live zeros. Fuel 334. -/
theorem hit_bodyEntry_to_ret
    (sp0 spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld raMid
      v8 v9 v18 v19 v5 v10 v20 s5 s6 : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 334 bodyEntryPc s.ra CR
      (((( (.x12 : Reg) ↦ᵣ hashPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
         ((.x13 : Reg) ↦ᵣ outOff) ** ((.x9 : Reg) ↦ᵣ v9) **
         ((.x14 : Reg) ↦ᵣ outLen) ** ((.x18 : Reg) ↦ᵣ v18) **
         ((.x19 : Reg) ↦ᵣ v19) **
         ((.x1 : Reg) ↦ᵣ raMid) ** ((.x2 : Reg) ↦ᵣ spC)) **
       hitMvAmb spC s v5 v10 v20 s5 s6) **
       hitExposedZeros **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       hitHashBytes hashPtr **
       hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
       (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
       (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
       frameSlotsSaved indexedFrame spC (indexedSavedVals s) **
       (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
       (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
       ((.x5 : Reg) ↦ᵣ hitLenW) **
       hitCmp32Extra hashPtr) := by
  have hsetup := hit_bodyEntry_to_loopHdr sp0 spC s hashPtr outOff outLen raMid
    v8 v9 v18 v19 v5 v10 v20 s5 s6 hspC
  have hsetupF := cpsTripleWithin_frameR
    (hitExposedZeros ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     hitHashBytes hashPtr ** hitCells outOff outLen offOld lenOld)
    (by
      exact pcFree_sepConj hitExposedZeros_pcFree
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (hitHashBytes_pcFree hashPtr)
            (hitCells_pcFree outOff outLen offOld lenOld)))) hsetup
  have hloop := hit_loopHdr_to_ret sp0 spC s hashPtr outOff outLen
    offOld lenOld raMid v10 s5 s6 hspC hret
    halignH hovH hvalidR hvalidH
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    -- setup post: (core ** loopHdrAmb) ** zeros ** x0 ** hash ** cells
    -- loop pre: core ** loopHdrAmb ** zeros ** x0 ** hash ** cells
    dsimp [hitLoopCore] at hp ⊢
    xperm_chunked hp) hsetupF hloop
  have hn : 7 + 327 = 334 := rfl
  rw [hn] at c
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) c

/-! ## Whole-routine one-hit top. Fuel 9+334 = 343. -/

/-- Whole-routine one-hit: coverHit record, a0=0, outs written.
    Domain: widx_count=1, target = sole record hash (coverHit).
    Frame regs x8/x9/x18-22 are `s.s*`; ABI a2-a4 + temps x5/x10 separate.
    Fuel 343 = prologue 9 + body 334. -/
theorem witness_lookup_by_hash_indexed_spec_within_one_hit
    (sp0 ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen offOld lenOld v5 v10 : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 343 B ret CR
      ((.x2 ↦ᵣ sp0) ** regsAt indexedFrame (indexedSavedVals { s with ra := ret }) **
        (.x12 ↦ᵣ hashPtr) ** (.x13 ↦ᵣ outOff) ** (.x14 ↦ᵣ outLen) **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        frameSlotsOwn indexedFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        (WidxCountLoc ↦ₘ (1 : Word)) **
        hitExposedZeros **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        hitHashBytes hashPtr **
        hitCells outOff outLen offOld lenOld)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved indexedFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (indexedSavedVals { s with ra := ret }) **
        (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
        (outOff ↦ₘ hitOffW) ** (outLen ↦ₘ hitLenW) **
        ((.x5 : Reg) ↦ᵣ hitLenW) **
        hitCmp32Extra hashPtr) := by
  set newSp := sp0 + signExtend12 (-64 : BitVec 12) with hNS
  let sRet : IndexedSaved := { s with ra := ret }
  have hsRet_ra : sRet.ra = ret := rfl
  -- Apro: non-frame temps only (frame regs live in regsAt)
  let Apro : Assertion :=
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen) **
    ((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ v10) **
    (WidxCountLoc ↦ₘ (1 : Word)) **
    hitExposedZeros **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    hitHashBytes hashPtr **
    hitCells outOff outLen offOld lenOld
  have hApro : Apro.pcFree := by
    dsimp [Apro]
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_memIs
                (pcFree_sepConj hitExposedZeros_pcFree
                  (pcFree_sepConj pcFree_regIs
                    (pcFree_sepConj (hitHashBytes_pcFree hashPtr)
                      (hitCells_pcFree outOff outLen offOld lenOld)))))))))
  have hpro := empty_prologue sp0 sRet Apro hApro
  -- body: live frame copies are s.s0..; raMid = ret
  have hbody := hit_bodyEntry_to_ret sp0 newSp sRet
    hashPtr outOff outLen offOld lenOld ret
    s.s0 s.s1 s.s2 s.s3 v5 v10 s.s4 s.s5 s.s6
    (by exact hNS) (by simpa [hsRet_ra] using halignRet)
    halignH hovH hvalidR hvalidH
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [← hNS, sRet, Apro, hitMvAmb, regsAt_indexedFrame] at hp ⊢
      xperm_chunked hp) hpro hbody
  have hn : 9 + 334 = 343 := rfl
  rw [hn] at c
  exact cpsTripleWithin_weaken
    (fun _ hp => by simp only [sRet] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by simp only [sRet] at hq ⊢; xperm_chunked hq) c

end EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
