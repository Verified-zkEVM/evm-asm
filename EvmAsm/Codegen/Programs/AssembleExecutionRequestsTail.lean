/-
  EvmAsm.Codegen.Programs.AssembleExecutionRequestsTail

  The return-value tail of `assemble_execution_requests` (#12206):
  instructions 67–79, i.e. `pc 67` → the `JALR` return.

    67   LI   x10, 20
    68   ADD  x10, x10, x11      -- + deposit len
    69   ADD  x10, x10, x13      -- + withdrawal len
    70   ADD  x10, x10, x15      -- + consolidation len
    71-72 la  x7, aer_bd_len
    73   LD   x28, 0(x7)
    74   ADD  x10, x10, x28      -- + builder-deposit len
    75-76 la  x7, aer_be_len
    77   LD   x28, 0(x7)
    78   ADD  x10, x10, x28      -- + builder-exit len
    79   JALR x0, 0(x1)

  `a0` on return is the total SSZ section length `20 + dl + wl + cl + bdl +
  bel` — the same running sum the header wrote, extended by the fifth body,
  recomputed from the registers and globals rather than carried in `x5`.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsHeader

namespace EvmAsm.Codegen.AssembleExecutionRequestsTail

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.AssembleExecutionRequestsBase
open EvmAsm.Codegen.AssembleExecutionRequestsHeader

set_option maxRecDepth 8000

/-- The routine's return value: the total SSZ `ExecutionRequests` section
    length, five offsets plus five bodies. -/
def aerTotal (dl wl cl bdl bel : Word) : Word := aerOff4 dl wl cl bdl + bel

local macro "pcfT" : tactic =>
  `(tactic| repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_emp
      | apply pcFree_sepConj)

/-- Tail working state: `a0` under construction, the two scratch registers,
    the three length arguments, `ra`, the two length globals, and an opaque
    pcFree ambient `F` (which carries the output region and everything else
    the tail does not touch). -/
def TS (dl wl cl bdl bel raVal : Word) (F : Assertion)
    (v10 v7 v28 : Word) : Assertion :=
  (.x10 ↦ᵣ v10) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
  (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x1 ↦ᵣ raVal) **
  (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F

theorem TS_pcFree (dl wl cl bdl bel raVal : Word) (F : Assertion) (hF : F.pcFree)
    (v10 v7 v28 : Word) : (TS dl wl cl bdl bel raVal F v10 v7 v28).pcFree := by
  simp only [TS]; pcfT; exact hF

/-! ## Address bridges -/

private theorem la_t_bd_hi :
    laHi GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 284) =
      Rv64.laHi (pc 71) BdLenA := by decide

private theorem la_t_bd_lo :
    laLo GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 284) =
      Rv64.laLo (pc 71) BdLenA := by decide

private theorem la_t_bd_range : laInRange (pc 71) BdLenA := by decide

private theorem la_t_be_hi :
    laHi GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 300) =
      Rv64.laHi (pc 75) BeLenA := by decide

private theorem la_t_be_lo :
    laLo GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 300) =
      Rv64.laLo (pc 75) BeLenA := by decide

private theorem la_t_be_range : laInRange (pc 75) BeLenA := by decide

private theorem beLenA_off0 : BeLenA + signExtend12 (0 : BitVec 12) = BeLenA := by decide
private theorem bdLenA_off0' : BdLenA + signExtend12 (0 : BitVec 12) = BdLenA := by decide

private theorem pc7172 : (pc 71 : Word) + 4 = pc 72 := by decide
private theorem pc7173 : (pc 71 : Word) + 8 = pc 73 := by decide
private theorem pc7576 : (pc 75 : Word) + 4 = pc 76 := by decide
private theorem pc7577 : (pc 75 : Word) + 8 = pc 77 := by decide

private theorem ra_off0 (raVal : Word) :
    (raVal + signExtend12 (0 : BitVec 12)) = raVal := by
  show raVal + (0 : Word) = raVal; exact BitVec.add_zero _

/-! ## The tail triple -/

/-- **The return-value tail.** Fuel 13, `pc 67` → `raVal &&& ~~~1`.

    Post: `a0 = 20 + dl + wl + cl + bdl + bel`, the total SSZ section
    length. -/
theorem aer_tail
    (dl wl cl bdl bel raVal v10 v7 v28 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 13 (pc 67) (raVal &&& ~~~1) aerCode
      (TS dl wl cl bdl bel raVal F v10 v7 v28)
      (TS dl wl cl bdl bel raVal F (aerTotal dl wl cl bdl bel) BeLenA bel) := by
  -- One accumulating `ADD x10, x10, rs2` step.
  have add_step : ∀ (j : Nat) (rs2 : Reg) (val addend : Word) (w7 w28 : Word)
      (Rest : Assertion), Rest.pcFree →
      (∀ a k, CodeReq.singleton (pc j) (.ADD .x10 .x10 rs2) a = some k → aerCode a = some k) →
      (∀ h, (TS dl wl cl bdl bel raVal F val w7 w28) h →
        (((.x10 ↦ᵣ val) ** (rs2 ↦ᵣ addend)) ** Rest) h) →
      (∀ h, (((.x10 ↦ᵣ (val + addend)) ** (rs2 ↦ᵣ addend)) ** Rest) h →
        (TS dl wl cl bdl bel raVal F (val + addend) w7 w28) h) →
      cpsTripleWithin 1 (pc j) (pc (j + 1)) aerCode
        (TS dl wl cl bdl bel raVal F val w7 w28)
        (TS dl wl cl bdl bel raVal F (val + addend) w7 w28) := by
    intro j rs2 val addend w7 w28 Rest hRest hmem hin hout
    have hcore := add_spec_gen_rd_eq_rs1_within .x10 rs2 val addend (pc j) (by decide)
    have hc := cpsTripleWithin_extend_code hmem hcore
    rw [pc_succ j] at hc
    exact cpsTripleWithin_weaken hin hout (cpsTripleWithin_frameR Rest hRest hc)
  -- 67: LI x10, 20
  have s67 : cpsTripleWithin 1 (pc 67) (pc 68) aerCode
      (TS dl wl cl bdl bel raVal F v10 v7 v28)
      (TS dl wl cl bdl bel raVal F aerOff0 v7 v28) := by
    have hcore := li_spec_gen_within .x10 v10 (20 : Word) (pc 67) (by decide)
    have hc := cpsTripleWithin_extend_code
      (mem_at 67 _ (pc 67) rfl (by rw [aerProgL_len]; norm_num) (by decide)) hcore
    rw [pc_succ 67] at hc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [TS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [TS, aerOff0] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) **
         (.x15 ↦ᵣ cl) ** (.x1 ↦ᵣ raVal) ** (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
        (by pcfT; exact hF) hc)
  have s68 := add_step 68 .x11 aerOff0 dl v7 v28
    ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
     (.x1 ↦ᵣ raVal) ** (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
    (by pcfT; exact hF)
    (mem_at 68 _ (pc 68) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [TS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [TS]; xperm_chunked hq)
  have s69 := add_step 69 .x13 (aerOff1 dl) wl v7 v28
    ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ dl) ** (.x15 ↦ᵣ cl) **
     (.x1 ↦ᵣ raVal) ** (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
    (by pcfT; exact hF)
    (mem_at 69 _ (pc 69) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [TS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [TS]; xperm_chunked hq)
  have s70 := add_step 70 .x15 (aerOff2 dl wl) cl v7 v28
    ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) **
     (.x1 ↦ᵣ raVal) ** (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
    (by pcfT; exact hF)
    (mem_at 70 _ (pc 70) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [TS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [TS]; xperm_chunked hq)
  -- 71-72: la x7, aer_bd_len
  have s71 : cpsTripleWithin 2 (pc 71) (pc 73) aerCode
      (TS dl wl cl bdl bel raVal F (aerOff3 dl wl cl) v7 v28)
      (TS dl wl cl bdl bel raVal F (aerOff3 dl wl cl) BdLenA v28) := by
    have hla := la_materialize_within (cr := aerCode) .x7 v7 (pc 71) BdLenA
      (by decide) la_t_bd_range
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 71)
            (.AUIPC .x7 (laHi GuestAddrs.aer_bd_len
              (GuestAddrs.assemble_execution_requests + 284))) a = some i := by
          rw [la_t_bd_hi]; exact hs
        exact mem_at 71 _ (pc 71) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 72)
            (.ADDI .x7 .x7 (laLo GuestAddrs.aer_bd_len
              (GuestAddrs.assemble_execution_requests + 284))) a = some i := by
          rw [la_t_bd_lo, ← pc7172]; exact hs
        exact mem_at 72 _ (pc 72) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    rw [pc7173] at hla
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [TS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [TS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x10 ↦ᵣ (aerOff3 dl wl cl)) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ dl) **
         (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x1 ↦ᵣ raVal) **
         (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
        (by pcfT; exact hF) hla)
  -- 73: LD x28, 0(x7)
  have s73 : cpsTripleWithin 1 (pc 73) (pc 74) aerCode
      (TS dl wl cl bdl bel raVal F (aerOff3 dl wl cl) BdLenA v28)
      (TS dl wl cl bdl bel raVal F (aerOff3 dl wl cl) BdLenA bdl) := by
    have hcore := ld_spec_gen_within .x28 .x7 BdLenA v28 bdl (0 : BitVec 12)
      (pc 73) (by decide)
    rw [bdLenA_off0'] at hcore
    have hc := cpsTripleWithin_extend_code
      (mem_at 73 _ (pc 73) rfl (by rw [aerProgL_len]; norm_num) (by decide)) hcore
    rw [pc_succ 73] at hc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [TS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [TS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x10 ↦ᵣ (aerOff3 dl wl cl)) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) **
         (.x15 ↦ᵣ cl) ** (.x1 ↦ᵣ raVal) ** (BeLenA ↦ₘ bel) ** F)
        (by pcfT; exact hF) hc)
  have s74 := add_step 74 .x28 (aerOff3 dl wl cl) bdl BdLenA bdl
    ((.x7 ↦ᵣ BdLenA) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
     (.x1 ↦ᵣ raVal) ** (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
    (by pcfT; exact hF)
    (mem_at 74 _ (pc 74) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [TS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [TS]; xperm_chunked hq)
  -- 75-76: la x7, aer_be_len
  have s75 : cpsTripleWithin 2 (pc 75) (pc 77) aerCode
      (TS dl wl cl bdl bel raVal F (aerOff4 dl wl cl bdl) BdLenA bdl)
      (TS dl wl cl bdl bel raVal F (aerOff4 dl wl cl bdl) BeLenA bdl) := by
    have hla := la_materialize_within (cr := aerCode) .x7 BdLenA (pc 75) BeLenA
      (by decide) la_t_be_range
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 75)
            (.AUIPC .x7 (laHi GuestAddrs.aer_be_len
              (GuestAddrs.assemble_execution_requests + 300))) a = some i := by
          rw [la_t_be_hi]; exact hs
        exact mem_at 75 _ (pc 75) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 76)
            (.ADDI .x7 .x7 (laLo GuestAddrs.aer_be_len
              (GuestAddrs.assemble_execution_requests + 300))) a = some i := by
          rw [la_t_be_lo, ← pc7576]; exact hs
        exact mem_at 76 _ (pc 76) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    rw [pc7577] at hla
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [TS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [TS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x10 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x28 ↦ᵣ bdl) ** (.x11 ↦ᵣ dl) **
         (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x1 ↦ᵣ raVal) **
         (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
        (by pcfT; exact hF) hla)
  -- 77: LD x28, 0(x7)
  have s77 : cpsTripleWithin 1 (pc 77) (pc 78) aerCode
      (TS dl wl cl bdl bel raVal F (aerOff4 dl wl cl bdl) BeLenA bdl)
      (TS dl wl cl bdl bel raVal F (aerOff4 dl wl cl bdl) BeLenA bel) := by
    have hcore := ld_spec_gen_within .x28 .x7 BeLenA bdl bel (0 : BitVec 12)
      (pc 77) (by decide)
    rw [beLenA_off0] at hcore
    have hc := cpsTripleWithin_extend_code
      (mem_at 77 _ (pc 77) rfl (by rw [aerProgL_len]; norm_num) (by decide)) hcore
    rw [pc_succ 77] at hc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [TS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [TS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x10 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) **
         (.x15 ↦ᵣ cl) ** (.x1 ↦ᵣ raVal) ** (BdLenA ↦ₘ bdl) ** F)
        (by pcfT; exact hF) hc)
  have s78 := add_step 78 .x28 (aerOff4 dl wl cl bdl) bel BeLenA bel
    ((.x7 ↦ᵣ BeLenA) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
     (.x1 ↦ᵣ raVal) ** (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
    (by pcfT; exact hF)
    (mem_at 78 _ (pc 78) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [TS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [TS]; xperm_chunked hq)
  -- 79: JALR x0, 0(x1) — return
  have s79 : cpsTripleWithin 1 (pc 79) (raVal &&& ~~~1) aerCode
      (TS dl wl cl bdl bel raVal F (aerTotal dl wl cl bdl bel) BeLenA bel)
      (TS dl wl cl bdl bel raVal F (aerTotal dl wl cl bdl bel) BeLenA bel) := by
    have hcore := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (pc 79)
    rw [ra_off0 raVal] at hcore
    have hc := cpsTripleWithin_extend_code
      (mem_at 79 _ (pc 79) rfl (by rw [aerProgL_len]; norm_num) (by decide)) hcore
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [TS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [TS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x10 ↦ᵣ (aerTotal dl wl cl bdl bel)) ** (.x7 ↦ᵣ BeLenA) ** (.x28 ↦ᵣ bel) **
         (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
         (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) ** F)
        (by pcfT; exact hF) hc)
  have c1 := cpsTripleWithin_seq_same_cr s67 s68
  have c2 := cpsTripleWithin_seq_same_cr c1 s69
  have c3 := cpsTripleWithin_seq_same_cr c2 s70
  have c4 := cpsTripleWithin_seq_same_cr c3 s71
  have c5 := cpsTripleWithin_seq_same_cr c4 s73
  have c6 := cpsTripleWithin_seq_same_cr c5 s74
  have c7 := cpsTripleWithin_seq_same_cr c6 s75
  have c8 := cpsTripleWithin_seq_same_cr c7 s77
  have c9 := cpsTripleWithin_seq_same_cr c8 s78
  have c10 := cpsTripleWithin_seq_same_cr c9 s79
  simpa only [aerTotal] using c10

end EvmAsm.Codegen.AssembleExecutionRequestsTail
