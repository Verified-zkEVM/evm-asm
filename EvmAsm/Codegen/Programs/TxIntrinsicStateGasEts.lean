/-
  Zeros ABI + LD is_creation + eip8037_tx_state_gas call + JAL epilogue
  (instr 28-38) for `tx_intrinsic_state_gas`.

  Proven leaf: eip8037_tx_state_gas (ets_zero_out_full) writes *out=0, a0=0.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasType
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.Eip8037TxStateGasSpec

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _)

abbrev LinkEts : Word := T + 152
abbrev AfterEtsJal : Word := T + 152
abbrev EtsEntry : Word := P

abbrev etsJalOff : BitVec 21 :=
  jalOff GuestAddrs.eip8037_tx_state_gas (GuestAddrs.tx_intrinsic_state_gas + 148)

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- LI x20,0; MV a0,x20; LI a1/a2/a3,0 (instr 28-32). -/
theorem tisEtsZeros (v20 v10 v11 v12 v13 : Word) :
    cpsTripleWithin 5 AfterTypeBne (T + 132) fullCode
      ((.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
      ((.x20 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word))) := by
  have h0 := li_spec_gen_within .x20 v20 (0 : Word) AfterTypeBne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T AfterTypeBne tisProg 28
        (.LI .x20 (0 : Word)) (by simp only [AfterTypeBne]; bv_omega)
        (by rw [tis_length]; decide) rfl (by rw [tis_length]; decide) a i hi)) h0
  have h1 := mv_spec_gen_within .x10 .x20 (0 : Word) v10 (T + 116) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 116) tisProg 29
        (.MV .x10 .x20) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) h1
  have h2 := li_spec_gen_within .x11 v11 (0 : Word) (T + 120) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 120) tisProg 30
        (.LI .x11 (0 : Word)) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) h2
  have h3 := li_spec_gen_within .x12 v12 (0 : Word) (T + 124) (by decide)
  have e3 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 124) tisProg 31
        (.LI .x12 (0 : Word)) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) h3
  have h4 := li_spec_gen_within .x13 v13 (0 : Word) (T + 128) (by decide)
  have e4 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 128) tisProg 32
        (.LI .x13 (0 : Word)) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) h4
  have e0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
    (by pcf) e0
  -- MV a0,x20 already pins x20=0; frame a1-a3 only
  have e1F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
    (by pcf) e1
  have e2F := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
    (by pcf) e2
  have e3F := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ v13))
    (by pcf) e3
  have e4F := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)))
    (by pcf) e4
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 e2F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 e3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 e4F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c04

/-- `la x5, tis_is_creation` at T+132 → T+140. -/
theorem tisLaIsCreationEts (v : Word) :
    cpsTripleWithin 2 (T + 132) (T + 140) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ IsCreationAddr) := by
  have hau : ∀ a i, CodeReq.singleton (T + 132)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 132)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 132) tisProg 33
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 132)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (T + 136)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 132)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 136) tisProg 34
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 132)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (T + 132) IsCreationAddr
    (by decide) (by decide) hau had
  rw [show (T + 132 : Word) + 8 = T + 140 from by bv_omega] at h
  exact h

/-- LD a4, 0(x5) is_creation (instr 35). -/
theorem tisEtsLdIsCreation (isCreationVal v14 : Word) :
    cpsTripleWithin 1 (T + 140) (T + 144) fullCode
      ((.x5 ↦ᵣ IsCreationAddr) ** (.x14 ↦ᵣ v14) **
        (IsCreationAddr ↦ₘ isCreationVal))
      ((.x5 ↦ᵣ IsCreationAddr) ** (.x14 ↦ᵣ isCreationVal) **
        (IsCreationAddr ↦ₘ isCreationVal)) := by
  have h0 := ld_spec_gen_within .x14 .x5 IsCreationAddr v14 isCreationVal
    (0 : BitVec 12) (T + 140) (by decide)
  rw [show IsCreationAddr + signExtend12 (0 : BitVec 12) = IsCreationAddr from by
    rw [se12_zero]; exact BitVec.add_zero IsCreationAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 140) tisProg 35
        (.LD .x14 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [tis_length]; decide) rfl (by rw [tis_length]; decide) a i hi)) h0
  have hpc : (T + 140 : Word) + 4 = T + 144 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- MV a5, s2 (outPtr) (instr 36). -/
theorem tisEtsMvOut (outPtr v15 : Word) :
    cpsTripleWithin 1 (T + 144) (T + 148) fullCode
      ((.x18 ↦ᵣ outPtr) ** (.x15 ↦ᵣ v15))
      ((.x18 ↦ᵣ outPtr) ** (.x15 ↦ᵣ outPtr)) := by
  have h0 := mv_spec_gen_within .x15 .x18 outPtr v15 (T + 144) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 144) tisProg 36
        (.MV .x15 .x18) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) h0
  have hpc : (T + 144 : Word) + 4 = T + 148 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- Callee footprint for ets (no ra). -/
def etsCalleeP (outPtr oldOut a2v a3v a4v t0Old : Word) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
  (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ t0Old) **
  (outPtr ↦ₘ oldOut) ** (.x0 ↦ᵣ (0 : Word))

def etsCalleeQ (outPtr a2v a3v a4v : Word) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
  (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (0 : Word)) **
  (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))

theorem etsCalleeP_pcFree (outPtr oldOut a2v a3v a4v t0Old : Word) :
    (etsCalleeP outPtr oldOut a2v a3v a4v t0Old).pcFree := by
  unfold etsCalleeP; pcf

set_option maxRecDepth 8000 in
/-- callWithin eip8037_tx_state_gas under proven zero_out (instr 37). -/
theorem tisEtsCall
    (outPtr oldOut a2v a3v a4v t0Old old1 : Word)
    (hret : (LinkEts &&& ~~~(1 : Word)) = LinkEts) :
    cpsTripleWithin (1 + 4) (T + 148) LinkEts fullCode
      ((.x1 ↦ᵣ old1) ** etsCalleeP outPtr oldOut a2v a3v a4v t0Old)
      ((.x1 ↦ᵣ LinkEts) ** etsCalleeQ outPtr a2v a3v a4v) := by
  have hcallee0 := ets_zero_out_full LinkEts outPtr oldOut a2v a3v a4v t0Old hret
  have hcallee : cpsTripleWithin 4 EtsEntry LinkEts fullCode
      ((.x1 ↦ᵣ LinkEts) ** etsCalleeP outPtr oldOut a2v a3v a4v t0Old)
      ((.x1 ↦ᵣ LinkEts) ** etsCalleeQ outPtr a2v a3v a4v) := by
    unfold etsCalleeP etsCalleeQ EtsEntry
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcall := callWithin_spec (T + 148) EtsEntry old1 etsJalOff 4
    (by show (T + 148) + signExtend21 etsJalOff = EtsEntry; decide)
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 148) tisProg 37
        (.JAL .x1 etsJalOff) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi))
    (etsCalleeP_pcFree outPtr oldOut a2v a3v a4v t0Old)
    hcallee
  rw [show (T + 148 + 4 : Word) = LinkEts from by
    simp only [LinkEts]; bv_omega] at hcall
  exact hcall

/-- JAL x0,+24 LinkEts → EpiRestore (instr 38). -/
theorem tisEtsJalEpi :
    cpsTripleWithin 1 LinkEts EpiRestore fullCode
      empAssertion empAssertion := by
  have h0 := jal_x0_spec_gen_within (24 : BitVec 21) LinkEts
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T LinkEts tisProg 38
        (.JAL .x0 (24 : BitVec 21))
        (by simp only [LinkEts]; bv_omega)
        (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) h0
  have hpc : LinkEts + signExtend21 (24 : BitVec 21) = EpiRestore := by
    simp only [LinkEts, EpiRestore, T]
    decide
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Full ets tail: AfterTypeBne → EpiRestore with *out=0, a0=0. -/
theorem tisEtsSuccess
    (outPtr oldOut isCreationVal v5 v10 v11 v12 v13 v14 v15 v20 old1 : Word)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts) :
    cpsTripleWithin (5 + 2 + 1 + 1 + (1 + 4) + 1) AfterTypeBne EpiRestore fullCode
      ((.x1 ↦ᵣ old1) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x18 ↦ᵣ outPtr) ** (.x20 ↦ᵣ v20) **
        (IsCreationAddr ↦ₘ isCreationVal) ** (outPtr ↦ₘ oldOut) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkEts) ** (.x5 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
        (.x14 ↦ᵣ isCreationVal) ** (.x15 ↦ᵣ outPtr) **
        (.x18 ↦ᵣ outPtr) ** (.x20 ↦ᵣ (0 : Word)) **
        (IsCreationAddr ↦ₘ isCreationVal) ** (outPtr ↦ₘ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  -- zeros
  have hz := tisEtsZeros v20 v10 v11 v12 v13
  have hzF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x5 ↦ᵣ v5) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
      (.x18 ↦ᵣ outPtr) **
      (IsCreationAddr ↦ₘ isCreationVal) ** (outPtr ↦ₘ oldOut) **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hz
  -- la is_creation into x5
  have hla := tisLaIsCreationEts v5
  have hlaF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x18 ↦ᵣ outPtr) **
      (.x20 ↦ᵣ (0 : Word)) **
      (IsCreationAddr ↦ₘ isCreationVal) ** (outPtr ↦ₘ oldOut) **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hla
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hzF hlaF
  -- LD a4
  have hld := tisEtsLdIsCreation isCreationVal v14
  have hldF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      (.x15 ↦ᵣ v15) ** (.x18 ↦ᵣ outPtr) ** (.x20 ↦ᵣ (0 : Word)) **
      (outPtr ↦ₘ oldOut) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) hld
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hldF
  -- MV a5,s2
  have hmv := tisEtsMvOut outPtr v15
  have hmvF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x5 ↦ᵣ IsCreationAddr) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      (.x14 ↦ᵣ isCreationVal) ** (.x20 ↦ᵣ (0 : Word)) **
      (IsCreationAddr ↦ₘ isCreationVal) ** (outPtr ↦ₘ oldOut) **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hmv
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hmvF
  -- call ets (t0Old = IsCreationAddr after la/ld)
  have hcall := tisEtsCall outPtr oldOut 0 0 isCreationVal IsCreationAddr old1 hlink
  have hcallF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x20 ↦ᵣ (0 : Word)) **
      (IsCreationAddr ↦ₘ isCreationVal)) (by pcf) hcall
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold etsCalleeP at *
    xperm_hyp hp) c03 hcallF
  -- JAL epi: frame ambient; cancel emp ** ambient
  let ambient : Assertion :=
    (.x1 ↦ᵣ LinkEts) ** (.x5 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
      (.x14 ↦ᵣ isCreationVal) ** (.x15 ↦ᵣ outPtr) **
      (.x18 ↦ᵣ outPtr) ** (.x20 ↦ᵣ (0 : Word)) **
      (IsCreationAddr ↦ₘ isCreationVal) ** (outPtr ↦ₘ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word))
  have hjal := tisEtsJalEpi
  have hjal0 := cpsTripleWithin_frameR ambient (by unfold ambient; pcf) hjal
  have hjalF : cpsTripleWithin 1 LinkEts EpiRestore fullCode ambient ambient := by
    exact cpsTripleWithin_weaken
      (fun h hp => by
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      hjal0
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold etsCalleeQ ambient at *
    xperm_hyp hp) c04 hjalF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by unfold ambient at hq; xperm_hyp hq) c05

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
