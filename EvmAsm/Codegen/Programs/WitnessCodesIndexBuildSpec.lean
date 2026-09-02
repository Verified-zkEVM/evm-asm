/-
  EvmAsm.Codegen.Programs.WitnessCodesIndexBuildSpec

  Builder-side composition for witness_codes_index_build.  The linked CodeReq,
  cells, reusable instruction triples, and concrete entry witness live in
  WitnessCodesLookupSpec; this module keeps the builder proof under the
  Codegen/Programs file-size cap.
-/

import EvmAsm.Codegen.Programs.WitnessCodesLookupSpec

namespace EvmAsm.Codegen.WitnessCodesLookupSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Evm64
open EvmAsm.Codegen

set_option maxRecDepth 8000

theorem wcb_builder_head_spec :
    cpsTripleWithin 5 (wcbB + 48) (wcbB + 68) wcbCr
      (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x8 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbEnabledLoc) ** regOwn .x5)
      (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
          (WcbEnabledLoc ↦ₘ (0 : Word)))) := by
  simpa using wcbBuilderInitHead (0x40000030 : Word) 0 0 0

theorem wcb_builder_status_len_spec (len : Word) :
    cpsTripleWithin 6 (wcbB + 68) (wcbB + 92) wcbCr
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbBuildStatusLoc **
        memOwn WcbBuildSectionLenLoc) ** regOwn .x5 ** ((.x9 : Reg) ↦ᵣ len))
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
        (WcbBuildSectionLenLoc ↦ₘ len) ** ((.x9 : Reg) ↦ᵣ len)) := by
  have h := wcbClearStorePair (wcbB + 68) WcbBuildStatusLoc
    WcbBuildSectionLenLoc len
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by decide) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
  rw [show (wcbB + 68 : Word) + 24 = wcbB + 92 by bv_omega] at h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => hq) h

theorem wcb_builder_count_lookup_spec :
    cpsTripleWithin 6 (wcbB + 92) (wcbB + 116) wcbCr
      (((((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbBuildCountLoc) **
        regOwn .x5) ** memOwn WcbLookupCallsLoc)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        (WcbBuildCountLoc ↦ₘ (0 : Word)) **
        (WcbLookupCallsLoc ↦ₘ (0 : Word))) := by
  have h := wcbClearPairReg (wcbB + 92) WcbBuildCountLoc WcbLookupCallsLoc
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by decide) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
  rw [show (wcbB + 92 : Word) + 24 = wcbB + 116 by bv_omega] at h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) h

def wcbBuilderPrefixPre : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x8 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbEnabledLoc **
    memOwn WcbBuildStatusLoc ** memOwn WcbBuildSectionLenLoc **
    memOwn WcbBuildCountLoc ** memOwn WcbLookupCallsLoc) ** regOwn .x5

def wcbBuilderPrefixPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
    (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
    (WcbBuildSectionLenLoc ↦ₘ (0 : Word)) **
    (WcbBuildCountLoc ↦ₘ (0 : Word)) **
    (WcbLookupCallsLoc ↦ₘ (0 : Word)))

theorem wcb_builder_prefix_spec :
    cpsTripleWithin 17 (wcbB + 48) (wcbB + 116) wcbCr
      wcbBuilderPrefixPre wcbBuilderPrefixPost := by
  have h1 := wcbBuilderInitHead (0x40000030 : Word) 0 0 0
  have h1f := cpsTripleWithin_frameR
    (memOwn WcbBuildStatusLoc ** memOwn WcbBuildSectionLenLoc **
      memOwn WcbBuildCountLoc ** memOwn WcbLookupCallsLoc) (by pcf) h1
  have h2 := wcb_builder_status_len_spec 0
  have h2f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
      ((WcbEnabledLoc ↦ₘ (0 : Word)) ** memOwn WcbBuildCountLoc **
        memOwn WcbLookupCallsLoc)) (by pcf) h2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h1f h2f
  have h3 := wcb_builder_count_lookup_spec
  have h3f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((WcbEnabledLoc ↦ₘ (0 : Word)) **
        (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
        (WcbBuildSectionLenLoc ↦ₘ (0 : Word)))) (by pcf) h3
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h12 h3f
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold wcbBuilderPrefixPre at hp
    xperm_chunked hp) (fun _ hq => by
    unfold wcbBuilderPrefixPost at ⊢
    xperm_chunked hq) h123

def wcbBuilderTelemetryPre : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
  memOwn WcbIndexedCallsLoc ** memOwn WcbIndexedHitsLoc **
  memOwn WcbIndexedMissesLoc ** memOwn WcbLinearCallsLoc **
  memOwn WcbLinearHitsLoc ** memOwn WcbLinearMissesLoc **
  memOwn WcbLinearIterationsLoc ** memOwn WcbLinearLastLenLoc

def wcbBuilderTelemetryPost : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
  (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
  (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
  (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
  (WcbLinearIterationsLoc ↦ₘ (0 : Word)) **
  (WcbLinearLastLenLoc ↦ₘ (0 : Word))

theorem wcb_builder_telemetry_spec :
    cpsTripleWithin 24 (wcbB + 116) (wcbB + 212) wcbCr
      wcbBuilderTelemetryPre wcbBuilderTelemetryPost := by
  have h1 := wcbClearPairReg (wcbB + 116) WcbIndexedCallsLoc WcbIndexedHitsLoc
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by decide) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
  have h1f := cpsTripleWithin_frameR
    (memOwn WcbIndexedMissesLoc ** memOwn WcbLinearCallsLoc **
      memOwn WcbLinearHitsLoc ** memOwn WcbLinearMissesLoc **
      memOwn WcbLinearIterationsLoc ** memOwn WcbLinearLastLenLoc) (by pcf) h1
  have h2 := wcbClearPairReg (wcbB + 140) WcbIndexedMissesLoc WcbLinearCallsLoc
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by decide) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
  have h2f := cpsTripleWithin_frameR
    ((WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      memOwn WcbLinearHitsLoc ** memOwn WcbLinearMissesLoc **
      memOwn WcbLinearIterationsLoc ** memOwn WcbLinearLastLenLoc) (by pcf) h2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h1f h2f
  have h3 := wcbClearPairReg (wcbB + 164) WcbLinearHitsLoc WcbLinearMissesLoc
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by decide) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
  have h3f := cpsTripleWithin_frameR
    ((WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      memOwn WcbLinearIterationsLoc ** memOwn WcbLinearLastLenLoc) (by pcf) h3
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h12 h3f
  have h4 := wcbClearPairReg (wcbB + 188) WcbLinearIterationsLoc WcbLinearLastLenLoc
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by decide) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
  have h4f := cpsTripleWithin_frameR
    ((WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word))) (by pcf) h4
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h123 h4f
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold wcbBuilderTelemetryPre at hp
    xperm_chunked hp) (fun _ hq => by
    unfold wcbBuilderTelemetryPost at ⊢
    xperm_chunked hq) h1234

theorem wcb_builder_max_spec :
    cpsTripleWithin 3 (wcbB + 212) (wcbB + 224) wcbCr
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbLinearMaxLenLoc ** regOwn .x5)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        (WcbLinearMaxLenLoc ↦ₘ (0 : Word))) := by
  have h := wcbClearOwnReg (wcbB + 212) WcbLinearMaxLenLoc
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 212 : Word) + 12 = wcbB + 224 by bv_omega] at h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => hq) h

def wcbBuilderTelemetryOwn : Assertion :=
  memOwn WcbIndexedCallsLoc ** memOwn WcbIndexedHitsLoc **
  memOwn WcbIndexedMissesLoc ** memOwn WcbLinearCallsLoc **
  memOwn WcbLinearHitsLoc ** memOwn WcbLinearMissesLoc **
  memOwn WcbLinearIterationsLoc ** memOwn WcbLinearLastLenLoc

def wcbBuilderStaticOwn : Assertion :=
  memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
  memOwn WcbCountLoc ** memOwn WcbLinearMaxLenLoc

theorem wcbStoreReg (A C : Word) (rs : Reg) (vData : Word)
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wcbCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wcbCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 rs (0 : BitVec 12)) a = some i →
      wcbCr a = some i) :
    cpsTripleWithin 3 A (A + 12) wcbCr
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn C) ** regOwn .x5 **
        (rs ↦ᵣ vData))
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        (C ↦ₘ vData) ** (rs ↦ᵣ vData)) := by
  have h : cpsTripleWithin 3 A (A + 12) wcbCr
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn C) ** regOwn .x5 **
        (rs ↦ᵣ vData))
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        (C ↦ₘ vData) ** (rs ↦ᵣ vData)) :=
    by
      have hraw := cpsTripleWithin_of_forall_regIs_to_regOwn
        (r := .x5)
        (P := (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn C) **
          (rs ↦ᵣ vData)) (fun vOld => by
        have hla := la_materialize_within .x5 vOld A C (by decide) hrange hau had
        have hstore := liftCode (cr' := wcbCr)
          (sd_spec_gen_own_within .x5 rs C vData (0 : BitVec 12) (A + 8)) hsd
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
          show C + (0 : Word) = C from by bv_omega,
          show (A + 8 : Word) + 4 = A + 12 from by bv_omega] at hstore
        have hla1 := cpsTripleWithin_frameR
          ((rs ↦ᵣ vData) ** memOwn C) (by pcf) hla
        have hf := cpsTripleWithin_frameL
          ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcf) hla1
        have hstore0 := cpsTripleWithin_frameL
          ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcf) hstore
        have hseq : cpsTripleWithin 3 A (A + 12) wcbCr
            (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (Reg.x5 ↦ᵣ vOld) **
              (rs ↦ᵣ vData) ** memOwn C)
            (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (Reg.x5 ↦ᵣ C) **
              (rs ↦ᵣ vData) ** (C ↦ₘ vData)) := by
          exact cpsTripleWithin_seq_same_cr hf hstore0
        exact cpsTripleWithin_mono_nSteps (show 3 ≤ 3 by omega)
          (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun s hq => by
              have hq1 : ((Reg.x5 ↦ᵣ C) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  (C ↦ₘ vData) ** (rs ↦ᵣ vData)) s := by
                xperm_hyp hq
              have hq2 := sepConj_mono (regIs_to_regOwn .x5 C)
                (fun _ hq' => hq') s hq1
              have hq3 : (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
                  (C ↦ₘ vData) ** (rs ↦ᵣ vData)) s := by
                xperm_hyp hq2
              exact hq3) hseq))
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hraw
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h

theorem wcb_empty_setup_spec :
    cpsTripleWithin 2 (wcbB + 392) (wcbB + 400) wcbCr
      (regOwn .x18 ** regOwn .x5)
      (((.x18 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (2 : Word))) := by
  have h1 := liftCode (cr' := wcbCr)
    (li_spec_gen_own_within .x18 (0 : Word) (wcbB + 392) (by decide))
    (by unfold wcbCr; code_mem)
  have h1f := cpsTripleWithin_frameR (regOwn .x5) (by pcf) h1
  have h2 := liftCode (cr' := wcbCr)
    (li_spec_gen_own_within .x5 (2 : Word) (wcbB + 396) (by decide))
    (by unfold wcbCr; code_mem)
  have h2f := cpsTripleWithin_frameR ((.x18 : Reg) ↦ᵣ (0 : Word))
    (by pcf) h2
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h1f h2f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

def wcbEmptySuccessPre (ptr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
  ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
  memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
  memOwn WcbEnabledLoc

def wcbEmptySuccessPost (ptr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ ptr) **
  ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
  (WcbSectionPtrLoc ↦ₘ ptr) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
  (WcbCountLoc ↦ₘ (0 : Word)) ** (WcbEnabledLoc ↦ₘ (1 : Word))

def wcbEmptySuccessPrefixPost (ptr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
  ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
  (WcbSectionPtrLoc ↦ₘ ptr) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
  (WcbCountLoc ↦ₘ (0 : Word)) ** memOwn WcbEnabledLoc

theorem wcb_empty_success_store_prefix_spec (ptr : Word) :
    cpsTripleWithin 24 (wcbB + 500) (wcbB + 536) wcbCr
      (wcbEmptySuccessPre ptr) (wcbEmptySuccessPrefixPost ptr) := by
  have h1 := wcbStoreReg (wcbB + 500) WcbSectionPtrLoc .x8 ptr
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 500 : Word) + 12 = wcbB + 512 by bv_omega] at h1
  have h1f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
      memOwn WcbEnabledLoc) (by pcf) h1
  have h2 := wcbStoreReg (wcbB + 512) WcbSectionLenLoc .x9 (0 : Word)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 512 : Word) + 12 = wcbB + 524 by bv_omega] at h2
  have h2f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x18 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** (WcbSectionPtrLoc ↦ₘ ptr) ** memOwn WcbCountLoc **
      memOwn WcbEnabledLoc) (by pcf) h2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h1f h2f
  have h3 := wcbStoreReg (wcbB + 524) WcbCountLoc .x18 (0 : Word)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 524 : Word) + 12 = wcbB + 536 by bv_omega] at h3
  have h3f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (WcbSectionPtrLoc ↦ₘ ptr) **
      (WcbSectionLenLoc ↦ₘ (0 : Word)) ** regOwn .x6 **
      memOwn WcbEnabledLoc) (by pcf) h3
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h12 h3f
  have h123w := cpsTripleWithin_weaken
    (P := ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbSectionPtrLoc) **
      regOwn .x5 ** ((.x8 : Reg) ↦ᵣ ptr)) ** ((.x10 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
      memOwn WcbEnabledLoc)
    (P' := wcbEmptySuccessPre ptr)
    (Q := (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      (WcbCountLoc ↦ₘ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word))) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (WcbSectionPtrLoc ↦ₘ ptr) **
      (WcbSectionLenLoc ↦ₘ (0 : Word)) ** regOwn .x6 ** memOwn WcbEnabledLoc)
    (Q' := wcbEmptySuccessPrefixPost ptr)
    (fun _ hp => by
      unfold wcbEmptySuccessPre at hp
      xperm_chunked hp)
    (fun s hq => by
      unfold wcbEmptySuccessPrefixPost
      xperm_chunked hq) h123
  exact cpsTripleWithin_mono_nSteps (show 3 + 3 + 3 ≤ 24 by omega) h123w

theorem wcb_empty_success_suffix_spec (ptr : Word) :
    cpsTripleWithin 12 (wcbB + 536) (wcbB + 580) wcbCr
      (wcbEmptySuccessPrefixPost ptr) (wcbEmptySuccessPost ptr) := by
  have h1 := liftCode (cr' := wcbCr)
    (li_spec_gen_own_within .x6 (1 : Word) (wcbB + 536) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 536 : Word) + 4 = wcbB + 540 by bv_omega] at h1
  have h1f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      (WcbSectionPtrLoc ↦ₘ ptr) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbCountLoc ↦ₘ (0 : Word)) ** memOwn WcbEnabledLoc) (by pcf) h1
  have h2 := wcbStoreReg (wcbB + 540) WcbEnabledLoc .x6 (1 : Word)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 540 : Word) + 12 = wcbB + 552 by bv_omega] at h2
  have h2f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
      (WcbSectionPtrLoc ↦ₘ ptr) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbCountLoc ↦ₘ (0 : Word))) (by pcf) h2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h1f h2f
  have h3 := liftCode (cr' := wcbCr)
    (li_spec_gen_within .x10 ptr (0 : Word) (wcbB + 552) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 552 : Word) + 4 = wcbB + 556 by bv_omega] at h3
  have h3f := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
      (WcbSectionPtrLoc ↦ₘ ptr) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbCountLoc ↦ₘ (0 : Word)) ** (WcbEnabledLoc ↦ₘ (1 : Word))) (by pcf) h3
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h12 h3f
  have h4 := liftCode (cr' := wcbCr)
    (jal_x0_spec_gen_within (24 : BitVec 21) (wcbB + 556))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 556 : Word) + signExtend21 (24 : BitVec 21) = wcbB + 580 by
    rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by decide]
    bv_omega] at h4
  have h4f := cpsTripleWithin_frameL
    (wcbEmptySuccessPost ptr) (by
      unfold wcbEmptySuccessPost
      pcf) h4
  rw [sepConj_emp_right'] at h4f
  unfold wcbEmptySuccessPost at h4f
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h123 h4f
  have hallw := cpsTripleWithin_weaken
    (P := (regOwn .x6 ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      (WcbSectionPtrLoc ↦ₘ ptr) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbCountLoc ↦ₘ (0 : Word)) ** memOwn WcbEnabledLoc))
    (P' := wcbEmptySuccessPrefixPost ptr)
    (Q := (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      ((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WcbSectionPtrLoc ↦ₘ ptr) **
      (WcbSectionLenLoc ↦ₘ (0 : Word)) ** (WcbCountLoc ↦ₘ (0 : Word)) **
      (WcbEnabledLoc ↦ₘ (1 : Word))))
    (Q' := wcbEmptySuccessPost ptr)
    (fun _ hp => by
      unfold wcbEmptySuccessPrefixPost at hp
      xperm_chunked hp)
    (fun _ hq => by
      unfold wcbEmptySuccessPost
      xperm_chunked hq) hall
  exact cpsTripleWithin_mono_nSteps (show 1 + 3 + 1 + 1 ≤ 12 by omega) hallw

def wcbEmptyBranchPre (ptr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
  ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
  regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
  memOwn WcbCountLoc ** memOwn WcbEnabledLoc

theorem wcb_empty_bltu_success_spec (ptr : Word) :
    cpsTripleWithin 1 (wcbB + 400) (wcbB + 500) wcbCr
      (wcbEmptyBranchPre ptr) (wcbEmptySuccessPre ptr) := by
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (generic_bltu_spec_within .x18 .x5
      (brOff (GuestAddrs.witness_codes_index_build + 500)
        (GuestAddrs.witness_codes_index_build + 400))
      (0 : Word) (2 : Word) (wcbB + 400))
  have h_absurd : ∀ hp,
      (((.x18 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (2 : Word)) **
        ⌜¬BitVec.ult (0 : Word) (2 : Word)⌝) hp → False := by
    intro hp hq
    obtain ⟨_, _, _, _, _, hB⟩ := hq
    obtain ⟨_, _, _, _, _, hP⟩ := hB
    have h := hP.2
    simp only [BitVec.ult, decide_eq_true_eq,
      show (0 : Word).toNat = 0 from by decide] at h
    simp at h
  have hbt := cpsBranchWithin_takenStripPure2 hbr h_absurd
  rw [show (wcbB + 400 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_index_build + 500)
        (GuestAddrs.witness_codes_index_build + 400)) = wcbB + 500 from by decide] at hbt
  have hbtF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
      memOwn WcbCountLoc ** memOwn WcbEnabledLoc) (by pcf) hbt
  exact cpsTripleWithin_weaken
    (P := (((.x18 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (2 : Word))) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
        memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (P' := wcbEmptyBranchPre ptr)
    (Q := (((.x18 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (2 : Word))) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
        memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (Q' := wcbEmptySuccessPre ptr)
    (fun _ hp => by
      unfold wcbEmptyBranchPre at hp
      xperm_chunked hp)
    (fun s hq => by
      have hq1 : (((.x5 : Reg) ↦ᵣ (2 : Word)) **
          (((.x18 : Reg) ↦ᵣ (0 : Word)) **
            (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
              ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
              memOwn WcbCountLoc ** memOwn WcbEnabledLoc))) s := by
        xperm_chunked hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x5 (2 : Word))
        (fun _ hh => hh) s hq1
      unfold wcbEmptySuccessPre
      xperm_chunked hq2) hbtF

theorem wcb_empty_success_path_spec (ptr : Word) :
    cpsTripleWithin 8 (wcbB + 392) (wcbB + 500) wcbCr
      (regOwn .x18 ** regOwn .x5 **
        (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
          ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
          memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
      (wcbEmptySuccessPre ptr) := by
  have hs := wcb_empty_setup_spec
  have hsf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
      memOwn WcbCountLoc ** memOwn WcbEnabledLoc) (by pcf) hs
  have hsb := cpsTripleWithin_weaken
    (P := (regOwn .x18 ** regOwn .x5) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
        memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (P' := (regOwn .x18 ** regOwn .x5) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
        memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (Q := (((.x18 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (2 : Word))) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
        memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (Q' := wcbEmptyBranchPre ptr)
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      unfold wcbEmptyBranchPre
      xperm_chunked hq) hsf
  have hall := cpsTripleWithin_seq_same_cr hsb
    (wcb_empty_bltu_success_spec ptr)
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 ≤ 8 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => hq) hall)

def wcbFailurePre (ptr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
  ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
  memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
  memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc

def wcbFailurePost (ptr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x8 : Reg) ↦ᵣ ptr) **
  ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
  (WcbBuildStatusLoc ↦ₘ (1 : Word)) ** memOwn WcbSectionPtrLoc **
  memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc

def wcbFailureStart (ptr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
  ((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
  (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
  (WcbBuildSectionLenLoc ↦ₘ (1 : Word)) ** memOwn WcbSectionPtrLoc **
  memOwn WcbSectionLenLoc ** memOwn WcbCountLoc

theorem wcb_failure_suffix_spec (ptr : Word) :
    cpsTripleWithin 12 (wcbB + 560) (wcbB + 580) wcbCr
      (wcbFailurePre ptr) (wcbFailurePost ptr) := by
  have h1 := liftCode (cr' := wcbCr)
    (li_spec_gen_own_within .x6 (1 : Word) (wcbB + 560) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 560 : Word) + 4 = wcbB + 564 by bv_omega] at h1
  have h1f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc) (by pcf) h1
  have h2 := wcbStoreReg (wcbB + 564) WcbBuildStatusLoc .x6 (1 : Word)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 564 : Word) + 12 = wcbB + 576 by bv_omega] at h2
  have h2f := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
      memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
      memOwn WcbCountLoc ** memOwn WcbEnabledLoc) (by pcf) h2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h1f h2f
  have h3 := liftCode (cr' := wcbCr)
    (li_spec_gen_within .x10 ptr (1 : Word) (wcbB + 576) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 576 : Word) + 4 = wcbB + 580 by bv_omega] at h3
  have h3f := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ (1 : Word)) **
      regOwn .x18 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
      (WcbBuildStatusLoc ↦ₘ (1 : Word)) ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc) (by pcf) h3
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h12 h3f
  have hallw := cpsTripleWithin_weaken
    (P := (regOwn .x6 ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (P' := wcbFailurePre ptr)
    (Q := (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
      (WcbBuildStatusLoc ↦ₘ (1 : Word)) ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (Q' := wcbFailurePost ptr)
    (fun _ hp => by
      unfold wcbFailurePre at hp
      xperm_chunked hp)
    (fun _ hq => by
      unfold wcbFailurePost
      xperm_chunked hq) hall
  exact cpsTripleWithin_mono_nSteps (show 1 + 3 + 1 ≤ 12 by omega) hallw

theorem wcb_failure_path_spec (ptr : Word) :
    cpsTripleWithin 20 (wcbB + 228) (wcbB + 580) wcbCr
      (wcbFailurePre ptr) (wcbFailurePost ptr) := by
  have hli := liftCode (cr' := wcbCr)
    (li_spec_gen_own_within .x5 (4 : Word) (wcbB + 228) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 228 : Word) + 4 = wcbB + 232 by bv_omega] at hli
  have hliF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 **
      memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc) (by pcf) hli
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (generic_bltu_spec_within .x9 .x5
      (brOff (GuestAddrs.witness_codes_index_build + 560)
        (GuestAddrs.witness_codes_index_build + 232))
      (1 : Word) (4 : Word) (wcbB + 232))
  have h_absurd : ∀ hp,
      (((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x5 : Reg) ↦ᵣ (4 : Word)) **
        ⌜¬BitVec.ult (1 : Word) (4 : Word)⌝) hp → False := by
    intro hp hq
    obtain ⟨_, _, _, _, _, hB⟩ := hq
    obtain ⟨_, _, _, _, _, hP⟩ := hB
    have h := hP.2
    simp only [BitVec.ult, decide_eq_true_eq,
      show (1 : Word).toNat = 1 from by decide,
      show (4 : Word).toNat = 4 from by decide] at h
    simp at h
  have hbt := cpsBranchWithin_takenStripPure2 hbr h_absurd
  rw [show (wcbB + 232 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_index_build + 560)
        (GuestAddrs.witness_codes_index_build + 232)) = wcbB + 560 from by decide] at hbt
  have hbtF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      regOwn .x18 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 **
      memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc) (by pcf) hbt
  have hmid0 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hbtF
  have hmid := cpsTripleWithin_weaken
    (P := (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 **
      memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (P' := wcbFailurePre ptr)
    (Q := ((((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x5 : Reg) ↦ᵣ (4 : Word))) **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
        regOwn .x18 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
        memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc)))
    (Q' := wcbFailurePre ptr)
    (fun _ hp => by
      unfold wcbFailurePre at hp
      xperm_chunked hp)
    (fun s hq => by
      have hq1 : (((.x5 : Reg) ↦ᵣ (4 : Word)) **
          (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
            ((.x9 : Reg) ↦ᵣ (1 : Word)) ** regOwn .x18 **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 **
            memOwn WcbBuildStatusLoc ** memOwn WcbSectionPtrLoc **
            memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbEnabledLoc)) s := by
        xperm_chunked hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x5 (4 : Word))
        (fun _ hh => hh) s hq1
      unfold wcbFailurePre
      xperm_chunked hq2) hmid0
  have hall := cpsTripleWithin_seq_same_cr hmid (wcb_failure_suffix_spec ptr)
  exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 12 ≤ 20 by omega) hall

def wcbBuilderInitPre : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x8 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbEnabledLoc **
    memOwn WcbBuildStatusLoc ** memOwn WcbBuildSectionLenLoc **
    memOwn WcbBuildCountLoc ** memOwn WcbLookupCallsLoc **
    wcbBuilderTelemetryOwn ** memOwn WcbSectionPtrLoc **
    memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
    memOwn WcbLinearMaxLenLoc) ** regOwn .x5

def wcbBuilderInitPost : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
    (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
    (WcbBuildSectionLenLoc ↦ₘ (0 : Word)) **
    (WcbBuildCountLoc ↦ₘ (0 : Word)) **
    (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
    (WcbIndexedCallsLoc ↦ₘ (0 : Word)) **
    (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
    (WcbIndexedMissesLoc ↦ₘ (0 : Word)) **
    (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
    (WcbLinearHitsLoc ↦ₘ (0 : Word)) **
    (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
    (WcbLinearIterationsLoc ↦ₘ (0 : Word)) **
    (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
    memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
    (WcbLinearMaxLenLoc ↦ₘ (0 : Word)))

theorem wcb_builder_initialization_spec :
    cpsTripleWithin 44 (wcbB + 48) (wcbB + 224) wcbCr
      wcbBuilderInitPre wcbBuilderInitPost := by
  have hp := wcb_builder_prefix_spec
  have hpf := cpsTripleWithin_frameR
    (wcbBuilderTelemetryOwn ** wcbBuilderStaticOwn) (by pcf) hp
  have ht := wcb_builder_telemetry_spec
  have htf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
      (WcbBuildSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbBuildCountLoc ↦ₘ (0 : Word)) ** (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
      wcbBuilderStaticOwn)
    (by pcf) ht
  have hpt := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold wcbBuilderPrefixPost wcbBuilderTelemetryOwn wcbBuilderStaticOwn at hp
      unfold wcbBuilderTelemetryPre wcbBuilderStaticOwn
      xperm_chunked hp) hpf htf
  have hm := wcb_builder_max_spec
  have hmf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
      (WcbBuildSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbBuildCountLoc ↦ₘ (0 : Word)) **
      (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) **
      (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      (WcbLinearHitsLoc ↦ₘ (0 : Word)) **
      (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
      (WcbLinearIterationsLoc ↦ₘ (0 : Word)) **
      (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
      memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc)
    (by pcf) hm
  have hptm := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold wcbBuilderTelemetryPost wcbBuilderStaticOwn at hp
      xperm_hyp hp) hpt hmf
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold wcbBuilderInitPre wcbBuilderTelemetryOwn at hp
    unfold wcbBuilderPrefixPre wcbBuilderTelemetryOwn wcbBuilderStaticOwn
    xperm_hyp hp) (fun _ hq => by
    unfold wcbBuilderInitPost
    xperm_hyp hq) hptm

def wcbBuilderInitPreLen (len : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ len) **
  ((.x8 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WcbEnabledLoc **
    memOwn WcbBuildStatusLoc ** memOwn WcbBuildSectionLenLoc **
    memOwn WcbBuildCountLoc ** memOwn WcbLookupCallsLoc **
    wcbBuilderTelemetryOwn ** memOwn WcbSectionPtrLoc **
    memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** memOwn WcbLinearMaxLenLoc) **
  regOwn .x5 ** regOwn .x18 ** regOwn .x6

def wcbBuilderInitPostLen (len : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ len) **
  ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ len) **
  (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x18 ** regOwn .x6 **
    (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
    (WcbBuildSectionLenLoc ↦ₘ len) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
    (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
    (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
    (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
    (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
    (WcbLinearIterationsLoc ↦ₘ (0 : Word)) **
    (WcbLinearLastLenLoc ↦ₘ (0 : Word)) ** memOwn WcbSectionPtrLoc **
    memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
    (WcbLinearMaxLenLoc ↦ₘ (0 : Word)))

theorem wcb_builder_initialization_spec_len (len : Word) :
    cpsTripleWithin 44 (wcbB + 48) (wcbB + 224) wcbCr
      (wcbBuilderInitPreLen len) (wcbBuilderInitPostLen len) := by
  have hp := wcbBuilderInitHead (0x40000030 : Word) len 0 0
  have hpf := cpsTripleWithin_frameR
    (memOwn WcbBuildStatusLoc ** memOwn WcbBuildSectionLenLoc **
      memOwn WcbBuildCountLoc ** memOwn WcbLookupCallsLoc **
      wcbBuilderTelemetryOwn ** wcbBuilderStaticOwn ** regOwn .x18 ** regOwn .x6)
    (by pcf) hp
  have hs := wcb_builder_status_len_spec len
  have hsf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** memOwn WcbBuildCountLoc **
      memOwn WcbLookupCallsLoc ** wcbBuilderTelemetryOwn **
      wcbBuilderStaticOwn ** regOwn .x18 ** regOwn .x6) (by pcf) hs
  have hps := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hpf hsf
  have hc := wcb_builder_count_lookup_spec
  have hcf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ len) **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
      (WcbBuildSectionLenLoc ↦ₘ len) ** wcbBuilderTelemetryOwn **
      wcbBuilderStaticOwn ** regOwn .x18 ** regOwn .x6) (by pcf) hc
  have hpsc := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hps hcf
  have ht := wcb_builder_telemetry_spec
  have htf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ len) **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
      (WcbBuildSectionLenLoc ↦ₘ len) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
      (WcbLookupCallsLoc ↦ₘ (0 : Word)) ** wcbBuilderStaticOwn **
      regOwn .x18 ** regOwn .x6) (by pcf) ht
  have hpsct := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold wcbBuilderTelemetryPre wcbBuilderStaticOwn
      unfold wcbBuilderTelemetryOwn wcbBuilderStaticOwn at hp
      xperm_chunked hp) hpsc htf
  have hm := wcb_builder_max_spec
  have hmf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ len) **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
      (WcbBuildSectionLenLoc ↦ₘ len) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
      (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
      (WcbLinearIterationsLoc ↦ₘ (0 : Word)) **
      (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
      memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
      regOwn .x18 ** regOwn .x6) (by pcf) hm
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold wcbBuilderTelemetryPost wcbBuilderStaticOwn at hp
      xperm_chunked hp) hpsct hmf
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [wcbBuilderInitPreLen,
      wcbBuilderTelemetryOwn, wcbBuilderStaticOwn] at hp ⊢
    xperm_chunked hp) (fun _ hq => by
    simp only [wcbBuilderInitPostLen] at hq ⊢
    xperm_chunked hq) hall

theorem wcb_empty_success_full_spec (ptr : Word) :
    cpsTripleWithin 44 (wcbB + 392) (wcbB + 580) wcbCr
      (wcbEmptyBranchPre ptr) (wcbEmptySuccessPost ptr) := by
  have hpath := wcb_empty_success_path_spec ptr
  have hpathw := cpsTripleWithin_weaken
    (P := regOwn .x18 ** regOwn .x5 **
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
        memOwn WcbCountLoc ** memOwn WcbEnabledLoc))
    (P' := wcbEmptyBranchPre ptr)
    (Q := wcbEmptySuccessPre ptr) (Q' := wcbEmptySuccessPre ptr)
    (fun s hq => by
      have hq1 : ((((.x18 : Reg) ↦ᵣ (0 : Word)) **
          ((.x5 : Reg) ↦ᵣ (2 : Word))) **
          (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
            ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
            memOwn WcbCountLoc ** memOwn WcbEnabledLoc)) s := by
        unfold wcbEmptyBranchPre at hq
        xperm_chunked hq
      have hq2 : (((.x18 : Reg) ↦ᵣ (0 : Word)) **
          (((.x5 : Reg) ↦ᵣ (2 : Word)) **
            (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
              ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
              memOwn WcbCountLoc ** memOwn WcbEnabledLoc))) s := by
        xperm_chunked hq1
      have hq3 := sepConj_mono (regIs_to_regOwn .x18 (0 : Word))
        (sepConj_mono (regIs_to_regOwn .x5 (2 : Word)) (fun _ hh => hh)) s hq2
      xperm_chunked hq3)
    (fun _ hq => hq) hpath
  have hstore := wcb_empty_success_store_prefix_spec ptr
  have hmid := cpsTripleWithin_seq_same_cr hpathw hstore
  have htail := wcb_empty_success_suffix_spec ptr
  have hfull := cpsTripleWithin_seq_same_cr hmid htail
  exact cpsTripleWithin_mono_nSteps (show 8 + 24 + 12 ≤ 44 by omega) hfull

private theorem wcb_beq_same_absurd {r1 r2 : Reg} {v : Word} :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ v) ** ⌜v ≠ v⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact hP.2 rfl

private theorem wcb_beq_one_zero_absurd :
    ∀ hp, (((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜(1 : Word) = (0 : Word)⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact (by decide : (1 : Word) ≠ (0 : Word)) hP.2

theorem wcb_builder_empty_branch_spec :
    cpsTripleWithin 1 (wcbB + 224) (wcbB + 392) wcbCr
      (wcbBuilderInitPostLen 0) (wcbBuilderInitPostLen 0) := by
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (generic_beq_spec_within .x9 .x0
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224))
      (0 : Word) (0 : Word) (wcbB + 224))
  have hbt := cpsBranchWithin_takenStripPure2 hbr
    (wcb_beq_same_absurd (r1 := .x9) (r2 := .x0) (v := (0 : Word)))
  rw [show (wcbB + 224 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224)) = wcbB + 392 from by decide] at hbt
  have hbtF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** regOwn .x5 ** regOwn .x18 ** regOwn .x6 **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
      (WcbBuildSectionLenLoc ↦ₘ (0 : Word)) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
      (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
      (WcbLinearIterationsLoc ↦ₘ (0 : Word)) ** (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
      memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
      (WcbLinearMaxLenLoc ↦ₘ (0 : Word))) (by pcf) hbt
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [wcbBuilderInitPostLen] at hp
    xperm_chunked hp) (fun _ hq => by
    simp only [wcbBuilderInitPostLen]
    xperm_chunked hq) hbtF

theorem wcb_builder_nonempty_branch_spec :
    cpsTripleWithin 1 (wcbB + 224) (wcbB + 228) wcbCr
      (wcbBuilderInitPostLen 1) (wcbBuilderInitPostLen 1) := by
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (generic_beq_spec_within .x9 .x0
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224))
      (1 : Word) (0 : Word) (wcbB + 224))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr wcb_beq_one_zero_absurd
  rw [show (wcbB + 224 : Word) + 4 = wcbB + 228 from by bv_omega] at hnt
  have hntF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (1 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** regOwn .x5 ** regOwn .x18 ** regOwn .x6 **
      (WcbEnabledLoc ↦ₘ (0 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
      (WcbBuildSectionLenLoc ↦ₘ (1 : Word)) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
      (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
      (WcbLinearIterationsLoc ↦ₘ (0 : Word)) ** (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
      memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
      (WcbLinearMaxLenLoc ↦ₘ (0 : Word))) (by pcf) hnt
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [wcbBuilderInitPostLen] at hp
    xperm_chunked hp) (fun _ hq => by
    simp only [wcbBuilderInitPostLen]
    xperm_chunked hq) hntF

def wcbEmptyPathPre (ptr : Word) : Assertion :=
  regOwn .x18 ** regOwn .x5 **
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
      memOwn WcbCountLoc ** memOwn WcbEnabledLoc)

def wcbBuilderBranchFrame (len : Word) : Assertion :=
  ((.x11 : Reg) ↦ᵣ len) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
  (WcbBuildSectionLenLoc ↦ₘ len) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
  (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
  (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
  (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
  (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
  (WcbLinearIterationsLoc ↦ₘ (0 : Word)) **
  (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
  (WcbLinearMaxLenLoc ↦ₘ (0 : Word))

def wcbBuilderFailureFrame (len : Word) : Assertion :=
  ((.x11 : Reg) ↦ᵣ len) **
  (WcbBuildSectionLenLoc ↦ₘ len) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
  (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
  (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
  (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
  (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
  (WcbLinearIterationsLoc ↦ₘ (0 : Word)) **
  (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
  (WcbLinearMaxLenLoc ↦ₘ (0 : Word))

theorem wcb_empty_success_full_path_spec (ptr : Word) :
    cpsTripleWithin 44 (wcbB + 392) (wcbB + 580) wcbCr
      (wcbEmptyPathPre ptr) (wcbEmptySuccessPost ptr) := by
  have hpath := wcb_empty_success_path_spec ptr
  have hpathw := cpsTripleWithin_weaken (fun _ hp => by
    simpa only [wcbEmptyPathPre] using hp) (fun _ hq => hq) hpath
  have hmid := cpsTripleWithin_seq_same_cr hpathw
    (wcb_empty_success_store_prefix_spec ptr)
  have hfull := cpsTripleWithin_seq_same_cr hmid
    (wcb_empty_success_suffix_spec ptr)
  exact cpsTripleWithin_mono_nSteps (show 8 + 24 + 12 ≤ 44 by omega) hfull

theorem wcb_builder_empty_path_spec :
    cpsTripleWithin 45 (wcbB + 224) (wcbB + 580) wcbCr
      (wcbBuilderInitPostLen 0)
      (wcbEmptySuccessPost (0x40000030 : Word) ** wcbBuilderBranchFrame 0) := by
  have hbranch := wcb_builder_empty_branch_spec
  have hfull := wcb_empty_success_full_path_spec (0x40000030 : Word)
  have hframe := cpsTripleWithin_frameR (wcbBuilderBranchFrame 0)
    (by pcf) hfull
  have hbranch' := cpsTripleWithin_weaken
    (P := wcbBuilderInitPostLen 0) (P' := wcbBuilderInitPostLen 0)
    (Q := wcbBuilderInitPostLen 0)
    (Q' := wcbEmptyPathPre (0x40000030 : Word) ** wcbBuilderBranchFrame 0)
    (fun _ hp => hp)
    (fun s hq => by
      simp only [wcbBuilderInitPostLen] at hq
      have hq1 : ((WcbEnabledLoc ↦ₘ (0 : Word)) **
          (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) **
            ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
              ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                regOwn .x5 ** regOwn .x18 ** regOwn .x6 **
                  memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
                    memOwn WcbCountLoc ** wcbBuilderBranchFrame 0)) s := by
        simp only [wcbBuilderBranchFrame] at hq ⊢
        xperm_chunked hq
      have hq2 := sepConj_mono memIs_implies_memOwn (fun _ hh => hh) s hq1
      simp only [wcbEmptyPathPre, wcbBuilderBranchFrame] at hq2 ⊢
      xperm_chunked hq2) hbranch
  have hseq := cpsTripleWithin_seq_same_cr hbranch' hframe
  exact cpsTripleWithin_mono_nSteps (show 1 + 44 ≤ 45 by omega) hseq

theorem wcb_builder_nonempty_path_spec :
    cpsTripleWithin 21 (wcbB + 224) (wcbB + 580) wcbCr
      (wcbBuilderInitPostLen 1)
      (wcbFailurePost (0x40000030 : Word) ** wcbBuilderFailureFrame 1) := by
  have hbranch := wcb_builder_nonempty_branch_spec
  have hfull := wcb_failure_path_spec (0x40000030 : Word)
  have hframe := cpsTripleWithin_frameR (wcbBuilderFailureFrame 1)
    (by pcf) hfull
  have hbranch' := cpsTripleWithin_weaken
    (P := wcbBuilderInitPostLen 1) (P' := wcbBuilderInitPostLen 1)
    (Q := wcbBuilderInitPostLen 1)
    (Q' := wcbFailurePre (0x40000030 : Word) ** wcbBuilderFailureFrame 1)
    (fun _ hp => hp)
    (fun s hq => by
      simp only [wcbBuilderInitPostLen] at hq
      have hq1 : ((WcbEnabledLoc ↦ₘ (0 : Word)) **
          ((WcbBuildStatusLoc ↦ₘ (0 : Word)) **
            (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) **
              ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
                ((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  regOwn .x5 ** regOwn .x18 ** regOwn .x6 **
                    memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
                      memOwn WcbCountLoc ** wcbBuilderFailureFrame 1))) s := by
        simp only [wcbBuilderFailureFrame] at hq ⊢
        xperm_chunked hq
      have hq2 := sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn (fun _ hh => hh)) s hq1
      simp only [wcbFailurePre, wcbBuilderFailureFrame] at hq2 ⊢
      xperm_chunked hq2) hbranch
  have hseq := cpsTripleWithin_seq_same_cr hbranch' hframe
  exact cpsTripleWithin_mono_nSteps (show 1 + 20 ≤ 21 by omega) hseq

def wcbBuilderPost (len : Word) : Assertion :=
  if len = 0 then
    wcbEmptySuccessPost (0x40000030 : Word) ** wcbBuilderBranchFrame 0
  else
    wcbFailurePost (0x40000030 : Word) ** wcbBuilderFailureFrame 1

theorem wcb_builder_spec (len : Word) (h_cases : len = 0 ∨ len = 1) :
    cpsTripleWithin 89 (wcbB + 48) (wcbB + 580) wcbCr
      (wcbBuilderInitPreLen len) (wcbBuilderPost len) := by
  rcases h_cases with rfl | rfl
  · have hi := wcb_builder_initialization_spec_len 0
    have hp := wcb_builder_empty_path_spec
    have hseq := cpsTripleWithin_seq_same_cr hi hp
    simpa [wcbBuilderPost] using
      (cpsTripleWithin_mono_nSteps (show 44 + 45 ≤ 89 by omega) hseq)
  · have hi := wcb_builder_initialization_spec_len 1
    have hp := wcb_builder_nonempty_path_spec
    have hseq := cpsTripleWithin_seq_same_cr hi hp
    simpa [wcbBuilderPost] using
      (cpsTripleWithin_mono_nSteps (show 44 + 21 ≤ 89 by omega) hseq)

/-
private theorem wcb_beq_same_absurd {r1 r2 : Reg} {v : Word} :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ v) ** ⌜v ≠ v⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact hP.2 rfl

private theorem wcb_beq_one_zero_absurd :
    ∀ hp, (((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜(1 : Word) = (0 : Word)⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact (by decide : (1 : Word) ≠ (0 : Word)) hP.2

theorem wcb_empty_branch_spec :
    cpsTripleWithin 1 (wcbB + 224) (wcbB + 392) wcbCr
      (wcbBuilderInitPostLen 0) (wcbBuilderInitPostLen 0) := by
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (generic_beq_spec_within .x9 .x0
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224))
      (0 : Word) (0 : Word) (wcbB + 224))
  have hbt := cpsBranchWithin_takenStripPure2 hbr
    (wcb_beq_same_absurd (r1 := .x9) (r2 := .x0) (v := (0 : Word)))
  rw [show (wcbB + 224 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224)) = wcbB + 392 from by decide] at hbt
  have hf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** regOwn .x5 ** regOwn .x18 **
      regOwn .x6 ** (WcbEnabledLoc ↦ₘ (0 : Word)) **
      (WcbBuildStatusLoc ↦ₘ (0 : Word)) ** (WcbBuildSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbBuildCountLoc ↦ₘ (0 : Word)) ** (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
      (WcbLinearIterationsLoc ↦ₘ (0 : Word)) ** (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
      memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
      (WcbLinearMaxLenLoc ↦ₘ (0 : Word))) (by pcf) hbt
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [wcbBuilderInitPostLen] at hp ⊢
    xperm_chunked hp) (fun _ hq => by
    simp only [wcbBuilderInitPostLen] at hq ⊢
    xperm_chunked hq) hf

theorem wcb_failure_branch_spec :
    cpsTripleWithin 22 (wcbB + 224) (wcbB + 580) wcbCr
      (wcbFailureStart (0x40000030 : Word)) (wcbFailurePost (0x40000030 : Word)) := by
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (generic_beq_spec_within .x9 .x0
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224))
      (1 : Word) (0 : Word) (wcbB + 224))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr wcb_beq_one_zero_absurd
  rw [show (wcbB + 224 : Word) + 4 = wcbB + 228 from by bv_omega] at hnt
  have hf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** regOwn .x5 **
      ((.x18 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 ** (WcbEnabledLoc ↦ₘ (0 : Word)) **
      (WcbBuildStatusLoc ↦ₘ (0 : Word)) ** (WcbBuildSectionLenLoc ↦ₘ (1 : Word)) **
      (WcbBuildCountLoc ↦ₘ (0 : Word)) ** (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
      (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
      (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
      (WcbLinearIterationsLoc ↦ₘ (0 : Word)) ** (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
      memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
      (WcbLinearMaxLenLoc ↦ₘ (0 : Word))) (by pcf) hnt
  have hff := cpsTripleWithin_weaken
    (P := (((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
      (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
        regOwn .x5 ** ((.x18 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 **
        (WcbEnabledLoc ↦ₘ (0 : Word)) **
        (WcbBuildStatusLoc ↦ₘ (0 : Word)) ** (WcbBuildSectionLenLoc ↦ₘ (1 : Word)) **
        (WcbBuildCountLoc ↦ₘ (0 : Word)) ** (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
        (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
        (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
        (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
        (WcbLinearIterationsLoc ↦ₘ (0 : Word)) ** (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
        memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
        (WcbLinearMaxLenLoc ↦ₘ (0 : Word))))
    (P' := wcbFailureStart (0x40000030 : Word))
    (Q := (((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
      (((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
        regOwn .x5 ** ((.x18 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 **
        (WcbEnabledLoc ↦ₘ (0 : Word)) **
        (WcbBuildStatusLoc ↦ₘ (0 : Word)) ** (WcbBuildSectionLenLoc ↦ₘ (1 : Word)) **
        (WcbBuildCountLoc ↦ₘ (0 : Word)) ** (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
        (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
        (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
        (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
        (WcbLinearIterationsLoc ↦ₘ (0 : Word)) ** (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
        memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc ** memOwn WcbCountLoc **
        (WcbLinearMaxLenLoc ↦ₘ (0 : Word))))
    (Q' := wcbFailurePre (0x40000030 : Word))
    (fun _ hp => by unfold wcbFailurePre at hp; xperm_chunked hp)
    (fun _ hq => by unfold wcbFailurePre; xperm_chunked hq) hf
  have hm := cpsTripleWithin_seq_same_cr hff
    (wcb_failure_path_spec (0x40000030 : Word))
  exact cpsTripleWithin_mono_nSteps (show 1 + 20 ≤ 22 by omega) hm

 -/

end EvmAsm.Codegen.WitnessCodesLookupSpec
