/-
  EvmAsm.Codegen.Programs.RlpRecursiveDecodeProductionBridge

  State/ownership bridge for the recursive decoder's snapshot contract.  The
  RecDecode proof speaks in `asrtM`/`Reach.exact`; the linked payload adapter
  speaks in explicit register, frame-arena, and input-region assertions.  This
  file only changes that assertion vocabulary.  It does not claim that the
  direct-JAL image has the `ItemsSound` proof: that semantic correspondence is
  the separate direct-call composition boundary.
-/

import EvmAsm.Codegen.Programs.RlpRecursiveDecodeDirect
import EvmAsm.Codegen.Programs.RlpValidatePayloadProductionContinuation
import EvmAsm.Rv64.SAsm.AssertionSpec

namespace EvmAsm.Codegen.RlpValidatePayloadProductionAdapter

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.RecDecode

private def itemsPreRegs (rf : RegFile) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x10 **
    regOwn .x11 ** (.x12 ↦ᵣ rf.get .x12) ** (.x13 ↦ᵣ rf.get .x13) **
    regOwn .x14 ** (.x15 ↦ᵣ rf.get .x15) ** (.x16 ↦ᵣ rf.get .x16) **
    regOwn .x17))

private def itemsPostRegs (status framePtr : Word) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x10 ↦ᵣ status) **
    regOwn .x11 ** regOwn .x12 ** (.x13 ↦ᵣ framePtr) ** regOwn .x14 **
    regOwn .x15 ** regOwn .x16 ** regOwn .x17))

private theorem regFileIs_to_itemsPreRegs (rf : RegFile) :
    ∀ h, regFileIs rf h → itemsPreRegs rf h := by
  intro h hp
  rw [regFileIs_eq_atoms] at hp
  exact sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _)
      (sepConj_mono (regIs_to_regOwn .x7 _)
        (sepConj_mono (regIs_to_regOwn .x28 _)
          (sepConj_mono (regIs_to_regOwn .x29 _)
            (sepConj_mono (regIs_to_regOwn .x30 _)
              (sepConj_mono (regIs_to_regOwn .x31 _)
                (sepConj_mono (regIs_to_regOwn .x10 _)
                  (sepConj_mono (regIs_to_regOwn .x11 _)
                    (sepConj_mono (fun _ h' => h')
                      (sepConj_mono (fun _ h' => h')
                        (sepConj_mono (regIs_to_regOwn .x14 _)
                          (sepConj_mono (fun _ h' => h')
                            (sepConj_mono (fun _ h' => h')
                              (regIs_to_regOwn .x17 _)))))))))))))) h hp

private theorem regFileIs_to_itemsPostRegs
    (rf : RegFile) (status framePtr : Word)
    (hstatus : rf.get .x10 = status) (hframe : rf.get .x13 = framePtr) :
    ∀ h, regFileIs rf h → itemsPostRegs status framePtr h := by
  intro h hp
  rw [regFileIs_eq_atoms] at hp
  have hp' := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _)
      (sepConj_mono (regIs_to_regOwn .x7 _)
        (sepConj_mono (regIs_to_regOwn .x28 _)
          (sepConj_mono (regIs_to_regOwn .x29 _)
            (sepConj_mono (regIs_to_regOwn .x30 _)
              (sepConj_mono (regIs_to_regOwn .x31 _)
                (sepConj_mono (fun _ h' => h')
                  (sepConj_mono (regIs_to_regOwn .x11 _)
                    (sepConj_mono (regIs_to_regOwn .x12 _)
                      (sepConj_mono (fun _ h' => h')
                        (sepConj_mono (regIs_to_regOwn .x14 _)
                          (sepConj_mono (regIs_to_regOwn .x15 _)
                            (sepConj_mono (regIs_to_regOwn .x16 _)
                              (regIs_to_regOwn .x17 _)))))))))))))) h hp
  simpa [hstatus, hframe] using hp'

/- The exact pre bridge retains the ambient assertion.  The production
   adapter's input region begins at its `listBase`; therefore this bridge is
   intentionally the top-level-entry case, where the caller's `x15` already
   names `inBase`.  The recursive items contract permits an interior `x15`,
   but a byte-granular slice cannot be separated from the surrounding
   `bytesRegion` without a dword-alignment premise. -/
theorem items_exact_pre_to_production_pre
    (bs : List (BitVec 8)) (inBase fp : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (A : Assertion)
    (hpre : itemsPreS bs inBase rlpRecursiveDecodeDepthCap fp rf ws A)
    (hbase : rf.get .x15 = inBase) :
    ∀ h, asrtM ⟨inBase, bs⟩
        (itemsRw rlpRecursiveDecodeDepthCap fp)
        (Reach.exact rf ws A) h →
      (productionItemsPre inBase (rf.get .x16) fp bs ws ** A) h := by
  intro h hM
  change (asrtOf (itemsRw rlpRecursiveDecodeDepthCap fp)
      (Reach.exact rf ws A) ** bytesRegion inBase bs) h at hM
  obtain ⟨hp, hcompat, hdisj, hunion, hstate, hinput⟩ := hM
  obtain ⟨rf', ws', A', hlen, hApc, hreach, hstate'⟩ := hstate
  obtain ⟨hrf, hws, hA⟩ := hreach
  subst rf'
  subst ws'
  subst A'
  have hstate'' := sepConj_mono_left
    (sepConj_mono_left (regFileIs_to_itemsPreRegs rf)) hp hstate'
  have hcombined0 :
      (((itemsPreRegs rf ** bytesRegion fp ws) ** A) **
        bytesRegion inBase bs) h := by
    exact ⟨hp, hcompat, hdisj, hunion, hstate'', hinput⟩
  have hcombined := hcombined0
  rw [sepConj_assoc', sepConj_comm' A (bytesRegion inBase bs),
    ← sepConj_assoc'] at hcombined
  obtain ⟨p, q, h15, h16, h12, h13, hpq, hq⟩ := hpre
  have hcap : (BitVec.ofNat 64 rlpRecursiveDecodeDepthCap) = Cap := by
    decide
  simp only [productionItemsPre, itemsPreRegs, h12, h13, hbase, hcap] at hcombined ⊢
  xperm_hyp hcombined

/- The post bridge keeps the writable frame bytes existential: `itemsPostS`
   deliberately leaves them unconstrained after the routine writes its frame.
   A fixed `frameBytes` post is therefore available only after the caller
   instantiates this existential with the actual output list. -/
theorem items_asrtM_post_to_production_post
    (bs : List (BitVec 8)) (inBase fp : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    :
    ∀ h, asrtM ⟨inBase, bs⟩
        (itemsRw rlpRecursiveDecodeDepthCap fp)
        (itemsPostS bs inBase rlpRecursiveDecodeDepthCap fp rf₀ ws₀ A₀) h →
      ∃ status : Word, ∃ frameBytes : List (BitVec 8), ∃ F : Assertion,
        frameBytes.length = FrameBytes ∧ F.pcFree ∧
        (productionItemsPost inBase fp status bs frameBytes ** F) h := by
  intro h hM
  change (asrtOf (itemsRw rlpRecursiveDecodeDepthCap fp)
      (itemsPostS bs inBase rlpRecursiveDecodeDepthCap fp rf₀ ws₀ A₀) **
      bytesRegion inBase bs) h at hM
  obtain ⟨hp, hcompat, hdisj, hunion, hstate, hinput⟩ := hM
  obtain ⟨rf', ws', A', hlen, hApc, hpost, hstate'⟩ := hstate
  have hframe : rf'.get .x13 = fp := hpost.2.1
  have hstate'' := sepConj_mono_left
    (sepConj_mono_left
      (regFileIs_to_itemsPostRegs rf' (rf'.get .x10) fp rfl hframe)) hp hstate'
  refine ⟨rf'.get .x10, ws', A', ?_, hApc, ?_⟩
  · simpa [FrameBytes, itemsRw, rlpRecursiveDecodeFrameBytes] using hlen
  · have hcombined0 :
        (((itemsPostRegs (rf'.get .x10) fp ** bytesRegion fp ws') ** A') **
          bytesRegion inBase bs) h := by
      exact ⟨hp, hcompat, hdisj, hunion, hstate'', hinput⟩
    have hcombined := hcombined0
    rw [sepConj_assoc', sepConj_comm' A' (bytesRegion inBase bs),
      ← sepConj_assoc'] at hcombined
    simp only [productionItemsPost, itemsPostRegs] at hcombined ⊢
    xperm_hyp hcombined

#print axioms items_exact_pre_to_production_pre
#print axioms items_asrtM_post_to_production_post

end EvmAsm.Codegen.RlpValidatePayloadProductionAdapter
