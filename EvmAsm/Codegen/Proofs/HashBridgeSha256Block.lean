/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Block

  Code containment for the first full-block body of `zkvm_sha256`.
  The copy segment is reused by the loop proof; keeping its code-map
  plumbing separate makes the dynamic body independent of the large wrapper.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Setup
import EvmAsm.Rv64.SAsm.SelectedRead

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL
private abbrev sha256CopyProg : List Instr :=
  dwordCopyProgFrom .x9 .x21 .x5 0 8
private abbrev sha256CopyPrefix : List Instr := sha256ProgL.take 27
private abbrev sha256CopySuffix : List Instr := sha256ProgL.drop 43

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256Copy_split :
    sha256ProgL = sha256CopyPrefix ++ sha256CopyProg ++ sha256CopySuffix := by
  simp only [sha256ProgL, sha256CopyPrefix, sha256CopyProg, sha256CopySuffix,
    zkvmSha256_prog, zkvmSha256_prog_of, dwordCopyProgFrom]
  decide

private theorem sha256CopyPrefix_len : sha256CopyPrefix.length = 27 := by
  simp only [sha256CopyPrefix, sha256ProgL, zkvmSha256_prog,
    zkvmSha256_prog_of]
  decide

private theorem sha256CopySuffix_len : sha256CopySuffix.length = 78 := by
  simp only [sha256CopySuffix, sha256ProgL, zkvmSha256_prog,
    zkvmSha256_prog_of]
  decide

private theorem sha256Copy_mem :
    ∀ a i, CodeReq.ofProg (B + 108) sha256CopyProg a = some i → sha256Cr a = some i := by
  intro a i h
  have hleft := ofProg_mono_left (base := B + 108)
    (p1 := sha256CopyProg) (p2 := sha256CopySuffix) a i h
  have haddr : B + BitVec.ofNat 64 (4 * sha256CopyPrefix.length) = B + 108 := by
    rw [sha256CopyPrefix_len]
    decide
  have hright := ofProg_mono_right
    (base := B) (p1 := sha256CopyPrefix)
    (p2 := sha256CopyProg ++ sha256CopySuffix)
    (by simp only [List.length_append, sha256CopyPrefix_len,
        sha256CopySuffix_len, dwordCopyProgFrom_length]
        norm_num) a i (by
      rw [haddr]
      exact hleft)
  change CodeReq.ofProg B sha256ProgL a = some i
  rw [sha256Copy_split]
  exact hright

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]
  norm_num

private theorem sha256_mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins
    sha256ProgL_bound a i h

private abbrev ShaParams : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params

private theorem la_params_hi :
    Codegen.laHi GuestAddrs.sha256_w_params (GuestAddrs.zkvm_sha256 + 172) =
      Rv64.laHi (B + 172) ShaParams := by decide

private theorem la_params_lo :
    Codegen.laLo GuestAddrs.sha256_w_params (GuestAddrs.zkvm_sha256 + 172) =
      Rv64.laLo (B + 172) ShaParams := by decide

private theorem la_params_range : laInRange (B + 172) ShaParams := by decide

theorem sha256BlockLaParams_spec (v10 : Word) :
    cpsTripleWithin 2 (B + 172) (B + 180) sha256Cr
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ ShaParams) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 172)
        (.AUIPC .x10 (Rv64.laHi (B + 172) ShaParams)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := sha256_mem_at 43
      (.AUIPC .x10 (Codegen.laHi GuestAddrs.sha256_w_params
        (GuestAddrs.zkvm_sha256 + 172))) (B + 172) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_params_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 172) + 4)
        (.ADDI .x10 .x10 (Rv64.laLo (B + 172) ShaParams)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := sha256_mem_at 44
      (.ADDI .x10 .x10 (Codegen.laLo GuestAddrs.sha256_w_params
        (GuestAddrs.zkvm_sha256 + 172))) (B + 176) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    have hpc : (B + 172 : Word) + 4 = B + 176 := by decide
    rw [hpc, ← la_params_lo] at hi
    exact hmem a i hi
  exact la_materialize_within .x10 v10 (B + 172) ShaParams
    (by decide) la_params_range hau had

/-- The SHA CSR seam with the three pointer registers exposed individually.
    This is the composition-friendly form of the frame-level external seam:
    callers can establish it from the wrapper's concrete register setup
    without manufacturing ownership of an unrelated whole `RegFile`. -/
theorem sha256ExternalCsrs_regs_spec_within
    (base : Word) (paramsBase stateBase inputBase : Word)
    (params state input : List (BitVec 8)) (payload : List Word)
    (v8 v10 v21 : Word) (hstate : state.length = 32)
    (hpayload : payload.length = 4)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ v21) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion inputBase input) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS 0x805 .x10))
      ((.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ v21) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion inputBase input)
      ((.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ v21) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion inputBase input) := by
  intro R hR s hcr hPR hpcs
  subst hpcs
  have hfetch : s.code s.pc = some (.CSRS 0x805 .x10) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  obtain ⟨hvalidCsrs, hwriteCsrs⟩ := hsem R s hPR
  simp only [sepConj_assoc'] at hPR
  have hMem :
      (bytesRegion stateBase state **
        (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ v21) **
        bytesRegion paramsBase params ** bytesRegion inputBase input ** R).holdsFor s := by
    sep_perm hPR
  have hW := holdsFor_bytesRegion_writeWords payload state s 0 hMem
    (by simp) (by omega)
  have hstep : step s = some (execInstrBr s (.CSRS 0x805 .x10)) :=
    step_csrs hfetch hvalidCsrs
  have hwrite : s.execCsrs 0x805 .x10 = s.writeWords stateBase payload := by
    show s.writeWords (s.csrsWrite 0x805 .x10).1
      (s.csrsWrite 0x805 .x10).2 = _
    rw [hwriteCsrs]
  refine ⟨1, Nat.le_refl 1,
    ((s.execCsrs 0x805 .x10).setPC (s.pc + 4)), ?_, ?_, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep]
    rfl
  · rfl
  · have hmemFree :
        (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ v21) **
          bytesRegion paramsBase params **
          bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
          bytesRegion inputBase input |>.pcFree := by
      exact pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)
    have hpcf := pcFree_sepConj hmemFree hR
    have hW' :
        (( (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ v21) **
          bytesRegion paramsBase params **
          bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
          bytesRegion inputBase input) ** R).holdsFor
          (s.writeWords (stateBase + 0#64) payload) := by
      sep_perm hW
    have hzero : stateBase + 0#64 = stateBase := by simp
    rw [hzero] at hW'
    have hfin := holdsFor_pcFree_setPC (v := s.pc + 4) hpcf hW'
    rw [← hwrite] at hfin
    exact hfin

theorem sha256Copy_spec
    (inputBase scratchBase stateBase : Word)
    (input scratch state : List (BitVec 8))
    (v5 v8 : Word) (hinput : input.length = 64)
    (hscratch : scratch.length = 64) :
    cpsTripleWithin 16 (B + 108) (B + 172) sha256Cr
      ((.x9 ↦ᵣ inputBase) ** (.x21 ↦ᵣ scratchBase) ** (.x5 ↦ᵣ v5) **
        (.x8 ↦ᵣ v8) ** bytesRegion inputBase input **
        bytesRegion scratchBase scratch ** bytesRegion stateBase state)
      ((.x9 ↦ᵣ inputBase) ** (.x21 ↦ᵣ scratchBase) ** regOwn .x5 **
        (.x8 ↦ᵣ v8) ** bytesRegion inputBase input **
        bytesRegion scratchBase input ** bytesRegion stateBase state) := by
  have hcopy := selectedDwordCopy_spec .x9 .x21 .x5
    (by decide) inputBase scratchBase v5 input scratch 0 8
    (by omega) (by omega) (by omega) (B + 108)
  have hcopy' := cpsTripleWithin_extend_code sha256Copy_mem hcopy
  have hcover : copyDwords input scratch 0 8 = input := by
    exact copyDwords_covers input scratch 8 hinput hscratch
  rw [hcover] at hcopy'
  have hfr := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ v8) ** bytesRegion stateBase state) (by pcf) hcopy'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hfr

/-- Copy one full 64-byte message block into the accelerator buffer, materialize
    the parameter pointer, and perform the SHA compression step.  The CSR
    validity/write facts remain an explicit semantic obligation; this theorem
    supplies the exact machine-level frame around that obligation. -/
theorem sha256FullBlockPrefix_spec
    (inputBase scratchBase stateBase paramsBase : Word)
    (input scratch state params : List (BitVec 8)) (payload : List Word)
    (v5 v10 : Word) (hinput : input.length = 64)
    (hscratch : scratch.length = 64) (hstate : state.length = 32)
    (_hparams : params.length = 16) (hpayload : payload.length = 4)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase state ** bytesRegion scratchBase input) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 19 (B + 108) (B + 184) sha256Cr
      ((.x9 ↦ᵣ inputBase) ** (.x21 ↦ᵣ scratchBase) ** (.x5 ↦ᵣ v5) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        bytesRegion inputBase input ** bytesRegion scratchBase scratch **
        bytesRegion stateBase state ** bytesRegion paramsBase params)
      ((.x9 ↦ᵣ inputBase) ** (.x21 ↦ᵣ scratchBase) ** regOwn .x5 **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        bytesRegion inputBase input ** bytesRegion scratchBase input **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion paramsBase params) := by
  have hcopy := sha256Copy_spec inputBase scratchBase stateBase input scratch state
    v5 stateBase hinput hscratch
  have hcopyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** bytesRegion paramsBase params) (by pcf) hcopy
  have hcopy' : cpsTripleWithin 16 (B + 108) (B + 172) sha256Cr
      ((.x9 ↦ᵣ inputBase) ** (.x21 ↦ᵣ scratchBase) ** (.x5 ↦ᵣ v5) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** bytesRegion inputBase input **
        bytesRegion scratchBase scratch ** bytesRegion stateBase state **
        bytesRegion paramsBase params)
      ((.x9 ↦ᵣ inputBase) ** (.x21 ↦ᵣ scratchBase) ** regOwn .x5 **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** bytesRegion inputBase input **
        bytesRegion scratchBase input ** bytesRegion stateBase state **
        bytesRegion paramsBase params) := by
    exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
      (fun _ hq => by sep_perm hq) hcopyF
  have hla := sha256BlockLaParams_spec v10
  have hlaF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ inputBase) ** (.x21 ↦ᵣ scratchBase) ** regOwn .x5 **
      (.x8 ↦ᵣ stateBase) ** bytesRegion inputBase input **
      bytesRegion scratchBase input ** bytesRegion stateBase state **
      bytesRegion paramsBase params) (by pcf) hla
  have hmid := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by sep_perm hp)
    hcopy' hlaF
  have hcs := sha256ExternalCsrs_regs_spec_within (B + 180)
    paramsBase stateBase scratchBase params state input payload
    stateBase ShaParams scratchBase hstate hpayload hsem
  have hcs' := cpsTripleWithin_extend_code
    (sha256_mem_at 45 (.CSRS 0x805 .x10) (B + 180) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hcs
  have hcsF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ inputBase) ** regOwn .x5 ** bytesRegion inputBase input) (by pcf) hcs'
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by sep_perm hp)
    hmid hcsF
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hall

end EvmAsm.Codegen.Proofs
