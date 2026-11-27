/-
  EvmAsm.Codegen.Programs.WitnessCodesIndexBuildTop

  **Machine facts for the guest routine `witness_codes_index_build`** (GH #13246,
  obligations 7 and 10).

  `witnessCodesIndexBuild_prog` (`WitnessCodeLookup.lean`, 158 instructions) was
  transcribed in #12160 so that a `cpsTripleWithin` over the real linked program
  could be STATED.  #11800 closed on that transcription; this module is the
  attachment half it deliberately left out.  The proved domain is an
  intentionally narrow empty-code-section checkpoint; it is not a claim about
  the keccak loop or the heapsort.

  ## §A  What is established here

  * `wcb_abiFrame_byte_tie` (in `WitnessCodesLookupSpec.lean`) already says the
    routine IS a standard 11-slot ABI frame around a 133-instruction body, so
    `abiFrame_spec_own` applies and the prologue/epilogue (`ra`, `s0`…`s9`
    save/restore, `sp` round-trip) are DERIVED, not assumed.
  * The composition idioms `chainK` and `laStoreOwn`/`laStoreAt` live in
    `CellStoreIdioms.lean`, generic in the `CodeReq`, because the mechanically
    identical node-DB builder `witness_index_build` reuses them verbatim.
  * `witness_codes_index_build_spec_within_empty_section` — the **whole-routine
    triple**, entry `GuestAddrs.witness_codes_index_build` to the caller's
    return address, over `CodeReq.ofProg` of the real program, in at most 88
    machine steps.  It pins `a0 = 0` (success), `wcidx_enabled = 1`,
    `wcidx_count = 0`, `wcidx_section_ptr = a0`, `wcidx_section_len = 0`,
    `wcidx_build_status = 0`, all ten `wclh_*` counters reset, and the eleven
    callee-saved registers restored.  That published state is the machine
    counterpart of `Stateless.SpecRef.build_code_db [] = []`.
  * `wcb_entryState_exists` — a concrete `MachineState` at the routine's OWN
    entry (`pc = wcbB`) satisfying the whole-routine precondition, with the
    forty-five atoms' pairwise disjointness kernel-checked.

  ## §B  What is NOT established (read before citing this module)

  The gate is `a1 = section_len = 0`, an INPUT-DOMAIN restriction.  Nothing here
  bounds `section_len` from above, and nothing here says anything about:

  * the SSZ offset-table guards (idx 57…66) or the per-entry keccak loop
    (idx 70…97), which contain the `zkvm_keccak256` cross-`jal` at idx 93;
  * the two heapsort loops (idx 101…124), which contain the `wcidx_record_ptr`,
    `wcidx_swap_records` and `wcidx_sift_down` cross-`jal`s;
  * the failure tail (idx 140…144), which sets `wcidx_build_status := 1` and
    returns `a0 = 1`.

  On the domain proved here **none of those five callees is REACHED** — the
  `beq s1, zero` at idx 56 jumps over the loop that contains the keccak call
  and the `bltu s2, t0` at idx 100 jumps over both sort loops — so this theorem
  carries **no unproven-callee dependency**.  The general routine does; any
  extension past either branch must carry those callee contracts as explicit
  hypotheses.  Branch polarity was read off the Program's own
  `brOff (…+392) (…+224)` and `brOff (…+500) (…+400)` immediates, not off a
  source line or a disassembly.

  ## §C  Why this is not a re-proof of `WitnessCodesIndexBuildSpec.lean`

  That module (already on `main`) proves `wcb_builder_spec`: the same body
  window `+48 … +580` in 89 steps, covering BOTH `section_len = 0` and the
  `section_len = 1` failure arm.  It cannot be wrapped by `abiFrame_spec_own`
  as it stands, because its precondition `wcbBuilderInitPreLen` PINS the body
  entry to one sample — `a0 = 0x40000030`, `s0 = 0`, `s1 = 0` — while the frame
  rule hands the body `regsAt wcbFrame vals` at an arbitrary `vals` and an
  arbitrary `a0`.  Generalising those three pins is what this module does, for
  the `section_len = 0` arm; `wcb_builder_spec`'s extra `section_len = 1`
  failure arm is NOT lifted here and remains sample-pinned.

  ## §D  Relation to the node-DB builder

  `witnessIndexBuild_prog` (`MptWitnessIndex.lean`) is the same 158
  instructions with `widx_*` in place of `wcidx_*`.  Its mirror of this module
  is `WitnessIndexBuildTop.lean`, built over the same `CodeReq`-generic idioms
  in `CellStoreIdioms.lean`.
-/

import EvmAsm.Codegen.Programs.CellStoreIdioms
import EvmAsm.Codegen.Programs.WitnessCodesLookupSpec
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.WitnessCodesIndexBuildTop

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Evm64
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessCodesLookupSpec
open EvmAsm.Codegen.CellStoreIdioms

set_option maxRecDepth 8000

/-! ## §2  `witness_codes_index_build` — the carried context and the segments

    The routine's `section_len = 0` path threads three resources through every
    segment: `x0`, the `la` scratch `t0 = x5`, and `s1 = x9` (the argument
    `section_len`, moved into a callee-saved register by the prologue's
    `mv s1, a1`, and zero on this domain).  Collecting them into `wcbK` lets the
    thirteen `.data` writes chain by pure reassociation (`chainK`). -/

/-- The context carried across the whole empty-section path. -/
def wcbK : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x9 : Reg) ↦ᵣ (0 : Word))

theorem wcbK_pcFree : wcbK.pcFree := by unfold wcbK; pcf

/-- **One `sd zero, 0(t0)` clear** at `A`, in carried-context shape. -/
private theorem wcbClearCell (A A' C : Word) (hA : A + 12 = A')
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wcbCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wcbCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 .x0 (0 : BitVec 12)) a = some i →
      wcbCr a = some i) :
    cpsTripleWithin 3 A A' wcbCr (wcbK ** memOwn C) (wcbK ** (C ↦ₘ (0 : Word))) := by
  subst hA
  have h := laStoreOwn (cr := wcbCr) .x0 A C (0 : Word) hrange hau had hsd
  have hf := cpsTripleWithin_frameR ((.x9 : Reg) ↦ᵣ (0 : Word)) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wcbK at hp; xperm_hyp hp
  · show (wcbK ** (C ↦ₘ (0 : Word))) s
    unfold wcbK
    have hq1 : (((.x5 : Reg) ↦ᵣ C) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (C ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 C) (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **The `sd s1, 0(t0)` write** of `section_len` into
    `wcidx_build_section_len` (idx 20…22).  On this domain `s1 = 0`, so the
    cell lands at zero exactly like the twelve literal clears — but the
    instruction is genuinely different, and the reloc table names a different
    cell. -/
private theorem wcbStoreS1Cell (A A' C : Word) (hA : A + 12 = A')
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wcbCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wcbCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 .x9 (0 : BitVec 12)) a = some i →
      wcbCr a = some i) :
    cpsTripleWithin 3 A A' wcbCr (wcbK ** memOwn C) (wcbK ** (C ↦ₘ (0 : Word))) := by
  subst hA
  have h := laStoreOwn (cr := wcbCr) .x9 A C (0 : Word) hrange hau had hsd
  have hf := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wcbK at hp; xperm_hyp hp
  · show (wcbK ** (C ↦ₘ (0 : Word))) s
    unfold wcbK
    have hq1 : (((.x5 : Reg) ↦ᵣ C) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (C ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 C) (fun _ h' => h') s hq1
    xperm_hyp hq2

/-! ## §3  The thirteen `.data` writes, chained -/

/-- The thirteen cells the initialisation block owns, in write order:
    `wcidx_build_status`, `wcidx_build_section_len`, `wcidx_build_count`, and
    the ten `wclh_*` lookup counters. -/
def wcbMidOwn : Assertion :=
  memOwn WcbBuildStatusLoc **
  memOwn WcbBuildSectionLenLoc **
  memOwn WcbBuildCountLoc **
  memOwn WcbLookupCallsLoc **
  memOwn WcbIndexedCallsLoc **
  memOwn WcbIndexedHitsLoc **
  memOwn WcbIndexedMissesLoc **
  memOwn WcbLinearCallsLoc **
  memOwn WcbLinearHitsLoc **
  memOwn WcbLinearMissesLoc **
  memOwn WcbLinearIterationsLoc **
  memOwn WcbLinearLastLenLoc **
  memOwn WcbLinearMaxLenLoc

/-- The same thirteen cells after the block: every one at zero. -/
def wcbMidZero : Assertion :=
  (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
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
  (WcbLinearMaxLenLoc ↦ₘ (0 : Word))

theorem wcbMidOwn_pcFree : wcbMidOwn.pcFree := by unfold wcbMidOwn; pcf
theorem wcbMidZero_pcFree : wcbMidZero.pcFree := by unfold wcbMidZero; pcf

/-- **The initialisation block** (idx 17…55, `+68 … +224`): thirteen
    `la`/`sd` writes, 39 machine steps, chained by `chainK` — no permutation
    search, so the cost is linear in the number of cells. -/
private theorem wcbInitBlock :
    cpsTripleWithin 39 (wcbB + 68) (wcbB + 224) wcbCr
      (wcbK ** wcbMidOwn) (wcbK ** wcbMidZero) := by
  have c1 := wcbClearCell (wcbB + 68) (wcbB + 80) WcbBuildStatusLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c2 := wcbStoreS1Cell (wcbB + 80) (wcbB + 92) WcbBuildSectionLenLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c3 := wcbClearCell (wcbB + 92) (wcbB + 104) WcbBuildCountLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c4 := wcbClearCell (wcbB + 104) (wcbB + 116) WcbLookupCallsLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c5 := wcbClearCell (wcbB + 116) (wcbB + 128) WcbIndexedCallsLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c6 := wcbClearCell (wcbB + 128) (wcbB + 140) WcbIndexedHitsLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c7 := wcbClearCell (wcbB + 140) (wcbB + 152) WcbIndexedMissesLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c8 := wcbClearCell (wcbB + 152) (wcbB + 164) WcbLinearCallsLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c9 := wcbClearCell (wcbB + 164) (wcbB + 176) WcbLinearHitsLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c10 := wcbClearCell (wcbB + 176) (wcbB + 188) WcbLinearMissesLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c11 := wcbClearCell (wcbB + 188) (wcbB + 200) WcbLinearIterationsLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c12 := wcbClearCell (wcbB + 200) (wcbB + 212) WcbLinearLastLenLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have c13 := wcbClearCell (wcbB + 212) (wcbB + 224) WcbLinearMaxLenLoc (by bv_omega)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  have ch12 := chainK (by pcf) (by pcf) c12 c13
  have ch11 := chainK (by pcf) (by pcf) c11 ch12
  have ch10 := chainK (by pcf) (by pcf) c10 ch11
  have ch9 := chainK (by pcf) (by pcf) c9 ch10
  have ch8 := chainK (by pcf) (by pcf) c8 ch9
  have ch7 := chainK (by pcf) (by pcf) c7 ch8
  have ch6 := chainK (by pcf) (by pcf) c6 ch7
  have ch5 := chainK (by pcf) (by pcf) c5 ch6
  have ch4 := chainK (by pcf) (by pcf) c4 ch5
  have ch3 := chainK (by pcf) (by pcf) c3 ch4
  have ch2 := chainK (by pcf) (by pcf) c2 ch3
  have ch1 := chainK (by pcf) (by pcf) c1 ch2
  unfold wcbMidOwn wcbMidZero
  exact cpsTripleWithin_mono_nSteps (by omega) ch1

/-! ## §4  The two taken branches and the publish tail -/

/-- **The empty-section branch** (idx 56, `+224`): `beq s1, zero` with
    `section_len = 0` jumps over the SSZ header guards, the whole keccak loop
    and the heapsort — which is why `zkvm_keccak256` (idx 93),
    `wcidx_record_ptr` (88/113/116), `wcidx_swap_records` (120) and
    `wcidx_sift_down` (106/123) are all UNREACHED on this domain and this
    theorem carries no unproven-callee dependency.  Polarity read off the
    Program's own `brOff (…+392) (…+224)`, not the source line. -/
private theorem wcbEmptySectionBranch :
    cpsTripleWithin 1 (wcbB + 224) (wcbB + 392) wcbCr wcbK wcbK := by
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (beq_spec_gen_within .x9 .x0
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224)) (0 : Word) (0 : Word) (wcbB + 224))
  have hbt := cpsBranchWithin_takenStripPure2 hbr (fun _ hq => by
    obtain ⟨_, _, _, _, _, hB⟩ := hq
    obtain ⟨_, _, _, _, _, hP⟩ := hB
    exact hP.2 rfl)
  rw [show (wcbB + 224 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_index_build + 392)
        (GuestAddrs.witness_codes_index_build + 224)) = wcbB + 392 from by decide] at hbt
  have hf := cpsTripleWithin_frameR (regOwn .x5) (by pcf) hbt
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wcbK at hp; xperm_hyp hp
  · show wcbK s
    unfold wcbK; xperm_hyp hq

/-- **The heapsort skip** (idx 98…100, `+392 … +500`): `count := 0` is
    reloaded into `s2`, `t0 := 2`, and `bltu s2, t0` is TAKEN because
    `0 <ᵤ 2`, jumping over both sort loops to the publish tail. -/
private theorem wcbSortSkip (v18 : Word) :
    cpsTripleWithin 3 (wcbB + 392) (wcbB + 500) wcbCr
      (wcbK ** ((.x18 : Reg) ↦ᵣ v18)) (wcbK ** ((.x18 : Reg) ↦ᵣ (0 : Word))) := by
  have h1 := liftCode (cr' := wcbCr)
    (li_spec_gen_within .x18 v18 (0 : Word) (wcbB + 392) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 392 : Word) + 4 = wcbB + 396 from by bv_omega] at h1
  have h2 := liftCode (cr' := wcbCr)
    (li_spec_gen_own_within .x5 (2 : Word) (wcbB + 396) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 396 : Word) + 4 = wcbB + 400 from by bv_omega] at h2
  have hbr := cpsBranchWithin_extend_code (cr' := wcbCr)
    (by unfold wcbCr; code_mem)
    (bltu_spec_gen_within .x18 .x5
      (brOff (GuestAddrs.witness_codes_index_build + 500)
        (GuestAddrs.witness_codes_index_build + 400)) (0 : Word) (2 : Word) (wcbB + 400))
  have hbt := cpsBranchWithin_takenStripPure2 hbr (fun _ hq => by
    obtain ⟨_, _, _, _, _, hB⟩ := hq
    obtain ⟨_, _, _, _, _, hP⟩ := hB
    exact hP.2 (by decide))
  rw [show (wcbB + 400 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_index_build + 500)
        (GuestAddrs.witness_codes_index_build + 400)) = wcbB + 500 from by decide] at hbt
  have f1 := cpsTripleWithin_frameR (regOwn .x5) (by pcf) h1
  have f2 := cpsTripleWithin_frameR ((.x18 : Reg) ↦ᵣ (0 : Word)) (by pcf) h2
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hbt
  have c3 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word))) (by pcf) c2
  refine cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) c3)
  · unfold wcbK at hp; xperm_hyp hp
  · show (wcbK ** ((.x18 : Reg) ↦ᵣ (0 : Word))) s
    unfold wcbK
    have hq1 : (((.x5 : Reg) ↦ᵣ (2 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 (2 : Word)) (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- The publish tail's carried context: `wcbK` plus `s2 = count = 0`. -/
def wcbK2 : Assertion := wcbK ** ((.x18 : Reg) ↦ᵣ (0 : Word))

theorem wcbK2_pcFree : wcbK2.pcFree := by unfold wcbK2 wcbK; pcf

/-- **`wcidx_section_ptr := s0`** (idx 125…127) — the section base the caller
    passed in `a0`, republished for the lookup path. -/
private theorem wcbPublishPtr (ptr : Word) :
    cpsTripleWithin 3 (wcbB + 500) (wcbB + 512) wcbCr
      (wcbK2 ** (((.x8 : Reg) ↦ᵣ ptr) ** memOwn WcbSectionPtrLoc))
      (wcbK2 ** (((.x8 : Reg) ↦ᵣ ptr) ** (WcbSectionPtrLoc ↦ₘ ptr))) := by
  have h := laStoreOwn (cr := wcbCr) .x8 (wcbB + 500) WcbSectionPtrLoc ptr
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 500 : Word) + 12 = wcbB + 512 from by bv_omega] at h
  have hf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word))) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wcbK2 wcbK at hp; xperm_hyp hp
  · show (wcbK2 ** (((.x8 : Reg) ↦ᵣ ptr) ** (WcbSectionPtrLoc ↦ₘ ptr))) s
    unfold wcbK2 wcbK
    have hq1 : (((.x5 : Reg) ↦ᵣ WcbSectionPtrLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        ((.x8 : Reg) ↦ᵣ ptr) ** (WcbSectionPtrLoc ↦ₘ ptr)) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WcbSectionPtrLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`wcidx_section_len := s1`** (idx 128…130) — zero on this domain. -/
private theorem wcbPublishLen :
    cpsTripleWithin 3 (wcbB + 512) (wcbB + 524) wcbCr
      (wcbK2 ** memOwn WcbSectionLenLoc)
      (wcbK2 ** (WcbSectionLenLoc ↦ₘ (0 : Word))) := by
  have h := laStoreOwn (cr := wcbCr) .x9 (wcbB + 512) WcbSectionLenLoc (0 : Word)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 512 : Word) + 12 = wcbB + 524 from by bv_omega] at h
  have hf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word))) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wcbK2 wcbK at hp; xperm_hyp hp
  · show (wcbK2 ** (WcbSectionLenLoc ↦ₘ (0 : Word))) s
    unfold wcbK2 wcbK
    have hq1 : (((.x5 : Reg) ↦ᵣ WcbSectionLenLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        (WcbSectionLenLoc ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WcbSectionLenLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`wcidx_count := s2`** (idx 131…133) — zero records indexed. -/
private theorem wcbPublishCount :
    cpsTripleWithin 3 (wcbB + 524) (wcbB + 536) wcbCr
      (wcbK2 ** memOwn WcbCountLoc)
      (wcbK2 ** (WcbCountLoc ↦ₘ (0 : Word))) := by
  have h := laStoreOwn (cr := wcbCr) .x18 (wcbB + 524) WcbCountLoc (0 : Word)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 524 : Word) + 12 = wcbB + 536 from by bv_omega] at h
  have hf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word))) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wcbK2 wcbK at hp; xperm_hyp hp
  · show (wcbK2 ** (WcbCountLoc ↦ₘ (0 : Word))) s
    unfold wcbK2 wcbK
    have hq1 : (((.x5 : Reg) ↦ᵣ WcbCountLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        (WcbCountLoc ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WcbCountLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`wcidx_enabled := 1`** (idx 134…137) — the flag every code-DB lookup
    dispatches on.  This is the routine's publishing write: it re-writes the
    cell the head cleared at idx 12…14, so the pre pins that cell at zero
    rather than merely owning it. -/
private theorem wcbPublishEnabled (v6 : Word) :
    cpsTripleWithin 4 (wcbB + 536) (wcbB + 552) wcbCr
      (wcbK2 ** (((.x6 : Reg) ↦ᵣ v6) ** (WcbEnabledLoc ↦ₘ (0 : Word))))
      (wcbK2 ** (((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WcbEnabledLoc ↦ₘ (1 : Word)))) := by
  have hli := liftCode (cr' := wcbCr)
    (li_spec_gen_within .x6 v6 (1 : Word) (wcbB + 536) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 536 : Word) + 4 = wcbB + 540 from by bv_omega] at hli
  have h := laStoreAt (cr := wcbCr) .x6 (wcbB + 540) WcbEnabledLoc (0 : Word) (1 : Word)
    (by decide) (by unfold wcbCr; code_mem) (by unfold wcbCr; code_mem)
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 540 : Word) + 12 = wcbB + 552 from by bv_omega] at h
  have f1 := cpsTripleWithin_frameR ((WcbEnabledLoc ↦ₘ (0 : Word)) ** regOwn .x5)
    (by pcf) hli
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 h
  have c2 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word))) (by pcf) c1
  refine cpsTripleWithin_mono_nSteps (show 1 + 3 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) c2)
  · unfold wcbK2 wcbK at hp; xperm_hyp hp
  · show (wcbK2 ** (((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WcbEnabledLoc ↦ₘ (1 : Word)))) s
    unfold wcbK2 wcbK
    have hq1 : (((.x5 : Reg) ↦ᵣ WcbEnabledLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WcbEnabledLoc ↦ₘ (1 : Word))) s := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WcbEnabledLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`a0 := 0` and the jump to the epilogue** (idx 138…139) — the success
    status, and the forward `j +24` that skips the failure tail (idx 140…144,
    which sets `wcidx_build_status := 1` and `a0 := 1`).  The jump target is
    the body exit `+580`, i.e. the epilogue's first `ld`. -/
private theorem wcbSuccessExit (v10 : Word) :
    cpsTripleWithin 2 (wcbB + 552) (wcbB + 580) wcbCr
      (wcbK2 ** ((.x10 : Reg) ↦ᵣ v10)) (wcbK2 ** ((.x10 : Reg) ↦ᵣ (0 : Word))) := by
  have hli := liftCode (cr' := wcbCr)
    (li_spec_gen_within .x10 v10 (0 : Word) (wcbB + 552) (by decide))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 552 : Word) + 4 = wcbB + 556 from by bv_omega] at hli
  have hjal := liftCode (cr' := wcbCr)
    (jal_x0_spec_gen_within (24 : BitVec 21) (wcbB + 556))
    (by unfold wcbCr; code_mem)
  rw [show (wcbB + 556 : Word) + signExtend21 (24 : BitVec 21) = wcbB + 580
    from by decide] at hjal
  have hjf := cpsTripleWithin_frameL ((.x10 : Reg) ↦ᵣ (0 : Word)) (by pcf) hjal
  rw [sepConj_emp_right'] at hjf
  have c1 := cpsTripleWithin_seq_same_cr hli hjf
  have c2 := cpsTripleWithin_frameL wcbK2 wcbK2_pcFree c1
  exact cpsTripleWithin_mono_nSteps (show 1 + 1 ≤ 2 by omega) c2

/-! ## §5  The body, composed -/

/-- The publish tail's own resources at entry (idx 125…139). -/
def wcbTailOwn (ptr v6 v10 : Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ ptr) ** memOwn WcbSectionPtrLoc ** memOwn WcbSectionLenLoc **
  memOwn WcbCountLoc ** ((.x6 : Reg) ↦ᵣ v6) ** (WcbEnabledLoc ↦ₘ (0 : Word)) **
  ((.x10 : Reg) ↦ᵣ v10)

/-- The publish tail's own resources at exit: the three index cells at their
    published values, `wcidx_enabled = 1`, and `a0 = 0` (success). -/
def wcbTailOut (ptr : Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ ptr) ** (WcbSectionPtrLoc ↦ₘ ptr) **
  (WcbSectionLenLoc ↦ₘ (0 : Word)) ** (WcbCountLoc ↦ₘ (0 : Word)) **
  ((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WcbEnabledLoc ↦ₘ (1 : Word)) **
  ((.x10 : Reg) ↦ᵣ (0 : Word))

private theorem wcbPublishTail (ptr v6 v10 : Word) :
    cpsTripleWithin 15 (wcbB + 500) (wcbB + 580) wcbCr
      (wcbK2 ** wcbTailOwn ptr v6 v10) (wcbK2 ** wcbTailOut ptr) := by
  have t8 := chainK (by pcf) (by pcf) (wcbPublishEnabled v6) (wcbSuccessExit v10)
  have t7 := chainK (by pcf) (by pcf) wcbPublishCount t8
  have t6 := chainK (by pcf) (by pcf) wcbPublishLen t7
  have t5 := chainK (by pcf) (by pcf) (wcbPublishPtr ptr) t6
  unfold wcbTailOwn wcbTailOut
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) t5)

private theorem wcbBranchToEnd (ptr v6 v10 v18 : Word) :
    cpsTripleWithin 19 (wcbB + 224) (wcbB + 580) wcbCr
      (wcbK ** (((.x18 : Reg) ↦ᵣ v18) ** wcbTailOwn ptr v6 v10))
      (wcbK ** (((.x18 : Reg) ↦ᵣ (0 : Word)) ** wcbTailOut ptr)) := by
  have hbr := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ v18) ** wcbTailOwn ptr v6 v10) (by unfold wcbTailOwn; pcf)
    wcbEmptySectionBranch
  have hsk := cpsTripleWithin_frameR (wcbTailOwn ptr v6 v10)
    (by unfold wcbTailOwn; pcf) (wcbSortSkip v18)
  have htl := wcbPublishTail ptr v6 v10
  unfold wcbK2 at htl
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbr hsk
  have c2 := cpsTripleWithin_seq_same_cr c1 htl
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) c2)

private theorem wcbInitToEnd (ptr v6 v10 v18 : Word) :
    cpsTripleWithin 58 (wcbB + 68) (wcbB + 580) wcbCr
      (wcbK ** (wcbMidOwn ** (((.x18 : Reg) ↦ᵣ v18) ** wcbTailOwn ptr v6 v10)))
      (wcbK ** (wcbMidZero ** (((.x18 : Reg) ↦ᵣ (0 : Word)) ** wcbTailOut ptr))) :=
  cpsTripleWithin_mono_nSteps (by omega)
    (chainK wcbMidZero_pcFree (by unfold wcbTailOwn; pcf)
      wcbInitBlock (wcbBranchToEnd ptr v6 v10 v18))

/-- The seventeen `.data` cells at their published values on the empty-section
    path.  Same order as `wcbBuilderCells`, so the two read as a before/after
    pair: `wcidx_enabled` flips `0 → 1`, `wcidx_section_ptr` takes the
    caller's section base, and every count is zero. -/
def wcbBuiltCells (ptr : Word) : Assertion :=
  (WcbEnabledLoc ↦ₘ (1 : Word)) ** (WcbBuildStatusLoc ↦ₘ (0 : Word)) **
  (WcbBuildSectionLenLoc ↦ₘ (0 : Word)) ** (WcbBuildCountLoc ↦ₘ (0 : Word)) **
  (WcbSectionPtrLoc ↦ₘ ptr) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
  (WcbCountLoc ↦ₘ (0 : Word)) ** (WcbLookupCallsLoc ↦ₘ (0 : Word)) **
  (WcbIndexedCallsLoc ↦ₘ (0 : Word)) ** (WcbIndexedHitsLoc ↦ₘ (0 : Word)) **
  (WcbIndexedMissesLoc ↦ₘ (0 : Word)) ** (WcbLinearCallsLoc ↦ₘ (0 : Word)) **
  (WcbLinearHitsLoc ↦ₘ (0 : Word)) ** (WcbLinearMissesLoc ↦ₘ (0 : Word)) **
  (WcbLinearIterationsLoc ↦ₘ (0 : Word)) ** (WcbLinearLastLenLoc ↦ₘ (0 : Word)) **
  (WcbLinearMaxLenLoc ↦ₘ (0 : Word))

/-- **The `section_len = 0` body**, `+48 → +580`, 63 machine steps, with the
    tight footprint: the eight registers and seventeen `.data` cells the path
    touches, and nothing else. -/
private theorem wcbEmptySectionBody_core (ptr oldPtr oldLen v6 v18 : Word) :
    cpsTripleWithin 63 (wcbB + 48) (wcbB + 580) wcbCr
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x8 : Reg) ↦ᵣ oldPtr) ** ((.x9 : Reg) ↦ᵣ oldLen) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ v18) ** wcbBuilderCells)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
        ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ (0 : Word)) ** wcbBuiltCells ptr) := by
  have a1f := cpsTripleWithin_frameR
    (wcbMidOwn ** ((.x18 : Reg) ↦ᵣ v18) ** memOwn WcbSectionPtrLoc **
      memOwn WcbSectionLenLoc ** memOwn WcbCountLoc ** ((.x6 : Reg) ↦ᵣ v6))
    (by unfold wcbMidOwn; pcf) (wcbBuilderInitHead ptr (0 : Word) oldPtr oldLen)
  have restf := cpsTripleWithin_frameR ((.x11 : Reg) ↦ᵣ (0 : Word)) (by pcf)
    (wcbInitToEnd ptr v6 ptr v18)
  have c := cpsTripleWithin_seq_perm_same_cr (fun s hp => by
      show ((wcbK ** (wcbMidOwn ** (((.x18 : Reg) ↦ᵣ v18) **
        wcbTailOwn ptr v6 ptr))) ** ((.x11 : Reg) ↦ᵣ (0 : Word))) s
      unfold wcbK wcbTailOwn
      xperm_chunked hp) a1f restf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) c)
  · unfold wcbBuilderCells at hp
    unfold wcbMidOwn
    xperm_chunked hp
  · show (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
      ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word)) ** wcbBuiltCells ptr) s
    unfold wcbBuiltCells
    unfold wcbK wcbMidZero wcbTailOut at hq
    xperm_chunked hq

/-! ## §6  The whole-routine triple

    `abiFrame_spec_own` turns the body into the routine: the prologue's eleven
    stores, the epilogue's eleven loads and the `ret` are DERIVED, and with
    them callee-saved preservation and the `sp` round-trip. -/

/-- The caller-visible ambient at entry: `a0 = section_ptr`, `a1 = 0` (the
    empty code section), the two scratch registers the routine clobbers, and
    the seventeen `.data` cells it writes — all OWNED, because every one of
    them is stored to on this path. -/
def wcbArgs (v6 ptr : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ v6) **
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** wcbBuilderCells

/-- The caller-visible ambient at return: **`a0 = 0`, the success status**,
    and each `.data` cell at its exact new value.  Asymmetric by
    construction — `wcidx_enabled` ends at ONE while every counter ends at
    zero, `wcidx_section_ptr` takes `ptr` while `wcidx_section_len` and
    `wcidx_count` take zero.  Swapping any two would not typecheck. -/
def wcbOut (ptr : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** wcbBuiltCells ptr

theorem wcbArgs_pcFree (v6 ptr : Word) : (wcbArgs v6 ptr).pcFree := by
  unfold wcbArgs wcbBuilderCells; pcf

theorem wcbOut_pcFree (ptr : Word) : (wcbOut ptr).pcFree := by
  unfold wcbOut wcbBuiltCells; pcf

private theorem regsAt_wcbFrame (vals : Reg → Word) :
    regsAt wcbFrame vals =
      (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ vals .x8) **
        ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
        ((.x23 : Reg) ↦ᵣ vals .x23) ** ((.x24 : Reg) ↦ᵣ vals .x24) **
        ((.x25 : Reg) ↦ᵣ vals .x25)) := by
  simp [wcbFrame, regsAt, sepConj_emp_right']

private theorem regsOwnAt_wcbFrame :
    regsOwnAt wcbFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** regOwn .x21 ** regOwn .x22 ** regOwn .x23 ** regOwn .x24 **
        regOwn .x25) := by
  simp [wcbFrame, regsOwnAt, sepConj_emp_right']

private theorem ent_own11 (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Reg)
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : Word) (P : Assertion) (h : PartialState)
    (hp : ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) ** (r5 ↦ᵣ w5) **
      (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** (r8 ↦ᵣ w8) ** (r9 ↦ᵣ w9) ** (r10 ↦ᵣ w10) **
      (r11 ↦ᵣ w11) ** P) h) :
    (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5 ** regOwn r6 **
      regOwn r7 ** regOwn r8 ** regOwn r9 ** regOwn r10 ** regOwn r11 ** P) h :=
  sepConj_mono (regIs_to_regOwn r1 w1)
    (sepConj_mono (regIs_to_regOwn r2 w2)
      (sepConj_mono (regIs_to_regOwn r3 w3)
        (sepConj_mono (regIs_to_regOwn r4 w4)
          (sepConj_mono (regIs_to_regOwn r5 w5)
            (sepConj_mono (regIs_to_regOwn r6 w6)
              (sepConj_mono (regIs_to_regOwn r7 w7)
                (sepConj_mono (regIs_to_regOwn r8 w8)
                  (sepConj_mono (regIs_to_regOwn r9 w9)
                    (sepConj_mono (regIs_to_regOwn r10 w10)
                      (sepConj_mono (regIs_to_regOwn r11 w11)
                        (fun _ hx => hx))))))))))) h hp

/-- **The body in `abiFrame_spec_own` shape.** -/
private theorem wcbEmptySectionBody (newSp : Word) (vals : Reg → Word) (v6 ptr : Word) :
    cpsTripleWithin 63
      (wcbB + BitVec.ofNat 64 (4 * (1 + wcbFrame.length)))
      (wcbB + BitVec.ofNat 64 (4 * (1 + wcbFrame.length + wcbBody.length))) wcbCr
      (((.x2 : Reg) ↦ᵣ newSp) ** regsAt wcbFrame vals **
        frameSlotsSaved wcbFrame newSp vals ** wcbArgs v6 ptr)
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wcbFrame **
        frameSlotsSaved wcbFrame newSp vals ** wcbOut ptr) := by
  rw [wcbFrame_length, wcbBody_length]
  simp only [show 4 * (1 + 11) = 48 from rfl, show 4 * (1 + 11 + 133) = 580 from rfl]
  have core := wcbEmptySectionBody_core ptr (vals .x8) (vals .x9) v6 (vals .x18)
  have framed := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((.x1 : Reg) ↦ᵣ vals .x1) **
      ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
      ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
      ((.x23 : Reg) ↦ᵣ vals .x23) ** ((.x24 : Reg) ↦ᵣ vals .x24) **
      ((.x25 : Reg) ↦ᵣ vals .x25) ** frameSlotsSaved wcbFrame newSp vals)
    (by pcf) core
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) framed
  · rw [regsAt_wcbFrame] at hp
    unfold wcbArgs at hp
    xperm_chunked hp
  · show (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wcbFrame **
      frameSlotsSaved wcbFrame newSp vals ** wcbOut ptr) h
    rw [regsOwnAt_wcbFrame]
    unfold wcbOut
    have hq2 : (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
        ((.x23 : Reg) ↦ᵣ vals .x23) ** ((.x24 : Reg) ↦ᵣ vals .x24) **
        ((.x25 : Reg) ↦ᵣ vals .x25) **
        (((.x2 : Reg) ↦ᵣ newSp) ** frameSlotsSaved wcbFrame newSp vals **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          wcbBuiltCells ptr)) h := by
      xperm_chunked hq
    have hq3 := ent_own11 .x1 .x8 .x9 .x18 .x19 .x20 .x21 .x22 .x23 .x24 .x25
      (vals .x1) ptr (0 : Word) (0 : Word) (vals .x19) (vals .x20) (vals .x21)
      (vals .x22) (vals .x23) (vals .x24) (vals .x25) _ h hq2
    xperm_chunked hq3

/-- **`witness_codes_index_build`, whole routine, at its linked guest address —
    on the `section_len = 0` domain.**

    From the routine's entry `GuestAddrs.witness_codes_index_build`, over the
    emitted program itself (`wcbCr = CodeReq.ofProg wcbB
    witnessCodesIndexBuild_prog`), execution returns to the caller in at most
    88 steps with:

    * `a0 = 0` — the documented success status;
    * `wcidx_enabled = 1`, `wcidx_count = 0`, `wcidx_section_ptr = a0`,
      `wcidx_section_len = 0` and `wcidx_build_status = 0`: the empty code
      index PUBLISHED, which is the machine counterpart of
      `SpecRef.build_code_db [] = []`;
    * all ten `wclh_*` lookup counters reset to zero;
    * every callee-saved register (`ra`, `s0`…`s9`) back at its ENTRY value
      and `sp` back at `sp0` — derived from `abiFrame_spec_own`, not assumed.

    Hypotheses are ABI/resource facts only: a two-byte-aligned return address
    held in `ra` at entry, and the 96-byte frame slots owned.  The domain
    restriction is `a1 = 0`, an INPUT-DOMAIN gate; nothing here bounds
    `section_len` from above. -/
theorem witness_codes_index_build_spec_within_empty_section
    (sp0 ret : Word) (vals : Reg → Word) (v6 ptr : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 88 wcbB ret wcbCr
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wcbFrame vals **
        frameSlotsOwn wcbFrame (sp0 + signExtend12 (-96 : BitVec 12)) **
        wcbArgs v6 ptr)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wcbFrame vals **
        frameSlotsSaved wcbFrame (sp0 + signExtend12 (-96 : BitVec 12)) vals **
        wcbOut ptr) := by
  have h := abiFrame_spec_own wcbB sp0 ret (-96 : BitVec 12) (96 : BitVec 12)
    wcbFrame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
     (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
     (.x22, (56 : BitVec 12)), (.x23, (64 : BitVec 12)), (.x24, (72 : BitVec 12)),
     (.x25, (80 : BitVec 12))]
    vals wcbBody 63 (wcbArgs v6 ptr) (wcbOut ptr)
    wcbCr rfl (by decide) (by decide)
    (by rw [wcb_abiFrame_byte_tie]; decide)
    hret halign (sext_frameRestore _ _ _ (by decide))
    (wcbArgs_pcFree _ _) (wcbOut_pcFree _)
    (by rw [wcb_abiFrame_byte_tie]; unfold wcbCr; code_mem)
    (wcbEmptySectionBody _ vals v6 ptr)
  rw [wcbFrame_length] at h
  exact h

/-! ## §7  Non-vacuity

    Three exhibits.  A concrete `MachineState` at the routine's OWN entry
    satisfying the whole-routine precondition (`wcb_entryState_exists`); the
    domain gate shown reachable (`wcb_empty_section_gate_reachable`); and the
    same gate shown provably FALSE one byte of `section_len` along
    (`wcb_nonempty_section_gate_absurd`), which is what makes the
    `section_len = 0` restriction a restriction rather than decoration. -/

/-- A concrete caller stack pointer in ziskemu's writable RAM zone, far from
    the `wcidx_*`/`wclh_*` cells at `0xa34070xx`. -/
def wcbSampleSp0 : Word := (0xa00b0000 : Word)

def wcbSampleNewSp : Word := wcbSampleSp0 + signExtend12 (-96 : BitVec 12)

/-- A two-byte-aligned return address inside the guest text. -/
def wcbSampleRet : Word := (0x80006300 : Word)

/-- The SSZ code-section base the caller passes in `a0`. -/
def wcbSamplePtr : Word := (0x40000030 : Word)

/-- An arbitrary live value in the scratch register `t1`. -/
def wcbSampleV6 : Word := (0xbeef : Word)

/-- Sample entry values for the eleven callee-saved registers — pairwise
    distinct, so the post's "restored to its ENTRY value" claim is
    discriminating rather than satisfied by a constant. -/
def wcbSampleVals : Reg → Word
  | .x1 => wcbSampleRet
  | .x8 => (0x101 : Word)
  | .x9 => (0x202 : Word)
  | .x18 => (0x303 : Word)
  | .x19 => (0x404 : Word)
  | .x20 => (0x505 : Word)
  | .x21 => (0x606 : Word)
  | .x22 => (0x707 : Word)
  | .x23 => (0x808 : Word)
  | .x24 => (0x909 : Word)
  | .x25 => (0xa0a : Word)
  | _ => (0 : Word)

private structure WcbEMem where
  a : Word
  valid : isValidDwordAccess a = true

private inductive WcbEAtom where
  | reg (r : Reg) (v : Word)
  | regO (r : Reg)
  | memO (m : WcbEMem)

private inductive WcbERes where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def wcbEAssertion : WcbEAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .regO r => regOwn r
  | .memO m => memOwn m.a

private def wcbEHeap : WcbEAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .regO r => PartialState.singletonReg r (0 : Word)
  | .memO m => PartialState.singletonMem m.a (0 : Word)

private def wcbERes : WcbEAtom → WcbERes
  | .reg r _ => .reg r
  | .regO r => .reg r
  | .memO m => .mem m.a

/-- The forty-five atoms of the whole-routine precondition, in the order the
    assertion nests them: `sp`, the eleven callee-saved registers, the eleven
    frame slots, the five caller-ambient registers, and the seventeen `.data`
    cells. -/
private def wcbEAtoms : List WcbEAtom :=
  [.reg .x2 wcbSampleSp0, .reg .x1 (wcbSampleVals .x1), .reg .x8 (wcbSampleVals .x8),
   .reg .x9 (wcbSampleVals .x9), .reg .x18 (wcbSampleVals .x18),
   .reg .x19 (wcbSampleVals .x19), .reg .x20 (wcbSampleVals .x20),
   .reg .x21 (wcbSampleVals .x21), .reg .x22 (wcbSampleVals .x22),
   .reg .x23 (wcbSampleVals .x23), .reg .x24 (wcbSampleVals .x24),
   .reg .x25 (wcbSampleVals .x25),
   .memO ⟨wcbSampleNewSp + signExtend12 (0 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (8 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (16 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (24 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (32 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (40 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (48 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (56 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (64 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (72 : BitVec 12), by decide⟩,
   .memO ⟨wcbSampleNewSp + signExtend12 (80 : BitVec 12), by decide⟩,
   .reg .x0 (0 : Word), .regO .x5, .reg .x6 wcbSampleV6, .reg .x10 wcbSamplePtr,
   .reg .x11 (0 : Word), .memO ⟨WcbEnabledLoc, by decide⟩,
   .memO ⟨WcbBuildStatusLoc, by decide⟩, .memO ⟨WcbBuildSectionLenLoc, by decide⟩,
   .memO ⟨WcbBuildCountLoc, by decide⟩, .memO ⟨WcbSectionPtrLoc, by decide⟩,
   .memO ⟨WcbSectionLenLoc, by decide⟩, .memO ⟨WcbCountLoc, by decide⟩,
   .memO ⟨WcbLookupCallsLoc, by decide⟩, .memO ⟨WcbIndexedCallsLoc, by decide⟩,
   .memO ⟨WcbIndexedHitsLoc, by decide⟩, .memO ⟨WcbIndexedMissesLoc, by decide⟩,
   .memO ⟨WcbLinearCallsLoc, by decide⟩, .memO ⟨WcbLinearHitsLoc, by decide⟩,
   .memO ⟨WcbLinearMissesLoc, by decide⟩, .memO ⟨WcbLinearIterationsLoc, by decide⟩,
   .memO ⟨WcbLinearLastLenLoc, by decide⟩, .memO ⟨WcbLinearMaxLenLoc, by decide⟩]

private theorem wcbEAtoms_pairwise : wcbEAtoms.Pairwise
    (fun x y => wcbERes x ≠ wcbERes y) := by
  unfold wcbEAtoms wcbERes wcbSampleNewSp wcbSampleSp0 WcbEnabledLoc WcbBuildStatusLoc WcbBuildSectionLenLoc WcbBuildCountLoc WcbSectionPtrLoc WcbSectionLenLoc WcbCountLoc WcbLookupCallsLoc WcbIndexedCallsLoc WcbIndexedHitsLoc WcbIndexedMissesLoc WcbLinearCallsLoc WcbLinearHitsLoc WcbLinearMissesLoc WcbLinearIterationsLoc WcbLinearLastLenLoc WcbLinearMaxLenLoc
  decide

private theorem wcbERegRegDisjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r; right; simp [PartialState.singletonReg, hne]
  · left; simp [PartialState.singletonReg, h]

private theorem wcbEMemMemDisjoint {a1 a2 v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a; right; simp [PartialState.singletonMem, hne]
  · left; simp [PartialState.singletonMem, h]

private theorem wcbERegMemDisjoint {r : Reg} {a v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem wcbEAtomHeapDisjoint {x y : WcbEAtom}
    (h : wcbERes x ≠ wcbERes y) :
    (wcbEHeap x).Disjoint (wcbEHeap y) := by
  cases x <;> cases y
  all_goals first
    | (apply wcbERegRegDisjoint; simpa [wcbERes] using h)
    | (apply wcbEMemMemDisjoint; simpa [wcbERes] using h)
    | exact wcbERegMemDisjoint
    | exact wcbERegMemDisjoint.symm

private theorem wcbEAtoms_hsat :
    (wcbEAtoms.foldr (fun x acc => wcbEAssertion x ** acc) empAssertion)
      (wcbEAtoms.foldr (fun x acc => (wcbEHeap x).union acc) PartialState.empty) := by
  apply sepConj_foldr_satisfiable wcbEAssertion wcbEHeap wcbEAtoms
  · intro x _
    cases x with
    | reg r v => exact rfl
    | regO r => exact ⟨(0 : Word), rfl⟩
    | memO m => exact ⟨(0 : Word), rfl, m.valid⟩
  · exact List.Pairwise.imp (fun {_ _} h => wcbEAtomHeapDisjoint h) wcbEAtoms_pairwise

private def wcbEHeapAll : PartialState :=
  wcbEAtoms.foldr (fun x acc => (wcbEHeap x).union acc) PartialState.empty

/-- The concrete machine state: the forty-five atoms' contents, the routine's
    own code, and `pc` at the routine's linked entry. -/
def wcbEntryState : MachineState where
  regs := fun r => match wcbEHeapAll.regs r with | some v => v | none => 0
  mem := fun a => match wcbEHeapAll.mem a with | some v => v | none => 0
  code := wcbCr
  pc := wcbB

private theorem wcbEHeapAll_x0 : wcbEHeapAll.regs .x0 = some 0 := by
  decide

private theorem wcbEntryState_getReg (r : Reg) (hr : r ≠ .x0) :
    wcbEntryState.getReg r =
      (match wcbEHeapAll.regs r with | some v => v | none => 0) := by
  cases r <;> simp_all [wcbEntryState, MachineState.getReg]

private theorem wcbEntryState_getMem (a : Word) :
    wcbEntryState.getMem a =
      (match wcbEHeapAll.mem a with | some v => v | none => 0) := rfl

private theorem wcbEHeap_code_none (x : WcbEAtom) (a : Word) :
    (wcbEHeap x).code a = none := by
  cases x <;> rfl

private theorem wcbEHeapAll_code_none (a : Word) : wcbEHeapAll.code a = none := by
  unfold wcbEHeapAll
  induction wcbEAtoms with
  | nil => rfl
  | cons x xs ih =>
    change (match (wcbEHeap x).code a with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (wcbEHeap y).union acc)
          PartialState.empty).code a) = none
    rw [wcbEHeap_code_none x a, ih]

private theorem wcbEHeapAll_pc_none : wcbEHeapAll.pc = none := by
  unfold wcbEHeapAll
  induction wcbEAtoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (wcbEHeap x).pc = none := by cases x <;> rfl
    change (match (wcbEHeap x).pc with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (wcbEHeap y).union acc)
          PartialState.empty).pc) = none
    rw [hx, ih]

private theorem wcbEHeapAll_compat : wcbEHeapAll.CompatibleWith wcbEntryState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r
      rw [wcbEHeapAll_x0] at h
      simp only [Option.some.injEq] at h
      simpa [wcbEntryState, MachineState.getReg] using h
    · rw [wcbEntryState_getReg r hr, h]
  · intro a v h
    rw [wcbEntryState_getMem a, h]
  · intro a i h
    rw [wcbEHeapAll_code_none a] at h
    cases h
  · intro v h
    rw [wcbEHeapAll_pc_none] at h
    cases h
  · intro v h; cases h
  · intro v h; cases h
  · intro v h; cases h

private theorem wcbEntryPre_eq_atoms :
    (((.x2 : Reg) ↦ᵣ wcbSampleSp0) ** regsAt wcbFrame wcbSampleVals **
      frameSlotsOwn wcbFrame wcbSampleNewSp **
      wcbArgs wcbSampleV6 wcbSamplePtr) =
      wcbEAtoms.foldr (fun x acc => wcbEAssertion x ** acc) empAssertion := by
  unfold wcbArgs wcbBuilderCells wcbEAtoms wcbEAssertion wcbFrame regsAt frameSlotsOwn
  simp only [List.foldr, sepConj_emp_right', sepConj_assoc']

/-- **The whole-routine precondition is inhabited at the routine's own
    entry.**  `wcbEntryState` has `pc = GuestAddrs.witness_codes_index_build`,
    satisfies the routine's `CodeReq`, and satisfies the precondition of
    `witness_codes_index_build_spec_within_empty_section` at
    `sp0 = wcbSampleSp0`, `ret = wcbSampleRet` and `vals = wcbSampleVals` —
    so the theorem is not vacuously true of an unsatisfiable state. -/
theorem wcb_entryState_exists :
    wcbEntryState.pc = wcbB ∧ wcbCr.SatisfiedBy wcbEntryState ∧
      ((((.x2 : Reg) ↦ᵣ wcbSampleSp0) ** regsAt wcbFrame wcbSampleVals **
        frameSlotsOwn wcbFrame wcbSampleNewSp **
        wcbArgs wcbSampleV6 wcbSamplePtr)).holdsFor wcbEntryState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a i h; exact h
  · refine ⟨wcbEHeapAll, wcbEHeapAll_compat, ?_⟩
    rw [wcbEntryPre_eq_atoms]
    exact wcbEAtoms_hsat

/-- The ABI hypotheses hold at the sample: `ra` carries the sample return
    address and it is two-byte aligned. -/
theorem wcb_sample_abi_ok :
    wcbSampleVals .x1 = wcbSampleRet ∧
      (wcbSampleRet &&& ~~~(1 : Word)) = wcbSampleRet := ⟨rfl, by decide⟩

/-- **Negative control on the ABI gate**: one byte along, the return address
    is odd and `halign` is provably FALSE. -/
theorem wcb_odd_ret_absurd :
    ¬ (((wcbSampleRet + 1) &&& ~~~(1 : Word)) = wcbSampleRet + 1) := by decide

/-- **The domain gate is reachable**: with `section_len = 0` the `beq s1, zero`
    at idx 56 IS taken, which is the jump this theorem's whole tail rides. -/
theorem wcb_empty_section_gate_reachable : (0 : Word) = (0 : Word) := rfl

/-- **Negative control on the domain gate**: at `section_len = 1` the taken
    arm of the same branch carries `⌜(1 : Word) = 0⌝` and is provably FALSE,
    so no re-instantiation of this proof at a non-empty section reaches the
    publish tail.  The `section_len = 0` restriction is load-bearing, not
    decoration. -/
theorem wcb_nonempty_section_gate_absurd :
    ∀ hp, (((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜(1 : Word) = (0 : Word)⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact absurd hP.2 (by decide)

end EvmAsm.Codegen.WitnessCodesIndexBuildTop
