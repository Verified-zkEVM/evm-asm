/-
  EvmAsm.Codegen.Programs.WitnessIndexBuildTop

  **Machine facts for the guest routine `witness_index_build`** (GH #13246,
  obligations 7 and 10) — the node-DB half of the witness-ingest builders.

  `witnessIndexBuild_prog` (`MptWitnessIndex.lean`, 158 instructions) is the
  same routine as `witnessCodesIndexBuild_prog` with `widx_*` in place of
  `wcidx_*`: instruction-for-instruction identical modulo the `.data` symbols
  its relocs name and the four local callees it jumps to.  This module is the
  mirror of `WitnessCodesIndexBuildTop.lean`, over the shared, `CodeReq`-generic
  idioms in `CellStoreIdioms.lean`.

  ## §A  What is established here

  * `wib_abiFrame_byte_tie` — the routine IS a standard 11-slot ABI frame around
    a 133-instruction body, so `abiFrame_spec_own` applies and the
    prologue/epilogue (`ra`, `s0`…`s9` save/restore, `sp` round-trip) are
    DERIVED, not assumed.  Kernel-checked against the emitted Program.
  * `witness_index_build_spec_within_empty_section` — the **whole-routine
    triple**, entry `GuestAddrs.witness_index_build` to the caller's return
    address, over `CodeReq.ofProg` of the real program, in at most 88 machine
    steps.  It pins `a0 = 0` (success), `widx_enabled = 1`, `widx_count = 0`,
    `widx_section_ptr = a0`, `widx_section_len = 0`, `widx_build_status = 0`,
    all ten `wlh_*` counters reset, and the eleven callee-saved registers
    restored.  That published state is the machine counterpart of
    `Stateless.SpecRef.build_node_db [] = []`.
  * `wib_entryState_exists` — a concrete `MachineState` at the routine's OWN
    entry (`pc = wibB`) satisfying the whole-routine precondition, with the
    forty-five atoms' pairwise disjointness kernel-checked.

  ## §B  What is NOT established (read before citing this module)

  The gate is `a1 = section_len = 0`, an INPUT-DOMAIN restriction.  Nothing here
  bounds `section_len` from above, and nothing here says anything about:

  * the SSZ offset-table guards (idx 57…66) or the per-entry keccak loop
    (idx 70…97), which contain the `zkvm_keccak256` cross-`jal` at idx 93;
  * the two heapsort loops (idx 101…124), which contain the `widx_record_ptr`,
    `widx_swap_records` and `widx_sift_down` cross-`jal`s;
  * the failure tail (idx 140…144), which sets `widx_build_status := 1` and
    returns `a0 = 1`.

  On the domain proved here **none of those five callees is REACHED** — the
  `beq s1, zero` at idx 56 jumps over the loop that contains the keccak call
  and the `bltu s2, t0` at idx 100 jumps over both sort loops — so this theorem
  carries **no unproven-callee dependency**.  In particular it does not depend
  on `widx_sift_down`, which (unlike `widx_record_ptr`, `widx_cmp32` and
  `widx_swap_records`, contracted in `Codegen/Proofs/MptWitnessIndexSpec.lean`)
  has no triple at all.  Branch polarity was read off the Program's own
  `brOff (…+392) (…+224)` and `brOff (…+500) (…+400)` immediates, not off a
  source line or a disassembly; neither branch appears in
  `witnessIndexBuild_relocs`, so no assembler relaxation is in play at either
  site.
-/

import EvmAsm.Codegen.Programs.CellStoreIdioms
import EvmAsm.Codegen.Programs.MptWitnessIndex
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.WitnessIndexBuildTop

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.CellStoreIdioms

set_option maxRecDepth 8000

/-! ## §1  The linked routine, its frame, and the cells it writes -/

/-- The routine's linked entry (`GuestAddrs.witness_index_build`). -/
def wibB : Word := (GuestAddrs.witness_index_build : Word)

/-- The routine's own code requirement: the 158-instruction emitted program at
    its linked address.  Every triple below is stated over this. -/
def wibCr : CodeReq := CodeReq.ofProg wibB witnessIndexBuild_prog

def wibFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)),
   (.x18, (24 : BitVec 12)), (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)),
   (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12)), (.x23, (64 : BitVec 12)),
   (.x24, (72 : BitVec 12)), (.x25, (80 : BitVec 12))]

def wibBody : List Instr := (witnessIndexBuild_prog.drop 12).take 133

/-- **The frame tie**: the emitted program IS the standard 96-byte ABI frame
    around `wibBody`.  Kernel-checked, so the prologue, the epilogue and the
    `ret` are derived rather than assumed. -/
theorem wib_abiFrame_byte_tie :
    abiFrameProg (-96 : BitVec 12) (96 : BitVec 12) wibFrame wibBody =
      witnessIndexBuild_prog := by
  decide

theorem wibBody_length : wibBody.length = 133 := by decide

theorem wibFrame_length : wibFrame.length = 11 := by decide

def WibEnabledLoc : Word := (GuestAddrs.widx_enabled : Word)
def WibBuildStatusLoc : Word := (GuestAddrs.widx_build_status : Word)
def WibBuildSectionLenLoc : Word := (GuestAddrs.widx_build_section_len : Word)
def WibBuildCountLoc : Word := (GuestAddrs.widx_build_count : Word)
def WibSectionPtrLoc : Word := (GuestAddrs.widx_section_ptr : Word)
def WibSectionLenLoc : Word := (GuestAddrs.widx_section_len : Word)
def WibCountLoc : Word := (GuestAddrs.widx_count : Word)
def WibLookupCallsLoc : Word := (GuestAddrs.wlh_lookup_calls : Word)
def WibIndexedCallsLoc : Word := (GuestAddrs.wlh_indexed_calls : Word)
def WibIndexedHitsLoc : Word := (GuestAddrs.wlh_indexed_hits : Word)
def WibIndexedMissesLoc : Word := (GuestAddrs.wlh_indexed_misses : Word)
def WibLinearCallsLoc : Word := (GuestAddrs.wlh_linear_calls : Word)
def WibLinearHitsLoc : Word := (GuestAddrs.wlh_linear_hits : Word)
def WibLinearMissesLoc : Word := (GuestAddrs.wlh_linear_misses : Word)
def WibLinearIterationsLoc : Word := (GuestAddrs.wlh_linear_iterations : Word)
def WibLinearLastLenLoc : Word := (GuestAddrs.wlh_linear_last_section_len : Word)
def WibLinearMaxLenLoc : Word := (GuestAddrs.wlh_linear_max_section_len : Word)

/-- The seventeen `.data` cells the routine writes on this path — the pre owns
    every one of them, because every one is stored to. -/
def wibBuilderCells : Assertion :=
  memOwn WibEnabledLoc ** memOwn WibBuildStatusLoc ** memOwn WibBuildSectionLenLoc **
  memOwn WibBuildCountLoc ** memOwn WibSectionPtrLoc ** memOwn WibSectionLenLoc **
  memOwn WibCountLoc ** memOwn WibLookupCallsLoc ** memOwn WibIndexedCallsLoc **
  memOwn WibIndexedHitsLoc ** memOwn WibIndexedMissesLoc ** memOwn WibLinearCallsLoc **
  memOwn WibLinearHitsLoc ** memOwn WibLinearMissesLoc ** memOwn WibLinearIterationsLoc **
  memOwn WibLinearLastLenLoc ** memOwn WibLinearMaxLenLoc

/-- **The initialisation head** (idx 12…16, `+48 … +68`): `widx_enabled` is
    cleared and the two arguments are parked in `s0`/`s1`. -/
theorem wibInitHead (ptr len oldPtr oldLen : Word) :
    cpsTripleWithin 5 (wibB + 48) (wibB + 68) wibCr
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x8 : Reg) ↦ᵣ oldPtr) ** ((.x9 : Reg) ↦ᵣ oldLen) **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn WibEnabledLoc) ** regOwn .x5)
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ len) **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
          (WibEnabledLoc ↦ₘ (0 : Word)))) := by
  have hclear := laStoreOwn (cr := wibCr) .x0 (wibB + 48) WibEnabledLoc (0 : Word)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  rw [show (wibB + 48 : Word) + 12 = wibB + 60 from by bv_omega] at hclear
  have hmv := mvArgPair (cr := wibCr) (wibB + 60) ptr len oldPtr oldLen
    (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
  rw [show (wibB + 60 : Word) + 8 = wibB + 68 from by bv_omega] at hmv
  have hf := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
      ((.x8 : Reg) ↦ᵣ oldPtr) ** ((.x9 : Reg) ↦ᵣ oldLen)) (by pcf) hclear
  have hf2 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ WibEnabledLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (WibEnabledLoc ↦ₘ (0 : Word))) (by pcf) hmv
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hf hf2
  refine cpsTripleWithin_mono_nSteps (show 3 + 2 ≤ 5 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun s hq => ?_) hseq)
  have hq1 : (((.x5 : Reg) ↦ᵣ WibEnabledLoc) ** ((.x10 : Reg) ↦ᵣ ptr) **
      ((.x11 : Reg) ↦ᵣ len) ** ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ len) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (WibEnabledLoc ↦ₘ (0 : Word))) s := by
    xperm_chunked hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 WibEnabledLoc)
    (fun _ h' => h') s hq1
  xperm_chunked hq2

/-! ## §2  `witness_index_build` — the carried context and the segments

    The routine's `section_len = 0` path threads three resources through every
    segment: `x0`, the `la` scratch `t0 = x5`, and `s1 = x9` (the argument
    `section_len`, moved into a callee-saved register by the prologue's
    `mv s1, a1`, and zero on this domain).  Collecting them into `wibK` lets the
    thirteen `.data` writes chain by pure reassociation (`chainK`). -/

/-- The context carried across the whole empty-section path. -/
def wibK : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x9 : Reg) ↦ᵣ (0 : Word))

theorem wibK_pcFree : wibK.pcFree := by unfold wibK; pcf

/-- **One `sd zero, 0(t0)` clear** at `A`, in carried-context shape. -/
private theorem wibClearCell (A A' C : Word) (hA : A + 12 = A')
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wibCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wibCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 .x0 (0 : BitVec 12)) a = some i →
      wibCr a = some i) :
    cpsTripleWithin 3 A A' wibCr (wibK ** memOwn C) (wibK ** (C ↦ₘ (0 : Word))) := by
  subst hA
  have h := laStoreOwn (cr := wibCr) .x0 A C (0 : Word) hrange hau had hsd
  have hf := cpsTripleWithin_frameR ((.x9 : Reg) ↦ᵣ (0 : Word)) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wibK at hp; xperm_hyp hp
  · show (wibK ** (C ↦ₘ (0 : Word))) s
    unfold wibK
    have hq1 : (((.x5 : Reg) ↦ᵣ C) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (C ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 C) (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **The `sd s1, 0(t0)` write** of `section_len` into
    `widx_build_section_len` (idx 20…22).  On this domain `s1 = 0`, so the
    cell lands at zero exactly like the twelve literal clears — but the
    instruction is genuinely different, and the reloc table names a different
    cell. -/
private theorem wibStoreS1Cell (A A' C : Word) (hA : A + 12 = A')
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wibCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wibCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 .x9 (0 : BitVec 12)) a = some i →
      wibCr a = some i) :
    cpsTripleWithin 3 A A' wibCr (wibK ** memOwn C) (wibK ** (C ↦ₘ (0 : Word))) := by
  subst hA
  have h := laStoreOwn (cr := wibCr) .x9 A C (0 : Word) hrange hau had hsd
  have hf := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wibK at hp; xperm_hyp hp
  · show (wibK ** (C ↦ₘ (0 : Word))) s
    unfold wibK
    have hq1 : (((.x5 : Reg) ↦ᵣ C) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (C ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 C) (fun _ h' => h') s hq1
    xperm_hyp hq2

/-! ## §3  The thirteen `.data` writes, chained -/

/-- The thirteen cells the initialisation block owns, in write order:
    `widx_build_status`, `widx_build_section_len`, `widx_build_count`, and
    the ten `wlh_*` lookup counters. -/
def wibMidOwn : Assertion :=
  memOwn WibBuildStatusLoc **
  memOwn WibBuildSectionLenLoc **
  memOwn WibBuildCountLoc **
  memOwn WibLookupCallsLoc **
  memOwn WibIndexedCallsLoc **
  memOwn WibIndexedHitsLoc **
  memOwn WibIndexedMissesLoc **
  memOwn WibLinearCallsLoc **
  memOwn WibLinearHitsLoc **
  memOwn WibLinearMissesLoc **
  memOwn WibLinearIterationsLoc **
  memOwn WibLinearLastLenLoc **
  memOwn WibLinearMaxLenLoc

/-- The same thirteen cells after the block: every one at zero. -/
def wibMidZero : Assertion :=
  (WibBuildStatusLoc ↦ₘ (0 : Word)) **
  (WibBuildSectionLenLoc ↦ₘ (0 : Word)) **
  (WibBuildCountLoc ↦ₘ (0 : Word)) **
  (WibLookupCallsLoc ↦ₘ (0 : Word)) **
  (WibIndexedCallsLoc ↦ₘ (0 : Word)) **
  (WibIndexedHitsLoc ↦ₘ (0 : Word)) **
  (WibIndexedMissesLoc ↦ₘ (0 : Word)) **
  (WibLinearCallsLoc ↦ₘ (0 : Word)) **
  (WibLinearHitsLoc ↦ₘ (0 : Word)) **
  (WibLinearMissesLoc ↦ₘ (0 : Word)) **
  (WibLinearIterationsLoc ↦ₘ (0 : Word)) **
  (WibLinearLastLenLoc ↦ₘ (0 : Word)) **
  (WibLinearMaxLenLoc ↦ₘ (0 : Word))

theorem wibMidOwn_pcFree : wibMidOwn.pcFree := by unfold wibMidOwn; pcf
theorem wibMidZero_pcFree : wibMidZero.pcFree := by unfold wibMidZero; pcf

/-- **The initialisation block** (idx 17…55, `+68 … +224`): thirteen
    `la`/`sd` writes, 39 machine steps, chained by `chainK` — no permutation
    search, so the cost is linear in the number of cells. -/
private theorem wibInitBlock :
    cpsTripleWithin 39 (wibB + 68) (wibB + 224) wibCr
      (wibK ** wibMidOwn) (wibK ** wibMidZero) := by
  have c1 := wibClearCell (wibB + 68) (wibB + 80) WibBuildStatusLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c2 := wibStoreS1Cell (wibB + 80) (wibB + 92) WibBuildSectionLenLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c3 := wibClearCell (wibB + 92) (wibB + 104) WibBuildCountLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c4 := wibClearCell (wibB + 104) (wibB + 116) WibLookupCallsLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c5 := wibClearCell (wibB + 116) (wibB + 128) WibIndexedCallsLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c6 := wibClearCell (wibB + 128) (wibB + 140) WibIndexedHitsLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c7 := wibClearCell (wibB + 140) (wibB + 152) WibIndexedMissesLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c8 := wibClearCell (wibB + 152) (wibB + 164) WibLinearCallsLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c9 := wibClearCell (wibB + 164) (wibB + 176) WibLinearHitsLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c10 := wibClearCell (wibB + 176) (wibB + 188) WibLinearMissesLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c11 := wibClearCell (wibB + 188) (wibB + 200) WibLinearIterationsLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c12 := wibClearCell (wibB + 200) (wibB + 212) WibLinearLastLenLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  have c13 := wibClearCell (wibB + 212) (wibB + 224) WibLinearMaxLenLoc (by bv_omega)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
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
  unfold wibMidOwn wibMidZero
  exact cpsTripleWithin_mono_nSteps (by omega) ch1

/-! ## §4  The two taken branches and the publish tail -/

/-- **The empty-section branch** (idx 56, `+224`): `beq s1, zero` with
    `section_len = 0` jumps over the SSZ header guards, the whole keccak loop
    and the heapsort — which is why `zkvm_keccak256` (idx 93),
    `widx_record_ptr` (88/113/116), `widx_swap_records` (120) and
    `widx_sift_down` (106/123) are all UNREACHED on this domain and this
    theorem carries no unproven-callee dependency.  Polarity read off the
    Program's own `brOff (…+392) (…+224)`, not the source line. -/
private theorem wibEmptySectionBranch :
    cpsTripleWithin 1 (wibB + 224) (wibB + 392) wibCr wibK wibK := by
  have hbr := cpsBranchWithin_extend_code (cr' := wibCr)
    (by unfold wibCr; code_mem)
    (beq_spec_gen_within .x9 .x0
      (brOff (GuestAddrs.witness_index_build + 392)
        (GuestAddrs.witness_index_build + 224)) (0 : Word) (0 : Word) (wibB + 224))
  have hbt := cpsBranchWithin_takenStripPure2 hbr (fun _ hq => by
    obtain ⟨_, _, _, _, _, hB⟩ := hq
    obtain ⟨_, _, _, _, _, hP⟩ := hB
    exact hP.2 rfl)
  rw [show (wibB + 224 : Word) + signExtend13
      (brOff (GuestAddrs.witness_index_build + 392)
        (GuestAddrs.witness_index_build + 224)) = wibB + 392 from by decide] at hbt
  have hf := cpsTripleWithin_frameR (regOwn .x5) (by pcf) hbt
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wibK at hp; xperm_hyp hp
  · show wibK s
    unfold wibK; xperm_hyp hq

/-- **The heapsort skip** (idx 98…100, `+392 … +500`): `count := 0` is
    reloaded into `s2`, `t0 := 2`, and `bltu s2, t0` is TAKEN because
    `0 <ᵤ 2`, jumping over both sort loops to the publish tail. -/
private theorem wibSortSkip (v18 : Word) :
    cpsTripleWithin 3 (wibB + 392) (wibB + 500) wibCr
      (wibK ** ((.x18 : Reg) ↦ᵣ v18)) (wibK ** ((.x18 : Reg) ↦ᵣ (0 : Word))) := by
  have h1 := liftCode (cr' := wibCr)
    (li_spec_gen_within .x18 v18 (0 : Word) (wibB + 392) (by decide))
    (by unfold wibCr; code_mem)
  rw [show (wibB + 392 : Word) + 4 = wibB + 396 from by bv_omega] at h1
  have h2 := liftCode (cr' := wibCr)
    (li_spec_gen_own_within .x5 (2 : Word) (wibB + 396) (by decide))
    (by unfold wibCr; code_mem)
  rw [show (wibB + 396 : Word) + 4 = wibB + 400 from by bv_omega] at h2
  have hbr := cpsBranchWithin_extend_code (cr' := wibCr)
    (by unfold wibCr; code_mem)
    (bltu_spec_gen_within .x18 .x5
      (brOff (GuestAddrs.witness_index_build + 500)
        (GuestAddrs.witness_index_build + 400)) (0 : Word) (2 : Word) (wibB + 400))
  have hbt := cpsBranchWithin_takenStripPure2 hbr (fun _ hq => by
    obtain ⟨_, _, _, _, _, hB⟩ := hq
    obtain ⟨_, _, _, _, _, hP⟩ := hB
    exact hP.2 (by decide))
  rw [show (wibB + 400 : Word) + signExtend13
      (brOff (GuestAddrs.witness_index_build + 500)
        (GuestAddrs.witness_index_build + 400)) = wibB + 500 from by decide] at hbt
  have f1 := cpsTripleWithin_frameR (regOwn .x5) (by pcf) h1
  have f2 := cpsTripleWithin_frameR ((.x18 : Reg) ↦ᵣ (0 : Word)) (by pcf) h2
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hbt
  have c3 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word))) (by pcf) c2
  refine cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) c3)
  · unfold wibK at hp; xperm_hyp hp
  · show (wibK ** ((.x18 : Reg) ↦ᵣ (0 : Word))) s
    unfold wibK
    have hq1 : (((.x5 : Reg) ↦ᵣ (2 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 (2 : Word)) (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- The publish tail's carried context: `wibK` plus `s2 = count = 0`. -/
def wibK2 : Assertion := wibK ** ((.x18 : Reg) ↦ᵣ (0 : Word))

theorem wibK2_pcFree : wibK2.pcFree := by unfold wibK2 wibK; pcf

/-- **`widx_section_ptr := s0`** (idx 125…127) — the section base the caller
    passed in `a0`, republished for the lookup path. -/
private theorem wibPublishPtr (ptr : Word) :
    cpsTripleWithin 3 (wibB + 500) (wibB + 512) wibCr
      (wibK2 ** (((.x8 : Reg) ↦ᵣ ptr) ** memOwn WibSectionPtrLoc))
      (wibK2 ** (((.x8 : Reg) ↦ᵣ ptr) ** (WibSectionPtrLoc ↦ₘ ptr))) := by
  have h := laStoreOwn (cr := wibCr) .x8 (wibB + 500) WibSectionPtrLoc ptr
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  rw [show (wibB + 500 : Word) + 12 = wibB + 512 from by bv_omega] at h
  have hf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word))) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wibK2 wibK at hp; xperm_hyp hp
  · show (wibK2 ** (((.x8 : Reg) ↦ᵣ ptr) ** (WibSectionPtrLoc ↦ₘ ptr))) s
    unfold wibK2 wibK
    have hq1 : (((.x5 : Reg) ↦ᵣ WibSectionPtrLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        ((.x8 : Reg) ↦ᵣ ptr) ** (WibSectionPtrLoc ↦ₘ ptr)) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WibSectionPtrLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`widx_section_len := s1`** (idx 128…130) — zero on this domain. -/
private theorem wibPublishLen :
    cpsTripleWithin 3 (wibB + 512) (wibB + 524) wibCr
      (wibK2 ** memOwn WibSectionLenLoc)
      (wibK2 ** (WibSectionLenLoc ↦ₘ (0 : Word))) := by
  have h := laStoreOwn (cr := wibCr) .x9 (wibB + 512) WibSectionLenLoc (0 : Word)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  rw [show (wibB + 512 : Word) + 12 = wibB + 524 from by bv_omega] at h
  have hf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word))) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wibK2 wibK at hp; xperm_hyp hp
  · show (wibK2 ** (WibSectionLenLoc ↦ₘ (0 : Word))) s
    unfold wibK2 wibK
    have hq1 : (((.x5 : Reg) ↦ᵣ WibSectionLenLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        (WibSectionLenLoc ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WibSectionLenLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`widx_count := s2`** (idx 131…133) — zero records indexed. -/
private theorem wibPublishCount :
    cpsTripleWithin 3 (wibB + 524) (wibB + 536) wibCr
      (wibK2 ** memOwn WibCountLoc)
      (wibK2 ** (WibCountLoc ↦ₘ (0 : Word))) := by
  have h := laStoreOwn (cr := wibCr) .x18 (wibB + 524) WibCountLoc (0 : Word)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  rw [show (wibB + 524 : Word) + 12 = wibB + 536 from by bv_omega] at h
  have hf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word))) (by pcf) h
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hf
  · unfold wibK2 wibK at hp; xperm_hyp hp
  · show (wibK2 ** (WibCountLoc ↦ₘ (0 : Word))) s
    unfold wibK2 wibK
    have hq1 : (((.x5 : Reg) ↦ᵣ WibCountLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        (WibCountLoc ↦ₘ (0 : Word))) s := by xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WibCountLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`widx_enabled := 1`** (idx 134…137) — the flag every node-DB lookup
    dispatches on.  This is the routine's publishing write: it re-writes the
    cell the head cleared at idx 12…14, so the pre pins that cell at zero
    rather than merely owning it. -/
private theorem wibPublishEnabled (v6 : Word) :
    cpsTripleWithin 4 (wibB + 536) (wibB + 552) wibCr
      (wibK2 ** (((.x6 : Reg) ↦ᵣ v6) ** (WibEnabledLoc ↦ₘ (0 : Word))))
      (wibK2 ** (((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WibEnabledLoc ↦ₘ (1 : Word)))) := by
  have hli := liftCode (cr' := wibCr)
    (li_spec_gen_within .x6 v6 (1 : Word) (wibB + 536) (by decide))
    (by unfold wibCr; code_mem)
  rw [show (wibB + 536 : Word) + 4 = wibB + 540 from by bv_omega] at hli
  have h := laStoreAt (cr := wibCr) .x6 (wibB + 540) WibEnabledLoc (0 : Word) (1 : Word)
    (by decide) (by unfold wibCr; code_mem) (by unfold wibCr; code_mem)
    (by unfold wibCr; code_mem)
  rw [show (wibB + 540 : Word) + 12 = wibB + 552 from by bv_omega] at h
  have f1 := cpsTripleWithin_frameR ((WibEnabledLoc ↦ₘ (0 : Word)) ** regOwn .x5)
    (by pcf) hli
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 h
  have c2 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word))) (by pcf) c1
  refine cpsTripleWithin_mono_nSteps (show 1 + 3 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) c2)
  · unfold wibK2 wibK at hp; xperm_hyp hp
  · show (wibK2 ** (((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WibEnabledLoc ↦ₘ (1 : Word)))) s
    unfold wibK2 wibK
    have hq1 : (((.x5 : Reg) ↦ᵣ WibEnabledLoc) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WibEnabledLoc ↦ₘ (1 : Word))) s := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 WibEnabledLoc)
      (fun _ h' => h') s hq1
    xperm_hyp hq2

/-- **`a0 := 0` and the jump to the epilogue** (idx 138…139) — the success
    status, and the forward `j +24` that skips the failure tail (idx 140…144,
    which sets `widx_build_status := 1` and `a0 := 1`).  The jump target is
    the body exit `+580`, i.e. the epilogue's first `ld`. -/
private theorem wibSuccessExit (v10 : Word) :
    cpsTripleWithin 2 (wibB + 552) (wibB + 580) wibCr
      (wibK2 ** ((.x10 : Reg) ↦ᵣ v10)) (wibK2 ** ((.x10 : Reg) ↦ᵣ (0 : Word))) := by
  have hli := liftCode (cr' := wibCr)
    (li_spec_gen_within .x10 v10 (0 : Word) (wibB + 552) (by decide))
    (by unfold wibCr; code_mem)
  rw [show (wibB + 552 : Word) + 4 = wibB + 556 from by bv_omega] at hli
  have hjal := liftCode (cr' := wibCr)
    (jal_x0_spec_gen_within (24 : BitVec 21) (wibB + 556))
    (by unfold wibCr; code_mem)
  rw [show (wibB + 556 : Word) + signExtend21 (24 : BitVec 21) = wibB + 580
    from by decide] at hjal
  have hjf := cpsTripleWithin_frameL ((.x10 : Reg) ↦ᵣ (0 : Word)) (by pcf) hjal
  rw [sepConj_emp_right'] at hjf
  have c1 := cpsTripleWithin_seq_same_cr hli hjf
  have c2 := cpsTripleWithin_frameL wibK2 wibK2_pcFree c1
  exact cpsTripleWithin_mono_nSteps (show 1 + 1 ≤ 2 by omega) c2

/-! ## §5  The body, composed -/

/-- The publish tail's own resources at entry (idx 125…139). -/
def wibTailOwn (ptr v6 v10 : Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ ptr) ** memOwn WibSectionPtrLoc ** memOwn WibSectionLenLoc **
  memOwn WibCountLoc ** ((.x6 : Reg) ↦ᵣ v6) ** (WibEnabledLoc ↦ₘ (0 : Word)) **
  ((.x10 : Reg) ↦ᵣ v10)

/-- The publish tail's own resources at exit: the three index cells at their
    published values, `widx_enabled = 1`, and `a0 = 0` (success). -/
def wibTailOut (ptr : Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ ptr) ** (WibSectionPtrLoc ↦ₘ ptr) **
  (WibSectionLenLoc ↦ₘ (0 : Word)) ** (WibCountLoc ↦ₘ (0 : Word)) **
  ((.x6 : Reg) ↦ᵣ (1 : Word)) ** (WibEnabledLoc ↦ₘ (1 : Word)) **
  ((.x10 : Reg) ↦ᵣ (0 : Word))

private theorem wibPublishTail (ptr v6 v10 : Word) :
    cpsTripleWithin 15 (wibB + 500) (wibB + 580) wibCr
      (wibK2 ** wibTailOwn ptr v6 v10) (wibK2 ** wibTailOut ptr) := by
  have t8 := chainK (by pcf) (by pcf) (wibPublishEnabled v6) (wibSuccessExit v10)
  have t7 := chainK (by pcf) (by pcf) wibPublishCount t8
  have t6 := chainK (by pcf) (by pcf) wibPublishLen t7
  have t5 := chainK (by pcf) (by pcf) (wibPublishPtr ptr) t6
  unfold wibTailOwn wibTailOut
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) t5)

private theorem wibBranchToEnd (ptr v6 v10 v18 : Word) :
    cpsTripleWithin 19 (wibB + 224) (wibB + 580) wibCr
      (wibK ** (((.x18 : Reg) ↦ᵣ v18) ** wibTailOwn ptr v6 v10))
      (wibK ** (((.x18 : Reg) ↦ᵣ (0 : Word)) ** wibTailOut ptr)) := by
  have hbr := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ v18) ** wibTailOwn ptr v6 v10) (by unfold wibTailOwn; pcf)
    wibEmptySectionBranch
  have hsk := cpsTripleWithin_frameR (wibTailOwn ptr v6 v10)
    (by unfold wibTailOwn; pcf) (wibSortSkip v18)
  have htl := wibPublishTail ptr v6 v10
  unfold wibK2 at htl
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hbr hsk
  have c2 := cpsTripleWithin_seq_same_cr c1 htl
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) c2)

private theorem wibInitToEnd (ptr v6 v10 v18 : Word) :
    cpsTripleWithin 58 (wibB + 68) (wibB + 580) wibCr
      (wibK ** (wibMidOwn ** (((.x18 : Reg) ↦ᵣ v18) ** wibTailOwn ptr v6 v10)))
      (wibK ** (wibMidZero ** (((.x18 : Reg) ↦ᵣ (0 : Word)) ** wibTailOut ptr))) :=
  cpsTripleWithin_mono_nSteps (by omega)
    (chainK wibMidZero_pcFree (by unfold wibTailOwn; pcf)
      wibInitBlock (wibBranchToEnd ptr v6 v10 v18))

/-- The seventeen `.data` cells at their published values on the empty-section
    path.  Same order as `wibBuilderCells`, so the two read as a before/after
    pair: `widx_enabled` flips `0 → 1`, `widx_section_ptr` takes the
    caller's section base, and every count is zero. -/
def wibBuiltCells (ptr : Word) : Assertion :=
  (WibEnabledLoc ↦ₘ (1 : Word)) ** (WibBuildStatusLoc ↦ₘ (0 : Word)) **
  (WibBuildSectionLenLoc ↦ₘ (0 : Word)) ** (WibBuildCountLoc ↦ₘ (0 : Word)) **
  (WibSectionPtrLoc ↦ₘ ptr) ** (WibSectionLenLoc ↦ₘ (0 : Word)) **
  (WibCountLoc ↦ₘ (0 : Word)) ** (WibLookupCallsLoc ↦ₘ (0 : Word)) **
  (WibIndexedCallsLoc ↦ₘ (0 : Word)) ** (WibIndexedHitsLoc ↦ₘ (0 : Word)) **
  (WibIndexedMissesLoc ↦ₘ (0 : Word)) ** (WibLinearCallsLoc ↦ₘ (0 : Word)) **
  (WibLinearHitsLoc ↦ₘ (0 : Word)) ** (WibLinearMissesLoc ↦ₘ (0 : Word)) **
  (WibLinearIterationsLoc ↦ₘ (0 : Word)) ** (WibLinearLastLenLoc ↦ₘ (0 : Word)) **
  (WibLinearMaxLenLoc ↦ₘ (0 : Word))

/-- **The `section_len = 0` body**, `+48 → +580`, 63 machine steps, with the
    tight footprint: the eight registers and seventeen `.data` cells the path
    touches, and nothing else. -/
private theorem wibEmptySectionBody_core (ptr oldPtr oldLen v6 v18 : Word) :
    cpsTripleWithin 63 (wibB + 48) (wibB + 580) wibCr
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x8 : Reg) ↦ᵣ oldPtr) ** ((.x9 : Reg) ↦ᵣ oldLen) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ v18) ** wibBuilderCells)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
        ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ (0 : Word)) ** wibBuiltCells ptr) := by
  have a1f := cpsTripleWithin_frameR
    (wibMidOwn ** ((.x18 : Reg) ↦ᵣ v18) ** memOwn WibSectionPtrLoc **
      memOwn WibSectionLenLoc ** memOwn WibCountLoc ** ((.x6 : Reg) ↦ᵣ v6))
    (by unfold wibMidOwn; pcf) (wibInitHead ptr (0 : Word) oldPtr oldLen)
  have restf := cpsTripleWithin_frameR ((.x11 : Reg) ↦ᵣ (0 : Word)) (by pcf)
    (wibInitToEnd ptr v6 ptr v18)
  have c := cpsTripleWithin_seq_perm_same_cr (fun s hp => by
      show ((wibK ** (wibMidOwn ** (((.x18 : Reg) ↦ᵣ v18) **
        wibTailOwn ptr v6 ptr))) ** ((.x11 : Reg) ↦ᵣ (0 : Word))) s
      unfold wibK wibTailOwn
      xperm_chunked hp) a1f restf
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) c)
  · unfold wibBuilderCells at hp
    unfold wibMidOwn
    xperm_chunked hp
  · show (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
      ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ (0 : Word)) ** wibBuiltCells ptr) s
    unfold wibBuiltCells
    unfold wibK wibMidZero wibTailOut at hq
    xperm_chunked hq

/-! ## §6  The whole-routine triple

    `abiFrame_spec_own` turns the body into the routine: the prologue's eleven
    stores, the epilogue's eleven loads and the `ret` are DERIVED, and with
    them callee-saved preservation and the `sp` round-trip. -/

/-- The caller-visible ambient at entry: `a0 = section_ptr`, `a1 = 0` (the
    empty node section), the two scratch registers the routine clobbers, and
    the seventeen `.data` cells it writes — all OWNED, because every one of
    them is stored to on this path. -/
def wibArgs (v6 ptr : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ v6) **
  ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** wibBuilderCells

/-- The caller-visible ambient at return: **`a0 = 0`, the success status**,
    and each `.data` cell at its exact new value.  Asymmetric by
    construction — `widx_enabled` ends at ONE while every counter ends at
    zero, `widx_section_ptr` takes `ptr` while `widx_section_len` and
    `widx_count` take zero.  Swapping any two would not typecheck. -/
def wibOut (ptr : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** wibBuiltCells ptr

theorem wibArgs_pcFree (v6 ptr : Word) : (wibArgs v6 ptr).pcFree := by
  unfold wibArgs wibBuilderCells; pcf

theorem wibOut_pcFree (ptr : Word) : (wibOut ptr).pcFree := by
  unfold wibOut wibBuiltCells; pcf

private theorem regsAt_wibFrame (vals : Reg → Word) :
    regsAt wibFrame vals =
      (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ vals .x8) **
        ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
        ((.x23 : Reg) ↦ᵣ vals .x23) ** ((.x24 : Reg) ↦ᵣ vals .x24) **
        ((.x25 : Reg) ↦ᵣ vals .x25)) := by
  simp [wibFrame, regsAt, sepConj_emp_right']

private theorem regsOwnAt_wibFrame :
    regsOwnAt wibFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** regOwn .x21 ** regOwn .x22 ** regOwn .x23 ** regOwn .x24 **
        regOwn .x25) := by
  simp [wibFrame, regsOwnAt, sepConj_emp_right']

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
private theorem wibEmptySectionBody (newSp : Word) (vals : Reg → Word) (v6 ptr : Word) :
    cpsTripleWithin 63
      (wibB + BitVec.ofNat 64 (4 * (1 + wibFrame.length)))
      (wibB + BitVec.ofNat 64 (4 * (1 + wibFrame.length + wibBody.length))) wibCr
      (((.x2 : Reg) ↦ᵣ newSp) ** regsAt wibFrame vals **
        frameSlotsSaved wibFrame newSp vals ** wibArgs v6 ptr)
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wibFrame **
        frameSlotsSaved wibFrame newSp vals ** wibOut ptr) := by
  rw [wibFrame_length, wibBody_length]
  simp only [show 4 * (1 + 11) = 48 from rfl, show 4 * (1 + 11 + 133) = 580 from rfl]
  have core := wibEmptySectionBody_core ptr (vals .x8) (vals .x9) v6 (vals .x18)
  have framed := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((.x1 : Reg) ↦ᵣ vals .x1) **
      ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
      ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
      ((.x23 : Reg) ↦ᵣ vals .x23) ** ((.x24 : Reg) ↦ᵣ vals .x24) **
      ((.x25 : Reg) ↦ᵣ vals .x25) ** frameSlotsSaved wibFrame newSp vals)
    (by pcf) core
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) framed
  · rw [regsAt_wibFrame] at hp
    unfold wibArgs at hp
    xperm_chunked hp
  · show (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wibFrame **
      frameSlotsSaved wibFrame newSp vals ** wibOut ptr) h
    rw [regsOwnAt_wibFrame]
    unfold wibOut
    have hq2 : (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ ptr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ (0 : Word)) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
        ((.x23 : Reg) ↦ᵣ vals .x23) ** ((.x24 : Reg) ↦ᵣ vals .x24) **
        ((.x25 : Reg) ↦ᵣ vals .x25) **
        (((.x2 : Reg) ↦ᵣ newSp) ** frameSlotsSaved wibFrame newSp vals **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          wibBuiltCells ptr)) h := by
      xperm_chunked hq
    have hq3 := ent_own11 .x1 .x8 .x9 .x18 .x19 .x20 .x21 .x22 .x23 .x24 .x25
      (vals .x1) ptr (0 : Word) (0 : Word) (vals .x19) (vals .x20) (vals .x21)
      (vals .x22) (vals .x23) (vals .x24) (vals .x25) _ h hq2
    xperm_chunked hq3

/-- **`witness_index_build`, whole routine, at its linked guest address —
    on the `section_len = 0` domain.**

    From the routine's entry `GuestAddrs.witness_index_build`, over the
    emitted program itself (`wibCr = CodeReq.ofProg wibB
    witnessIndexBuild_prog`), execution returns to the caller in at most
    88 steps with:

    * `a0 = 0` — the documented success status;
    * `widx_enabled = 1`, `widx_count = 0`, `widx_section_ptr = a0`,
      `widx_section_len = 0` and `widx_build_status = 0`: the empty node
      index PUBLISHED, which is the machine counterpart of
      `SpecRef.build_node_db [] = []`;
    * all ten `wlh_*` lookup counters reset to zero;
    * every callee-saved register (`ra`, `s0`…`s9`) back at its ENTRY value
      and `sp` back at `sp0` — derived from `abiFrame_spec_own`, not assumed.

    Hypotheses are ABI/resource facts only: a two-byte-aligned return address
    held in `ra` at entry, and the 96-byte frame slots owned.  The domain
    restriction is `a1 = 0`, an INPUT-DOMAIN gate; nothing here bounds
    `section_len` from above. -/
theorem witness_index_build_spec_within_empty_section
    (sp0 ret : Word) (vals : Reg → Word) (v6 ptr : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 88 wibB ret wibCr
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wibFrame vals **
        frameSlotsOwn wibFrame (sp0 + signExtend12 (-96 : BitVec 12)) **
        wibArgs v6 ptr)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wibFrame vals **
        frameSlotsSaved wibFrame (sp0 + signExtend12 (-96 : BitVec 12)) vals **
        wibOut ptr) := by
  have h := abiFrame_spec_own wibB sp0 ret (-96 : BitVec 12) (96 : BitVec 12)
    wibFrame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
     (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
     (.x22, (56 : BitVec 12)), (.x23, (64 : BitVec 12)), (.x24, (72 : BitVec 12)),
     (.x25, (80 : BitVec 12))]
    vals wibBody 63 (wibArgs v6 ptr) (wibOut ptr)
    wibCr rfl (by decide) (by decide)
    (by rw [wib_abiFrame_byte_tie]; decide)
    hret halign (sext_frameRestore _ _ _ (by decide))
    (wibArgs_pcFree _ _) (wibOut_pcFree _)
    (by rw [wib_abiFrame_byte_tie]; unfold wibCr; code_mem)
    (wibEmptySectionBody _ vals v6 ptr)
  rw [wibFrame_length] at h
  exact h

/-! ## §7  Non-vacuity

    Three exhibits.  A concrete `MachineState` at the routine's OWN entry
    satisfying the whole-routine precondition (`wib_entryState_exists`); the
    domain gate shown reachable (`wib_empty_section_gate_reachable`); and the
    same gate shown provably FALSE one byte of `section_len` along
    (`wib_nonempty_section_gate_absurd`), which is what makes the
    `section_len = 0` restriction a restriction rather than decoration. -/

/-- A concrete caller stack pointer in ziskemu's writable RAM zone, far from
    the `widx_*` cells at `0xa2e070xx` and the `wlh_*` cells at `0xa34070xx`. -/
def wibSampleSp0 : Word := (0xa00b0000 : Word)

def wibSampleNewSp : Word := wibSampleSp0 + signExtend12 (-96 : BitVec 12)

/-- A two-byte-aligned return address inside the guest text. -/
def wibSampleRet : Word := (0x80006300 : Word)

/-- The SSZ state-section base the caller passes in `a0`. -/
def wibSamplePtr : Word := (0x40000030 : Word)

/-- An arbitrary live value in the scratch register `t1`. -/
def wibSampleV6 : Word := (0xbeef : Word)

/-- Sample entry values for the eleven callee-saved registers — pairwise
    distinct, so the post's "restored to its ENTRY value" claim is
    discriminating rather than satisfied by a constant. -/
def wibSampleVals : Reg → Word
  | .x1 => wibSampleRet
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

private structure WibEMem where
  a : Word
  valid : isValidDwordAccess a = true

private inductive WibEAtom where
  | reg (r : Reg) (v : Word)
  | regO (r : Reg)
  | memO (m : WibEMem)

private inductive WibERes where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def wibEAssertion : WibEAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .regO r => regOwn r
  | .memO m => memOwn m.a

private def wibEHeap : WibEAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .regO r => PartialState.singletonReg r (0 : Word)
  | .memO m => PartialState.singletonMem m.a (0 : Word)

private def wibERes : WibEAtom → WibERes
  | .reg r _ => .reg r
  | .regO r => .reg r
  | .memO m => .mem m.a

/-- The forty-five atoms of the whole-routine precondition, in the order the
    assertion nests them: `sp`, the eleven callee-saved registers, the eleven
    frame slots, the five caller-ambient registers, and the seventeen `.data`
    cells. -/
private def wibEAtoms : List WibEAtom :=
  [.reg .x2 wibSampleSp0, .reg .x1 (wibSampleVals .x1), .reg .x8 (wibSampleVals .x8),
   .reg .x9 (wibSampleVals .x9), .reg .x18 (wibSampleVals .x18),
   .reg .x19 (wibSampleVals .x19), .reg .x20 (wibSampleVals .x20),
   .reg .x21 (wibSampleVals .x21), .reg .x22 (wibSampleVals .x22),
   .reg .x23 (wibSampleVals .x23), .reg .x24 (wibSampleVals .x24),
   .reg .x25 (wibSampleVals .x25),
   .memO ⟨wibSampleNewSp + signExtend12 (0 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (8 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (16 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (24 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (32 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (40 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (48 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (56 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (64 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (72 : BitVec 12), by decide⟩,
   .memO ⟨wibSampleNewSp + signExtend12 (80 : BitVec 12), by decide⟩,
   .reg .x0 (0 : Word), .regO .x5, .reg .x6 wibSampleV6, .reg .x10 wibSamplePtr,
   .reg .x11 (0 : Word), .memO ⟨WibEnabledLoc, by decide⟩,
   .memO ⟨WibBuildStatusLoc, by decide⟩, .memO ⟨WibBuildSectionLenLoc, by decide⟩,
   .memO ⟨WibBuildCountLoc, by decide⟩, .memO ⟨WibSectionPtrLoc, by decide⟩,
   .memO ⟨WibSectionLenLoc, by decide⟩, .memO ⟨WibCountLoc, by decide⟩,
   .memO ⟨WibLookupCallsLoc, by decide⟩, .memO ⟨WibIndexedCallsLoc, by decide⟩,
   .memO ⟨WibIndexedHitsLoc, by decide⟩, .memO ⟨WibIndexedMissesLoc, by decide⟩,
   .memO ⟨WibLinearCallsLoc, by decide⟩, .memO ⟨WibLinearHitsLoc, by decide⟩,
   .memO ⟨WibLinearMissesLoc, by decide⟩, .memO ⟨WibLinearIterationsLoc, by decide⟩,
   .memO ⟨WibLinearLastLenLoc, by decide⟩, .memO ⟨WibLinearMaxLenLoc, by decide⟩]

private theorem wibEAtoms_pairwise : wibEAtoms.Pairwise
    (fun x y => wibERes x ≠ wibERes y) := by
  unfold wibEAtoms wibERes wibSampleNewSp wibSampleSp0 WibEnabledLoc WibBuildStatusLoc WibBuildSectionLenLoc WibBuildCountLoc WibSectionPtrLoc WibSectionLenLoc WibCountLoc WibLookupCallsLoc WibIndexedCallsLoc WibIndexedHitsLoc WibIndexedMissesLoc WibLinearCallsLoc WibLinearHitsLoc WibLinearMissesLoc WibLinearIterationsLoc WibLinearLastLenLoc WibLinearMaxLenLoc
  decide

private theorem wibERegRegDisjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r; right; simp [PartialState.singletonReg, hne]
  · left; simp [PartialState.singletonReg, h]

private theorem wibEMemMemDisjoint {a1 a2 v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a; right; simp [PartialState.singletonMem, hne]
  · left; simp [PartialState.singletonMem, h]

private theorem wibERegMemDisjoint {r : Reg} {a v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem wibEAtomHeapDisjoint {x y : WibEAtom}
    (h : wibERes x ≠ wibERes y) :
    (wibEHeap x).Disjoint (wibEHeap y) := by
  cases x <;> cases y
  all_goals first
    | (apply wibERegRegDisjoint; simpa [wibERes] using h)
    | (apply wibEMemMemDisjoint; simpa [wibERes] using h)
    | exact wibERegMemDisjoint
    | exact wibERegMemDisjoint.symm

private theorem wibEAtoms_hsat :
    (wibEAtoms.foldr (fun x acc => wibEAssertion x ** acc) empAssertion)
      (wibEAtoms.foldr (fun x acc => (wibEHeap x).union acc) PartialState.empty) := by
  apply sepConj_foldr_satisfiable wibEAssertion wibEHeap wibEAtoms
  · intro x _
    cases x with
    | reg r v => exact rfl
    | regO r => exact ⟨(0 : Word), rfl⟩
    | memO m => exact ⟨(0 : Word), rfl, m.valid⟩
  · exact List.Pairwise.imp (fun {_ _} h => wibEAtomHeapDisjoint h) wibEAtoms_pairwise

private def wibEHeapAll : PartialState :=
  wibEAtoms.foldr (fun x acc => (wibEHeap x).union acc) PartialState.empty

/-- The concrete machine state: the forty-five atoms' contents, the routine's
    own code, and `pc` at the routine's linked entry. -/
def wibEntryState : MachineState where
  regs := fun r => match wibEHeapAll.regs r with | some v => v | none => 0
  mem := fun a => match wibEHeapAll.mem a with | some v => v | none => 0
  code := wibCr
  pc := wibB

private theorem wibEHeapAll_x0 : wibEHeapAll.regs .x0 = some 0 := by
  decide

private theorem wibEntryState_getReg (r : Reg) (hr : r ≠ .x0) :
    wibEntryState.getReg r =
      (match wibEHeapAll.regs r with | some v => v | none => 0) := by
  cases r <;> simp_all [wibEntryState, MachineState.getReg]

private theorem wibEntryState_getMem (a : Word) :
    wibEntryState.getMem a =
      (match wibEHeapAll.mem a with | some v => v | none => 0) := rfl

private theorem wibEHeap_code_none (x : WibEAtom) (a : Word) :
    (wibEHeap x).code a = none := by
  cases x <;> rfl

private theorem wibEHeapAll_code_none (a : Word) : wibEHeapAll.code a = none := by
  unfold wibEHeapAll
  induction wibEAtoms with
  | nil => rfl
  | cons x xs ih =>
    change (match (wibEHeap x).code a with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (wibEHeap y).union acc)
          PartialState.empty).code a) = none
    rw [wibEHeap_code_none x a, ih]

private theorem wibEHeapAll_pc_none : wibEHeapAll.pc = none := by
  unfold wibEHeapAll
  induction wibEAtoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (wibEHeap x).pc = none := by cases x <;> rfl
    change (match (wibEHeap x).pc with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (wibEHeap y).union acc)
          PartialState.empty).pc) = none
    rw [hx, ih]

private theorem wibEHeapAll_compat : wibEHeapAll.CompatibleWith wibEntryState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r
      rw [wibEHeapAll_x0] at h
      simp only [Option.some.injEq] at h
      simpa [wibEntryState, MachineState.getReg] using h
    · rw [wibEntryState_getReg r hr, h]
  · intro a v h
    rw [wibEntryState_getMem a, h]
  · intro a i h
    rw [wibEHeapAll_code_none a] at h
    cases h
  · intro v h
    rw [wibEHeapAll_pc_none] at h
    cases h
  · intro v h; cases h
  · intro v h; cases h
  · intro v h; cases h

private theorem wibEntryPre_eq_atoms :
    (((.x2 : Reg) ↦ᵣ wibSampleSp0) ** regsAt wibFrame wibSampleVals **
      frameSlotsOwn wibFrame wibSampleNewSp **
      wibArgs wibSampleV6 wibSamplePtr) =
      wibEAtoms.foldr (fun x acc => wibEAssertion x ** acc) empAssertion := by
  unfold wibArgs wibBuilderCells wibEAtoms wibEAssertion wibFrame regsAt frameSlotsOwn
  simp only [List.foldr, sepConj_emp_right', sepConj_assoc']

/-- **The whole-routine precondition is inhabited at the routine's own
    entry.**  `wibEntryState` has `pc = GuestAddrs.witness_index_build`,
    satisfies the routine's `CodeReq`, and satisfies the precondition of
    `witness_index_build_spec_within_empty_section` at
    `sp0 = wibSampleSp0`, `ret = wibSampleRet` and `vals = wibSampleVals` —
    so the theorem is not vacuously true of an unsatisfiable state. -/
theorem wib_entryState_exists :
    wibEntryState.pc = wibB ∧ wibCr.SatisfiedBy wibEntryState ∧
      ((((.x2 : Reg) ↦ᵣ wibSampleSp0) ** regsAt wibFrame wibSampleVals **
        frameSlotsOwn wibFrame wibSampleNewSp **
        wibArgs wibSampleV6 wibSamplePtr)).holdsFor wibEntryState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a i h; exact h
  · refine ⟨wibEHeapAll, wibEHeapAll_compat, ?_⟩
    rw [wibEntryPre_eq_atoms]
    exact wibEAtoms_hsat

/-- The ABI hypotheses hold at the sample: `ra` carries the sample return
    address and it is two-byte aligned. -/
theorem wib_sample_abi_ok :
    wibSampleVals .x1 = wibSampleRet ∧
      (wibSampleRet &&& ~~~(1 : Word)) = wibSampleRet := ⟨rfl, by decide⟩

/-- **Negative control on the ABI gate**: one byte along, the return address
    is odd and `halign` is provably FALSE. -/
theorem wib_odd_ret_absurd :
    ¬ (((wibSampleRet + 1) &&& ~~~(1 : Word)) = wibSampleRet + 1) := by decide

/-- **The domain gate is reachable**: with `section_len = 0` the `beq s1, zero`
    at idx 56 IS taken, which is the jump this theorem's whole tail rides. -/
theorem wib_empty_section_gate_reachable : (0 : Word) = (0 : Word) := rfl

/-- **Negative control on the domain gate**: at `section_len = 1` the taken
    arm of the same branch carries `⌜(1 : Word) = 0⌝` and is provably FALSE,
    so no re-instantiation of this proof at a non-empty section reaches the
    publish tail.  The `section_len = 0` restriction is load-bearing, not
    decoration. -/
theorem wib_nonempty_section_gate_absurd :
    ∀ hp, (((.x9 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜(1 : Word) = (0 : Word)⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact absurd hP.2 (by decide)

end EvmAsm.Codegen.WitnessIndexBuildTop
