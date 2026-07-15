/-
  EvmAsm.Codegen.Programs.HeaderFieldsSpec

  Caller `Fn.Spec`-shaped contracts (raw pinned `cpsTripleWithin`) for the
  migrated RLP-header-field extractors in `HeaderFields.lean`:

    * `header_extract_state_root`      (field 3  = rlp_walk_init + 4 rlp_walk_next)
    * `header_extract_receipts_root`   (field 5  = init + 6)
    * `header_extract_withdrawals_root`(field 16 = init + 17)

  Each body is proven as a raw `cpsTripleWithin` over
  `CodeReq.ofProg base headerExtract*_prog`: ABI prologue/frame → one
  `rlp_walk_init` call → N sequential `rlp_walk_next` calls (composed via
  `EvmAsm.Codegen.RlpWalkCallSAsm.walk_init_next_N`, threading the strict
  `StrictListPayload`/`StrictPrefix`/`rlpWalkNextOk` invariants each next's
  precondition needs) → the status/length branch → the fixed 32-byte LBU/SB
  copy loop (the alignment-free re-emit, modeled on `mset_memcpy`) → the
  restore/return epilogue.

  This file is PROOF-ONLY over the already-emitted (LBU-fixed) bytes; it changes
  no guest bytes. Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/

import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells (local re-declaration of the `mset_memcpy` helper macro). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-! ## Fixed guest addresses and code -/

/-- Guest entry of `header_extract_state_root`. -/
def hesrBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.header_extract_state_root

/-- The `header_extract_state_root` body at its linked guest address. -/
abbrev hesrCode : CodeReq :=
  CodeReq.ofProg hesrBase Codegen.headerExtractStateRoot_prog

theorem hesr_prog_length : Codegen.headerExtractStateRoot_prog.length = 68 := rfl

/-- The two global scratch cells the success tail round-trips the decoded field
    offset and length through (`la ; sd ; … ; la ; ld`). -/
abbrev hesrOffAddr : Word := (Codegen.GuestAddrs.hesr_offset : Word)
abbrev hesrLenAddr : Word := (Codegen.GuestAddrs.hesr_length : Word)

/-- `la x5, hesr_offset` at [35]-[36] (`+140 → +148`): materialize `hesrOffAddr`.
    (Also confirms the codegen-`laHi` ↔ `Rv64.laHi` defeq at these addresses.) -/
private theorem hesrLaOff140 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 140) (hesrBase + 148) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrOffAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 140)
    Codegen.headerExtractStateRoot_prog 35
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 140))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 144)
    Codegen.headerExtractStateRoot_prog 36
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 140))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 140) hesrOffAddr
    (by decide) (by unfold hesrBase hesrOffAddr; decide) hau had
  rw [show (hesrBase + 140 : Word) + 8 = hesrBase + 148 from by bv_omega] at h
  exact h

/-- `la x5, hesr_length` at [38]-[39] (`+152 → +160`): materialize `hesrLenAddr`. -/
private theorem hesrLaLen152 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 152) (hesrBase + 160) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrLenAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 152)
    Codegen.headerExtractStateRoot_prog 38
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 152))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 156)
    Codegen.headerExtractStateRoot_prog 39
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 152))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 152) hesrLenAddr
    (by decide) (by unfold hesrBase hesrLenAddr; decide) hau had
  rw [show (hesrBase + 152 : Word) + 8 = hesrBase + 160 from by bv_omega] at h
  exact h

/-- `la x5, hesr_length` at [42]-[43] (`+168 → +176`): materialize `hesrLenAddr`. -/
private theorem hesrLaLen168 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 168) (hesrBase + 176) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrLenAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 168)
    Codegen.headerExtractStateRoot_prog 42
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 168))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 172)
    Codegen.headerExtractStateRoot_prog 43
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_length
      (Codegen.GuestAddrs.header_extract_state_root + 168))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 168) hesrLenAddr
    (by decide) (by unfold hesrBase hesrLenAddr; decide) hau had
  rw [show (hesrBase + 168 : Word) + 8 = hesrBase + 176 from by bv_omega] at h
  exact h

/-- `la x5, hesr_offset` at [47]-[48] (`+188 → +196`): materialize `hesrOffAddr`. -/
private theorem hesrLaOff188 (v : Word) :
    cpsTripleWithin 2 (hesrBase + 188) (hesrBase + 196) hesrCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ hesrOffAddr) := by
  have hau := CodeReq.ofProg_mem_at hesrBase (hesrBase + 188)
    Codegen.headerExtractStateRoot_prog 47
    (.AUIPC .x5 (Codegen.laHi Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 188))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have had := CodeReq.ofProg_mem_at hesrBase (hesrBase + 192)
    Codegen.headerExtractStateRoot_prog 48
    (.ADDI .x5 .x5 (Codegen.laLo Codegen.GuestAddrs.hesr_offset
      (Codegen.GuestAddrs.header_extract_state_root + 188))) (by bv_omega)
    (by rw [hesr_prog_length]; decide) rfl (by rw [hesr_prog_length]; decide)
  have h := la_materialize_within .x5 v (hesrBase + 188) hesrOffAddr
    (by decide) (by unfold hesrBase hesrOffAddr; decide) hau had
  rw [show (hesrBase + 188 : Word) + 8 = hesrBase + 196 from by bv_omega] at h
  exact h

/-! ## ABI frame: save ra/s0/s1/s2 into a 48-byte frame

    The prologue allocates 48 bytes and saves `ra` (x1), `s0` (x8), `s1` (x9),
    `s2` (x18) at slots 0/8/16/24.  Slots 32/40 are the two scratch spill slots
    used between the walker calls; they are owned but not part of the saved
    register frame. -/

/-- The saved-register frame descriptor for the header extractors. -/
def hxFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]

theorem hxFrame_length : hxFrame.length = 4 := by decide

/-- Saved caller register values. -/
structure Saved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word

def savedVals (saved : Saved) : Reg → Word
  | .x1 => saved.ra
  | .x8 => saved.s0
  | .x9 => saved.s1
  | .x18 => saved.s2
  | _ => 0

theorem regsAt_hxFrame (saved : Saved) :
    regsAt hxFrame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
       (.x18 ↦ᵣ saved.s2)) := by
  simp [hxFrame, regsAt, savedVals]
  rw [sepConj_emp_right']

/-- The saved frame slots holding the saved values. -/
def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2)

theorem frameSlotsSaved_hxFrame (newSp : Word) (saved : Saved) :
    frameSlotsSaved hxFrame newSp (savedVals saved) = savedFrame newSp saved := by
  simp [hxFrame, frameSlotsSaved, savedFrame, savedVals,
    sepConj_emp_right', signExtend12]

/-! ## Prologue

    Instructions [0]-[9]:
      [0] addi sp, sp, -48
      [1-4] sd  ra/s0/s1/s2, {0,8,16,24}(sp)
      [5] mv s0, a0    [6] mv s1, a1    [7] mv s2, a2
      [8] mv a0, s0    [9] mv a1, s1
    establishing `s0 = listBase`, `s1 = listLen`, `s2 = outPtr`, and leaving
    `a0 = listBase`, `a1 = listLen` ready for the `rlp_walk_init` call. -/

/-- The five register moves [5]-[9] (`hesrBase+20 → hesrBase+40`). -/
theorem setupMoves5 (listBase listLen outPtr v8 v9 v18 : Word) :
    cpsTripleWithin 5 (hesrBase + 20) (hesrBase + 40) hesrCode
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
      ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) := by
  -- [5] mv s0, a0
  have h5 := mv_spec_gen_within .x8 .x10 listBase v8 (hesrBase + 20) (by decide)
  rw [show (hesrBase + 20 : Word) + 4 = hesrBase + 24 from by bv_omega] at h5
  have e5 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 20) Codegen.headerExtractStateRoot_prog 5 (.MV .x8 .x10) (by bv_omega) (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h5
  have f5 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e5
  -- [6] mv s1, a1
  have h6 := mv_spec_gen_within .x9 .x11 listLen v9 (hesrBase + 24) (by decide)
  rw [show (hesrBase + 24 : Word) + 4 = hesrBase + 28 from by bv_omega] at h6
  have e6 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 24) Codegen.headerExtractStateRoot_prog 6 (.MV .x9 .x11) (by bv_omega) (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h6
  have f6 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ v18) ** (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e6
  -- [7] mv s2, a2
  have h7 := mv_spec_gen_within .x18 .x12 outPtr v18 (hesrBase + 28) (by decide)
  rw [show (hesrBase + 28 : Word) + 4 = hesrBase + 32 from by bv_omega] at h7
  have e7 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 28) Codegen.headerExtractStateRoot_prog 7 (.MV .x18 .x12) (by bv_omega) (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h7
  have f7 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen))
    (by pcf) e7
  -- [8] mv a0, s0
  have h8 := mv_spec_gen_within .x10 .x8 listBase listBase (hesrBase + 32) (by decide)
  rw [show (hesrBase + 32 : Word) + 4 = hesrBase + 36 from by bv_omega] at h8
  have e8 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 32) Codegen.headerExtractStateRoot_prog 8 (.MV .x10 .x8) (by bv_omega) (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h8
  have f8 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e8
  -- [9] mv a1, s1
  have h9 := mv_spec_gen_within .x11 .x9 listLen listLen (hesrBase + 36) (by decide)
  rw [show (hesrBase + 36 : Word) + 4 = hesrBase + 40 from by bv_omega] at h9
  have e9 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 36) Codegen.headerExtractStateRoot_prog 9 (.MV .x11 .x9) (by bv_omega) (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h9
  have f9 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) ** (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e9
  -- compose
  have s56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f5 f6
  have s567 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s56 f7
  have s5678 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s567 f8
  have s56789 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s5678 f9
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) s56789

/-- The full prologue [0]-[9] (`hesrBase → hesrBase+40`): allocate the 48-byte
    frame, save `ra/s0/s1/s2`, and set up `s0/s1/s2 = listBase/listLen/outPtr`
    with `a0/a1 = listBase/listLen` ready for the `rlp_walk_init` call.  The two
    scratch spill slots (`newSp+32`, `newSp+40`) are carried untouched. -/
theorem hesrPrologue (sp0 newSp listBase listLen outPtr : Word) (saved : Saved)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12)) :
    cpsTripleWithin 10 hesrBase (hesrBase + 40) hesrCode
      ((.x2 ↦ᵣ sp0) ** regsAt hxFrame (savedVals saved) **
       frameSlotsOwn hxFrame newSp **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) ** savedFrame newSp saved **
       (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) := by
  -- [0] addi sp, sp, -48
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-48 : BitVec 12) hesrBase (by decide)
  rw [← h_newSp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase hesrBase Codegen.headerExtractStateRoot_prog 0
      (.ADDI .x2 .x2 (-48 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt hxFrame (savedVals saved) ** frameSlotsOwn hxFrame newSp **
      (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) (by
      repeat' first
        | exact pcFree_regsAt _ _
        | exact pcFree_frameSlotsOwn _ _
        | apply pcFree_sepConj
        | exact pcFree_regIs) ha
  -- [1]-[4] store sequence
  have hs0 := storeSeq_spec hxFrame newSp (savedVals saved) (hesrBase + 4) (by decide)
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (hesrBase + 4) (storeProg hxFrame) a = some i → hesrCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub hesrBase (hesrBase + 4)
      Codegen.headerExtractStateRoot_prog (storeProg hxFrame) 1 (by bv_omega) rfl
      (by rw [hesr_prog_length]; simp [hxFrame])
      (by rw [hesr_prog_length]; norm_num) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show hesrBase + 4 + BitVec.ofNat 64 (4 * hxFrame.length) = hesrBase + 20 from by
    simp [hxFrame]; bv_omega] at hs
  have hsF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) (by
      repeat' first | apply pcFree_sepConj | exact pcFree_regIs) hs
  -- [5]-[9] the moves
  have hm := setupMoves5 listBase listLen outPtr saved.s0 saved.s1 saved.s2
  have hmF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) ** savedFrame newSp saved) (by
      unfold savedFrame
      repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs) hm
  -- compose ADDI ; store ; moves
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hsF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_hxFrame, frameSlotsSaved_hxFrame] at hp
    xperm_hyp hp) h01 hmF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) h012

/-! ## Cross-function walker call lifts

    `header_extract_state_root` calls the separately-linked `rlp_walk_init` /
    `rlp_walk_next` functions (not embedded).  These thin wrappers add the direct
    `JAL` at the call site into an ambient `cr` that must contain the callee's
    code, via the generic `RlpWalkCallSAsm` adapters. -/

/-- Guest entry of `rlp_walk_init`. -/
def wiBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.rlp_walk_init
/-- Guest entry of `rlp_walk_next`. -/
def wnBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.rlp_walk_next

/-- The `jal ra, rlp_walk_init` immediate at instruction [10] (`hesrBase+40`). -/
def hesrInitOffset : BitVec 21 :=
  jalOff Codegen.GuestAddrs.rlp_walk_init (Codegen.GuestAddrs.header_extract_state_root + 40)

/-- Lift the `rlp_walk_init` call at [10] (`hesrBase+40 → hesrBase+44`) into an
    ambient `cr` containing both the JAL and `rlp_walk_init_code`. -/
theorem hesrInitCall {cr : CodeReq} {Prest Q : Assertion} {n : Nat} (oldRa : Word)
    (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (hesrBase + 40) (.JAL .x1 hesrInitOffset)).union
        (rlp_walk_init_code wiBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n wiBase ((hesrBase + 40 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code wiBase)
      ((.x1 ↦ᵣ (hesrBase + 40 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (hesrBase + 40) (hesrBase + 40 + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q :=
  EvmAsm.Codegen.RlpWalkCallSAsm.rlp_walk_init_call_within
    (hesrBase + 40) wiBase oldRa hesrInitOffset hpre
    (by simp only [wiBase, hesrInitOffset, hesrBase]; decide)
    (by simp only [hesrBase]; decide)
    (by simp only [wiBase, hesrInitOffset, hesrBase]
        exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee

/-- Lift one `rlp_walk_next` call at call site `callPC` into an ambient `cr`
    containing both the JAL and `rlp_walk_next_code`.  Parametrized by the call
    site so all four state-root next calls (and the receipts/withdrawals sites)
    reuse it; the per-site `hoffset`/`halign`/`hdisj` discharge by `decide`. -/
theorem hesrNextCall {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (callPC oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callPC + signExtend21 offset = wnBase)
    (halign : (callPC + 4) &&& ~~~(1 : Word) = callPC + 4)
    (hdisj : (CodeReq.singleton callPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_next_code wnBase))
    (hcode : ∀ a i,
      (CodeReq.singleton callPC (.JAL .x1 offset)).union
        (rlp_walk_next_code wnBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n wnBase ((callPC + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code wnBase)
      ((.x1 ↦ᵣ (callPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callPC (callPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q :=
  EvmAsm.Codegen.RlpWalkCallSAsm.rlp_walk_next_call_within
    callPC wnBase oldRa offset hpre hoffset halign hdisj hcode hcallee

/-! ## The init call step (raw `rlp_walk_init` outcome)

    Instruction [10] (`hesrBase+40 → hesrBase+44`): call `rlp_walk_init`,
    producing the genuine 9-way `RlpListNthItemSAsm.initOutcome` on the
    cursor/end/status registers, framed against the caller-owned ambient
    (`s0/s1/s2`, saved frame, the two scratch spill slots, the output buffer)
    which the initializer does not touch. -/

/-- The caller-owned ambient carried across the walker calls: the frame pointer
    and saved registers, the saved-register frame, the two scratch spill slots
    (`newSp+32`, `newSp+40`), and the 32-byte output buffer. -/
def hesrAmbient (newSp outPtr listBase listLen : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) **
  savedFrame newSp saved ** memOwn (newSp + 32) ** memOwn (newSp + 40) **
  bytesRegion outPtr outBytes

theorem pcFree_hesrAmbient (newSp outPtr listBase listLen : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) :
    (hesrAmbient newSp outPtr listBase listLen saved outBytes).pcFree := by
  unfold hesrAmbient savedFrame
  repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_memOwn

/-- The scratch-register + `ra` + input-region block the initializer leaves,
    mirroring `RlpListNthItemSAsm.initCommon` but with the caller's own return
    address (`hesrBase+44`). -/
def hesrInitCommon (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 40 + 4)) ** bytesRegion listBase bytes

/-- The init call step: `rlp_walk_init` at [10], producing the genuine 9-way
    `initOutcome` framed against the caller ambient.  Mirrors
    `RlpListNthItemSAsm.initCallExact`, but for the cross-function call site and
    with the header-caller ambient carried across. -/
theorem hesrInitStep {cr : CodeReq}
    (listBase outPtr newSp oldRa v5 v6 v7 v28 v29 v30 v31 : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLenN + 9 ≤ headerBytes.length)
    (h_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hcode : ∀ a i,
      (CodeReq.singleton (hesrBase + 40) (.JAL .x1 hesrInitOffset)).union
        (rlp_walk_init_code wiBase) a = some i → cr a = some i) :
    cpsTripleWithin (1 + 81) (hesrBase + 40) (hesrBase + 40 + 4) cr
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) **
         (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes))
      (((hesrInitCommon listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
         RlpListNthItemSAsm.initOutcome listBase headerBytes listLenN (by omega)) **
        hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes) := by
  have hoff : 0 < headerBytes.length := by omega
  have hwi := rlp_walk_init_spec_within wiBase listBase (hesrBase + 40 + 4)
    (BitVec.ofNat 64 listLenN) outPtr v5 v6 v7 v28 v29 v30 v31 headerBytes 0
    h_align hoff (by omega) (h_valid 0 hoff)
    (fun h_f8 => by
      have h_lo : ((headerBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (headerBytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 => by
      have h_lo : ((headerBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (headerBytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 => by
      intro k hk
      have h_lo : ((headerBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (headerBytes[0]'hoff).isLt
        bv_omega
      exact h_valid _ (by omega))
  rw [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at hwi
  have hwiA := cpsTripleWithin_frameR
    (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes)
    (pcFree_hesrAmbient _ _ _ _ _ _) hwi
  set Prest : Assertion :=
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) **
     (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
     hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes) with hPrest
  set Q : Assertion :=
    ((hesrInitCommon listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
      RlpListNthItemSAsm.initOutcome listBase headerBytes listLenN hoff) **
      hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes with hQ
  have hwi' : cpsTripleWithin 81 wiBase ((hesrBase + 40 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code wiBase) ((.x1 ↦ᵣ (hesrBase + 40 + 4)) ** Prest) Q :=
    cpsTripleWithin_weaken
      (fun h hp => by rw [hPrest] at hp; xperm_hyp hp)
      (fun h hp => by
        rw [hQ]
        unfold hesrInitCommon RlpListNthItemSAsm.initOutcome
        simp only [Nat.zero_add] at hp ⊢
        xperm_hyp hp) hwiA
  have hc := hesrInitCall oldRa (by
    rw [hPrest]
    repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_hesrAmbient _ _ _ _ _ _
      | apply pcFree_sepConj
      | exact pcFree_regIs) hcode hwi'
  simpa [hPrest, hQ] using hc

/-! ## The next call step (raw `rlp_walk_next` outcome)

    One `rlp_walk_next` call at a parametric call site (`callPC → callPC+4`):
    consume the cursor (`x10`) and end pointer (`x11`) — set up by the preceding
    marshalling loads — and produce the genuine 6-way `hesrNextOutcome` on the
    cursor/status/len registers, framed against an ambient `F` the walker does not
    touch.  Mirrors `RlpListNthItemSAsm.nextCallBlock` but with the stack-marshalled
    calling convention (no `x20`) and the cross-function `JAL` lift. -/

/-- Local copy of the 6-way `rlp_walk_next` outcome (the header caller does not
    import `RlpListNthItemSAsmScan`). -/
def hesrNextOutcome (listBase endPtr : Word) (bytes : List (BitVec 8)) (off : Nat) : Assertion :=
  fun h =>
    rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (2 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true⌝) h) ∨
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (3 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (4 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (5 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (6 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h)

/-- The next call step: `rlp_walk_next` at `callPC`, producing the genuine 6-way
    `hesrNextOutcome` framed against an ambient `F`.  `cursor = listBase + off`. -/
theorem hesrNextStep {cr : CodeReq}
    (callPC : Word) (offset : BitVec 21)
    (listBase endPtr : Word) (off listLen : Nat)
    (oldRa v12 v5 v6 v7 v28 v29 v30 v31 : Word)
    (bytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length → isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hoff : off ≤ listLen)
    (hoffset : callPC + signExtend21 offset = wnBase)
    (halign : (callPC + 4) &&& ~~~(1 : Word) = callPC + 4)
    (hdisj : (CodeReq.singleton callPC (.JAL .x1 offset)).Disjoint (rlp_walk_next_code wnBase))
    (hcode : ∀ a i,
      (CodeReq.singleton callPC (.JAL .x1 offset)).union
        (rlp_walk_next_code wnBase) a = some i → cr a = some i) :
    cpsTripleWithin (1 + 87) callPC (callPC + 4) cr
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** F))
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (callPC + 4)) ** bytesRegion listBase bytes) **
        hesrNextOutcome listBase endPtr bytes off) ** F) := by
  have hoffb : off < bytes.length := by omega
  have hwn := rlp_walk_next_spec_within wnBase listBase endPtr (callPC + 4) v12
    v5 v6 v7 v28 v29 v30 v31 bytes off hsalign hoffb (by omega) (hvalid off hoffb)
    (fun _ _ => ⟨by omega, by omega, hvalid _ (by omega)⟩)
    (fun hb8 hc0 => by
      have hlo : ((bytes[off]'hoffb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hb8 hc0
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
    (fun hf8 => by
      have hlo : ((bytes[off]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hf8
        have h3 := (bytes[off]'hoffb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
  have hwnF := cpsTripleWithin_frameR F hF hwn
  have hwn' := cpsTripleWithin_weaken
    (P' := (.x1 ↦ᵣ (callPC + 4)) **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** F))
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwnF
  have hc := hesrNextCall callPC oldRa offset
    (by repeat' first
      | exact hF | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj)
    hoffset halign hdisj hcode hwn'
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by unfold hesrNextOutcome; xperm_hyp hq) hc

/-! ## Epilogue

    Instructions [64]-[69] (`hesrBase+256 → raVal &&& ~~~1`): restore
    `ra/s0/s1/s2` from the frame, deallocate the 48-byte frame, and `ret`.
    The status word `a0` (and any framed rest `Fr`) is carried untouched.  This
    is the shared tail all three exit paths (status 0/1/2) reach. -/
theorem hesrEpilogue (newSp a0v v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin 6 (hesrBase + 248) (saved.ra &&& ~~~(1 : Word)) hesrCode
      (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  -- [62]-[65] restore ra/s0/s1/s2 via individual LDs (per-instruction ofProg_mem_at;
  -- loadSeq_spec's drop/take reduction is too heavy at this index).
  unfold savedFrame
  -- [62] ld ra, 0(sp)
  have hl0 := ld_spec_gen_within .x1 .x2 newSp v1 saved.ra (0 : BitVec 12) (hesrBase + 248) (by decide)
  rw [signExtend12_0, show (newSp + 0 : Word) = newSp from by bv_omega,
      show (hesrBase + 248 : Word) + 4 = hesrBase + 252 from by bv_omega] at hl0
  have el0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 248) Codegen.headerExtractStateRoot_prog 62
      (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hl0
  have el0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
     ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) **
     ((newSp + 24) ↦ₘ saved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el0
  -- [63] ld s0, 8(sp)
  have hl1 := ld_spec_gen_within .x8 .x2 newSp v8 saved.s0 (8 : BitVec 12) (hesrBase + 252) (by decide)
  rw [show newSp + signExtend12 (8 : BitVec 12) = newSp + 8 from by
        rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide],
      show (hesrBase + 252 : Word) + 4 = hesrBase + 256 from by bv_omega] at hl1
  have el1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 252) Codegen.headerExtractStateRoot_prog 63
      (.LD .x8 .x2 (8 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hl1
  have el1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
     (newSp ↦ₘ saved.ra) ** ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el1
  -- [64] ld s1, 16(sp)
  have hl2 := ld_spec_gen_within .x9 .x2 newSp v9 saved.s1 (16 : BitVec 12) (hesrBase + 256) (by decide)
  rw [show newSp + signExtend12 (16 : BitVec 12) = newSp + 16 from by
        rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide],
      show (hesrBase + 256 : Word) + 4 = hesrBase + 260 from by bv_omega] at hl2
  have el2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 256) Codegen.headerExtractStateRoot_prog 64
      (.LD .x9 .x2 (16 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hl2
  have el2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x18 ↦ᵣ v18) **
     (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 24) ↦ₘ saved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el2
  -- [65] ld s2, 24(sp)
  have hl3 := ld_spec_gen_within .x18 .x2 newSp v18 saved.s2 (24 : BitVec 12) (hesrBase + 260) (by decide)
  rw [show newSp + signExtend12 (24 : BitVec 12) = newSp + 24 from by
        rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide],
      show (hesrBase + 260 : Word) + 4 = hesrBase + 264 from by bv_omega] at hl3
  have el3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 260) Codegen.headerExtractStateRoot_prog 65
      (.LD .x18 .x2 (24 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hl3
  have el3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
     (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el3
  -- compose the 4 restores
  have hr01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) el0F el1F
  have hr012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hr01 el2F
  have hldF := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hr012 el3F
  -- [66] addi sp, sp, 48
  have haddi := addi_spec_gen_same_within .x2 newSp (48 : BitVec 12) (hesrBase + 264) (by decide)
  rw [show newSp + signExtend12 (48 : BitVec 12) = newSp + 48 from by
      rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide],
    show (hesrBase + 264 : Word) + 4 = hesrBase + 268 from by bv_omega] at haddi
  have haddiE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 264) Codegen.headerExtractStateRoot_prog 66
      (.ADDI .x2 .x2 (48 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) haddi
  have haddiF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) **
      (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2)) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) haddiE
  -- [69] jalr x0, 0(x1)  → return to saved.ra &&& ~~~1
  have hjalr := jalr_x0_spec_gen_within .x1 saved.ra (0 : BitVec 12) (hesrBase + 268)
  simp only [signExtend12_0] at hjalr
  rw [show (saved.ra + 0 : Word) = saved.ra from by bv_omega] at hjalr
  have hjalrE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 268) Codegen.headerExtractStateRoot_prog 67
      (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hjalr
  have hjalrF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x8 ↦ᵣ saved.s0) **
      (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2)) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hjalrE
  -- compose loads ; addi ; jalr
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hldF haddiF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hjalrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) s2

/-! ## Status-1 (parse/walk failure) return tail

    Instructions [59]-[60] then the epilogue: set `a0 = 1` and jump to the shared
    epilogue.  `[59]` (`hesrBase+236`) is the target of all five status-dispatch
    BNE branches (init + 4 nexts). -/
theorem hesrStatus1Return (newSp a0old v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin (2 + 6) (hesrBase + 236) (saved.ra &&& ~~~(1 : Word)) hesrCode
      (((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  -- [59] li a0, 1
  have hli := li_spec_gen_within .x10 a0old (1 : Word) (hesrBase + 236) (by decide)
  rw [show (hesrBase + 236 : Word) + 4 = hesrBase + 240 from by bv_omega] at hli
  have hliE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 236) Codegen.headerExtractStateRoot_prog 59
      (.LI .x10 (1 : Word)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hliE
  -- [60] jal x0, +8  → hesrBase+248 (epilogue)
  have hj := jal_x0_spec_gen_within (8 : BitVec 21) (hesrBase + 240)
  rw [show hesrBase + 240 + signExtend21 (8 : BitVec 21) = hesrBase + 248 from by
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at hj
  have hjE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 240) Codegen.headerExtractStateRoot_prog 60
      (.JAL .x0 (8 : BitVec 21)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hj
  have hjF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hjE
  rw [sepConj_emp_left'] at hjF
  -- epilogue with a0 = 1
  have hep := hesrEpilogue newSp (1 : Word) v1 v8 v9 v18 saved Fr hFr
  -- compose li ; jal ; epilogue
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hep
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)

/-! ## Status-2 (wrong-length) return tail

    Instruction [61] (`hesrBase+244`) then the epilogue: set `a0 = 2` and fall
    straight into the shared epilogue.  `[61]` is the target of the length-check
    `BNE` at [46] (`hesrBase+184`, offset `+60`). -/
theorem hesrStatus2Return (newSp a0old v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin (1 + 6) (hesrBase + 244) (saved.ra &&& ~~~(1 : Word)) hesrCode
      (((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ (2 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  -- [61] li a0, 2
  have hli := li_spec_gen_within .x10 a0old (2 : Word) (hesrBase + 244) (by decide)
  rw [show (hesrBase + 244 : Word) + 4 = hesrBase + 248 from by bv_omega] at hli
  have hliE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 244) Codegen.headerExtractStateRoot_prog 61
      (.LI .x10 (2 : Word)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hliE
  -- epilogue with a0 = 2
  have hep := hesrEpilogue newSp (2 : Word) v1 v8 v9 v18 saved Fr hFr
  -- compose li ; epilogue
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hep
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s1

/-! ## Status-0 (success) finish tail

    Instructions [57]-[58] (`hesrBase+228`) then the epilogue: set `a0 = 0` and
    jump to the shared epilogue (`jal x0, +16` → `hesrBase+248`).  This is the
    fall-through target of the copy loop (`hesrCopyLoop` exits at `hesrBase+228`). -/
theorem hesrSuccessFinish (newSp a0old v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin (2 + 6) (hesrBase + 228) (saved.ra &&& ~~~(1 : Word)) hesrCode
      (((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  -- [57] li a0, 0
  have hli := li_spec_gen_within .x10 a0old (0 : Word) (hesrBase + 228) (by decide)
  rw [show (hesrBase + 228 : Word) + 4 = hesrBase + 232 from by bv_omega] at hli
  have hliE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 228) Codegen.headerExtractStateRoot_prog 57
      (.LI .x10 (0 : Word)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hliE
  -- [58] jal x0, +16  → hesrBase+248 (epilogue)
  have hj := jal_x0_spec_gen_within (16 : BitVec 21) (hesrBase + 232)
  rw [show hesrBase + 232 + signExtend21 (16 : BitVec 21) = hesrBase + 248 from by
      rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]; bv_omega] at hj
  have hjE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 232) Codegen.headerExtractStateRoot_prog 58
      (.JAL .x0 (16 : BitVec 21)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hj
  have hjF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hjE
  rw [sepConj_emp_left'] at hjF
  -- epilogue with a0 = 0
  have hep := hesrEpilogue newSp (0 : Word) v1 v8 v9 v18 saved Fr hFr
  -- compose li ; jal ; epilogue
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hep
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)

/-! ## The success-tail LBU/SB byte-copy loop ([51]-[56])

    The alignment-free re-emit: `x28` = source pointer (`listBase + fieldOffset`,
    an absolute content pointer), `x18` = destination (output buffer), `x6` =
    byte countdown (32 on entry, from the length check), `x29` = per-byte temp.
    Structurally identical to the verified `mset_memcpy` loop (LBU/SB body +
    `BNE` back-edge) but over the header-caller registers and inline code, so it
    is re-derived here reusing the `copyIntoRegion` content model. -/

/-- Word decrement of a successor counter. -/
private theorem hesr_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem hesr_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- Pointer advance by 1 byte. -/
private theorem hesr_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-- **One copy-loop iteration** ([51]-[55], `hesrBase+204 → hesrBase+224`):
    copy the byte at `src[srcOff+i]` into `dst[dstOff+i]`, advance both pointers
    and decrement the countdown. -/
private theorem hesrCopyBody (srcBase dstBase x29old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff i m : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_lt : srcOff + i < srcBytes.length)
    (h_dst_lt : dstOff + i < dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 5 (hesrBase + 204) (hesrBase + 224) hesrCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x29 : Reg) ↦ᵣ x29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 m) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) := by
  set bval := srcBytes[srcOff + i]'h_src_lt with hbval
  have htrunc : (bval.zeroExtend 64).truncate 8 = bval := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := bval.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hgetd : srcBytes.getD (srcOff + i) 0 = bval := by
    rw [hbval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_src_lt]; rfl
  have hstep : copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)
      = (copyIntoRegion dstBytes srcBytes dstOff srcOff i).set (dstOff + i) bval := by
    simp only [copyIntoRegion, hgetd]
  -- [51] LBU x29 ← src[srcOff+i].
  have hlbu := bytesRegion_lbu_within .x29 .x28 srcBase x29old (hesrBase + 204)
    srcBytes (srcOff + i) (by decide) h_src_align h_src_lt (by omega)
    (h_src_valid (srcOff + i) h_src_lt)
  rw [show (hesrBase + 204 : Word) + 4 = hesrBase + 208 from by bv_omega, ← hbval] at hlbu
  have hlbue := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 204) Codegen.headerExtractStateRoot_prog 51
      (.LBU .x29 .x28 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hlbu
  have hlbuf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
    (by pcFreeR) hlbue
  -- [52] SB dst[dstOff+i] ← x29 (= bval).
  have hsb := bytesRegion_sb_within .x18 .x29 dstBase (bval.zeroExtend 64) (hesrBase + 208)
    (copyIntoRegion dstBytes srcBytes dstOff srcOff i) (dstOff + i) h_dst_align
    (by rw [copyIntoRegion_length]; omega) (by omega)
    (h_dst_valid (dstOff + i) h_dst_lt)
  rw [htrunc, ← hstep, show (hesrBase + 208 : Word) + 4 = hesrBase + 212 from by bv_omega] at hsb
  have hsbe := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 208) Codegen.headerExtractStateRoot_prog 52
      (.SB .x18 .x29 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) hsb
  have hsbf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes)
    (by pcFreeR) hsbe
  -- [53] ADDI x28 += 1 (src++).
  have h3 := addi_spec_gen_same_within .x28
    (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (hesrBase + 212) (by decide)
  rw [hesr_advance srcBase (srcOff + i),
      show srcOff + i + 1 = srcOff + (i + 1) from by omega,
      show (hesrBase + 212 : Word) + 4 = hesrBase + 216 from by bv_omega] at h3
  have h3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 212) Codegen.headerExtractStateRoot_prog 53
      (.ADDI .x28 .x28 (1 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h3
  have h3f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h3e
  -- [54] ADDI x18 += 1 (dst++).
  have h4 := addi_spec_gen_same_within .x18
    (dstBase + BitVec.ofNat 64 (dstOff + i)) (1 : BitVec 12) (hesrBase + 216) (by decide)
  rw [hesr_advance dstBase (dstOff + i),
      show dstOff + i + 1 = dstOff + (i + 1) from by omega,
      show (hesrBase + 216 : Word) + 4 = hesrBase + 220 from by bv_omega] at h4
  have h4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 216) Codegen.headerExtractStateRoot_prog 54
      (.ADDI .x18 .x18 (1 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h4
  have h4f := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
     ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h4e
  -- [55] ADDI x6 -= 1 (count--).
  have h5 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
    (hesrBase + 220) (by decide)
  rw [hesr_succ_dec m, show (hesrBase + 220 : Word) + 4 = hesrBase + 224 from by bv_omega] at h5
  have h5e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 220) Codegen.headerExtractStateRoot_prog 55
      (.ADDI .x6 .x6 (-1 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h5
  have h5f := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
     ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
    (by pcFreeR) h5e
  -- Compose the five body steps.
  have s12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlbuf hsbf
  have s123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s12 h3f
  have s1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s123 h4f
  have s12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1234 h5f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by rw [hgetd]; xperm_chunked hq) s12345)

/-- **The copy-loop closure** ([51]-[56], `hesrBase+204 → hesrBase+228`): by
    induction on the byte countdown, copy the remaining `n+1` bytes and fall
    through past the `BNE` back-edge with `x6 = 0`. -/
private theorem hesrCopyLoop (srcBase dstBase x29old : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff dstOff n i : Nat)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_src_bound : srcOff + i + (n + 1) ≤ srcBytes.length)
    (h_dst_bound : dstOff + i + (n + 1) ≤ dstBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * (n + 1)) (hesrBase + 204) (hesrBase + 228) hesrCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i))) **
       ((.x29 : Reg) ↦ᵣ x29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff i))
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i + (n + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + i + (n + 1)))) **
       regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + (n + 1)))) := by
  have ha_back : (hesrBase + 224 : Word) + signExtend13 (-20 : BitVec 13) = hesrBase + 204 := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have ha_fall : (hesrBase + 224 : Word) + 4 = hesrBase + 228 := by bv_omega
  have hmono6 : ∀ a i', CodeReq.singleton (hesrBase + 224) (.BNE .x6 .x0 (-20 : BitVec 13)) a = some i'
      → hesrCode a = some i' :=
    CodeReq.ofProg_mem_at hesrBase (hesrBase + 224) Codegen.headerExtractStateRoot_prog 56
      (.BNE .x6 .x0 (-20 : BitVec 13)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)
  induction n generalizing i x29old with
  | zero =>
    have hbody := hesrCopyBody srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i 0
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (hesrBase + 224)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono6 hbne
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by pcFreeR) hnt
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hbody hntf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          simp only [show srcOff + i + (0 + 1) = srcOff + (i + 1) from by omega,
                     show dstOff + i + (0 + 1) = dstOff + (i + 1) from by omega,
                     show i + (0 + 1) = i + 1 from by omega]
          have hq2 : (((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
              ((.x6 : Reg) ↦ᵣ (0 : Word)) **
              ((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
              ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes **
              bytesRegion dstBase
                (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1))) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x29) _ hq2
          xperm_chunked hq3) sfull)
  | succ k ih =>
    have hbody := hesrCopyBody srcBase dstBase x29old srcBytes dstBytes srcOff dstOff i (k + 1)
      h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
    have hbne := bne_spec_gen_within .x6 .x0 (-20 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (hesrBase + 224)
    rw [ha_back, ha_fall] at hbne
    have hbnee := cpsBranchWithin_extend_code hmono6 hbne
    have htaken := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hesr_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x18 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (dstOff + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((srcBytes.getD (srcOff + i) 0).zeroExtend 64)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyIntoRegion dstBytes srcBytes dstOff srcOff (i + 1)))
      (by pcFreeR) htaken
    have hih := ih ((srcBytes.getD (srcOff + i) 0).zeroExtend 64) (i + 1)
      (by omega) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hbody htf
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show srcOff + (i + 1) + (k + 1) = srcOff + i + (k + 1 + 1) from by omega,
                     show dstOff + (i + 1) + (k + 1) = dstOff + i + (k + 1 + 1) from by omega,
                     show i + 1 + (k + 1) = i + (k + 1 + 1) from by omega] at hq
          xperm_chunked hq) sfull)

/-! ## Success-tail: offset/length compute + global-cell store ([33]-[41])

    `SUB x6,x10,x12` (`next-len`), `SUB x6,x6,x8` (`next-len-listBase` =
    fieldOffset), then `la x5,hesr_offset ; sd x6,0(x5)` and
    `la x5,hesr_length ; sd x12,0(x5)` round-trip the decoded offset and length
    through the two global scratch cells; `jal x0,+4` falls through to [42]. -/
private theorem hesrOffsetStore
    (next len listBase v5old v6old offOld lenOld : Word) :
    cpsTripleWithin 9 (hesrBase + 132) (hesrBase + 168) hesrCode
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
       (.x6 ↦ᵣ v6old) ** (.x5 ↦ᵣ v5old) **
       (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
       (.x6 ↦ᵣ (next - len - listBase)) ** (.x5 ↦ᵣ hesrLenAddr) **
       (hesrOffAddr ↦ₘ (next - len - listBase)) ** (hesrLenAddr ↦ₘ len)) := by
  -- [33] sub x6, x10, x12  → x6 = next - len
  have h33 := sub_spec_gen_within .x6 .x10 .x12 next len v6old (hesrBase + 132) (by decide)
  rw [show (hesrBase + 132 : Word) + 4 = hesrBase + 136 from by bv_omega] at h33
  have e33 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 132) Codegen.headerExtractStateRoot_prog 33
      (.SUB .x6 .x10 .x12) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h33
  have f33 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x5 ↦ᵣ v5old) ** (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e33
  -- [34] sub x6, x6, x8  → x6 = (next-len) - listBase
  have h34 := sub_spec_gen_rd_eq_rs1_within .x6 .x8 (next - len) listBase (hesrBase + 136) (by decide)
  rw [show (hesrBase + 136 : Word) + 4 = hesrBase + 140 from by bv_omega] at h34
  have e34 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 136) Codegen.headerExtractStateRoot_prog 34
      (.SUB .x6 .x6 .x8) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h34
  have f34 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x5 ↦ᵣ v5old) **
     (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e34
  -- [35-36] la x5, hesr_offset
  have f35 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
     (.x6 ↦ᵣ (next - len - listBase)) ** (hesrOffAddr ↦ₘ offOld) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) (hesrLaOff140 v5old)
  -- [37] sd x6, 0(x5)  → *hesr_offset := next-len-listBase
  have h37 := sd_spec_gen_within .x5 .x6 hesrOffAddr (next - len - listBase) offOld
    (0 : BitVec 12) (hesrBase + 148)
  rw [signExtend12_0, show (hesrOffAddr + 0 : Word) = hesrOffAddr from by bv_omega,
      show (hesrBase + 148 : Word) + 4 = hesrBase + 152 from by bv_omega] at h37
  have e37 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 148) Codegen.headerExtractStateRoot_prog 37
      (.SD .x5 .x6 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h37
  have f37 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) e37
  -- [38-39] la x5, hesr_length
  have f38 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
     (.x6 ↦ᵣ (next - len - listBase)) ** (hesrOffAddr ↦ₘ (next - len - listBase)) **
     (hesrLenAddr ↦ₘ lenOld))
    (by pcFreeR) (hesrLaLen152 hesrOffAddr)
  -- [40] sd x12, 0(x5)  → *hesr_length := len
  have h40 := sd_spec_gen_within .x5 .x12 hesrLenAddr len lenOld (0 : BitVec 12) (hesrBase + 160)
  rw [signExtend12_0, show (hesrLenAddr + 0 : Word) = hesrLenAddr from by bv_omega,
      show (hesrBase + 160 : Word) + 4 = hesrBase + 164 from by bv_omega] at h40
  have e40 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 160) Codegen.headerExtractStateRoot_prog 40
      (.SD .x5 .x12 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h40
  have f40 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ (next - len - listBase)) **
     (hesrOffAddr ↦ₘ (next - len - listBase)))
    (by pcFreeR) e40
  -- [41] jal x0, +4  → hesrBase+168
  have h41 := jal_x0_spec_gen_within (4 : BitVec 21) (hesrBase + 164)
  rw [show hesrBase + 164 + signExtend21 (4 : BitVec 21) = hesrBase + 168 from by
      rw [show signExtend21 (4 : BitVec 21) = (4 : Word) from by decide]; bv_omega] at h41
  have e41 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 164) Codegen.headerExtractStateRoot_prog 41
      (.JAL .x0 (4 : BitVec 21)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h41
  have f41 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ (next - len - listBase)) **
     (.x5 ↦ᵣ hesrLenAddr) ** (hesrOffAddr ↦ₘ (next - len - listBase)) ** (hesrLenAddr ↦ₘ len))
    (by pcFreeR) e41
  rw [sepConj_emp_left'] at f41
  -- compose the seven steps
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f33 f34
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f35
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f37
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f38
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s4 f40
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s5 f41
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s6

/-! ## Success-tail: reload offset + form content pointer ([47]-[50])

    `la x5,hesr_offset ; ld x28,0(x5)` reloads the stored field offset into `x28`,
    then `add x28,x8,x28` forms the absolute content pointer `listBase + fo`. -/
private theorem hesrOffsetLoadAdd (fo listBase v5old v28old : Word) :
    cpsTripleWithin 4 (hesrBase + 188) (hesrBase + 204) hesrCode
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo))
      ((.x5 ↦ᵣ hesrOffAddr) ** (.x28 ↦ᵣ (listBase + fo)) ** (.x8 ↦ᵣ listBase) **
       (hesrOffAddr ↦ₘ fo)) := by
  -- [47-48] la x5, hesr_offset
  have f47 := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo))
    (by pcFreeR) (hesrLaOff188 v5old)
  -- [49] ld x28, 0(x5)  → x28 = fo
  have h49 := ld_spec_gen_within .x28 .x5 hesrOffAddr v28old fo (0 : BitVec 12)
    (hesrBase + 196) (by decide)
  rw [signExtend12_0, show (hesrOffAddr + 0 : Word) = hesrOffAddr from by bv_omega,
      show (hesrBase + 196 : Word) + 4 = hesrBase + 200 from by bv_omega] at h49
  have e49 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 196) Codegen.headerExtractStateRoot_prog 49
      (.LD .x28 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h49
  have f49 := cpsTripleWithin_frameR ((.x8 ↦ᵣ listBase))
    (by pcFreeR) e49
  -- [50] add x28, x8, x28  → x28 = listBase + fo
  have h50 := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase fo (hesrBase + 200) (by decide)
  rw [show (hesrBase + 200 : Word) + 4 = hesrBase + 204 from by bv_omega] at h50
  have e50 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 200) Codegen.headerExtractStateRoot_prog 50
      (.ADD .x28 .x8 .x28) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h50
  have f50 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ hesrOffAddr) ** (hesrOffAddr ↦ₘ fo))
    (by pcFreeR) e50
  -- compose
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f47 f49
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f50
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-! ## Success-tail: reload length + load compare constant ([42]-[45])

    `la x5,hesr_length ; ld x6,0(x5)` reloads the stored length into `x6`, then
    `li x7,32` loads the expected 32-byte root length; the `bne x6,x7` at [46]
    dispatches on whether the decoded length is exactly 32. -/
private theorem hesrLenLoad (len v5old v6old v7old : Word) :
    cpsTripleWithin 4 (hesrBase + 168) (hesrBase + 184) hesrCode
      ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (hesrLenAddr ↦ₘ len))
      ((.x5 ↦ᵣ hesrLenAddr) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (hesrLenAddr ↦ₘ len)) := by
  -- [42-43] la x5, hesr_length
  have f42 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6old) ** (.x7 ↦ᵣ v7old) ** (hesrLenAddr ↦ₘ len))
    (by pcFreeR) (hesrLaLen168 v5old)
  -- [44] ld x6, 0(x5)  → x6 = len
  have h44 := ld_spec_gen_within .x6 .x5 hesrLenAddr v6old len (0 : BitVec 12)
    (hesrBase + 176) (by decide)
  rw [signExtend12_0, show (hesrLenAddr + 0 : Word) = hesrLenAddr from by bv_omega,
      show (hesrBase + 176 : Word) + 4 = hesrBase + 180 from by bv_omega] at h44
  have e44 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 176) Codegen.headerExtractStateRoot_prog 44
      (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h44
  have f44 := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7old))
    (by pcFreeR) e44
  -- [45] li x7, 32
  have h45 := li_spec_gen_within .x7 v7old (32 : Word) (hesrBase + 180) (by decide)
  rw [show (hesrBase + 180 : Word) + 4 = hesrBase + 184 from by bv_omega] at h45
  have e45 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 180) Codegen.headerExtractStateRoot_prog 45
      (.LI .x7 (32 : Word)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h45
  have f45 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ hesrLenAddr) ** (.x6 ↦ᵣ len) ** (hesrLenAddr ↦ₘ len))
    (by pcFreeR) e45
  -- compose
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f42 f44
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f45
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-- Round-trip identity: `ofNat 64 fo.toNat = fo` for a 64-bit word. -/
private theorem hesr_ofNat_toNat (fo : Word) : (BitVec.ofNat 64 fo.toNat : Word) = fo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt fo.isLt

/-! ## Success-tail: copy 32 content bytes then finish ([51]-[58])

    The `hesrCopyLoop` 32-byte LBU/SB copy (`bytesRegion outPtr` becomes the field
    content `copyIntoRegion outBytes headerBytes 0 fo.toNat 32`) composed with the
    `hesrSuccessFinish` `li a0,0`/`jal`/epilogue tail.  This is the a0=0 arm's
    load-bearing "output = the 32 field-content bytes" claim. -/
private theorem hesrCopyThenFinish
    (fo listBase outPtr newSp x29old v1 v9 a0old : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : fo.toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * 32 + (2 + 6)) (hesrBase + 204) (saved.ra &&& ~~~(1 : Word)) hesrCode
      (((.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 fo.toNat)) **
        (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes) **
       ((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ listBase) **
        (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr))
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) **
       ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
        regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
        bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ** Fr)) := by
  -- The copy loop over 32 bytes (n = 31), starting at src offset fo.toNat, dst offset 0.
  have hcopy := hesrCopyLoop listBase outPtr x29old headerBytes outBytes fo.toNat 0 31 0
    h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
  -- Normalize the copy loop's `ofNat` indices to the entry form.
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd] at hcopy
  rw [show (outPtr + BitVec.ofNat 64 0 : Word) = outPtr from by bv_omega,
      show copyIntoRegion outBytes headerBytes 0 fo.toNat 0 = outBytes from rfl] at hcopy
  -- Frame the copy loop with the finish-tail registers/frame.
  have hcopyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) **
     savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hcopy
  -- The finish tail with a0 := 0, framed by the copy residual + Fr.
  have hfin := hesrSuccessFinish newSp a0old v1 listBase v9 (outPtr + BitVec.ofNat 64 32) saved
    ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
     regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
     bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
  -- compose copy ;; finish
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hcopyF hfin
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-! ## Success-tail: the a0=0 continuation ([47]-[58])

    The length-check not-taken (`len = 32`) arm: reload the offset and form the
    content pointer (`hesrOffsetLoadAdd`), then copy the 32 content bytes and
    return with `a0 = 0` (`hesrCopyThenFinish`).  Entry `x6 = 32` comes from the
    reloaded length on the success path. -/
private theorem hesrSuccessContinue
    (fo listBase outPtr newSp v5old v28old x29old v1 v9 a0old : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : fo.toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (4 + (6 * 32 + (2 + 6))) (hesrBase + 188) (saved.ra &&& ~~~(1 : Word)) hesrCode
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) **
       (.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved **
       Fr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
       ((.x6 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) **
        regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
        bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) **
        ((.x5 ↦ᵣ hesrOffAddr) ** (hesrOffAddr ↦ₘ fo) ** Fr))) := by
  -- [47]-[50] reload offset + form content pointer.
  have hola := hesrOffsetLoadAdd fo listBase v5old v28old
  have holaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ BitVec.ofNat 64 32) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hola
  -- [51]-[58] copy + finish, framed by the offset residual + Fr.
  have hctf := hesrCopyThenFinish fo listBase outPtr newSp x29old v1 v9 a0old saved
    headerBytes outBytes ((.x5 ↦ᵣ hesrOffAddr) ** (hesrOffAddr ↦ₘ fo) ** Fr)
    (by repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
  rw [hesr_ofNat_toNat fo] at hctf
  -- compose
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) holaF hctf
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s

/-! ## Length-check dispatch ([46]→ret)

    `BNE x6, x7, +60` (`hesrBase+184`): if the decoded field length `len` differs
    from 32, jump to the `status2` return (`a0 = 2`); otherwise fall through to the
    success continuation (`a0 = 0`, copy the 32 content bytes).  Both arms embed the
    epilogue and merge at `ret`.  The post is the two-way disjunction pinning the
    genuine result: on `a0 = 0` (`len = 32`) the output region holds the extracted
    32 field-content bytes (`copyIntoRegion`), on `a0 = 2` (`len ≠ 32`) it is
    unchanged. -/
private theorem hesrLenDispatch
    (fo listBase outPtr newSp len v5old v28old x29old v1 v9 a0old : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : fo.toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + 204) (hesrBase + 184) (saved.ra &&& ~~~(1 : Word)) hesrCode
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
       (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) ** (hesrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) **
       (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
       bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) **
       (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)),
        ((((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
           (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
           memOwn hesrLenAddr ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           bytesRegion outPtr finalOut ** (hesrOffAddr ↦ₘ fo) ** Fr)) **
         ⌜(a0v = (0 : Word) ∧ len = (32 : Word) ∧
              finalOut = copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ∨
           (a0v = (2 : Word) ∧ len ≠ (32 : Word) ∧ finalOut = outBytes)⌝) h) := by
  -- [46] BNE x6, x7, +60 : taken (len ≠ 32) → status2 (+244), fall-through (len = 32) → +188.
  have ha_t : (hesrBase + 184 : Word) + signExtend13 (60 : BitVec 13) = hesrBase + 244 := by
    rw [show signExtend13 (60 : BitVec 13) = (60 : Word) from by decide]; bv_omega
  have ha_f : (hesrBase + 184 : Word) + 4 = hesrBase + 188 := by bv_omega
  have hmono : ∀ a i', CodeReq.singleton (hesrBase + 184) (.BNE .x6 .x7 (60 : BitVec 13)) a = some i'
      → hesrCode a = some i' :=
    CodeReq.ofProg_mem_at hesrBase (hesrBase + 184) Codegen.headerExtractStateRoot_prog 46
      (.BNE .x6 .x7 (60 : BitVec 13)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)
  have hbne := bne_spec_gen_within .x6 .x7 (60 : BitVec 13) len (32 : Word) (hesrBase + 184)
  rw [ha_t, ha_f] at hbne
  have hbnee := cpsBranchWithin_extend_code hmono hbne
  by_cases hlen : len = (32 : Word)
  · -- Fall-through arm: len = 32, run the success continuation; taken arm is vacuous.
    have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 hlen)
    have hntF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) **
       (hesrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (by unfold savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) hnt
    have hlen2 : len = BitVec.ofNat 64 32 := by rw [hlen]; decide
    have hsucc := hesrSuccessContinue fo listBase outPtr newSp v5old v28old x29old v1 v9 a0old saved
      headerBytes outBytes ((.x7 ↦ᵣ (32 : Word)) ** (hesrLenAddr ↦ₘ len) ** Fr)
      (by repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
      h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
    have s := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by rw [← hlen2]; xperm_chunked hp) hntF hsucc
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun h hq => by
        refine ⟨(0 : Word), copyIntoRegion outBytes headerBytes 0 fo.toNat 32, ?_⟩
        refine (sepConj_pure_right h).2 ⟨?_, Or.inl ⟨rfl, hlen, rfl⟩⟩
        have hq2 : (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
            (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
           ((.x5 ↦ᵣ hesrOffAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (32 : Word)) **
            (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (fo.toNat + 32))) ** regOwn .x29 **
            (hesrLenAddr ↦ₘ len) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
            bytesRegion outPtr (copyIntoRegion outBytes headerBytes 0 fo.toNat 32) **
            (hesrOffAddr ↦ₘ fo) ** Fr)) h := by xperm_chunked hq
        exact sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x6)
              (sepConj_mono (regIs_implies_regOwn .x7)
                (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (fun _ hh => hh)
                    (sepConj_mono_left memIs_implies_memOwn)))))) h hq2) s
  · -- Taken arm: len ≠ 32, run status2 return; fall-through arm is vacuous.
    have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hlen ((sepConj_pure_right _).1 hQ).2)
    have htkF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) ** (.x8 ↦ᵣ listBase) ** (hesrOffAddr ↦ₘ fo) **
       (hesrLenAddr ↦ₘ len) ** (.x18 ↦ᵣ outPtr) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** (.x10 ↦ᵣ a0old) **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (by unfold savedFrame; repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj) htk
    have hs2 := hesrStatus2Return newSp a0old v1 listBase v9 outPtr saved
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ v5old) ** (.x28 ↦ᵣ v28old) **
       (hesrOffAddr ↦ₘ fo) ** (hesrLenAddr ↦ₘ len) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes ** Fr)
      (by repeat' first
        | exact hFr | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj)
    have hs2' := cpsTripleWithin_mono_nSteps (show (1 + 6) ≤ 204 by omega) hs2
    have s := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) htkF hs2'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun h hq => by
        refine ⟨(2 : Word), outBytes, ?_⟩
        refine (sepConj_pure_right h).2 ⟨?_, Or.inr ⟨rfl, hlen, rfl⟩⟩
        have hq2 : (((.x10 ↦ᵣ (2 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
            (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
           ((.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x28 ↦ᵣ v28old) **
            (.x29 ↦ᵣ x29old) ** (hesrLenAddr ↦ₘ len) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
            (hesrOffAddr ↦ₘ fo) ** Fr)) h := by xperm_chunked hq
        exact sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x6)
              (sepConj_mono (regIs_implies_regOwn .x7)
                (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (regIs_implies_regOwn .x29)
                    (sepConj_mono_left memIs_implies_memOwn)))))) h hq2) s

/-! ## Full success tail ([33]→ret)

    All five RLP walks succeeded: `x10 = next` (final cursor), `x12 = len` (field
    length), `x8 = listBase`.  Compute the field offset `fo = next − len − listBase`,
    round-trip `fo`/`len` through the two global scratch cells (`hesrOffsetStore`),
    reload the length and set the copy counter (`hesrLenLoad`), then dispatch on the
    length check (`hesrLenDispatch`).  The post pins the genuine result:
    `a0 = 0` with the output region holding the extracted 32 field-content bytes when
    `len = 32`, else `a0 = 2` with the output unchanged. -/
private theorem hesrSuccessTail
    (next len listBase outPtr newSp v5old v6old v7old v28old x29old offOld lenOld v1 v9 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_src_bound : (next - len - listBase).toNat + 32 ≤ headerBytes.length)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (9 + 4 + (1 + 204)) (hesrBase + 132) (saved.ra &&& ~~~(1 : Word)) hesrCode
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ v6old) **
       (.x5 ↦ᵣ v5old) ** (.x7 ↦ᵣ v7old) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) **
       (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) ** (hesrOffAddr ↦ₘ offOld) **
       (hesrLenAddr ↦ₘ lenOld) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
      (fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)),
        ((((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
           (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
           memOwn hesrLenAddr ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           bytesRegion outPtr finalOut ** (hesrOffAddr ↦ₘ (next - len - listBase)) **
           ((.x12 ↦ᵣ len) ** Fr))) **
         ⌜(a0v = (0 : Word) ∧ len = (32 : Word) ∧
              finalOut = copyIntoRegion outBytes headerBytes 0 (next - len - listBase).toNat 32) ∨
           (a0v = (2 : Word) ∧ len ≠ (32 : Word) ∧ finalOut = outBytes)⌝) h) := by
  -- [33]-[41] offset/length compute + global-cell store, framed by the ambient state.
  have hoffF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7old) ** (.x18 ↦ᵣ outPtr) ** (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ x29old) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
     (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) ** savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    (hesrOffsetStore next len listBase v5old v6old offOld lenOld)
  -- [42]-[45] reload length + set copy counter, framed by the rest.
  have hllF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) **
     (.x28 ↦ᵣ v28old) ** (.x29 ↦ᵣ x29old) ** (.x0 ↦ᵣ (0 : Word)) **
     (hesrOffAddr ↦ₘ (next - len - listBase)) ** bytesRegion listBase headerBytes **
     bytesRegion outPtr outBytes ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x9 ↦ᵣ v9) **
     savedFrame newSp saved ** Fr)
    (by unfold savedFrame; repeat' first
      | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
    (hesrLenLoad len hesrLenAddr (next - len - listBase) v7old)
  -- [46]→ret length-check dispatch.
  have hdisp := hesrLenDispatch (next - len - listBase) listBase outPtr newSp len hesrLenAddr
    v28old x29old v1 v9 next saved headerBytes outBytes ((.x12 ↦ᵣ len) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | apply pcFree_sepConj)
    h_src_align h_dst_align h_src_bound h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid
  -- compose offsetStore ;; lenLoad ;; lenDispatch.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hoffF hllF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hdisp
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => hp) s2

#print axioms hesrNextStep
#print axioms hesrSuccessTail
#print axioms hesrLenDispatch
#print axioms hesrSuccessContinue
#print axioms hesrCopyThenFinish
#print axioms hesrLenLoad
#print axioms hesrOffsetLoadAdd
#print axioms hesrOffsetStore
#print axioms hesrCopyLoop
#print axioms hesrInitStep
#print axioms hesrEpilogue
#print axioms hesrStatus1Return
#print axioms hesrStatus2Return
#print axioms hesrSuccessFinish

end EvmAsm.Codegen.HeaderFieldsSpec
