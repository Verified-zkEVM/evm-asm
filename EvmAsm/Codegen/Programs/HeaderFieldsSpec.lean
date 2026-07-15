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
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

/-! ## Fixed guest addresses and code -/

/-- Guest entry of `header_extract_state_root`. -/
def hesrBase : Word := BitVec.ofNat 64 Codegen.GuestAddrs.header_extract_state_root

/-- The `header_extract_state_root` body at its linked guest address. -/
abbrev hesrCode : CodeReq :=
  CodeReq.ofProg hesrBase Codegen.headerExtractStateRoot_prog

theorem hesr_prog_length : Codegen.headerExtractStateRoot_prog.length = 68 := rfl

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
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 44)) ** bytesRegion listBase bytes

end EvmAsm.Codegen.HeaderFieldsSpec
