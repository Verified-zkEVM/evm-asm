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

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells (local re-declaration of the `mset_memcpy` helper macro). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

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

#print axioms hesrCopyLoop
#print axioms hesrInitStep
#print axioms hesrEpilogue
#print axioms hesrStatus1Return

end EvmAsm.Codegen.HeaderFieldsSpec
