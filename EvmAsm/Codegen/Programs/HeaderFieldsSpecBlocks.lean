import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Codegen.Programs.HeaderFieldsSpecCommon

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

/-! ## Register marshalling between walker calls

    The header extractor spills the cursor to `sp+32` and the end pointer to
    `sp+40` and reloads them around each `rlp_walk_next` call.  `hesrMarshalInit`
    ([12]-[15], `+48 → +64`) seeds both slots after the init call; `hesrMarshalNext`
    ([18]-[20] etc., 3 instructions) re-spills the fresh cursor and reloads the
    preserved end pointer from `sp+40` before each subsequent call. -/

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


end EvmAsm.Codegen.HeaderFieldsSpec
