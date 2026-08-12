/-
  Caller contract for the 22-instruction `header_validate_extra_data_length`
  accessor.

  `headerValidateExtraDataLength_prog` allocates a 16-byte frame, saves `ra`,
  loads the field index (12 = `extra_data`) and the two output-cell pointers
  (`hved_off`, `hved_len`), tail-calls the verified strict `rlp_list_nth_item`
  selector, then dispatches on the callee's status:

    * callee status ≠ 0  → RLP parse failure, return `a0 = 2`;
    * callee status = 0 (field 12 exists) → reload the field length and compare
      with 32 (`bltu x7, x6` = `32 <ᵤ len`):
        - `len > 32`  → return `a0 = 1` (reject);
        - `len ≤ 32`  → return `a0 = 0` (accept).

  Its whole-program contract is therefore

      prologue+setup  ;;  rlpListNthItem_spec_within (field index 12)  ;;
        status dispatch  ;;  length compare  ;;  epilogue

  and its three-way post pins `a0` to the ACTUAL field-12 content length via
  K20's `Result` relation:  `a0 = 0 ↔ len ≤ 32`, `a0 = 1 ↔ len > 32`
  (both on a genuine `Success`), and `a0 = 2 ↔` a genuine `Failure`.
-/

import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## Base addresses and linked code -/

abbrev H : Word := (GuestAddrs.header_validate_extra_data_length : Word)
abbrev Off : Word := (GuestAddrs.hved_off : Word)
abbrev Len : Word := (GuestAddrs.hved_len : Word)

/-- The wrapper's own program. -/
abbrev hvedProg : Program := EvmAsm.Codegen.headerValidateExtraDataLength_prog

theorem hved_length : hvedProg.length = 22 := by decide

/-- The wrapper's own re-emitted instructions at `header_validate_extra_data_length`. -/
def hvedCode : CodeReq := CodeReq.ofProg H hvedProg

/-- The full linked closure: this wrapper plus the strict K20 selector and its
    transitive callees. -/
def fullCode : CodeReq := hvedCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem hved_disjoint :
    hvedCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold hvedCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hved_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · right
    rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide


/-- K20's linked code is subsumed by the wrapper's full closure. -/
theorem k20_mono :
    ∀ a i, EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right hved_disjoint (fun _ _ h => h) a i hi

theorem hved_mono : ∀ a i, hvedCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-- Weaken the three dispatch scratch registers `x5/x6/x7` from concrete values
    to owned. -/
theorem weaken_x567 (v5 v6 v7 : Word) (F : Assertion) :
    ∀ h, ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** F) h →
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** F) h :=
  sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (fun _ hx => hx)))

/-- Weaken the callee's `x11/x12` result-scratch registers to owned. -/
theorem weaken_x1112 (v11 v12 : Word) (F : Assertion) :
    ∀ h, ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** F) h →
      (regOwn .x11 ** regOwn .x12 ** F) h :=
  sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12) (fun _ hx => hx))

/-- K20's `returnResult` body for a fixed set of existential witnesses,
    specialized to this wrapper (`sp0 = spH`, field index 12, output cells
    `Off`/`Len`). -/
def retBody (spH newSp listBase oldOffset oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (status offset len v11 v12 : Word) : Assertion :=
  (((.x2 ↦ᵣ spH) ** regsAt listNthFrame (savedVals saved) ** savedFrame newSp saved) **
    ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (Off ↦ₘ offset) ** (Len ↦ₘ len))) **
   ⌜Result bytes listBase listLen 12 oldOffset oldLen status offset len⌝

/-! ## Caller-facing pre/post -/

/-- Pre-prologue caller footprint.  `a0/a1 = listBase/listLenW` are the RLP
    list base pointer and its byte length; `x8/x9/x18/x19/x20/x21` are the
    callee-saved values (`saved.s0..s5`); the K20 stack frame
    (`frameSlotsOwn listNthFrame newSp`) and the wrapper's own return slot
    (`spH ↦ₘ oldRaSlot`) sit below `sp`; the two output cells `hved_off`,
    `hved_len` hold arbitrary `oldOffset`/`oldLen`. -/
def hvedPre
    (sp0 raIn oldRaSlot spH newSp listBase listLenW old12 old13 old14
      oldOffset oldLen : Word) (saved : Saved) (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (spH ↦ₘ oldRaSlot) **
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ old12) **
  (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) **
  (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
  (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion listBase bytes ** frameSlotsOwn listNthFrame newSp **
  (Off ↦ₘ oldOffset) ** (Len ↦ₘ oldLen)

/-- The callee's caller-visible footprint, minus `x1` (which `jal` writes to
    `H + 32`).  Exactly `rlpListNthItem_spec_within`'s pre with `x1` pulled to
    the front (via `regsAt_listNthFrame`) and dropped. -/
def calleePre
    (spH newSp listBase listLenW oldOffset oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) **
  (.x21 ↦ᵣ saved.s5) ** frameSlotsOwn listNthFrame newSp **
  entryRest listBase listLenW (12 : Word) Off Len oldOffset oldLen bytes

/-- The payload frame carried unchanged through the status dispatch, length
    compare, and epilogue: callee-saved registers, K20 frame memory, the byte
    region, and the non-dispatch scratch registers owned.  (`x5/x6/x7` are
    tracked separately — they are actively written on the accept/reject path.) -/
def frameG (newSp listBase : Word) (saved : Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
  (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
  savedFrame newSp saved **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes

/-- Restored caller footprint on return (shared by all three post arms):
    `ra`/`sp` restored, `x5/x6/x7` owned, plus the preserved `frameG` payload. -/
def commonRet
    (sp0 spH newSp raIn listBase : Word) (saved : Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  frameG newSp listBase saved bytes

/-- Success return (`a0 = 0`): field 12 exists and its content length ≤ 32. -/
def hvedSuccess
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ offset len,
    (⌜Result bytes listBase listLen 12 oldOffset oldLen 0 offset len ∧
        ¬ BitVec.ult (32 : Word) len⌝ **
      (.x10 ↦ᵣ (0 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
      commonRet sp0 spH newSp raIn listBase saved bytes) h

/-- Reject return (`a0 = 1`): field 12 exists but its content length > 32. -/
def hvedReject
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ offset len,
    (⌜Result bytes listBase listLen 12 oldOffset oldLen 0 offset len ∧
        BitVec.ult (32 : Word) len⌝ **
      (.x10 ↦ᵣ (1 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
      commonRet sp0 spH newSp raIn listBase saved bytes) h

/-- Failure return (`a0 = 2`): a genuine RLP `Failure` for field 12; the output
    cells are unchanged (`oldOffset`/`oldLen`). -/
def hvedFail
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  (⌜Result bytes listBase listLen 12 oldOffset oldLen 1 oldOffset oldLen⌝ **
    (.x10 ↦ᵣ (2 : Word)) ** (Off ↦ₘ oldOffset) ** (Len ↦ₘ oldLen) **
    commonRet sp0 spH newSp raIn listBase saved bytes)

/-- Three-way caller post: `a0 ∈ {0,1,2}`, each arm tying `a0` to the actual
    field-12 length relation carried by K20's `Result`. -/
def hvedPost
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h =>
    hvedSuccess sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen h ∨
    hvedReject sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen h ∨
    hvedFail sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen h

/-! ## Prologue + argument setup (instructions 0--6) -/

set_option maxRecDepth 8000 in
/-- Allocate the 16-byte frame, save `ra`, load the field index (12) and the
    two output-cell pointers.  The post is exactly `calleePre`, framed by the
    wrapper's own saved-`ra` slot and the incumbent `x1 = raIn`. -/
theorem hvedHead
    (sp0 raIn oldRaSlot spH newSp listBase listLenW old12 old13 old14
      oldOffset oldLen : Word) (saved : Saved) (bytes : List (BitVec 8))
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12)) :
    cpsTripleWithin 7 H (H + 28) fullCode
      (hvedPre sp0 raIn oldRaSlot spH newSp listBase listLenW old12 old13 old14
        oldOffset oldLen saved bytes)
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
        calleePre spH newSp listBase listLenW oldOffset oldLen saved bytes) := by
  -- [0] ADDI x2 x2 -16 : sp0 → spH
  have h0 := addi_spec_gen_same_within .x2 sp0 (-16 : BitVec 12) H (by decide)
  rw [← hspH] at h0
  have h0' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H H hvedProg 0
        (.ADDI .x2 .x2 (-16 : BitVec 12)) (by decide) (by rw [hved_length]; decide)
        rfl (by rw [hved_length]; decide)) h0)
  -- [1] SD x2 x1 0 : store raIn at [spH]
  have h1 := sd_spec_gen_within .x2 .x1 spH raIn oldRaSlot (0 : BitVec 12) (H + 4)
  rw [show spH + signExtend12 (0 : BitVec 12) = spH from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 4) hvedProg 1
        (.SD .x2 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [hved_length]; decide)
        rfl (by rw [hved_length]; decide)) h1)
  -- [2] LI x12 12
  have h2 := li_spec_gen_within .x12 old12 (12 : Word) (H + 8) (by decide)
  have h2' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 8) hvedProg 2 (.LI .x12 (12 : Word))
        (by bv_omega) (by rw [hved_length]; decide) rfl
        (by rw [hved_length]; decide)) h2)
  -- [3-4] la x13 = hved_off
  have hau3 := CodeReq.ofProg_mem_at H (H + 12) hvedProg 3
    (.AUIPC .x13 (EvmAsm.Codegen.laHi GuestAddrs.hved_off
      (GuestAddrs.header_validate_extra_data_length + 12))) (by bv_omega)
    (by rw [hved_length]; decide) rfl (by rw [hved_length]; decide)
  have had4 := CodeReq.ofProg_mem_at H (H + 16) hvedProg 4
    (.ADDI .x13 .x13 (EvmAsm.Codegen.laLo GuestAddrs.hved_off
      (GuestAddrs.header_validate_extra_data_length + 12))) (by bv_omega)
    (by rw [hved_length]; decide) rfl (by rw [hved_length]; decide)
  have h3 := EvmAsm.Rv64.la_materialize_within .x13 old13 (H + 12) Off (by decide)
    (by unfold H Off; decide) (fun a i hi => hved_mono a i (hau3 a i hi))
    (fun a i hi => hved_mono a i (had4 a i hi))
  -- [5-6] la x14 = hved_len
  have hau5 := CodeReq.ofProg_mem_at H (H + 20) hvedProg 5
    (.AUIPC .x14 (EvmAsm.Codegen.laHi GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 20))) (by bv_omega)
    (by rw [hved_length]; decide) rfl (by rw [hved_length]; decide)
  have had6 := CodeReq.ofProg_mem_at H (H + 24) hvedProg 6
    (.ADDI .x14 .x14 (EvmAsm.Codegen.laLo GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 20))) (by bv_omega)
    (by rw [hved_length]; decide) rfl (by rw [hved_length]; decide)
  have h5 := EvmAsm.Rv64.la_materialize_within .x14 old14 (H + 20) Len (by decide)
    (by unfold H Len; decide) (fun a i hi => hved_mono a i (hau5 a i hi))
    (fun a i hi => hved_mono a i (had6 a i hi))
  -- Frame each step's untouched active atoms and compose.
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ oldRaSlot) ** (.x12 ↦ᵣ old12) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) (by pcf) h0'
  have h1F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
      (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) (by pcf) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
      (.x12 ↦ᵣ (12 : Word)) ** (.x14 ↦ᵣ old14)) (by pcf) h3
  have h5F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) **
      (.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ Off)) (by pcf) h5
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 h3F
  have h012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0123 h5F
  -- The six active atoms, established.
  have hlocal : cpsTripleWithin 7 H (H + 28) fullCode
      ((.x2 ↦ᵣ sp0) ** (spH ↦ₘ oldRaSlot) ** (.x1 ↦ᵣ raIn) **
        (.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14))
      ((.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) ** (.x1 ↦ᵣ raIn) **
        (.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ Off) ** (.x14 ↦ᵣ Len)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h012345
  -- Frame the untouched remainder.
  have hframed := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
      (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
      (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase bytes ** frameSlotsOwn listNthFrame newSp **
      (Off ↦ₘ oldOffset) ** (Len ↦ₘ oldLen)) (by pcf) hlocal
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold hvedPre at hp; xperm_hyp hp) (fun h hq => by
      unfold calleePre entryRest; xperm_hyp hq) hframed


/-! ## Call (instruction 7): jal + K20 selector -/

/-- K20's whole-routine step count, specialized to field index 12. -/
abbrev nCall : Nat := (12 + ((85 + 93 * (12 + 2)) + 6)) + 9

set_option maxRecDepth 8000 in
/-- Prologue+setup ;; `jal rlp_list_nth_item` ;; the strict K20 selector.  The
    post is K20's `returnResult` (its output cells `Off`/`Len` written, its
    semantic `Result` pinned), framed by the wrapper's saved-`ra` slot. -/
theorem hvedCall
    (sp0 raIn oldRaSlot spH newSp listBase listLenW old12 old13 old14
      oldOffset oldLen : Word) (saved : Saved) (bytes : List (BitVec 8))
    (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hnewSp : newSp = spH + signExtend12 (-64 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hraSaved : saved.ra = H + 32) :
    cpsTripleWithin (7 + 1 + nCall) H (H + 32) fullCode
      (hvedPre sp0 raIn oldRaSlot spH newSp listBase listLenW old12 old13 old14
        oldOffset oldLen saved bytes)
      (returnResult spH newSp listBase (12 : Word) Off Len oldOffset oldLen saved
        bytes listLen 12 ** (spH ↦ₘ raIn)) := by
  have hhead := hvedHead sp0 raIn oldRaSlot spH newSp listBase listLenW old12
    old13 old14 oldOffset oldLen saved bytes hspH
  -- [7] jal x1, rlp_list_nth_item
  have hjal := jal_link_spec_within (jalOff GuestAddrs.rlp_list_nth_item
    (GuestAddrs.header_validate_extra_data_length + 28)) (H + 28) raIn
  rw [show (H + 28) + signExtend21 (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.header_validate_extra_data_length + 28)) = B from by
    change BitVec.ofNat 64 GuestAddrs.header_validate_extra_data_length + BitVec.ofNat 64 28 + _ =
      BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
    exact jalOff_correct_add GuestAddrs.rlp_list_nth_item GuestAddrs.header_validate_extra_data_length 28
      (by decide) (by decide) (by decide) (by decide),
    show (H + 28 + 4 : Word) = H + 32 from by bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 28) hvedProg 7
        (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
          (GuestAddrs.header_validate_extra_data_length + 28))) (by bv_omega)
        (by rw [hved_length]; decide) rfl (by rw [hved_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    (calleePre spH newSp listBase listLenW oldOffset oldLen saved bytes **
      (spH ↦ₘ raIn)) (by unfold calleePre entryRest; pcf) hjalC
  -- The K20 selector.
  have hcallee0 := rlpListNthItem_spec_within spH newSp listBase listLenW
    (12 : Word) Off Len oldOffset oldLen saved bytes listLen 12 hnewSp hlistLenW
    rfl (by decide) hsalign hslack hover hvalid (by rw [hraSaved]; decide)
  rw [hraSaved] at hcallee0
  have hcalleeC := cpsTripleWithin_extend_code k20_mono hcallee0
  have hcalleeF := cpsTripleWithin_frameR (spH ↦ₘ raIn) (by pcf) hcalleeC
  have hcallee : cpsTripleWithin nCall B (H + 32) fullCode
      ((.x1 ↦ᵣ (H + 32)) **
        (calleePre spH newSp listBase listLenW oldOffset oldLen saved bytes **
          (spH ↦ₘ raIn)))
      (returnResult spH newSp listBase (12 : Word) Off Len oldOffset oldLen saved
        bytes listLen 12 ** (spH ↦ₘ raIn)) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold calleePre entryRest at hp
      rw [regsAt_listNthFrame, hraSaved]
      unfold entryRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeF
  -- Compose: head ;; jal ;; callee.
  have hhj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hhead hjalF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hhj hcallee


/-! ## Epilogue (instructions 19--21) -/

set_option maxRecDepth 8000 in
/-- Restore `ra`, deallocate the wrapper's 16-byte frame, and return, generic
    over the payload footprint `G` carried through unchanged. -/
theorem hvedEpi (sp0 spH raIn : Word) (G : Assertion) (hG : G.pcFree)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 3 (H + 76) raIn fullCode
      ((.x1 ↦ᵣ (H + 32)) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ spH) ** G)
      ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) ** G) := by
  -- [19] LD x1 x2 0 : restore ra
  have h0 := ld_spec_gen_within .x1 .x2 spH (H + 32) raIn (0 : BitVec 12) (H + 76)
    (by decide)
  rw [show spH + signExtend12 (0 : BitVec 12) = spH from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h0
  have h0' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 76) hvedProg 19
        (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega) (by rw [hved_length]; decide)
        rfl (by rw [hved_length]; decide)) h0)
  -- [20] ADDI x2 x2 16 : deallocate
  have h1 := addi_spec_gen_same_within .x2 spH (16 : BitVec 12) (H + 80) (by decide)
  rw [show spH + signExtend12 (16 : BitVec 12) = sp0 from by
    rw [hspH]; exact sext_frameRestore sp0 (-16 : BitVec 12) (16 : BitVec 12)
      (by decide)] at h1
  have h1' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 80) hvedProg 20
        (.ADDI .x2 .x2 (16 : BitVec 12)) (by bv_omega) (by rw [hved_length]; decide)
        rfl (by rw [hved_length]; decide)) h1)
  -- [21] JALR x0 x1 0 : return
  have h2 := EvmAsm.Evm64.ret_spec_within' (H + 84) raIn
  rw [hret] at h2
  have h2' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 84) hvedProg 21
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [hved_length]; decide)
        rfl (by rw [hved_length]; decide)) h2)
  have h0F := cpsTripleWithin_frameR ((.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn)) (by pcf) h1'
  have h1F := cpsTripleWithin_frameR ((.x2 ↦ᵣ sp0) ** (spH ↦ₘ raIn)) (by pcf) h2'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0' h0F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h1F
  have hcore : cpsTripleWithin 3 (H + 76) raIn fullCode
      ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ (H + 32)) ** (spH ↦ₘ raIn))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (spH ↦ₘ raIn)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h012
  have hframed := cpsTripleWithin_frameR G hG hcore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hframed


/-! ## Length load + compare dispatch (instructions 9--15/16--17, then epilogue) -/

set_option maxRecDepth 8000 in
/-- The `status = 0` (field-12 exists) path: reload the field length, compare
    with 32, and route to the accept (`a0 = 0`, `len ≤ 32`) or reject
    (`a0 = 1`, `len > 32`) arm, each returning through the epilogue.  `a0` is
    tied to the genuine `BitVec.ult 32 len`. -/
theorem hvedDispatch
    (sp0 spH newSp raIn listBase oldOffset oldLen offset len v5 v6 : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hResult : Result bytes listBase listLen 12 oldOffset oldLen 0 offset len) :
    cpsTripleWithin 10 (H + 36) raIn fullCode
      ((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x7 **
        (Off ↦ₘ offset) ** (Len ↦ₘ len) ** frameG newSp listBase saved bytes)
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
  -- [9-10] la x5 = hved_len
  have hau9 := CodeReq.ofProg_mem_at H (H + 36) hvedProg 9
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 36))) (by bv_omega)
    (by rw [hved_length]; decide) rfl (by rw [hved_length]; decide)
  have had10 := CodeReq.ofProg_mem_at H (H + 40) hvedProg 10
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 36))) (by bv_omega)
    (by rw [hved_length]; decide) rfl (by rw [hved_length]; decide)
  have hla := EvmAsm.Rv64.la_materialize_within .x5 v5 (H + 36) Len (by decide)
    (by unfold H Len; decide) (fun a i hi => hved_mono a i (hau9 a i hi))
    (fun a i hi => hved_mono a i (had10 a i hi))
  -- [11] LD x6 x5 0 : x6 := len
  have hld := ld_spec_gen_within .x6 .x5 Len v6 len (0 : BitVec 12) (H + 44) (by decide)
  rw [show Len + signExtend12 (0 : BitVec 12) = Len from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at hld
  have hld' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 44) hvedProg 11 (.LD .x6 .x5 (0 : BitVec 12))
        (by bv_omega) (by rw [hved_length]; decide) rfl
        (by rw [hved_length]; decide)) hld)
  -- [12] LI x7 32
  have hli := li_spec_gen_own_within .x7 (32 : Word) (H + 48) (by decide)
  have hli' := cpsTripleWithin_extend_code hved_mono
    (cpsTripleWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 48) hvedProg 12 (.LI .x7 (32 : Word))
        (by bv_omega) (by rw [hved_length]; decide) rfl
        (by rw [hved_length]; decide)) hli)
  -- Straight-line load [9-12]: establish x5=Len, x6=len, x7=32.
  have hlaF := cpsTripleWithin_frameR ((.x6 ↦ᵣ v6) ** regOwn .x7 ** (Len ↦ₘ len))
    (by pcf) hla
  have hldF := cpsTripleWithin_frameR (regOwn .x7) (by pcf) hld'
  have hload01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlaF hldF
  have hload := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hload01 (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ Len) ** (.x6 ↦ᵣ len) ** (Len ↦ₘ len)) (by pcf) hli')
  -- Frame the dispatch-invariant remainder around the load.
  have hloadF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
      (Off ↦ₘ offset) ** frameG newSp listBase saved bytes) (by unfold frameG; pcf)
    hload
  -- [13] BLTU x7 x6 12 : 32 <ᵤ len ?
  have hbltu := bltu_spec_gen_within .x7 .x6 (12 : BitVec 13) (32 : Word) len (H + 52)
  rw [show (H + 52) + signExtend13 (12 : BitVec 13) = H + 64 from by
    rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega]
    at hbltu
  have hbltuC := cpsBranchWithin_extend_code hved_mono
    (cpsBranchWithin_extend_code (cr' := hvedCode)
      (CodeReq.ofProg_mem_at H (H + 52) hvedProg 13 (.BLTU .x7 .x6 (12 : BitVec 13))
        (by bv_omega) (by rw [hved_length]; decide) rfl
        (by rw [hved_length]; decide)) hbltu)
  have hbltuF := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ Len) ** (.x10 ↦ᵣ (0 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
      (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) **
      frameG newSp listBase saved bytes) (by unfold frameG; pcf) hbltuC
  -- Compose load ;; branch.
  have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hloadF hbltuF
  -- Reject arm [16-17] then epilogue (H+64 → raIn).
  have hrej : cpsTripleWithin 5 (H + 64) raIn fullCode
      (((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** ⌜BitVec.ult (32 : Word) len⌝) **
        ((.x5 ↦ᵣ Len) ** (.x10 ↦ᵣ (0 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) **
          frameG newSp listBase saved bytes))
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre (P := BitVec.ult (32 : Word) len)
        (H := (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) **
          (.x10 ↦ᵣ (0 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) **
          frameG newSp listBase saved bytes) (fun hult => ?_))
    -- [16] LI x10 1
    have h16 := li_spec_gen_within .x10 (0 : Word) (1 : Word) (H + 64) (by decide)
    have h16' := cpsTripleWithin_extend_code hved_mono
      (cpsTripleWithin_extend_code (cr' := hvedCode)
        (CodeReq.ofProg_mem_at H (H + 64) hvedProg 16 (.LI .x10 (1 : Word))
          (by bv_omega) (by rw [hved_length]; decide) rfl
          (by rw [hved_length]; decide)) h16)
    have h16F := cpsTripleWithin_frameR
      ((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) ** (Off ↦ₘ offset) **
        (Len ↦ₘ len) ** (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) **
        frameG newSp listBase saved bytes) (by unfold frameG; pcf) h16'
    -- [17] JAL x0 8 : full-state jump
    have h17 := jal_x0_spec_gen_within (8 : BitVec 21) (H + 68)
    rw [show (H + 68) + signExtend21 (8 : BitVec 21) = H + 76 from by
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega]
      at h17
    have h17' := cpsTripleWithin_extend_code hved_mono
      (cpsTripleWithin_extend_code (cr' := hvedCode)
        (CodeReq.ofProg_mem_at H (H + 68) hvedProg 17 (.JAL .x0 (8 : BitVec 21))
          (by bv_omega) (by rw [hved_length]; decide) rfl
          (by rw [hved_length]; decide)) h17)
    have h17F : cpsTripleWithin 1 (H + 68) (H + 76) fullCode
        ((.x10 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) **
          (Off ↦ₘ offset) ** (Len ↦ₘ len) ** (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) **
          (spH ↦ₘ raIn) ** frameG newSp listBase saved bytes)
        ((.x10 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) **
          (Off ↦ₘ offset) ** (Len ↦ₘ len) ** (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) **
          (spH ↦ₘ raIn) ** frameG newSp listBase saved bytes) :=
      cpsTripleWithin_weaken (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR _ (by unfold frameG; pcf) h17')
    have hepi := hvedEpi sp0 spH raIn
      ((.x10 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ Len) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
        (Off ↦ₘ offset) ** (Len ↦ₘ len) ** frameG newSp listBase saved bytes)
      (by unfold frameG; pcf) hspH hret
    -- Compose [16] ;; [17] ;; epilogue.
    have h1617 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      h16F h17F
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      xperm_hyp hp) h1617 hepi
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hall
    refine Or.inr (Or.inl ⟨offset, len, ?_⟩)
    unfold commonRet
    refine (sepConj_pure_left h).2 ⟨⟨hResult, hult⟩, ?_⟩
    have hq2 := weaken_x567 Len len (32 : Word)
      ((.x10 ↦ᵣ (1 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
        (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) **
        frameG newSp listBase saved bytes) h (by xperm_hyp hq)
    xperm_hyp hq2
  -- Success arm [14-15] then epilogue (H+56 → raIn).
  have hsucc : cpsTripleWithin 5 (H + 56) raIn fullCode
      (((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** ⌜¬ BitVec.ult (32 : Word) len⌝) **
        ((.x5 ↦ᵣ Len) ** (.x10 ↦ᵣ (0 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) **
          frameG newSp listBase saved bytes))
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre (P := ¬ BitVec.ult (32 : Word) len)
        (H := (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) **
          (.x10 ↦ᵣ (0 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) **
          frameG newSp listBase saved bytes) (fun hnult => ?_))
    -- [14] LI x10 0
    have h14 := li_spec_gen_within .x10 (0 : Word) (0 : Word) (H + 56) (by decide)
    have h14' := cpsTripleWithin_extend_code hved_mono
      (cpsTripleWithin_extend_code (cr' := hvedCode)
        (CodeReq.ofProg_mem_at H (H + 56) hvedProg 14 (.LI .x10 (0 : Word))
          (by bv_omega) (by rw [hved_length]; decide) rfl
          (by rw [hved_length]; decide)) h14)
    have h14F := cpsTripleWithin_frameR
      ((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) ** (Off ↦ₘ offset) **
        (Len ↦ₘ len) ** (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) **
        frameG newSp listBase saved bytes) (by unfold frameG; pcf) h14'
    -- [15] JAL x0 16 : full-state jump
    have h15 := jal_x0_spec_gen_within (16 : BitVec 21) (H + 60)
    rw [show (H + 60) + signExtend21 (16 : BitVec 21) = H + 76 from by
      rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]; bv_omega]
      at h15
    have h15' := cpsTripleWithin_extend_code hved_mono
      (cpsTripleWithin_extend_code (cr' := hvedCode)
        (CodeReq.ofProg_mem_at H (H + 60) hvedProg 15 (.JAL .x0 (16 : BitVec 21))
          (by bv_omega) (by rw [hved_length]; decide) rfl
          (by rw [hved_length]; decide)) h15)
    have h15F : cpsTripleWithin 1 (H + 60) (H + 76) fullCode
        ((.x10 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) **
          (Off ↦ₘ offset) ** (Len ↦ₘ len) ** (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) **
          (spH ↦ₘ raIn) ** frameG newSp listBase saved bytes)
        ((.x10 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ Len) **
          (Off ↦ₘ offset) ** (Len ↦ₘ len) ** (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) **
          (spH ↦ₘ raIn) ** frameG newSp listBase saved bytes) :=
      cpsTripleWithin_weaken (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR _ (by unfold frameG; pcf) h15')
    have hepi := hvedEpi sp0 spH raIn
      ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ Len) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
        (Off ↦ₘ offset) ** (Len ↦ₘ len) ** frameG newSp listBase saved bytes)
      (by unfold frameG; pcf) hspH hret
    have h1415 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      h14F h15F
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      xperm_hyp hp) h1415 hepi
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hall
    refine Or.inl ⟨offset, len, ?_⟩
    unfold commonRet
    refine (sepConj_pure_left h).2 ⟨⟨hResult, hnult⟩, ?_⟩
    have hq2 := weaken_x567 Len len (32 : Word)
      ((.x10 ↦ᵣ (0 : Word)) ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
        (.x1 ↦ᵣ raIn) ** (spH ↦ₘ raIn) ** (.x2 ↦ᵣ sp0) **
        frameG newSp listBase saved bytes) h (by xperm_hyp hq)
    xperm_hyp hq2
  -- Merge the two arms.
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsBranchWithin_merge_same_cr hbranch hrej hsucc)


set_option maxRecDepth 8000 in
/-- `hvedDispatch` with `x5/x6` presented as owned (their pre-values are
    irrelevant — they are overwritten by the `la`/`ld`). -/
theorem hvedDispatchOwned
    (sp0 spH newSp raIn listBase oldOffset oldLen offset len : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hResult : Result bytes listBase listLen 12 oldOffset oldLen 0 offset len) :
    cpsTripleWithin 10 (H + 36) raIn fullCode
      ((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (Off ↦ₘ offset) ** (Len ↦ₘ len) ** frameG newSp listBase saved bytes)
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin 10 (H + 36) raIn fullCode
      (((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
          regOwn .x7 ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          frameG newSp listBase saved bytes ** regOwn .x5) ** regOwn .x6)
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) from ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v6 => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (show cpsTripleWithin 10 (H + 36) raIn fullCode
      (((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (spH ↦ₘ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
          regOwn .x7 ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          frameG newSp listBase saved bytes ** (.x6 ↦ᵣ v6)) ** regOwn .x5)
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) from ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v5 => ?_)
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hvedDispatch sp0 spH newSp raIn listBase oldOffset oldLen offset len v5 v6 saved
      bytes listLen hspH hret hResult)


/-! ## Status dispatch + full rest (instruction 8 onward) -/

set_option maxRecDepth 8000 in
/-- From K20's `returnResult` (at the `bne` at `H+32`) to the wrapper's post.
    `bne x10, x0` splits on the callee status; `Result` inversion pins the
    `a0 = 2` parse-failure arm and feeds the accept/reject dispatch. -/
theorem hvedRest
    (sp0 spH newSp raIn listBase oldOffset oldLen : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hraSaved : saved.ra = H + 32) :
    cpsTripleWithin 11 (H + 32) raIn fullCode
      (returnResult spH newSp listBase (12 : Word) Off Len oldOffset oldLen saved
        bytes listLen 12 ** (spH ↦ₘ raIn))
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
  -- Strip `returnResult`'s existentials.
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
    (cpsTripleWithin_exists_assertion (fun status =>
      cpsTripleWithin_exists_assertion (fun offset =>
        cpsTripleWithin_exists_assertion (fun len =>
          cpsTripleWithin_exists_assertion (fun v11 =>
            cpsTripleWithin_exists_assertion (fun v12 =>
              (?core : cpsTripleWithin 11 (H + 32) raIn fullCode
                (retBody spH newSp listBase oldOffset oldLen saved bytes listLen
                  status offset len v11 v12 ** (spH ↦ₘ raIn))
                (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes
                  listLen))))))))
  · -- returnResult ** slot ⟹ ∃ …, retBody ** slot
    obtain ⟨h1, h2, hd, hu, hrr, hslot⟩ := hp
    obtain ⟨status, offset, len, v11, v12, hbody⟩ := hrr
    exact ⟨status, offset, len, v11, v12, h1, h2, hd, hu, hbody, hslot⟩
  -- Core, for fixed witnesses: extract `Result`, expand the frame.
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
    (cpsTripleWithin_pure_pre
      (P := Result bytes listBase listLen 12 oldOffset oldLen status offset len)
      (H := (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) **
        (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
        (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** savedFrame newSp saved **
        (.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (Off ↦ₘ offset) ** (Len ↦ₘ len) ** (spH ↦ₘ raIn))
      (fun hResult => ?_))
  · -- retBody ** slot ⟹ ⌜Result⌝ ** frame  (weaken x11/x12 to owned, x1 = H+32)
    unfold retBody at hp
    rw [regsAt_listNthFrame, hraSaved] at hp
    have hp2 := weaken_x1112 v11 v12
      (⌜Result bytes listBase listLen 12 oldOffset oldLen status offset len⌝ **
        (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) **
        (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
        (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** savedFrame newSp saved **
        (.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
        (spH ↦ₘ raIn)) h (by xperm_hyp hp)
    xperm_hyp hp2
  -- The `bne x10, x0` branch.
  have hbne := bne_spec_gen_within .x10 .x0 (40 : BitVec 13) status (0 : Word) (H + 32)
  rw [show (H + 32) + signExtend13 (40 : BitVec 13) = H + 72 from by
    rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega]
    at hbne
  have hbneF := cpsBranchWithin_frameR
    ((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) **
      (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
      (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** savedFrame newSp saved **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
      (spH ↦ₘ raIn)) (by pcf)
    (cpsBranchWithin_extend_code hved_mono
      (cpsBranchWithin_extend_code (cr' := hvedCode)
        (CodeReq.ofProg_mem_at H (H + 32) hvedProg 8 (.BNE .x10 .x0 (40 : BitVec 13))
          (by bv_omega) (by rw [hved_length]; decide) rfl
          (by rw [hved_length]; decide)) hbne))
  -- Fail continuation (H+72 → raIn): status ≠ 0 ⟹ `Failure`, a0 = 2.
  have h_t : cpsTripleWithin 10 (H + 72) raIn fullCode
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status ≠ (0 : Word)⌝) **
        ((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) **
          (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
          (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** savedFrame newSp saved **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (spH ↦ₘ raIn)))
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre (P := status ≠ (0 : Word))
        (H := (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) **
          (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
          (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** savedFrame newSp saved **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (spH ↦ₘ raIn)) (fun hne => ?_))
    cases hResult with
    | ok _ _ hSucc => exact absurd rfl hne
    | fail hFail =>
      -- status = 1, offset = oldOffset, len = oldLen.
      -- [18] LI x10 2
      have h18 := li_spec_gen_within .x10 (1 : Word) (2 : Word) (H + 72) (by decide)
      have h18F := cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) **
          (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
          (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
          savedFrame newSp saved ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes ** (Off ↦ₘ oldOffset) ** (Len ↦ₘ oldLen) **
          (spH ↦ₘ raIn)) (by pcf)
        (cpsTripleWithin_extend_code hved_mono
          (cpsTripleWithin_extend_code (cr' := hvedCode)
            (CodeReq.ofProg_mem_at H (H + 72) hvedProg 18 (.LI .x10 (2 : Word))
              (by bv_omega) (by rw [hved_length]; decide) rfl
              (by rw [hved_length]; decide)) h18))
      have hepi := hvedEpi sp0 spH raIn
        ((.x10 ↦ᵣ (2 : Word)) ** (Off ↦ₘ oldOffset) ** (Len ↦ₘ oldLen) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** frameG newSp listBase saved bytes)
        (by unfold frameG; pcf) hspH hret
      have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
        unfold frameG; xperm_hyp hp) h18F hepi
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
        (cpsTripleWithin_mono_nSteps (show 1 + 3 ≤ 10 by omega) hall)
      refine Or.inr (Or.inr ?_)
      unfold hvedFail commonRet
      exact (sepConj_pure_left h).2 ⟨Result.fail hFail, by xperm_hyp hq⟩
  -- Non-fail continuation (H+36 → raIn): status = 0 ⟹ accept/reject dispatch.
  have h_f : cpsTripleWithin 10 (H + 36) raIn fullCode
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status = (0 : Word)⌝) **
        ((.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) **
          (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
          (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** savedFrame newSp saved **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (spH ↦ₘ raIn)))
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre (P := status = (0 : Word))
        (H := (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (H + 32)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ saved.s0) **
          (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
          (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** savedFrame newSp saved **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion listBase bytes ** (Off ↦ₘ offset) ** (Len ↦ₘ len) **
          (spH ↦ₘ raIn)) (fun heq => ?_))
    subst heq
    refine cpsTripleWithin_weaken (fun h hp => by unfold frameG; xperm_hyp hp)
      (fun _ hq => hq)
      (hvedDispatchOwned sp0 spH newSp raIn listBase oldOffset oldLen offset len
        saved bytes listLen hspH hret hResult)
  -- Merge the two arms.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsBranchWithin_merge_same_cr hbneF h_t h_f)


/-! ## Whole-program caller contract -/

set_option maxRecDepth 8000 in
/-- **`header_validate_extra_data_length` caller contract.**  The 22-instruction
    accessor = prologue+setup ;; `rlpListNthItem_spec_within` (field index 12) ;;
    status dispatch ;; length compare ;; epilogue.  Its three-way post pins the
    ABI status `a0` to the ACTUAL field-12 content length via K20's `Result`:
    `a0 = 0` iff field 12 exists with content length ≤ 32; `a0 = 1` iff it exists
    with length > 32 (`32 <ᵤ len`); `a0 = 2` iff a genuine RLP `Failure`. -/
theorem header_validate_extra_data_length_spec_within
    (sp0 raIn oldRaSlot spH newSp listBase listLenW old12 old13 old14
      oldOffset oldLen : Word) (saved : Saved) (bytes : List (BitVec 8))
    (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hnewSp : newSp = spH + signExtend12 (-64 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hraSaved : saved.ra = H + 32) :
    cpsTripleWithin (7 + 1 + nCall + 11) H raIn fullCode
      (hvedPre sp0 raIn oldRaSlot spH newSp listBase listLenW old12 old13 old14
        oldOffset oldLen saved bytes)
      (hvedPost sp0 spH newSp raIn listBase oldOffset oldLen saved bytes listLen) := by
  have hcall := hvedCall sp0 raIn oldRaSlot spH newSp listBase listLenW old12
    old13 old14 oldOffset oldLen saved bytes listLen hspH hnewSp hlistLenW hsalign
    hslack hover hvalid hraSaved
  have hrest := hvedRest sp0 spH newSp raIn listBase oldOffset oldLen saved bytes
    listLen hspH hret hraSaved
  exact cpsTripleWithin_seq_same_cr hcall hrest


end EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec
