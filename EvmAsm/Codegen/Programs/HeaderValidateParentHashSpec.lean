/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashSpec

  Whole-routine machine contract for `header_validate_parent_hash` (#12346
  residual callee triple).  Pre/post match the pinned premise shape in
  `ValidateHeaderParentHashCorrespondence` (PR #12362) exactly:

    hvphEntryRest / hvphCalleePost
      — x1 link, x2 at caller sp0, 32-byte frameSlotsOwn/Saved,
        a0..a3 = this/parent RLP, scratch ownership, both byte regions.

  Cut from origin/main @ db997caeb.  Program length 43.

  Inner calls (objdump-verified on stateless_guest.elf):
    +36 → headers_parent_hash (NO machine triple — named premise)
    +68 → zkvm_keccak256 one-shot (proven `zkvm_keccak256_spec_within`)

  Status (a0): 0 match, 1 RLP extract fail, 2 hash mismatch.
  Conjunct 11 depth: adapter → HVPH → headers_parent_hash → keccak.
-/

import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.HeaderValidateParentHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)

/-! ## Bases, code, and the pinned ABI shape (#12362) -/

abbrev H : Word := (GuestAddrs.header_validate_parent_hash : Word)
abbrev K : Word := (GuestAddrs.zkvm_keccak256 : Word)
abbrev P : Word := (GuestAddrs.headers_parent_hash : Word)
abbrev Claimed : Word := (GuestAddrs.hvph_claimed : Word)
abbrev Computed : Word := (GuestAddrs.hvph_computed : Word)

abbrev hvphProg : Program := headerValidateParentHash_prog
abbrev keccakProg : Program := zkvmKeccak256_prog
abbrev headersProg : Program := headersParentHash_prog

theorem hvph_length : hvphProg.length = 43 := by decide
theorem headers_length : headersProg.length = 34 := by decide

def hvphCode : CodeReq := CodeReq.ofProg H hvphProg
def keccakCode : CodeReq := CodeReq.ofProg K keccakProg
def headersCode : CodeReq := CodeReq.ofProg P headersProg

/-- HVPH plus both callees. -/
def fullCode : CodeReq :=
  hvphCode.union (headersCode.union keccakCode)

/-- 32-byte ABI frame — identical to the #12362 adapter pin. -/
def hvphFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]

def hvphSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24)]

def hvphFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

/-- Entry assertion — identical to adapter `hvphEntryRest`. -/
def hvphPre
    (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn hvphFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
  (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes

/-- Exit assertion — identical to adapter `hvphCalleePost`. -/
def hvphPost
    (sp0 thisPtr parentPtr ret status : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved hvphFrame (sp0 + signExtend12 (-32 : BitVec 12))
    (hvphFrameVals ret vals) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ status) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes

theorem hvphPre_pcFree
    (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) :
    (hvphPre sp0 thisPtr thisLen parentPtr parentLen vals
      thisBytes parentBytes).pcFree := by
  unfold hvphPre hvphFrame hvphSavedFrame
  pcf

/-- Keccak jal at H+68 is the one-shot entry (not segments). -/
theorem hvph_keccak_jal_oneshot :
    (∀ a i, CodeReq.singleton (H + 68)
        (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.header_validate_parent_hash + 68))) a = some i →
      hvphCode a = some i) ∧
    (GuestAddrs.zkvm_keccak256 : Nat) ≠ GuestAddrs.zkvm_keccak256_segments := by
  refine ⟨?_, by decide⟩
  exact CodeReq.ofProg_mem_at H (H + 68) hvphProg 17 _
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)

/-! ## Code membership helpers -/

theorem hvph_mono : ∀ a i, hvphCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

theorem hvph_headers_disjoint : hvphCode.Disjoint headersCode := by
  unfold hvphCode headersCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hvph_length]; decide
  · rw [headers_length]; decide
  · rw [hvph_length, headers_length]; decide

theorem hvph_keccak_disjoint : hvphCode.Disjoint keccakCode := by
  unfold hvphCode keccakCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hvph_length]; decide
  · decide  -- zkvmKeccak256_prog.length
  · decide

theorem headers_keccak_disjoint : headersCode.Disjoint keccakCode := by
  unfold headersCode keccakCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [headers_length]; decide
  · decide
  · rw [headers_length]; decide

theorem headers_mono : ∀ a i, headersCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right hvph_headers_disjoint
    (fun a i h => CodeReq.union_mono_left a i h) a i hi

theorem keccak_mono : ∀ a i, keccakCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right hvph_keccak_disjoint
    (fun a i h => CodeReq.mono_union_right headers_keccak_disjoint
      (fun _ _ h' => h') a i h) a i hi

/-! ## Callees (objdump-confirmed)

    `header_validate_parent_hash` is **not** self-contained:

    | Offset | Target | Machine status |
    |--------|--------|----------------|
    | **+36** | `headers_parent_hash` | **no** Progress row / no triple (emit drift only) |
    | **+68** | `zkvm_keccak256` (one-shot) | **proven** `zkvm_keccak256_spec_within` |

    Conjunct 11 chain: validate_header adapter → HVPH → headers_parent_hash → keccak.
    The HVPH top triple therefore names an explicit **`headers_parent_hash`
    premise**; keccak is discharged by the proven leaf (not a premise).
-/

/-- Objdump pin: +36 jal targets `headers_parent_hash`. -/
theorem hvph_headers_jal_mem :
    ∀ a i, CodeReq.singleton (H + 36)
        (.JAL .x1 (jalOff GuestAddrs.headers_parent_hash
          (GuestAddrs.header_validate_parent_hash + 36))) a = some i →
      hvphCode a = some i :=
  CodeReq.ofProg_mem_at H (H + 36) hvphProg 9 _
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)

/-! ## Top theorem (shape pin)

    Landed: prologue ;; headers premise ;; extract-fail (`19+nH`); keccak setup+call
    (`5+nK`); compare rounds + match/mismatch exits; from-`H+72` match (`24`) /
    mismatch0 (`14`) with `regOwn` scratch; keccak→compare-match (`29+nK`);
    from-`H+40` match (`30+nK`) / mismatch0 (`20+nK`);
    prologue→match (`40+nH+nK`) / mismatch0 (`30+nH+nK`);
    adapter-shaped: match / mismatch0 / extract-fail (hvphPre/Post + BSS).
-/

/-- **Shape-locked top contract** for `header_validate_parent_hash`.

    Matches #12362 adapter `hvphPre`/`hvphPost` exactly.  The statement takes a
    named `headers_parent_hash` premise (`h_headers`); the keccak call at +68 is
    *not* a premise — proofs must invoke `zkvm_keccak256_spec_within`.

    `claimedBytes` / ambient BSS ownership will be threaded through the body
    composition (adapter shape itself does not name them). -/
def header_validate_parent_hash_spec_within_type
    (n : Nat) (sp0 thisPtr thisLen parentPtr parentLen ret status : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8))
    (h_headers : Prop) : Prop :=
  h_headers →
  cpsTripleWithin n H ret fullCode
    ((.x1 ↦ᵣ ret) **
      hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes)
    (hvphPost sp0 thisPtr parentPtr ret status vals thisBytes parentBytes)

-- Length / pin KATs used by review and by the adapter's oneshot check.
example : hvphProg.length = 43 := hvph_length
example : (GuestAddrs.zkvm_keccak256 : Nat) ≠ GuestAddrs.zkvm_keccak256_segments :=
  hvph_keccak_jal_oneshot.2

/-! ## Prologue (instr 0–4): allocate + storeSeq -/

theorem regsAt_hvphFrame_of_vals (ret : Word) (vals : Reg → Word) :
    regsAt hvphFrame (hvphFrameVals ret vals) =
      ((.x1 ↦ᵣ ret) ** regsAt hvphSavedFrame vals) := by
  simp [hvphFrame, hvphSavedFrame, hvphFrameVals, regsAt, sepConj_emp_right']

theorem regsAt_hvphSavedFrame (vals : Reg → Word) :
    regsAt hvphSavedFrame vals =
      ((.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18)) := by
  simp [hvphSavedFrame, regsAt, sepConj_emp_right']

set_option maxRecDepth 8000 in
/-- ADDI sp,-32 ;; SD ra/s0/s1/s2 (instr 0–4). Leaves PC at `H+20`. -/
theorem hvphFrameSave (sp0 spC ret : Word) (vals : Reg → Word)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin 5 H (H + 20) hvphCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC)
      ((.x2 ↦ᵣ spC) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) H (by decide)
  rw [← hspC] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H H hvphProg 0
      (.ADDI .x2 .x2 (-32 : BitVec 12)) rfl
      (by rw [hvph_length]; decide) rfl
      (by rw [hvph_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt hvphFrame (hvphFrameVals ret vals) ** frameSlotsOwn hvphFrame spC)
    (by pcf) ha
  have hs0 := storeSeq_spec hvphFrame spC (hvphFrameVals ret vals) (H + 4) (by decide)
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (H + 4) (storeProg hvphFrame) a = some i →
        hvphCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub H (H + 4) hvphProg (storeProg hvphFrame) 1
      (by bv_omega) rfl
      (by rw [hvph_length]; simp [hvphFrame, storeProg])
      (by rw [hvph_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show H + 4 + BitVec.ofNat 64 (4 * hvphFrame.length) = H + 20 from by
    simp [hvphFrame]; bv_omega] at hs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hs

/-! ## Setup (instr 5–8): park parent in s0/s1; `la a2, hvph_claimed` -/

set_option maxRecDepth 8000 in
/-- `mv s0,a2` ;; `mv s1,a3` ;; `la a2, claimed` (instr 5–8). Leaves PC at
    `H+36` — the `jal headers_parent_hash` site. -/
theorem hvphSetup
    (spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word) :
    cpsTripleWithin 4 (H + 20) (H + 36) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ Claimed) ** (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) := by
  have h0 := mv_spec_gen_within .x8 .x12 parentPtr (vals .x8) (H + 20) (by decide)
  have h1 := mv_spec_gen_within .x9 .x13 parentLen (vals .x9) (H + 24) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 20) hvphProg 5 (.MV .x8 .x12)
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) h0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 24) hvphProg 6 (.MV .x9 .x13)
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) h1
  have hau := CodeReq.ofProg_mem_at H (H + 28) hvphProg 7
    (.AUIPC .x12 (EvmAsm.Codegen.laHi GuestAddrs.hvph_claimed
      (GuestAddrs.header_validate_parent_hash + 28)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had := CodeReq.ofProg_mem_at H (H + 32) hvphProg 8
    (.ADDI .x12 .x12 (EvmAsm.Codegen.laLo GuestAddrs.hvph_claimed
      (GuestAddrs.header_validate_parent_hash + 28)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla := EvmAsm.Rv64.la_materialize_within .x12 parentPtr (H + 28) Claimed (by decide)
    (by unfold H Claimed; decide) hau had
  have e0F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ret) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
      (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x13 ↦ᵣ parentLen) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) e0
  have e1F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ parentPtr) ** (.x18 ↦ᵣ vals .x18) **
      (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ parentPtr) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) e1
  have hlaF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
      (.x13 ↦ᵣ parentLen) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) hla
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hlaF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Frame save + setup through `H+36` (ready for `jal headers_parent_hash`). -/
theorem hvphPrologue
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin 9 H (H + 36) hvphCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ Claimed) ** (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) := by
  have hsave := hvphFrameSave sp0 spC ret vals hspC
  have hsaveF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
      (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen)) (by pcf) hsave
  have hsetup := hvphSetup spC ret thisPtr thisLen parentPtr parentLen vals
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_hvphFrame_of_vals, regsAt_hvphSavedFrame] at hp
    xperm_hyp hp) hsaveF hsetup
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h01

/-! ## `headers_parent_hash` premise shape (no machine triple yet)

    Call at `H+36` returns to `H+40`.  ABI: `a0/a1` = this RLP, `a2` = Claimed
    out-buffer.  `a0=0` success (32 bytes written); nonzero → extract fail. -/

/-- Out-buffer ownership for the claimed parent-hash scratch (32 bytes). -/
abbrev claimedOwn (claimedBytes : List (BitVec 8)) : Assertion :=
  bytesRegion Claimed claimedBytes

/-- Call-site premise for `headers_parent_hash` under HVPH's frame.

    Pre: a0/a1/a2 set, Claimed buffer owned, this-bytes ambient, frame/saved
    regs/`sp` framed in `F`.  Post: a0 = `statusHdr`; Claimed holds
    `claimedOut` (caller picks; equal to `claimedBytes` on the fail path);
    a1/a2 returned as `regOwn` (havoc — callee clobbers entry values;
    ownership is required for the caller's re-bind at `H+52`). -/
def headersCallPremise
    (nH : Nat) (retHdr statusHdr thisPtr thisLen : Word)
    (thisBytes claimedBytes claimedOut : List (BitVec 8))
    (F : Assertion) : Prop :=
  cpsTripleWithin nH P retHdr headersCode
    ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
      (.x12 ↦ᵣ Claimed) ** claimedOwn claimedBytes **
      bytesRegion thisPtr thisBytes ** F)
    ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ statusHdr) **
      claimedOwn claimedOut **
      bytesRegion thisPtr thisBytes **
      regOwn .x11 ** regOwn .x12 ** F)

/-! ## Epilogue (instr 37–42 at `H+148`)

    `loadSeq` ra/s0/s1/s2; ADDI sp,+32; JALR.  Carries `a0 = status` and ambient
    `G` (byte regions / scratch).  Saved slot values (`vals`) are restored into
    regs; `vals'` are the clobbered pre-restore register values. -/

theorem hvphFrame_hne : ∀ p ∈ hvphFrame, p.1 ≠ .x0 := by decide

theorem regsAt_hvphFrame (vals : Reg → Word) :
    regsAt hvphFrame vals =
      ((.x1 ↦ᵣ vals .x1) ** (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
        (.x18 ↦ᵣ vals .x18)) := by
  simp [hvphFrame, regsAt, sepConj_emp_right']

theorem frameSlotsSaved_hvphFrame (spC : Word) (vals : Reg → Word) :
    frameSlotsSaved hvphFrame spC vals =
      (((spC + signExtend12 (0 : BitVec 12)) ↦ₘ vals .x1) **
        ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ vals .x8) **
        ((spC + signExtend12 (16 : BitVec 12)) ↦ₘ vals .x9) **
        ((spC + signExtend12 (24 : BitVec 12)) ↦ₘ vals .x18)) := by
  simp [hvphFrame, frameSlotsSaved, sepConj_emp_right']

set_option maxRecDepth 8000 in
theorem hvphEpi
    (sp0 spC status : Word) (vals vals' : Reg → Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 6 (H + 148) (vals .x1) hvphCode
      ((.x10 ↦ᵣ status) ** (.x2 ↦ᵣ spC) **
        regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals ** G) := by
  have hs0 := loadSeq_spec hvphFrame spC vals vals' (H + 148)
    (by decide) hvphFrame_hne
  have h_loadMono : ∀ a i,
      CodeReq.ofProg (H + 148) (loadProg hvphFrame) a = some i →
        hvphCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub H (H + 148) hvphProg (loadProg hvphFrame) 37
      (by bv_omega) (by rfl)
      (by rw [hvph_length]; simp [hvphFrame, loadProg])
      (by rw [hvph_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  rw [show H + 148 + BitVec.ofNat 64 (4 * hvphFrame.length) = H + 164 from by
    simp [hvphFrame]; bv_omega] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (32 : BitVec 12) (H + 164) (by decide)
  have hsp : spC + signExtend12 (32 : BitVec 12) = sp0 := by
    rw [hspC]
    rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 164) hvphProg 41
      (.ADDI .x2 .x2 (32 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl
      (by rw [hvph_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt hvphFrame vals ** frameSlotsSaved hvphFrame spC vals)
    (by pcf) ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hs haF
  have hpc : (H + 164 : Word) + 4 = H + 168 := by bv_omega
  rw [hpc] at hload_addi
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' (H + 168) (vals .x1)
  rw [hret] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 168) hvphProg 42
      (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl
      (by rw [hvph_length]; decide)) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
      frameSlotsSaved hvphFrame spC vals)
    (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_hvphFrame] at hp
    xperm_hyp hp) hload_addi hjalrF
  have hn : hvphFrame.length + 1 + 1 = 6 := by simp [hvphFrame]
  rw [hn] at hall
  have hcore : cpsTripleWithin 6 (H + 148) (vals .x1) hvphCode
      ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals)
      ((.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hall
  have hframed := cpsTripleWithin_frameR ((.x10 ↦ᵣ status) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hcore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hframed

/-! ## Status-1 exit — `li a0, 1` @ `H+44` → `j` → epilogue

    Taken when `headers_parent_hash` returns nonzero (extract failure). -/

set_option maxRecDepth 8000 in
theorem hvphStatus1Exit
    (sp0 spC o10 : Word) (vals vals' : Reg → Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 8 (H + 44) (vals .x1) hvphCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) **
        regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (1 : Word) (H + 44) (by decide)
  have s1 := jal_x0_spec_gen_within (100 : BitVec 21) (H + 48)
  rw [show (H + 48) + signExtend21 (100 : BitVec 21) = H + 148 from by
    rw [show signExtend21 (100 : BitVec 21) = (100 : Word) from by decide]
    bv_omega] at s1
  have s0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 44) hvphProg 11 (.LI .x10 (1 : Word))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s0
  have s1C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 48) hvphProg 12 (.JAL .x0 (100 : BitVec 21))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s1
  have hblock : cpsTripleWithin 2 (H + 44) (H + 148) hvphCode
      ((.x10 ↦ᵣ o10)) ((.x10 ↦ᵣ (1 : Word))) := by
    runBlock s0C s1C
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))
        <;> pcf) hblock
  have hepi := hvphEpi sp0 spC (1 : Word) vals vals' G hG hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepi
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Extract-fail branch (instr 10): `beq a0,x0` fall-through when nonzero -/

set_option maxRecDepth 8000 in
/-- `beq a0, x0` not-taken when `statusHdr ≠ 0` (fall through to `H+44`). -/
theorem hvphBeqExtractFail (statusHdr : Word) (h_nz : statusHdr ≠ (0 : Word)) :
    cpsTripleWithin 1 (H + 40) (H + 44) hvphCode
      ((.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x10 .x0 (12 : BitVec 13) statusHdr (0 : Word) (H + 40)
  rw [show (H + 40 : Word) + 4 = H + 44 from by bv_omega,
    show (H + 40) + signExtend13 (12 : BitVec 13) = H + 52 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 40) hvphProg 10 (.BEQ .x10 .x0 (12 : BitVec 13))
        (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact h_nz ((sepConj_pure_right _).1 hBP).2)

set_option maxRecDepth 8000 in
/-- `beq a0, x0` taken when `a0 = 0` (branch to success setup at `H+52`). -/
theorem hvphBeqExtractOk :
    cpsTripleWithin 1 (H + 40) (H + 52) hvphCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x10 .x0 (12 : BitVec 13) (0 : Word) (0 : Word) (H + 40)
  rw [show (H + 40 : Word) + 4 = H + 44 from by bv_omega,
    show (H + 40) + signExtend13 (12 : BitVec 13) = H + 52 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 40) hvphProg 10 (.BEQ .x10 .x0 (12 : BitVec 13))
        (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- Ambient framed across the `headers_parent_hash` call (HVPH frame + parent). -/
def headersCallFrame
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
  (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
  frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
  bytesRegion parentPtr parentBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))

theorem headersCallFrame_pcFree
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) :
    (headersCallFrame spC ret parentPtr parentLen vals parentBytes).pcFree := by
  unfold headersCallFrame hvphFrame; pcf

/-- Current regs at post-headers (link = `H+40`, parent still in s0/s1). -/
def hvphPostHeadersVals (parentPtr parentLen : Word) (vals : Reg → Word) : Reg → Word :=
  fun r =>
    if r = .x1 then (H + 40 : Word)
    else if r = .x8 then parentPtr
    else if r = .x9 then parentLen
    else vals r

theorem hvph_headers_jal_disj :
    (CodeReq.singleton (H + 36)
      (.JAL .x1 (jalOff GuestAddrs.headers_parent_hash
        (GuestAddrs.header_validate_parent_hash + 36)))).Disjoint headersCode :=
  CodeReq.Disjoint.singleton_ofProg (by decide)

/-- Prest for `WP.cpsCallWithin` at the headers jal (everything but link). -/
def headersCallPrest
    (spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ Claimed) **
  claimedOwn claimedBytes ** bytesRegion thisPtr thisBytes **
  headersCallFrame spC ret parentPtr parentLen vals parentBytes

theorem headersCallPrest_pcFree
    (spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) :
    (headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals
      thisBytes parentBytes claimedBytes).pcFree := by
  unfold headersCallPrest headersCallFrame claimedOwn hvphFrame; pcf

set_option maxRecDepth 8000 in
/-- `jal headers_parent_hash` at `H+36` under `headersCallPremise` (returns `H+40`). -/
theorem hvphHeadersCall
    (nH : Nat) (spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (h_headers : headersCallPremise nH (H + 40) statusHdr thisPtr thisLen
      thisBytes claimedBytes claimedOut
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (1 + nH) (H + 36) (H + 40) fullCode
      ((.x1 ↦ᵣ ret) **
        headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals
          thisBytes parentBytes claimedBytes)
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
  have htarget : (H + 36) + signExtend21 (jalOff GuestAddrs.headers_parent_hash
      (GuestAddrs.header_validate_parent_hash + 36)) = P := by
    change BitVec.ofNat 64 GuestAddrs.header_validate_parent_hash + BitVec.ofNat 64 36 + _ =
      BitVec.ofNat 64 GuestAddrs.headers_parent_hash
    exact jalOff_correct_add GuestAddrs.headers_parent_hash
      GuestAddrs.header_validate_parent_hash 36
      (by decide) (by decide) (by decide) (by decide)
  have hret40 : ((H + 36 : Word) + 4) &&& ~~~(1 : Word) = (H + 36) + 4 := by decide
  have hPrest := headersCallPrest_pcFree spC ret thisPtr thisLen parentPtr parentLen vals
    thisBytes parentBytes claimedBytes
  have hcallee : cpsTripleWithin nH P ((H + 36 + 4) &&& ~~~(1 : Word)) headersCode
      ((.x1 ↦ᵣ (H + 36 + 4)) **
        headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals
          thisBytes parentBytes claimedBytes)
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
    rw [hret40, show (H + 36 + 4 : Word) = H + 40 from by bv_omega]
    unfold headersCallPremise at h_headers
    refine cpsTripleWithin_weaken (fun _ hp => by
      unfold headersCallPrest at hp
      xperm_hyp hp) (fun _ hq => hq) h_headers
  have hcall0 := WP.cpsCallWithin
    (nSteps := nH) (callerPC := H + 36) (calleeEntry := P) (vOld := ret)
    (calleeCode := headersCode)
    (Prest := headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals
      thisBytes parentBytes claimedBytes)
    (Q := (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
      claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
      regOwn .x11 ** regOwn .x12 **
      headersCallFrame spC ret parentPtr parentLen vals parentBytes)
    (jalOff GuestAddrs.headers_parent_hash
      (GuestAddrs.header_validate_parent_hash + 36))
    htarget hret40 hPrest hvph_headers_jal_disj hcallee
  have hcallCode : ∀ a i,
      ((CodeReq.singleton (H + 36)
        (.JAL .x1 (jalOff GuestAddrs.headers_parent_hash
          (GuestAddrs.header_validate_parent_hash + 36)))).union headersCode) a = some i →
      fullCode a = some i :=
    CodeReq.union_split_mono
      (fun a i h => hvph_mono a i (hvph_headers_jal_mem a i h))
      headers_mono
  exact cpsTripleWithin_extend_code hcallCode hcall0

set_option maxRecDepth 8000 in
/-- Prologue through headers return (`H → H+40`) under `headersCallPremise`. -/
theorem hvphPrologueHeaders
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (h_headers : headersCallPremise nH (H + 40) statusHdr thisPtr thisLen
      thisBytes claimedBytes claimedOut
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (9 + (1 + nH)) H (H + 40) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
  have hpro0 := hvphPrologue sp0 spC ret thisPtr thisLen parentPtr parentLen vals hspC
  have hpro := cpsTripleWithin_extend_code hvph_mono hpro0
  have hproF := cpsTripleWithin_frameR
    (claimedOwn claimedBytes ** bytesRegion thisPtr thisBytes **
      bytesRegion parentPtr parentBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hpro
  have hcall0 := hvphHeadersCall nH spC ret thisPtr thisLen parentPtr parentLen statusHdr
    vals thisBytes parentBytes claimedBytes claimedOut h_headers
  have hcall : cpsTripleWithin (1 + nH) (H + 36) (H + 40) fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ Claimed) ** (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrame spC ret parentPtr parentLen vals parentBytes) :=
    cpsTripleWithin_weaken (fun _ hp => by
      unfold headersCallPrest headersCallFrame claimedOwn
      xperm_hyp hp) (fun _ hq => hq) hcall0
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hproF hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h01

/-- `headersCallFrame` without the `x0` atom (for framing around `beq`). -/
def headersCallFrameCore
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
  (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
  frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
  bytesRegion parentPtr parentBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31

set_option maxRecDepth 8000 in
/-- Post-headers `beq` fall-through, framed by call-frame core (no double-`x0`). -/
theorem hvphBeqExtractFailFramed
    (spC ret parentPtr parentLen statusHdr : Word) (vals : Reg → Word)
    (thisPtr : Word) (thisBytes claimedOut parentBytes : List (BitVec 8))
    (h_nz : statusHdr ≠ (0 : Word)) :
    cpsTripleWithin 1 (H + 40) (H + 44) fullCode
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrameCore spC ret parentPtr parentLen vals parentBytes)
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrameCore spC ret parentPtr parentLen vals parentBytes) := by
  have hbeq0 := hvphBeqExtractFail statusHdr h_nz
  have hbeq := cpsTripleWithin_extend_code hvph_mono hbeq0
  have hbeqF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
      regOwn .x11 ** regOwn .x12 **
      headersCallFrameCore spC ret parentPtr parentLen vals parentBytes)
    (by unfold headersCallFrameCore claimedOwn; pcf) hbeq
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hbeqF

/-- Ambient for status-1 exit on the extract-fail path. -/
def hvphFailG
    (thisPtr : Word) (thisBytes claimedOut : List (BitVec 8)) (parentLen : Word) :
    Assertion :=
  claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  regOwn .x11 ** regOwn .x12 **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x13 ↦ᵣ parentLen)

theorem hvphFailG_pcFree
    (thisPtr : Word) (thisBytes claimedOut : List (BitVec 8)) (parentLen : Word) :
    (hvphFailG thisPtr thisBytes claimedOut parentLen).pcFree := by
  unfold hvphFailG claimedOwn; pcf

set_option maxRecDepth 8000 in
/-- Post-headers `beq` taken (status 0), framed by call-frame core. -/
theorem hvphBeqExtractOkFramed
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (thisPtr : Word) (thisBytes claimedOut parentBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree) :
    cpsTripleWithin 1 (H + 40) (H + 52) fullCode
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        headersCallFrameCore spC ret parentPtr parentLen vals parentBytes ** G)
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        headersCallFrameCore spC ret parentPtr parentLen vals parentBytes ** G) := by
  have hbeq0 := hvphBeqExtractOk
  have hbeq := cpsTripleWithin_extend_code hvph_mono hbeq0
  have hbeqF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
      headersCallFrameCore spC ret parentPtr parentLen vals parentBytes ** G)
    (by unfold headersCallFrameCore claimedOwn; refine pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hbeq
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hbeqF

set_option maxRecDepth 8000 in
/-- Extract-fail residual: prologue+headers ;; beq fall ;; status-1. Cost `19+nH`. -/
theorem hvphExtractFail_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_nz : statusHdr ≠ (0 : Word))
    (h_headers : headersCallPremise nH (H + 40) statusHdr thisPtr thisLen
      thisBytes claimedBytes claimedOut
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (19 + nH) H ret fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        hvphFailG thisPtr thisBytes claimedOut parentLen) := by
  have hph := hvphPrologueHeaders nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    statusHdr vals thisBytes parentBytes claimedBytes claimedOut hspC h_headers
  have hphW : cpsTripleWithin (9 + (1 + nH)) H (H + 40) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrameCore spC ret parentPtr parentLen vals parentBytes) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      unfold headersCallFrame at hq
      unfold headersCallFrameCore
      xperm_hyp hq) hph
  have hbeq := hvphBeqExtractFailFramed spC ret parentPtr parentLen statusHdr vals
    thisPtr thisBytes claimedOut parentBytes h_nz
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hphW hbeq
  have hvals' :
      regsAt hvphFrame (hvphPostHeadersVals parentPtr parentLen vals) =
        ((.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18)) := by
    simp [hvphPostHeadersVals, hvphFrame, regsAt, sepConj_emp_right']
  have hepi0 := hvphStatus1Exit sp0 spC statusHdr (hvphFrameVals ret vals)
    (hvphPostHeadersVals parentPtr parentLen vals)
    (bytesRegion parentPtr parentBytes **
      hvphFailG thisPtr thisBytes claimedOut parentLen)
    (by refine pcFree_sepConj (bytesRegion_pcFree _ _)
          (hvphFailG_pcFree thisPtr thisBytes claimedOut parentLen))
    hspC (by simpa [hvphFrameVals] using hret)
  have hepi := cpsTripleWithin_extend_code hvph_mono hepi0
  have hepiW : cpsTripleWithin 8 (H + 44) ret fullCode
      ((.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x11 ** regOwn .x12)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        hvphFailG thisPtr thisBytes claimedOut parentLen) :=
    cpsTripleWithin_weaken (fun _ hp => by
      rw [hvals']
      unfold hvphFailG claimedOwn
      xperm_hyp hp) (fun _ hq => by
      simp [hvphFrameVals] at hq ⊢
      xperm_hyp hq) hepi
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold headersCallFrameCore at hp
    xperm_hyp hp) h01 hepiW
  have hn : (9 + (1 + nH)) + 1 + 8 = 19 + nH := by omega
  rw [← hn]
  exact h012

/-! ## Success-path setup (instr 13–16 at `H+52`): parent → a0/a1; `la a2, computed` -/

set_option maxRecDepth 8000 in
/-- After extract-ok: `mv a0,s0` ;; `mv a1,s1` ;; `la a2, hvph_computed`.
    Leaves PC at `H+68` — the `jal zkvm_keccak256` site. -/
theorem hvphKeccakSetup
    (spC ret link parentPtr parentLen old10 old11 old12 : Word) (vals : Reg → Word) :
    cpsTripleWithin 4 (H + 52) (H + 68) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ parentPtr) ** (.x11 ↦ᵣ parentLen) ** (.x12 ↦ᵣ Computed) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) := by
  have h0 := mv_spec_gen_within .x10 .x8 parentPtr old10 (H + 52) (by decide)
  have h1 := mv_spec_gen_within .x11 .x9 parentLen old11 (H + 56) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 52) hvphProg 13 (.MV .x10 .x8)
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) h0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 56) hvphProg 14 (.MV .x11 .x9)
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) h1
  have hau := CodeReq.ofProg_mem_at H (H + 60) hvphProg 15
    (.AUIPC .x12 (EvmAsm.Codegen.laHi GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 60)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had := CodeReq.ofProg_mem_at H (H + 64) hvphProg 16
    (.ADDI .x12 .x12 (EvmAsm.Codegen.laLo GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 60)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla := EvmAsm.Rv64.la_materialize_within .x12 old12 (H + 60) Computed (by decide)
    (by unfold H Computed; decide) hau had
  have e0F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) e0
  have e1F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) **
      (.x18 ↦ᵣ vals .x18) ** (.x10 ↦ᵣ parentPtr) ** (.x12 ↦ᵣ old12) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) e1
  have hlaF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x10 ↦ᵣ parentPtr) ** (.x11 ↦ᵣ parentLen) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) hla
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hlaF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Keccak call at `H+68` (proven leaf, not a premise) -/

theorem stackFree4_eq_keccakFrameSlotsOwn (sp : Word) :
    stackFree sp 4 =
      frameSlotsOwn keccakFrame (sp + signExtend12 (-32 : BitVec 12)) := by
  show (memOwn (sp - BitVec.ofNat 64 (8 * 4)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 2)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 1)) ** empAssertion) = _
  show _ = (memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (8 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (16 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (24 : BitVec 12)) ** empAssertion)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show sp - BitVec.ofNat 64 (8 * 4) = sp + (-32 : Word) + (0 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 3) = sp + (-32 : Word) + (8 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 2) = sp + (-32 : Word) + (16 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 1) = sp + (-32 : Word) + (24 : Word) from by bv_omega]

theorem hvph_keccak_jal_disj :
    (CodeReq.singleton (H + 68)
      (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
        (GuestAddrs.header_validate_parent_hash + 68)))).Disjoint keccakCode :=
  CodeReq.Disjoint.singleton_ofProg (by decide)

theorem hvph_keccak_jal_mem :
    ∀ a i, CodeReq.singleton (H + 68)
        (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.header_validate_parent_hash + 68))) a = some i →
      fullCode a = some i :=
  fun a i h => hvph_mono a i (hvph_keccak_jal_oneshot.1 a i h)

/-- Step count of the one-shot keccak leaf. -/
abbrev nKeccak (N rem : Nat) : Nat := 5 + keccakBodyFuel N rem + 6

set_option maxRecDepth 8000 in
/-- `jal zkvm_keccak256` at `H+68` under the proven leaf (returns `H+72`).

    Requires `stackFree spC 4` for keccak's frame, parent RLP as input, and the
    `hvph_computed` out-buffer.  HVPH frame / claimed / this-bytes live in `F`. -/
theorem hvphKeccakCall
    (spC ret : Word)
    (parentPtr : Word) (parentBytes : List (BitVec 8))
    (N rem : Nat)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    let lenW := BitVec.ofNat 64 (keccakAbsorbStep * N + rem)
    let out0 := List.replicate 32 (0 : BitVec 8)
    let kvals := keccakEntryVals v8 v9 v18 v20
    cpsTripleWithin (1 + nKeccak N rem) (H + 68) (H + 72) fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spC) **
        (stackFree spC 4 ** regsAt keccakFrame kvals **
          keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
            empAssertion) ** F)
      ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          regsAt keccakFrame kvals **
          keccakCallerPost parentPtr Computed parentBytes N rem empAssertion) ** F) := by
  intro lenW out0 kvals
  have htarget : (H + 68) + signExtend21 (jalOff GuestAddrs.zkvm_keccak256
      (GuestAddrs.header_validate_parent_hash + 68)) = K := by
    change BitVec.ofNat 64 GuestAddrs.header_validate_parent_hash + BitVec.ofNat 64 68 + _ =
      BitVec.ofNat 64 GuestAddrs.zkvm_keccak256
    exact jalOff_correct_add GuestAddrs.zkvm_keccak256
      GuestAddrs.header_validate_parent_hash 68
      (by decide) (by decide) (by decide) (by decide)
  have hret72 : ((H + 72 : Word) &&& ~~~(1 : Word)) = H + 72 := by decide
  have hcallee0 := zkvm_keccak256_spec_within spC (H + 72)
    parentPtr Computed parentBytes N rem v8 v9 v18 v20 v28 v29 os empAssertion
    (by pcf) hret72 hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  have hcallee' :
      cpsTripleWithin (nKeccak N rem) K (H + 72) keccakCode
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (H + 72)) **
          regsAt keccakFrame kvals **
          frameSlotsOwn keccakFrame (spC + signExtend12 (-32 : BitVec 12)) **
          keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
            empAssertion)
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (H + 72)) **
          regsAt keccakFrame kvals **
          frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          keccakCallerPost parentPtr Computed parentBytes N rem empAssertion) := by
    simp only [nKeccak, lenW, out0, kvals, K, keccakCode] at hcallee0 ⊢
    simpa [K, keccakCode] using hcallee0
  rw [← stackFree4_eq_keccakFrameSlotsOwn spC] at hcallee'
  have hcalleeFull :
      cpsTripleWithin (nKeccak N rem) K (H + 72) fullCode
        ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
          (stackFree spC 4 ** regsAt keccakFrame kvals **
            keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
              empAssertion))
        ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
          (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
            regsAt keccakFrame kvals **
            keccakCallerPost parentPtr Computed parentBytes N rem empAssertion)) := by
    have h := cpsTripleWithin_extend_code keccak_mono hcallee'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h
  have hcallPc : (H + 68 : Word) + 4 = H + 72 := by bv_omega
  have hcall := abiFrameCall_spec (cr := fullCode)
    (calleePre := stackFree spC 4 ** regsAt keccakFrame kvals **
      keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
        empAssertion)
    (calleePost := frameSlotsSaved keccakFrame
        (spC + signExtend12 (-32 : BitVec 12)) kvals **
      regsAt keccakFrame kvals **
      keccakCallerPost parentPtr Computed parentBytes N rem empAssertion)
    (F := F) (H + 68) K ret spC
    (jalOff GuestAddrs.zkvm_keccak256
      (GuestAddrs.header_validate_parent_hash + 68))
    0 (nKeccak N rem)
    htarget
    hvph_keccak_jal_mem
    (by
      refine pcFree_sepConj (pcFree_stackFree _ _)
        (pcFree_sepConj (pcFree_regsAt _ _) ?_)
      exact keccakCallerPre_pcFree parentPtr lenW Computed v28 v29 os parentBytes out0
        empAssertion (by pcf))
    hF
    (by
      simpa only [hcallPc, stackFree_zero, sepConj_emp_left', sepConj_emp_right',
        nKeccak] using hcalleeFull)
  simpa only [stackFree_zero, sepConj_emp_left', hcallPc, nKeccak] using hcall

set_option maxRecDepth 8000 in
/-- Keccak setup (`H+52`) ;; leaf call (`H+68`) → `H+72`. Cost `5+nK`. -/
theorem hvphKeccakSetupAndCall
    (spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (old10 old11 old12 v20 v28 v29 : Word)
    (parentBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    let out0 := List.replicate 32 (0 : BitVec 8)
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    cpsTripleWithin (5 + nKeccak N rem) (H + 52) (H + 72) fullCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x20 ↦ᵣ v20) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        stackFree spC 4 **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
        bytesRegion parentPtr parentBytes **
        bytesRegion Computed out0 ** F)
      ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          regsAt keccakFrame kvals **
          keccakCallerPost parentPtr Computed parentBytes N rem empAssertion) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) ** F) := by
  intro out0 kvals
  let lenW : Word := BitVec.ofNat 64 (keccakAbsorbStep * N + rem)
  have hsetup0 := hvphKeccakSetup spC ret link parentPtr parentLen old10 old11 old12 vals
  have hsetup := cpsTripleWithin_extend_code hvph_mono <|
    cpsTripleWithin_frameR
      ((.x20 ↦ᵣ v20) ** stackFree spC 4 **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
        bytesRegion parentPtr parentBytes **
        bytesRegion Computed out0 ** F)
      (by refine pcFree_sepConj ?_ (pcFree_sepConj (pcFree_stackFree _ _)
            (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
              (pcFree_sepConj (pcFree_regOwns _) (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj (bytesRegion_pcFree _ _)
                  (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))))))
          <;> pcf) hsetup0
  have hcall := hvphKeccakCall spC link parentPtr parentBytes N rem
    parentPtr parentLen (vals .x18) v20 v28 v29 os
    (frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) ** F)
    (by refine pcFree_sepConj ?_ hF; pcf)
    hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  have hregs : regsAt keccakFrame kvals =
      ((.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ vals .x18) **
        (.x20 ↦ᵣ v20)) := by
    have hlenW : parentLen = lenW := by simp only [lenW]; exact hplen
    simp [kvals, keccakEntryVals, keccakFrame, regsAt, sepConj_emp_right', hlenW]
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    have hlenW : parentLen = lenW := by simp only [lenW]; exact hplen
    rw [hlenW] at hp
    unfold keccakCallerPre
    rw [hregs, sepConj_emp_right']
    xperm_hyp hp) hsetup hcall
  have hn : 4 + (1 + nKeccak N rem) = 5 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Compare setup (instr 18–21 at `H+72`): `la t0,claimed` ;; `la t1,computed` -/

set_option maxRecDepth 8000 in
/-- After keccak returns: materialize Claimed/Computed bases into `x5`/`x6`.
    Leaves PC at `H+88` — first `LD` of the 4-dword compare. -/
theorem hvphCompareSetup
    (spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (old5 old6 : Word) :
    cpsTripleWithin 4 (H + 72) (H + 88) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) := by
  have hau5 := CodeReq.ofProg_mem_at H (H + 72) hvphProg 18
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.hvph_claimed
      (GuestAddrs.header_validate_parent_hash + 72)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had5 := CodeReq.ofProg_mem_at H (H + 76) hvphProg 19
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.hvph_claimed
      (GuestAddrs.header_validate_parent_hash + 72)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla5 := EvmAsm.Rv64.la_materialize_within .x5 old5 (H + 72) Claimed (by decide)
    (by unfold H Claimed; decide) hau5 had5
  have hau6 := CodeReq.ofProg_mem_at H (H + 80) hvphProg 20
    (.AUIPC .x6 (EvmAsm.Codegen.laHi GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 80)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had6 := CodeReq.ofProg_mem_at H (H + 84) hvphProg 21
    (.ADDI .x6 .x6 (EvmAsm.Codegen.laLo GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 80)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla6 := EvmAsm.Rv64.la_materialize_within .x6 old6 (H + 80) Computed (by decide)
    (by unfold H Computed; decide) hau6 had6
  have hla5F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x6 ↦ᵣ old6) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) hla5
  have hla6F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x5 ↦ᵣ Claimed) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) hla6
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla5F hla6F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Status-0 / status-2 exits (match → `li a0,0` ;; `j` ;; epi; mismatch → `li a0,2` ;; epi) -/

set_option maxRecDepth 8000 in
/-- Match exit: `li a0, 0` @ `H+136` → `j` skip status-2 → epilogue. -/
theorem hvphStatus0Exit
    (sp0 spC o10 : Word) (vals vals' : Reg → Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 8 (H + 136) (vals .x1) hvphCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) **
        regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (0 : Word) (H + 136) (by decide)
  have s1 := jal_x0_spec_gen_within (8 : BitVec 21) (H + 140)
  rw [show (H + 140) + signExtend21 (8 : BitVec 21) = H + 148 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
    bv_omega] at s1
  have s0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 136) hvphProg 34 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s0
  have s1C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 140) hvphProg 35 (.JAL .x0 (8 : BitVec 21))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s1
  have hblock : cpsTripleWithin 2 (H + 136) (H + 148) hvphCode
      ((.x10 ↦ᵣ o10)) ((.x10 ↦ᵣ (0 : Word))) := by
    runBlock s0C s1C
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))
        <;> pcf) hblock
  have hepi := hvphEpi sp0 spC (0 : Word) vals vals' G hG hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepi
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Mismatch exit: `li a0, 2` @ `H+144` → epilogue. -/
theorem hvphStatus2Exit
    (sp0 spC o10 : Word) (vals vals' : Reg → Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 7 (H + 144) (vals .x1) hvphCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) **
        regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (2 : Word) (H + 144) (by decide)
  have s0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 144) hvphProg 36 (.LI .x10 (2 : Word))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s0
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))
        <;> pcf) s0C
  have hepi := hvphEpi sp0 spC (2 : Word) vals vals' G hG hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepi
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## 4-dword compare (instr 22–33): LD claimed ;; LD computed ;; BNE → status-2

    Equal fall-through advances `+12` per round; mismatch BNE targets `H+144`. -/

abbrev dwordAt (bs : List (BitVec 8)) (q : Nat) : Word :=
  packBytes ((bs.drop (8 * q)).take 8)

set_option maxRecDepth 8000 in
/-- Round 0 equal: `LD/LD/BNE` at `H+88` fall through to `H+100`. -/
theorem hvphCompareRound0Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 0 = dwordAt computedBytes 0) :
    cpsTripleWithin 3 (H + 88) (H + 100) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 88) claimedBytes 0
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 88) hvphProg 22 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 92) computedBytes 0
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 92) hvphProg 23 (.LD .x28 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 0) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (48 : BitVec 13)
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) (H + 96)
  rw [show (H + 96 : Word) + 4 = H + 100 from by bv_omega,
    show (H + 96) + signExtend13 (48 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (48 : BitVec 13) = (48 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 96) hvphProg 24 (.BNE .x7 .x28 (48 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 0 mismatch: `LD/LD/BNE` at `H+88` taken to `H+144` (status-2 site). -/
theorem hvphCompareRound0Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    cpsTripleWithin 3 (H + 88) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 88) claimedBytes 0
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 88) hvphProg 22 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 92) computedBytes 0
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 92) hvphProg 23 (.LD .x28 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 0) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (48 : BitVec 13)
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) (H + 96)
  rw [show (H + 96 : Word) + 4 = H + 100 from by bv_omega,
    show (H + 96) + signExtend13 (48 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (48 : BitVec 13) = (48 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 96) hvphProg 24 (.BNE .x7 .x28 (48 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 1 equal: `H+100` → `H+112`. -/
theorem hvphCompareRound1Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 1 = dwordAt computedBytes 1) :
    cpsTripleWithin 3 (H + 100) (H + 112) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 100) claimedBytes 1
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 100) hvphProg 25 (.LD .x7 .x5 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 104) computedBytes 1
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 104) hvphProg 26 (.LD .x28 .x6 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 1) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (36 : BitVec 13)
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) (H + 108)
  rw [show (H + 108 : Word) + 4 = H + 112 from by bv_omega,
    show (H + 108) + signExtend13 (36 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 108) hvphProg 27 (.BNE .x7 .x28 (36 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 1 mismatch: `H+100` → `H+144`. -/
theorem hvphCompareRound1Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 1 ≠ dwordAt computedBytes 1) :
    cpsTripleWithin 3 (H + 100) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 100) claimedBytes 1
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 100) hvphProg 25 (.LD .x7 .x5 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 104) computedBytes 1
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 104) hvphProg 26 (.LD .x28 .x6 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 1) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (36 : BitVec 13)
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) (H + 108)
  rw [show (H + 108 : Word) + 4 = H + 112 from by bv_omega,
    show (H + 108) + signExtend13 (36 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 108) hvphProg 27 (.BNE .x7 .x28 (36 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 2 equal: `H+112` → `H+124`. -/
theorem hvphCompareRound2Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 2 = dwordAt computedBytes 2) :
    cpsTripleWithin 3 (H + 112) (H + 124) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 112) claimedBytes 2
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 112) hvphProg 28 (.LD .x7 .x5 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 116) computedBytes 2
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 116) hvphProg 29 (.LD .x28 .x6 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 2) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (24 : BitVec 13)
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) (H + 120)
  rw [show (H + 120 : Word) + 4 = H + 124 from by bv_omega,
    show (H + 120) + signExtend13 (24 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 120) hvphProg 30 (.BNE .x7 .x28 (24 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 2 mismatch: `H+112` → `H+144`. -/
theorem hvphCompareRound2Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 2 ≠ dwordAt computedBytes 2) :
    cpsTripleWithin 3 (H + 112) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 112) claimedBytes 2
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 112) hvphProg 28 (.LD .x7 .x5 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 116) computedBytes 2
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 116) hvphProg 29 (.LD .x28 .x6 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 2) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (24 : BitVec 13)
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) (H + 120)
  rw [show (H + 120 : Word) + 4 = H + 124 from by bv_omega,
    show (H + 120) + signExtend13 (24 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 120) hvphProg 30 (.BNE .x7 .x28 (24 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 3 equal: `H+124` → `H+136` (status-0 site). -/
theorem hvphCompareRound3Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    cpsTripleWithin 3 (H + 124) (H + 136) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 124) claimedBytes 3
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 124) hvphProg 31 (.LD .x7 .x5 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 128) computedBytes 3
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 128) hvphProg 32 (.LD .x28 .x6 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 3) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (12 : BitVec 13)
    (dwordAt claimedBytes 3) (dwordAt computedBytes 3) (H + 132)
  rw [show (H + 132 : Word) + 4 = H + 136 from by bv_omega,
    show (H + 132) + signExtend13 (12 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 132) hvphProg 33 (.BNE .x7 .x28 (12 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 3 mismatch: `H+124` → `H+144`. -/
theorem hvphCompareRound3Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 3 ≠ dwordAt computedBytes 3) :
    cpsTripleWithin 3 (H + 124) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 124) claimedBytes 3
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 124) hvphProg 31 (.LD .x7 .x5 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 128) computedBytes 3
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 128) hvphProg 32 (.LD .x28 .x6 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 3) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (12 : BitVec 13)
    (dwordAt claimedBytes 3) (dwordAt computedBytes 3) (H + 132)
  rw [show (H + 132 : Word) + 4 = H + 136 from by bv_omega,
    show (H + 132) + signExtend13 (12 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 132) hvphProg 33 (.BNE .x7 .x28 (12 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- All four dwords equal: `H+88` → `H+136` (12 steps). -/
theorem hvphCompareAllEq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    cpsTripleWithin 12 (H + 88) (H + 136) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Eq claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h1
  have r2 := hvphCompareRound2Eq claimedBytes computedBytes
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) hclen hcdlen h2
  have r3 := hvphCompareRound3Eq claimedBytes computedBytes
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) hclen hcdlen h3
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 r2
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 r3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Match residual from compare start: all-eq ;; status-0 exit. Cost `20`. -/
theorem hvphCompareMatchExit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    cpsTripleWithin 20 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have hcmp0 := hvphCompareAllEq claimedBytes computedBytes v7 v28 hclen hcdlen h0 h1 h2 h3
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus0Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : 12 + 8 = 20 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- First-dword mismatch residual: round0-ne ;; status-2 exit. Cost `10`. -/
theorem hvphCompareMismatch0Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    cpsTripleWithin 10 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have hcmp0 := hvphCompareRound0Ne claimedBytes computedBytes v7 v28 hclen hcdlen h_ne
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : 3 + 7 = 10 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Dword-1 mismatch: eq0 ;; ne1 ;; status-2. Cost `13`. -/
theorem hvphCompareMismatch1Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h_ne : dwordAt claimedBytes 1 ≠ dwordAt computedBytes 1) :
    cpsTripleWithin 13 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Ne claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h_ne
  have hcmp0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : (3 + 3) + 7 = 13 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Dword-2 mismatch: eq0–1 ;; ne2 ;; status-2. Cost `16`. -/
theorem hvphCompareMismatch2Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h_ne : dwordAt claimedBytes 2 ≠ dwordAt computedBytes 2) :
    cpsTripleWithin 16 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Eq claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h1
  have r2 := hvphCompareRound2Ne claimedBytes computedBytes
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) hclen hcdlen h_ne
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have hcmp0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 r2
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : (3 + 3 + 3) + 7 = 16 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Dword-3 mismatch: eq0–2 ;; ne3 ;; status-2. Cost `19`. -/
theorem hvphCompareMismatch3Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h_ne : dwordAt claimedBytes 3 ≠ dwordAt computedBytes 3) :
    cpsTripleWithin 19 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Eq claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h1
  have r2 := hvphCompareRound2Eq claimedBytes computedBytes
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) hclen hcdlen h2
  have r3 := hvphCompareRound3Ne claimedBytes computedBytes
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) hclen hcdlen h_ne
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 r2
  have hcmp0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 r3
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : (3 + 3 + 3 + 3) + 7 = 19 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Concrete-scratch helper for `hvphFromCompareSetupMatch`. -/
theorem hvphFromCompareSetupMatch_vals
    (sp0 spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (old5 old6 v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    let saved := hvphFrameVals ret vals
    cpsTripleWithin 24 (H + 72) (saved .x1) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  intro saved
  let cur : Reg → Word := fun r =>
    if r = .x1 then link else if r = .x8 then parentPtr else
    if r = .x9 then parentLen else if r = .x18 then vals .x18 else (0 : Word)
  have hsetup0 := hvphCompareSetup spC ret link parentPtr parentLen vals old5 old6
  have hsetup := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hsetup0
  have hexit := hvphCompareMatchExit sp0 spC ret saved cur
    claimedBytes computedBytes v7 v28 o10 G hG hspC
    (by simpa [saved, hvphFrameVals] using hret) hclen hcdlen h0 h1 h2 h3
  have hregs : regsAt hvphFrame cur =
      ((.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
        (.x18 ↦ᵣ vals .x18)) := by
    simp [cur, hvphFrame, regsAt, sepConj_emp_right']
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [hregs]
    xperm_hyp hp) hsetup hexit
  have hn : 4 + 20 = 24 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [saved, hvphFrameVals] at hq ⊢
      xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- From `H+72` (post-keccak): `la` ptrs ;; all-eq compare ;; status-0. Cost `24`.
    Scratch `x5/x6/x7/x28` are `regOwn` so keccak's post connects. -/
theorem hvphFromCompareSetupMatch
    (sp0 spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    let saved := hvphFrameVals ret vals
    cpsTripleWithin 24 (H + 72) (saved .x1) hvphCode
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
          (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
          (.x10 ↦ᵣ o10) **
          frameSlotsSaved hvphFrame spC saved **
          claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G **
          regOwn .x5 ** regOwn .x6) **
        regOwn .x7 ** regOwn .x28)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  intro saved
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x28)
    (fun v7 v28 => ?_)
  refine cpsTripleWithin_weaken
    (P := (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ o10) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      regOwn .x5 ** regOwn .x6))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x5) (r2 := .x6)
    (fun old5 old6 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
      (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
      (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
      frameSlotsSaved hvphFrame spC saved **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  simpa [saved] using
    hvphFromCompareSetupMatch_vals sp0 spC ret link parentPtr parentLen vals
      claimedBytes computedBytes old5 old6 v7 v28 o10 G hG hspC hret
      hclen hcdlen h0 h1 h2 h3

set_option maxRecDepth 8000 in
/-- Concrete-scratch helper for `hvphFromCompareSetupMismatch0`. -/
theorem hvphFromCompareSetupMismatch0_vals
    (sp0 spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (old5 old6 v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    let saved := hvphFrameVals ret vals
    cpsTripleWithin 14 (H + 72) (saved .x1) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  intro saved
  let cur : Reg → Word := fun r =>
    if r = .x1 then link else if r = .x8 then parentPtr else
    if r = .x9 then parentLen else if r = .x18 then vals .x18 else (0 : Word)
  have hsetup0 := hvphCompareSetup spC ret link parentPtr parentLen vals old5 old6
  have hsetup := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hsetup0
  have hexit := hvphCompareMismatch0Exit sp0 spC ret saved cur
    claimedBytes computedBytes v7 v28 o10 G hG hspC
    (by simpa [saved, hvphFrameVals] using hret) hclen hcdlen h_ne
  have hregs : regsAt hvphFrame cur =
      ((.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
        (.x18 ↦ᵣ vals .x18)) := by
    simp [cur, hvphFrame, regsAt, sepConj_emp_right']
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [hregs]
    xperm_hyp hp) hsetup hexit
  have hn : 4 + 10 = 14 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [saved, hvphFrameVals] at hq ⊢
      xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- From `H+72`: `la` ptrs ;; first-dword mismatch ;; status-2. Cost `14`.
    Scratch `x5/x6/x7/x28` are `regOwn`. -/
theorem hvphFromCompareSetupMismatch0
    (sp0 spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    let saved := hvphFrameVals ret vals
    cpsTripleWithin 14 (H + 72) (saved .x1) hvphCode
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
          (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
          (.x10 ↦ᵣ o10) **
          frameSlotsSaved hvphFrame spC saved **
          claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G **
          regOwn .x5 ** regOwn .x6) **
        regOwn .x7 ** regOwn .x28)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  intro saved
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x28)
    (fun v7 v28 => ?_)
  refine cpsTripleWithin_weaken
    (P := (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ o10) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      regOwn .x5 ** regOwn .x6))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x5) (r2 := .x6)
    (fun old5 old6 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
      (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
      (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
      frameSlotsSaved hvphFrame spC saved **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  simpa [saved] using
    hvphFromCompareSetupMismatch0_vals sp0 spC ret link parentPtr parentLen vals
      claimedBytes computedBytes old5 old6 v7 v28 o10 G hG hspC hret
      hclen hcdlen h_ne

set_option maxRecDepth 8000 in
/-- Keccak setup+call (`H+52`) ;; compare-match exit. Cost `29+nK`.

    `claimedBytes` must equal the digest dwords (match path). Ambient `F` carries
    anything beyond HVPH frame / claimed / parent / Zk3 / stackFree. -/
theorem hvphKeccakThenMatch
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (old10 old11 old12 v20 v28 v29 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt (keccakBodyDigest parentBytes N rem) 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt (keccakBodyDigest parentBytes N rem) 3) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    cpsTripleWithin (29 + nKeccak N rem) (H + 52) (saved .x1) fullCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (H + 40)) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x20 ↦ᵣ v20) **
        frameSlotsSaved hvphFrame spC saved **
        stackFree spC 4 **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
        bytesRegion parentPtr parentBytes **
        bytesRegion Computed out0 **
        claimedOwn claimedBytes ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt digest 3) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion ** F)) := by
  intro digest kvals out0 saved
  have hcdlen : digest.length = 32 := by
    simp only [digest, keccakBodyDigest]
    exact keccakDigestCopy_length _
  have hcall := hvphKeccakSetupAndCall spC ret (H + 40) parentPtr parentLen vals
    old10 old11 old12 v20 v28 v29 parentBytes N rem os
    (claimedOwn claimedBytes ** F)
    (by refine pcFree_sepConj ?_ hF; exact bytesRegion_pcFree _ _)
    hplen hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  -- Match path under fullCode; G absorbs keccak residuals.
  set Gmatch : Assertion :=
    (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
      (.x20 ↦ᵣ v20) **
      bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
        (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
          (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
      keccakCallerFreeA parentPtr parentBytes N empAssertion ** F)
  have hG : Gmatch.pcFree := by
    unfold Gmatch
    refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj (bytesRegion_pcFree _ _)
      (pcFree_sepConj ?_ (pcFree_sepConj (pcFree_regOwns _)
        (pcFree_sepConj (keccakCallerFreeA_pcFree _ _ _ _ (by pcf)) hF)))))
      <;> pcf
  have hmatch0 := hvphFromCompareSetupMatch sp0 spC ret (H + 72) parentPtr parentLen vals
    claimedBytes digest (0 : Word) Gmatch hG hspC hret hclen hcdlen h0 h1 h2 h3
  have hmatch := cpsTripleWithin_extend_code hvph_mono hmatch0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold keccakCallerPost at hp
    have hregs : regsAt keccakFrame kvals =
        ((.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
          (.x20 ↦ᵣ v20)) := by
      simp [kvals, keccakEntryVals, keccakFrame, regsAt, sepConj_emp_right']
    rw [hregs] at hp
    -- Peel scratch owns for Match; keep the residual list bundled for Gmatch.
    have hcsrs :
        regOwns keccakCsrsRestNoX5 =
          (regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]) := by
      simp only [regOwns, keccakCsrsRestNoX5, sepConj_emp_right']
    rw [hcsrs] at hp
    unfold Gmatch
    xperm_hyp hp) hcall hmatch
  have hn : (5 + nKeccak N rem) + 24 = 29 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [saved, out0] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest, Gmatch] at hq ⊢
    xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Keccak setup+call (`H+52`) ;; first-dword mismatch exit. Cost `19+nK`. -/
theorem hvphKeccakThenMismatch0
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (old10 old11 old12 v20 v28 v29 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    cpsTripleWithin (19 + nKeccak N rem) (H + 52) (saved .x1) fullCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (H + 40)) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x20 ↦ᵣ v20) **
        frameSlotsSaved hvphFrame spC saved **
        stackFree spC 4 **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
        bytesRegion parentPtr parentBytes **
        bytesRegion Computed out0 **
        claimedOwn claimedBytes ** F)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion ** F)) := by
  intro digest kvals out0 saved
  have hcdlen : digest.length = 32 := by
    simp only [digest, keccakBodyDigest]
    exact keccakDigestCopy_length _
  have hcall := hvphKeccakSetupAndCall spC ret (H + 40) parentPtr parentLen vals
    old10 old11 old12 v20 v28 v29 parentBytes N rem os
    (claimedOwn claimedBytes ** F)
    (by refine pcFree_sepConj ?_ hF; exact bytesRegion_pcFree _ _)
    hplen hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  set Gmm : Assertion :=
    (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
      (.x20 ↦ᵣ v20) **
      bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
        (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
          (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
      keccakCallerFreeA parentPtr parentBytes N empAssertion ** F)
  have hG : Gmm.pcFree := by
    unfold Gmm
    refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj (bytesRegion_pcFree _ _)
      (pcFree_sepConj ?_ (pcFree_sepConj (pcFree_regOwns _)
        (pcFree_sepConj (keccakCallerFreeA_pcFree _ _ _ _ (by pcf)) hF)))))
      <;> pcf
  have hmm0 := hvphFromCompareSetupMismatch0 sp0 spC ret (H + 72) parentPtr parentLen vals
    claimedBytes digest (0 : Word) Gmm hG hspC hret hclen hcdlen h_ne
  have hmm := cpsTripleWithin_extend_code hvph_mono hmm0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold keccakCallerPost at hp
    have hregs : regsAt keccakFrame kvals =
        ((.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
          (.x20 ↦ᵣ v20)) := by
      simp [kvals, keccakEntryVals, keccakFrame, regsAt, sepConj_emp_right']
    rw [hregs] at hp
    have hcsrs :
        regOwns keccakCsrsRestNoX5 =
          (regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]) := by
      simp only [regOwns, keccakCsrsRestNoX5, sepConj_emp_right']
    rw [hcsrs] at hp
    unfold Gmm
    xperm_hyp hp) hcall hmm
  have hn : (5 + nKeccak N rem) + 14 = 19 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [saved, out0] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest, Gmm] at hq ⊢
    xperm_hyp hq) hall

/-! ## From headers return (`H+40`): extract-ok beq ;; keccak ;; compare-match -/

/-- Ambient past the headers frame for the keccak success path.
    Does not include a1/a2 — those are havoc `regOwn` from `headersCallPremise`. -/
def hvphSuccKeccakAmb
    (spC v20 : Word)
    (os out0 : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x20 ↦ᵣ v20) **
  stackFree spC 4 **
  regOwns [.x14, .x15, .x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F

theorem hvphSuccKeccakAmb_pcFree
    (spC v20 : Word)
    (os out0 : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    (hvphSuccKeccakAmb spC v20 os out0 F).pcFree := by
  unfold hvphSuccKeccakAmb
  refine pcFree_sepConj ?_ (pcFree_sepConj (pcFree_stackFree _ _)
    (pcFree_sepConj (pcFree_regOwns _)
      (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))
  · pcf

/-- `headersCallFrameCore` without `x28`/`x29` owns (concrete on keccak success). -/
def headersCallFrameSuccCore
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
  (.x18 ↦ᵣ vals .x18) **
  frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
  bytesRegion parentPtr parentBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x13 ** regOwn .x30 ** regOwn .x31

set_option maxRecDepth 8000 in
/-- Concrete-scratch helper: `H+40` beq-ok ;; keccak ;; compare-match. Cost `30+nK`. -/
theorem hvphFromHeadersMatch_vals
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (old11 old12 v20 v28 v29 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (thisPtr : Word) (thisBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt (keccakBodyDigest parentBytes N rem) 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt (keccakBodyDigest parentBytes N rem) 3) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0
      (bytesRegion thisPtr thisBytes ** F)
    cpsTripleWithin (30 + nKeccak N rem) (H + 40) (saved .x1) fullCode
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedBytes **
        headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt digest 3) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  have hAmb : Amb.pcFree :=
    hvphSuccKeccakAmb_pcFree spC v20 os out0 _
      (by refine pcFree_sepConj (bytesRegion_pcFree _ _) hF)
  have hbeq0 := hvphBeqExtractOk
  have hbeq := cpsTripleWithin_extend_code hvph_mono hbeq0
  have hbeqF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** claimedOwn claimedBytes **
      headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb)
    (by
      refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
        (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hAmb))))))
      · pcf
      · exact bytesRegion_pcFree _ _
      · unfold headersCallFrameSuccCore; pcf
      · pcf
      · pcf
      · pcf
      · pcf) hbeq
  have hkm := hvphKeccakThenMatch sp0 spC ret parentPtr parentLen vals
    (0 : Word) old11 old12 v20 v28 v29 parentBytes claimedBytes N rem os
    (bytesRegion thisPtr thisBytes ** F)
    (by refine pcFree_sepConj (bytesRegion_pcFree _ _) hF)
    hspC hret hplen hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h0 h1 h2 h3
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold headersCallFrameSuccCore Amb hvphSuccKeccakAmb at hp
    simp only [out0, regOwns, keccakBodyFreeTemps, sepConj_emp_right'] at hp ⊢
    xperm_hyp hp) hbeqF hkm
  have hn : 1 + (29 + nKeccak N rem) = 30 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [Amb] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest] at hq ⊢
    xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- From `H+40` with status 0: beq-ok ;; keccak ;; compare-match. Cost `30+nK`.
    Scratch `x28`/`x29` are `regOwn`. -/
theorem hvphFromHeadersMatch
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (thisPtr : Word) (thisBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt (keccakBodyDigest parentBytes N rem) 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt (keccakBodyDigest parentBytes N rem) 3) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0
      (bytesRegion thisPtr thisBytes ** F)
    cpsTripleWithin (30 + nKeccak N rem) (H + 40) (saved .x1) fullCode
      ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn claimedBytes **
            headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
            Amb) **
          regOwn .x11 ** regOwn .x12) **
        regOwn .x28 ** regOwn .x29)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt digest 3) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x28) (r2 := .x29)
    (fun v28 v29 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          claimedOwn claimedBytes **
          headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
          Amb) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29)) **
      regOwn .x11 ** regOwn .x12))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x11) (r2 := .x12)
    (fun old11 old12 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      claimedOwn claimedBytes **
      headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  simpa [digest, kvals, out0, saved, Amb] using
    hvphFromHeadersMatch_vals sp0 spC ret parentPtr parentLen vals
      old11 old12 v20 v28 v29 parentBytes claimedBytes N rem os
      thisPtr thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hclen h0 h1 h2 h3

set_option maxRecDepth 8000 in
/-- Concrete-scratch helper: `H+40` beq-ok ;; keccak ;; dword0-mismatch. Cost `20+nK`. -/
theorem hvphFromHeadersMismatch0_vals
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (old11 old12 v20 v28 v29 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (thisPtr : Word) (thisBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0
      (bytesRegion thisPtr thisBytes ** F)
    cpsTripleWithin (20 + nKeccak N rem) (H + 40) (saved .x1) fullCode
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedBytes **
        headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  have hAmb : Amb.pcFree :=
    hvphSuccKeccakAmb_pcFree spC v20 os out0 _
      (by refine pcFree_sepConj (bytesRegion_pcFree _ _) hF)
  have hbeq0 := hvphBeqExtractOk
  have hbeq := cpsTripleWithin_extend_code hvph_mono hbeq0
  have hbeqF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** claimedOwn claimedBytes **
      headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb)
    (by
      refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
        (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hAmb))))))
      · pcf
      · exact bytesRegion_pcFree _ _
      · unfold headersCallFrameSuccCore; pcf
      · pcf
      · pcf
      · pcf
      · pcf) hbeq
  have hkm := hvphKeccakThenMismatch0 sp0 spC ret parentPtr parentLen vals
    (0 : Word) old11 old12 v20 v28 v29 parentBytes claimedBytes N rem os
    (bytesRegion thisPtr thisBytes ** F)
    (by refine pcFree_sepConj (bytesRegion_pcFree _ _) hF)
    hspC hret hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h_ne
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold headersCallFrameSuccCore Amb hvphSuccKeccakAmb at hp
    simp only [out0, regOwns, keccakBodyFreeTemps, sepConj_emp_right'] at hp ⊢
    xperm_hyp hp) hbeqF hkm
  have hn : 1 + (19 + nKeccak N rem) = 20 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [Amb] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest] at hq ⊢
    xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- From `H+40` with status 0: beq-ok ;; keccak ;; dword0-mismatch. Cost `20+nK`. -/
theorem hvphFromHeadersMismatch0
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (thisPtr : Word) (thisBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0
      (bytesRegion thisPtr thisBytes ** F)
    cpsTripleWithin (20 + nKeccak N rem) (H + 40) (saved .x1) fullCode
      ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn claimedBytes **
            headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
            Amb) **
          regOwn .x11 ** regOwn .x12) **
        regOwn .x28 ** regOwn .x29)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x28) (r2 := .x29)
    (fun v28 v29 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          claimedOwn claimedBytes **
          headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
          Amb) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29)) **
      regOwn .x11 ** regOwn .x12))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x11) (r2 := .x12)
    (fun old11 old12 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      claimedOwn claimedBytes **
      headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  simpa [digest, kvals, out0, saved, Amb] using
    hvphFromHeadersMismatch0_vals sp0 spC ret parentPtr parentLen vals
      old11 old12 v20 v28 v29 parentBytes claimedBytes N rem os
      thisPtr thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hclen h_ne

/-! ## Prologue ;; headers ;; match (`H → ret`). Cost `40+nH+nK`. -/

set_option maxRecDepth 8000 in
/-- Full success-match residual: prologue+headers ;; beq-ok ;; keccak ;; compare-match.
    Cost `40+nH+nK`. Requires `statusHdr = 0` and claimed dwords = digest.
    Keccak ambient (`Amb`) is framed around the headers call (not in the premise `F`). -/
theorem hvphMatch_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_headers : headersCallPremise nH (H + 40) (0 : Word) thisPtr thisLen
      thisBytes claimedBytes claimedBytes
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes))
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt (keccakBodyDigest parentBytes N rem) 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt (keccakBodyDigest parentBytes N rem) 3) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (40 + nH + nKeccak N rem) H (saved .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt digest 3) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
  have hph0 := hvphPrologueHeaders nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    (0 : Word) vals thisBytes parentBytes claimedBytes claimedBytes hspC h_headers
  have hph := cpsTripleWithin_frameR Amb hAmb hph0
  have hmatch := hvphFromHeadersMatch sp0 spC ret parentPtr parentLen vals
    v20 parentBytes claimedBytes N rem os thisPtr thisBytes F hF
    hspC hret hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h0 h1 h2 h3
  -- Bridge PrologueHeaders.post ** Amb → FromHeadersMatch.pre (demote x13; peel owns).
  have hphW :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
      unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
      let Rest : Assertion :=
        (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          claimedOwn claimedBytes ** bytesRegion thisPtr thisBytes **
          (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x30 ** regOwn .x31 **
          (.x20 ↦ᵣ v20) ** stackFree spC 4 **
          regOwns [.x14, .x15, .x16, .x17] **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
          bytesRegion Computed out0 ** F **
          regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
      have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
        simp only [Rest]
        xperm_hyp hq
      have hqOwn : (Rest ** regOwn .x13) s :=
        sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
      change
        (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              claimedOwn claimedBytes **
              headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
              hvphSuccKeccakAmb spC v20 os out0
                (bytesRegion thisPtr thisBytes ** F)) **
            regOwn .x11 ** regOwn .x12) **
          regOwn .x28 ** regOwn .x29) s)
      · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
        simp only [Rest] at hqOwn
        xperm_hyp hqOwn) hph
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [out0] at hp ⊢
    xperm_hyp hp) hphW hmatch
  have hn : (9 + (1 + nH)) + (30 + nKeccak N rem) = 40 + nH + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    -- Reassociate frameR's `(P) ** Amb` into the flat entry pre.
    simp only [Amb] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest] at hq ⊢
    xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Full dword0-mismatch residual: prologue+headers ;; beq-ok ;; keccak ;; mismatch0.
    Cost `30+nH+nK`. Requires `statusHdr = 0` and claimed dword0 ≠ digest. -/
theorem hvphMismatch0_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_headers : headersCallPremise nH (H + 40) (0 : Word) thisPtr thisLen
      thisBytes claimedBytes claimedBytes
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes))
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + nH + nKeccak N rem) H (saved .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
  have hph0 := hvphPrologueHeaders nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    (0 : Word) vals thisBytes parentBytes claimedBytes claimedBytes hspC h_headers
  have hph := cpsTripleWithin_frameR Amb hAmb hph0
  have hmm := hvphFromHeadersMismatch0 sp0 spC ret parentPtr parentLen vals
    v20 parentBytes claimedBytes N rem os thisPtr thisBytes F hF
    hspC hret hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h_ne
  have hphW :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
      unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
      let Rest : Assertion :=
        (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          claimedOwn claimedBytes ** bytesRegion thisPtr thisBytes **
          (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x30 ** regOwn .x31 **
          (.x20 ↦ᵣ v20) ** stackFree spC 4 **
          regOwns [.x14, .x15, .x16, .x17] **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
          bytesRegion Computed out0 ** F **
          regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
      have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
        simp only [Rest]
        xperm_hyp hq
      have hqOwn : (Rest ** regOwn .x13) s :=
        sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
      change
        (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              claimedOwn claimedBytes **
              headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
              hvphSuccKeccakAmb spC v20 os out0
                (bytesRegion thisPtr thisBytes ** F)) **
            regOwn .x11 ** regOwn .x12) **
          regOwn .x28 ** regOwn .x29) s)
      · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
        simp only [Rest] at hqOwn
        xperm_hyp hqOwn) hph
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [out0] at hp ⊢
    xperm_hyp hp) hphW hmm
  have hn : (9 + (1 + nH)) + (20 + nKeccak N rem) = 30 + nH + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [Amb] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest] at hq ⊢
    xperm_hyp hq) hall

/-! ## Adapter helpers (BSS frame around hvphPre/Post) -/

/-- Reassemble parent bytes from the keccak caller's split free assertion. -/
theorem bytesRegion_of_keccakCallerFreeA
    (parentPtr : Word) (parentBytes : List (BitVec 8)) (N rem : Nat)
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem) :
    ∀ h, (keccakCallerFreeA parentPtr parentBytes N empAssertion) h →
      bytesRegion parentPtr parentBytes h := by
  intro h hp
  unfold keccakCallerFreeA keccakResidual keccakAbsorbCursor at hp
  set n := keccakAbsorbStep * N
  have hpre : (parentBytes.take n).length = n := by
    simp only [n, List.length_take, hlen]; omega
  have hmod : n % 8 = 0 := by
    simp only [n, keccakAbsorbStep]; omega
  have h8 : 8 ∣ (parentBytes.take n).length := by
    rw [hpre]; exact Nat.dvd_of_mod_eq_zero hmod
  have hp2 :
      (bytesRegion parentPtr (parentBytes.take n) **
        bytesRegion (parentPtr + BitVec.ofNat 64 n) (parentBytes.drop n)) h := by
    have hp' :
        (bytesRegion (parentPtr + BitVec.ofNat 64 n) (parentBytes.drop n) **
          bytesRegion parentPtr (parentBytes.take n)) h := by
      simpa [sepConj_emp_right'] using hp
    xperm_hyp hp'
  have happ := bytesRegion_append parentPtr
    (parentBytes.take n) (parentBytes.drop n) h8
  have hfull : bytesRegion parentPtr (parentBytes.take n ++ parentBytes.drop n) h := by
    rw [happ, hpre]
    exact hp2
  simpa [List.take_append_drop] using hfull

/-- Leftover ambient after a match exit (BSS + keccak frame + caller-saved scratch). -/
def hvphMatchExitExtra
    (spC parentPtr parentLen v20 : Word) (vals : Reg → Word)
    (parentBytes claimedBytes digest : List (BitVec 8)) (N rem : Nat)
    (F : Assertion) : Assertion :=
  claimedOwn claimedBytes ** bytesRegion Computed digest **
  frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12))
    (keccakEntryVals parentPtr parentLen (vals .x18) v20) **
  (.x20 ↦ᵣ v20) **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
    (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
      (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
  regOwns [.x14, .x15, .x16, .x17] **
  F

/-- Keccak-exit residual post → `hvphPost ** Extra` (demote scratch; reassemble parent).
    Parameterized by exit `status` and the concrete compare scratch dwords in x7/x28. -/
theorem hvphKeccakExit_post_to_adapter
    (sp0 spC ret parentPtr parentLen v20 status d7 d28 : Word) (vals : Reg → Word)
    (thisPtr : Word) (thisBytes parentBytes claimedBytes : List (BitVec 8))
    (N rem : Nat) (F : Assertion)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem) :
    let digest := keccakBodyDigest parentBytes N rem
    let saved := hvphFrameVals ret vals
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    ∀ s,
      ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) s →
      (hvphPost sp0 thisPtr parentPtr ret status vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals
          parentBytes claimedBytes digest N rem F) s := by
  intro digest saved kvals s hq
  -- Reassemble parent, then demote x5/x6/x7/x28.
  have hqTrail :
      ((((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
          frameSlotsSaved hvphFrame spC saved **
          (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
          (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
          claimedOwn claimedBytes ** bytesRegion Computed digest **
          frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          bytesRegion thisPtr thisBytes ** F) **
        keccakCallerFreeA parentPtr parentBytes N empAssertion)) s := by
    xperm_hyp hq
  have hqParent :
      ((((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
          frameSlotsSaved hvphFrame spC saved **
          (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
          (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
          claimedOwn claimedBytes ** bytesRegion Computed digest **
          frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          bytesRegion thisPtr thisBytes ** F) **
        bytesRegion parentPtr parentBytes)) s :=
    sepConj_mono_right (bytesRegion_of_keccakCallerFreeA parentPtr parentBytes N rem hlen)
      s hqTrail
  -- Rotate each concrete scratch to the front and demote.
  have hx5 : ((.x5 ↦ᵣ Claimed) **
      ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp hqParent
  have o5 := sepConj_mono_left (regIs_to_regOwn .x5 Claimed) s hx5
  have hx6 : ((.x6 ↦ᵣ Computed) **
      (regOwn .x5 **
        (.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp o5
  have o6 := sepConj_mono_left (regIs_to_regOwn .x6 Computed) s hx6
  have hx7 : ((.x7 ↦ᵣ d7) **
      (regOwn .x6 ** regOwn .x5 **
        (.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp o6
  have o7 := sepConj_mono_left (regIs_to_regOwn .x7 d7) s hx7
  have hx28 : ((.x28 ↦ᵣ d28) **
      (regOwn .x7 ** regOwn .x6 ** regOwn .x5 **
        (.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp o7
  have o28 := sepConj_mono_left (regIs_to_regOwn .x28 d28) s hx28
  have hx1 : saved .x1 = ret := by simp [saved, hvphFrameVals]
  have hx8 : saved .x8 = vals .x8 := by simp [saved, hvphFrameVals]
  have hx9 : saved .x9 = vals .x9 := by simp [saved, hvphFrameVals]
  have hx18 : saved .x18 = vals .x18 := by simp [saved, hvphFrameVals]
  unfold hvphPost hvphMatchExitExtra
  -- Expand `regsAt` on the goal so it matches the concrete s0/s1/s2 atoms.
  simp only [regsAt_hvphSavedFrame, hx1, hx8, hx9, hx18, kvals, digest, saved, hspC,
    regOwns, sepConj_emp_right'] at o28 ⊢
  xperm_hyp o28

set_option maxRecDepth 8000 in
/-- Match path in adapter shape: `hvphPre`/`hvphPost` with BSS ambient framed.
    Cost `40+nH+nK`. -/
theorem header_validate_parent_hash_match_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_headers : headersCallPremise nH (H + 40) (0 : Word) thisPtr thisLen
      thisBytes claimedBytes claimedBytes
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes))
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt (keccakBodyDigest parentBytes N rem) 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt (keccakBodyDigest parentBytes N rem) 3) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (40 + nH + nKeccak N rem) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn claimedBytes ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (0 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals
          parentBytes claimedBytes digest N rem F) := by
  intro digest out0 Amb
  have hmatch := hvphMatch_spec_within nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    vals v20 thisBytes parentBytes claimedBytes N rem os F hF
    hspC hret h_headers hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h0 h1 h2 h3
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hmatch
  · -- Entry: adapter pre → Match pre
    unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · -- Exit: Match post → hvphPost ** Extra
    simpa [digest, Amb] using
      hvphKeccakExit_post_to_adapter sp0 spC ret parentPtr parentLen v20
        (0 : Word) (dwordAt claimedBytes 3) (dwordAt digest 3) vals
        thisPtr thisBytes parentBytes claimedBytes N rem F hspC hlen s hq

set_option maxRecDepth 8000 in
/-- Dword0-mismatch path in adapter shape. Cost `30+nH+nK`. Status `2`. -/
theorem header_validate_parent_hash_mismatch0_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_headers : headersCallPremise nH (H + 40) (0 : Word) thisPtr thisLen
      thisBytes claimedBytes claimedBytes
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes))
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + nH + nKeccak N rem) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn claimedBytes ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (2 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals
          parentBytes claimedBytes digest N rem F) := by
  intro digest out0 Amb
  have hmm := hvphMismatch0_spec_within nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    vals v20 thisBytes parentBytes claimedBytes N rem os F hF
    hspC hret h_headers hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h_ne
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hmm
  · unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · simpa [digest, Amb] using
      hvphKeccakExit_post_to_adapter sp0 spC ret parentPtr parentLen v20
        (2 : Word) (dwordAt claimedBytes 0) (dwordAt digest 0) vals
        thisPtr thisBytes parentBytes claimedBytes N rem F hspC hlen s hq

/-! ## Adapter-shaped extract-fail (`status = 1`). Cost `19+nH`. -/

/-- Extract-fail residual → `hvphPost ** claimedOwn`. -/
theorem hvphExtractFail_post_to_adapter
    (sp0 spC ret thisPtr parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12)) :
    ∀ s,
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        hvphFailG thisPtr thisBytes claimedOut parentLen) s →
      (hvphPost sp0 thisPtr parentPtr ret (1 : Word) vals thisBytes parentBytes **
        claimedOwn claimedOut) s := by
  intro s hq
  unfold hvphFailG at hq
  have hqTrail :
      ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word))) **
        (.x13 ↦ᵣ parentLen))) s := by
    xperm_hyp hq
  have hqOwn :
      ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word))) **
        regOwn .x13)) s :=
    sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
  unfold hvphPost
  simp only [regsAt_hvphSavedFrame, hspC] at hqOwn ⊢
  xperm_hyp hqOwn

set_option maxRecDepth 8000 in
/-- Extract-fail path in adapter shape. Cost `19+nH`. -/
theorem header_validate_parent_hash_extract_fail_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_nz : statusHdr ≠ (0 : Word))
    (h_headers : headersCallPremise nH (H + 40) statusHdr thisPtr thisLen
      thisBytes claimedBytes claimedOut
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (19 + nH) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn claimedBytes)
      (hvphPost sp0 thisPtr parentPtr ret (1 : Word) vals thisBytes parentBytes **
        claimedOwn claimedOut) := by
  have hfail := hvphExtractFail_spec_within nH sp0 spC ret thisPtr thisLen
    parentPtr parentLen statusHdr vals thisBytes parentBytes claimedBytes claimedOut
    hspC hret h_nz h_headers
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hfail
  · unfold hvphPre at hp
    simp only [regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · exact hvphExtractFail_post_to_adapter sp0 spC ret thisPtr parentPtr parentLen
      vals thisBytes parentBytes claimedOut hspC s hq

end EvmAsm.Codegen.HeaderValidateParentHashSpec
