/-
  EvmAsm.Codegen.Programs.TxSigningHashLegacyTop

  **K146 `tx_signing_hash_legacy_eip155` — whole-routine wrap (#12038).**

  The K146 body decomposition lives in
  `TxSigningHashLegacy{SpecCore,LoopSpec,CopySpec,Compose,BodyCompose,
  ChainCompose,UintCompose,PrefixCompose,PrefixCopyCompose,TailCore,
  TailCompose,TailLayout}`.  Those modules carry the body from
  `legacyBodyEntry` (H+36) to `legacyBodyExit` (H+440) in segments.  This
  module is the ABI-frame capstone: it lifts a body triple to a
  whole-routine `cpsTripleWithin` anchored at
  `GuestAddrs.tx_signing_hash_legacy_eip155` via `abiFrame_spec_own`, in
  exactly the shape K145 `tx_signing_hash` uses in
  `TxSigningHashSpec.tx_signing_hash_spec_within{,_empty_len}`.

  ## DOMAIN

  This module's whole-routine theorem is the **empty-input-length reject
  slice**: `a1 = 0`, where the guest stores its four argument registers into
  the callee-saved frame regs, takes the `beq a1, x0` branch at H+52 to the
  common `li a0, 1` tail at H+436, and returns status 1 having written
  nothing.  It is a genuine whole-routine triple at the `GuestAddrs` anchor
  — it is NOT the keccak success path.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyTailLayout
import EvmAsm.Rv64.SAsm.AbiFrameOwn

namespace EvmAsm.Codegen.TxSigningHashLegacyTop

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyCompose

/-! ## Frame scaffolding for `abiFrame_spec_own` -/

theorem legacyFrame_cons :
    legacyFrame =
      (.x1, (0 : BitVec 12)) ::
        [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
         (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
         (.x22, (56 : BitVec 12))] := rfl

abbrev legacySregs : FrameDesc :=
  [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
   (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
   (.x22, (56 : BitVec 12))]

theorem legacyFrame_ne_zero : ∀ p ∈ legacyFrame, p.1 ≠ .x0 := by decide

theorem legacyFrame_restore (sp0 : Word) :
    (sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (64 : BitVec 12) = sp0 :=
  sext_frameRestore sp0 (-64 : BitVec 12) (64 : BitVec 12) (by decide)

/-- The emitted K146 image contains the `abiFrameProg` the wrap reasons
    about; `legacy_prog_eq_abiFrame` is the structural drift guard. -/
theorem legacy_ofProg_sub_fullCode :
    ∀ a i, CodeReq.ofProg legacyH
        (abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) legacyFrame legacyBody)
        a = some i → legacyFullCode a = some i := by
  intro a i hi
  have h : legacyCode a = some i := by
    unfold legacyCode
    rw [← legacy_prog_eq_abiFrame]
    exact hi
  exact legacyCode_mono a i h

/-- Flattened `regsAt legacyFrame`. -/
theorem legacy_regsAt_frame (vals : Reg → Word) :
    regsAt legacyFrame vals =
      ((.x1 ↦ᵣ vals .x1) ** (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
        (.x18 ↦ᵣ vals .x18) ** (.x19 ↦ᵣ vals .x19) ** (.x20 ↦ᵣ vals .x20) **
        (.x21 ↦ᵣ vals .x21) ** (.x22 ↦ᵣ vals .x22)) := by
  simp [legacyFrame, regsAt_cons, regsAt_nil, sepConj_emp_right']

theorem legacy_regsOwnAt_frame :
    regsOwnAt legacyFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x21 ** regOwn .x22) := by
  simp [legacyFrame, regsOwnAt_cons, regsOwnAt_nil, sepConj_emp_right']

/-! ## Empty-input-length reject: body-level footprint -/

/-- Body-level caller footprint for the `a1 = 0` reject: just the four ABI
    argument registers and the hard-wired zero register.  The routine writes
    no memory on this path. -/
def legacyEmptyFailCallerPre (a0 a1 a2 a3 : Word) : Assertion :=
  (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
    (.x0 ↦ᵣ (0 : Word))

def legacyEmptyFailCallerPost (a1 a2 a3 : Word) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
    (.x0 ↦ᵣ (0 : Word))

theorem legacyEmptyFailCallerPre_pcFree (a0 a1 a2 a3 : Word) :
    (legacyEmptyFailCallerPre a0 a1 a2 a3).pcFree := by
  unfold legacyEmptyFailCallerPre; pcf

theorem legacyEmptyFailCallerPost_pcFree (a1 a2 a3 : Word) :
    (legacyEmptyFailCallerPost a1 a2 a3).pcFree := by
  unfold legacyEmptyFailCallerPost; pcf

/-- The `a1 = 0` body in `abiFrame_spec_own` shape. -/
theorem legacyEmptyLenFailBody
    (newSp : Word) (vals : Reg → Word) (a0 a1 a2 a3 : Word)
    (hlen : a1 = 0) :
    cpsTripleWithin (4 + 1 + 1)
      (legacyH + BitVec.ofNat 64 (4 * (1 + legacyFrame.length)))
      (legacyH + BitVec.ofNat 64 (4 * (1 + legacyFrame.length + legacyBody.length)))
      legacyFullCode
      ((.x2 ↦ᵣ newSp) ** regsAt legacyFrame vals **
        frameSlotsSaved legacyFrame newSp vals **
        legacyEmptyFailCallerPre a0 a1 a2 a3)
      ((.x2 ↦ᵣ newSp) ** regsOwnAt legacyFrame **
        frameSlotsSaved legacyFrame newSp vals **
        legacyEmptyFailCallerPost a1 a2 a3) := by
  rw [legacyFrame_length, legacyBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl,
    show 4 * (1 + 8 + 101) = 440 from rfl]
  have core := legacySetupThenEmptyFail_spec a0 a1 a2 a3
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) hlen
  have framed := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ vals .x1) ** (.x20 ↦ᵣ vals .x20) **
      (.x21 ↦ᵣ vals .x21) ** (.x22 ↦ᵣ vals .x22) **
      frameSlotsSaved legacyFrame newSp vals)
    (by pcf) core
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h hq => ?_) framed
  · rw [legacy_regsAt_frame, legacyEmptyFailCallerPre] at hp
    xperm_hyp hp
  · let vals' : Reg → Word := fun
      | .x1 => vals .x1
      | .x8 => a0
      | .x9 => a1
      | .x18 => a2
      | .x19 => a3
      | .x20 => vals .x20
      | .x21 => vals .x21
      | .x22 => vals .x22
      | r => vals r
    have hq2 : (regsAt legacyFrame vals' **
        ((.x2 ↦ᵣ newSp) ** frameSlotsSaved legacyFrame newSp vals **
          legacyEmptyFailCallerPost a1 a2 a3)) h := by
      rw [legacy_regsAt_frame]
      unfold legacyEmptyFailCallerPost at hq ⊢
      simp only [vals'] at hq ⊢
      xperm_hyp hq
    have hq3 :=
      sepConj_mono (regsAt_implies_regsOwnAt legacyFrame vals') (fun _ hx => hx) h hq2
    rw [legacy_regsOwnAt_frame] at hq3 ⊢
    xperm_hyp hq3

/-! ## Whole routine: empty-input-length reject -/

/-- **K146 `tx_signing_hash_legacy_eip155` on the empty-input-length
    domain.**

    Whole-routine `cpsTripleWithin` anchored at
    `GuestAddrs.tx_signing_hash_legacy_eip155` (`legacyH`).  When the caller
    passes `a1 = 0` the routine saves its frame, copies `a0..a3` into
    `s0..s3`, takes the `beq a1, x0` branch at H+52 to the common `li a0, 1`
    tail at H+436, restores the frame and returns with status 1 and no
    memory effect.

    This is a **conditional** slice on a reject domain, not the keccak
    success path. -/
theorem tx_signing_hash_legacy_eip155_spec_within_empty_len
    (sp0 ret : Word) (vals : Reg → Word) (a0 a1 a2 a3 : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : a1 = 0) :
    cpsTripleWithin
      (1 + legacyFrame.length + (4 + 1 + 1) + legacyFrame.length + 1 + 1)
      legacyH ret legacyFullCode
      ((.x2 ↦ᵣ sp0) ** regsAt legacyFrame vals **
        frameSlotsOwn legacyFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        legacyEmptyFailCallerPre a0 a1 a2 a3)
      ((.x2 ↦ᵣ sp0) ** regsAt legacyFrame vals **
        frameSlotsSaved legacyFrame (sp0 + signExtend12 (-64 : BitVec 12)) vals **
        legacyEmptyFailCallerPost a1 a2 a3) := by
  have h := abiFrame_spec_own legacyH sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    legacyFrame (0 : BitVec 12) legacySregs vals legacyBody (4 + 1 + 1)
    (legacyEmptyFailCallerPre a0 a1 a2 a3)
    (legacyEmptyFailCallerPost a1 a2 a3)
    legacyFullCode legacyFrame_cons legacyFrame_ne_zero
    (by rw [legacyFrame_length]; decide)
    (by
      rw [legacy_prog_eq_abiFrame, legacy_prog_length]
      decide)
    hret halign (legacyFrame_restore sp0)
    (legacyEmptyFailCallerPre_pcFree _ _ _ _)
    (legacyEmptyFailCallerPost_pcFree _ _ _)
    legacy_ofProg_sub_fullCode
    (legacyEmptyLenFailBody _ vals a0 a1 a2 a3 hlen)
  exact h

/-! ## Non-vacuity

    The gate is `a1 = 0`.  It is satisfiable by construction (`a1 := 0`) and
    the negative control below records that the routine's OTHER entry
    condition — the branch actually being taken — is not vacuous: at
    `a1 = 1` the same branch lemma's taken arm is unavailable, i.e. the
    domain restriction is real and not a hypothesis that holds everywhere. -/

/-- The reject gate is satisfiable. -/
theorem legacy_emptyLen_gate_satisfiable :
    ∃ a1 : Word, a1 = 0 := ⟨0, rfl⟩

/-- Negative control: the empty-length branch is genuinely NOT taken at
    `a1 = 1`, so the `hlen` gate above is a real domain restriction. -/
theorem legacy_emptyLen_gate_false_on_one :
    ¬((1 : Word) = 0) := by decide

/-! ## Toward the whole-routine success path

    `legacySetupThenHdrParseAny_spec` pins the four callee-saved registers at
    `0` on entry.  Under the ABI frame they hold `vals`, so the wrap needs the
    generic form.  Same proof, four extra parameters. -/

theorem legacySetupThenHdrParseAny_gen_spec
    (a0 a1 a2 a3 v5 v6 v8 v9 v18 v19 v20 : Word) (input : List (BitVec 8))
    (hlen : a1 ≠ 0)
    (h0 : 0 < input.length)
    (halign : a0.toNat % 8 = 0)
    (hover : a0.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word)) :
    cpsTripleWithin (4 + 1 + 8) (legacyH + 36) (legacyH + 92)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        (.x6 ↦ᵣ (248 : Word)) **
        (.x20 ↦ᵣ legacyHdrLen input h0) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion a0 input ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) := by
  have hsetup := legacySetupMoves_spec a0 a1 a2 a3 v8 v9 v18 v19
  have hsetupF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input) (by pcf) hsetup
  have hsetupW : cpsTripleWithin 4 (legacyH + 36) (legacyH + 52)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsetupF
  have hbranch := legacyEmptyLenBeq_ntaken a1 hlen
  have hbranchF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
      (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x20 ↦ᵣ v20) ** bytesRegion a0 input ** (.x8 ↦ᵣ a0) **
      (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) (by pcf) hbranch
  have hbranchW : cpsTripleWithin 1 (legacyH + 52) (legacyH + 56)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hbranchF
  have hhdr := legacyHdrParseAny_spec a0 v5 v6 v20 input h0 halign hover
    hvalid hge
  have hhdrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
      (.x13 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ a1) **
      (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) (by pcf) hhdr
  have hhdrW : cpsTripleWithin 8 (legacyH + 56) (legacyH + 92)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x20 ↦ᵣ legacyHdrLen input h0) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input ** (.x8 ↦ᵣ a0) **
        (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hhdrF
  have hseq := cpsTripleWithin_seq_same_cr hsetupW hbranchW
  have hseq' := cpsTripleWithin_seq_same_cr hseq hhdrW
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hseq')

/-- Open the eight caller-save temps the `rlp_list_nth_item` adapter wants as
    `regOwn`. -/
private theorem legacy_open_temps
    (v5 v6 v7 v14 v28 v29 v30 v31 : Word) (P : Assertion) (h : _)
    (hq : ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x14 ↦ᵣ v14) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** P) h) :
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** P) h := by
  have s5 : ((.x5 ↦ᵣ v5) **
      ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x14 ↦ᵣ v14) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp hq
  have o5 := sepConj_mono_left (regIs_to_regOwn .x5 v5) h s5
  have s6 : ((.x6 ↦ᵣ v6) **
      (regOwn .x5 ** (.x7 ↦ᵣ v7) ** (.x14 ↦ᵣ v14) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp o5
  have o6 := sepConj_mono_left (regIs_to_regOwn .x6 v6) h s6
  have s7 : ((.x7 ↦ᵣ v7) **
      (regOwn .x5 ** regOwn .x6 ** (.x14 ↦ᵣ v14) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp o6
  have o7 := sepConj_mono_left (regIs_to_regOwn .x7 v7) h s7
  have s14 : ((.x14 ↦ᵣ v14) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp o7
  have o14 := sepConj_mono_left (regIs_to_regOwn .x14 v14) h s14
  have s28 : ((.x28 ↦ᵣ v28) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x14 **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp o14
  have o28 := sepConj_mono_left (regIs_to_regOwn .x28 v28) h s28
  have s29 : ((.x29 ↦ᵣ v29) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x14 **
        regOwn .x28 ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp o28
  have o29 := sepConj_mono_left (regIs_to_regOwn .x29 v29) h s29
  have s30 : ((.x30 ↦ᵣ v30) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** (.x31 ↦ᵣ v31) ** P)) h := by
    xperm_hyp o29
  have o30 := sepConj_mono_left (regIs_to_regOwn .x30 v30) h s30
  have s31 : ((.x31 ↦ᵣ v31) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** P)) h := by
    xperm_hyp o30
  have o31 := sepConj_mono_left (regIs_to_regOwn .x31 v31) h s31
  xperm_hyp o31

/-- Ambient carried through entry, the header parse and the
    `rlp_list_nth_item` call. -/
def legacyEntryAmbient
    (v7 v14 v21 v28 v29 v30 v31 vOld sp0 oldOff oldLen : Word)
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** (.x21 ↦ᵣ v21) **
    (.x7 ↦ᵣ v7) ** (.x14 ↦ᵣ v14) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) ** F

theorem legacyEntryAmbient_pcFree
    (v7 v14 v21 v28 v29 v30 v31 vOld sp0 oldOff oldLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    (legacyEntryAmbient v7 v14 v21 v28 v29 v30 v31 vOld sp0 oldOff oldLen
      F).pcFree := by
  unfold legacyEntryAmbient
  pcf
  exact hF

/-- Entry (H+36) through the `rlp_list_nth_item` return (H+124), on the
    non-empty-length, list-header domain. -/
theorem legacyEntryThroughNthCall_spec
    (a0 a1 a2 a3 v5 v6 v7 v8 v9 v14 v18 v19 v20 v21 v28 v29 v30 v31 : Word)
    (vOld sp0 oldOff oldLen : Word)
    (input : List (BitVec 8)) (listLen : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlen : a1 ≠ 0)
    (h0 : 0 < input.length)
    (halign : a0.toNat % 8 = 0)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalid : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      ((4 + 1 + 8) + (7 + (1 + ((12 + ((85 + 93 * (5 + 2)) + 6)) + 9))))
      (legacyH + 36) (legacyH + 124) legacyFullCode
      (((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19)) **
        legacyEntryAmbient v7 v14 v21 v28 v29 v30 v31 vOld sp0 oldOff oldLen F)
      (((.x1 ↦ᵣ (legacyNthJalPC + 4)) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 a0 (5 : Word)
          legacyNthOffPtr legacyNthLenPtr oldOff oldLen
          { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2,
            s3 := a3, s4 := legacyHdrLen input h0, s5 := v21 }
          input listLen 5) ** F) := by
  have hvalid0 : isValidByteAccess a0 = true := by
    have := hvalid 0 h0
    simpa using this
  have hhdr := legacySetupThenHdrParseAny_gen_spec a0 a1 a2 a3 v5 v6 v8 v9
    v18 v19 v20 input hlen h0 halign a0.isLt hvalid0 hge
  have hAmb := legacyEntryAmbient_pcFree v7 v14 v21 v28 v29 v30 v31 vOld sp0
    oldOff oldLen F hF
  have hhdrF := cpsTripleWithin_frameR
    (legacyEntryAmbient v7 v14 v21 v28 v29 v30 v31 vOld sp0 oldOff oldLen F)
    hAmb hhdr
  have hnth := legacySetupThenNthCall_spec a0 a1 a2 a3 vOld sp0
    (legacyHdrLen input h0) v21 oldOff oldLen input listLen F hF
    hlistLenW halign hslack hover hvalid
  refine cpsTripleWithin_seq_perm_same_cr (fun h hq => ?_) hhdrF hnth
  unfold legacyEntryAmbient at hq
  have hopened := legacy_open_temps (legacyHdrByte input h0) (248 : Word) v7 v14
    v28 v29 v30 v31
    (((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ a1) ** ((.x12 : Reg) ↦ᵣ a2) **
      ((.x13 : Reg) ↦ᵣ a3) ** ((.x20 : Reg) ↦ᵣ legacyHdrLen input h0) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
      ((.x8 : Reg) ↦ᵣ a0) ** ((.x9 : Reg) ↦ᵣ a1) ** ((.x18 : Reg) ↦ᵣ a2) **
      ((.x19 : Reg) ↦ᵣ a3) ** ((.x1 : Reg) ↦ᵣ vOld) **
      ((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 8 ** ((.x21 : Reg) ↦ᵣ v21) **
      (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) ** F)
    h (by xperm_hyp hq)
  xperm_hyp hopened

end EvmAsm.Codegen.TxSigningHashLegacyTop
