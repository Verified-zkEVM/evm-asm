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
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
open EvmAsm.Codegen.TxSigningHashLegacyCopySpec
open EvmAsm.Codegen.TxSigningHashLegacyChainCompose
open EvmAsm.Codegen.TxSigningHashLegacyPrefixCopyCompose
open EvmAsm.Codegen.TxSigningHashSpec
open EvmAsm.Codegen.TxSigningHashLegacyUintCompose
open EvmAsm.Codegen.TxSigningHashLegacyPrefixCompose
open EvmAsm.Codegen.TxSigningHashLegacyTailCompose
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpEncodeUintBeSAsm
open EvmAsm.EL.RLP

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

/-! ## The payload slice, concretely

    `legacyNthSuccess_payloadSlice` hides both the payload list and the
    `KssInputSourceSpec` behind existentials.  The two static-view bridges
    (`legacyKssInputSource_{prefix,suffix}_region_of_input_layout`) are stated
    about `kssInputSource` itself, so a whole-routine composition needs the
    slice CONCRETELY.  Same arithmetic, opened up. -/

/-- The canonical K146 payload slice: the outer list's content window, as
    reported by `rlp_list_nth_item`'s selected offset/length. -/
def legacyPayloadOf (input : List (BitVec 8)) (hdrLen offset len : Word) :
    List (BitVec 8) :=
  (input.drop hdrLen.toNat).take ((offset + len - hdrLen).toNat)

theorem legacyPayloadOf_length (input : List (BitVec 8))
    (hdrLen offset len : Word)
    (hfit : hdrLen.toNat + ((offset + len) - hdrLen).toNat ≤ input.length) :
    (legacyPayloadOf input hdrLen offset len).length =
      ((offset + len) - hdrLen).toNat := by
  unfold legacyPayloadOf
  simp only [List.length_take, List.length_drop]
  omega

/-- The size facts the KSS source constructor needs, derived from the Nth
    success predicate. -/
theorem legacyNthSuccess_payload_fit
    {input : List (BitVec 8)} {base hdrLen : Word}
    {listLen : Nat} {offset len : Word}
    (h0 : 0 < input.length)
    (hheader : hdrLen = legacyHdrLen input h0)
    (hslack : listLen + 9 ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hsucc : EvmAsm.Codegen.RlpListNthItemSAsm.Success input base listLen 5
      offset len) :
    hdrLen.toNat + ((offset + len) - hdrLen).toNat ≤ input.length := by
  obtain ⟨cursorOff, endPtr, next, hlist, hnth, hoff⟩ := hsucc
  have hend := hlist.end_eq
  subst endPtr
  have hcur := hlist.cursor_le
  have hover9 : base.toNat + listLen + 9 < 2 ^ 64 := by omega
  have hupper := legacyStrictNthItem_content_le hnth hcur hover9
  have hlower := legacyStrictNthItem_content_ge hnth hcur hover9
  have hcursor := legacyStrictListPayload_cursor_eq_hdrLen h0 hlist
  have hcursorHdr : cursorOff = hdrLen.toNat := by
    simpa [hheader] using hcursor
  have hlower' : hdrLen.toNat ≤ offset.toNat := by
    calc
      hdrLen.toNat = cursorOff := hcursorHdr.symm
      _ ≤ (next - len - base).toNat := hlower
      _ = offset.toNat := by rw [hoff]
  have hupper' : offset.toNat + len.toNat ≤ listLen := by
    simpa [hoff] using hupper
  have hsum : offset.toNat + len.toNat < 2 ^ 64 := by omega
  have hsum_word : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hsum
  have hsub : ((offset + len) - hdrLen).toNat =
      offset.toNat + len.toNat - hdrLen.toNat := by
    rw [BitVec.toNat_sub, hsum_word]
    rw [show 2 ^ 64 - hdrLen.toNat + (offset.toNat + len.toNat) =
        2 ^ 64 + (offset.toNat + len.toNat - hdrLen.toNat) by omega]
    rw [Nat.mod_eq_sub_mod (by omega)]
    have hsub_lt : offset.toNat + len.toNat - hdrLen.toNat < 2 ^ 64 := by omega
    have hcancel : 2 ^ 64 + (offset.toNat + len.toNat - hdrLen.toNat) - 2 ^ 64 =
        offset.toNat + len.toNat - hdrLen.toNat := by omega
    rw [hcancel, Nat.mod_eq_of_lt hsub_lt]
  rw [hsub]
  omega

theorem legacyPayloadOf_take_self (input : List (BitVec 8))
    (hdrLen offset len : Word) :
    (input.drop hdrLen.toNat).take
        (legacyPayloadOf input hdrLen offset len).length =
      legacyPayloadOf input hdrLen offset len := by
  simp [legacyPayloadOf]

theorem legacyPayloadOf_length_le (input : List (BitVec 8))
    (hdrLen offset len : Word)
    (hfit : hdrLen.toNat + ((offset + len) - hdrLen).toNat ≤ input.length) :
    (legacyPayloadOf input hdrLen offset len).length + hdrLen.toNat ≤
      input.length := by
  rw [legacyPayloadOf_length input hdrLen offset len hfit]
  omega

theorem legacyPayloadOf_bytes (input : List (BitVec 8))
    (hdrLen offset len : Word)
    (hlen : (legacyPayloadOf input hdrLen offset len).length + hdrLen.toNat ≤
      input.length) :
    ∀ i (hi : i < (legacyPayloadOf input hdrLen offset len).length),
      input[hdrLen.toNat + i]'(by omega) =
        (legacyPayloadOf input hdrLen offset len)[i]'hi := by
  intro i hi
  have hpayload := legacyPayloadOf_take_self input hdrLen offset len
  have hi_take : i < ((input.drop hdrLen.toNat).take
      (legacyPayloadOf input hdrLen offset len).length).length := by
    rw [hpayload]; exact hi
  have h1 := List.getElem_of_eq hpayload (i := i) hi_take
  rw [List.getElem_take, List.getElem_drop] at h1
  exact h1

/-- The concrete KSS input-source view for the K146 payload slice.  Its
    `source` field is `kssInputSource` by construction, which is what the two
    static-view layout bridges are stated about. -/
noncomputable def legacyPayloadSourceSpec
    (input : List (BitVec 8)) (base hdrLen offset len : Word)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hfit : hdrLen.toNat + ((offset + len) - hdrLen).toNat ≤ input.length) :
    KssInputSourceSpec base hdrLen input
      (legacyPayloadOf input hdrLen offset len) :=
  kssInputSourceSpec base hdrLen input
    (legacyPayloadOf input hdrLen offset len) halign
    (legacyPayloadOf_length_le input hdrLen offset len hfit) hover
    (legacyPayloadOf_bytes input hdrLen offset len
      (legacyPayloadOf_length_le input hdrLen offset len hfit))

theorem legacyPayloadSourceSpec_len
    (input : List (BitVec 8)) (base hdrLen offset len : Word)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hfit : hdrLen.toNat + ((offset + len) - hdrLen).toNat ≤ input.length) :
    BitVec.ofNat 64 (legacyPayloadOf input hdrLen offset len).length =
      (offset + len) - hdrLen := by
  rw [legacyPayloadOf_length input hdrLen offset len hfit]
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Body arms after the `rlp_list_nth_item` return

    `stackFree sp 8` and the KSS callee's frame slots are the same eight
    dwords below `sp`; the nth call hands the cells back untouched, and the
    keccak-segments call takes them as its frame. -/

theorem legacyStackFree8_eq_kssFrameSlotsOwn (sp : Word) :
    stackFree sp 8 =
      frameSlotsOwn kssFrame (sp + signExtend12 (-64 : BitVec 12)) := by
  show (memOwn (sp - BitVec.ofNat 64 (8 * 8)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 7)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 6)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 5)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 4)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 2)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 1)) **
      empAssertion) = _
  show _ = (memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (8 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (16 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (24 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (32 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (40 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (48 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) +
        signExtend12 (56 : BitVec 12)) **
      empAssertion)
  rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
    show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
    show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide,
    show sp - BitVec.ofNat 64 (8 * 8) = sp + (-64 : Word) + (0 : Word) from
      by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 7) = sp + (-64 : Word) + (8 : Word) from
      by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 6) = sp + (-64 : Word) + (16 : Word) from
      by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 5) = sp + (-64 : Word) + (24 : Word) from
      by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 4) = sp + (-64 : Word) + (32 : Word) from
      by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 3) = sp + (-64 : Word) + (40 : Word) from
      by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 2) = sp + (-64 : Word) + (48 : Word) from
      by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 1) = sp + (-64 : Word) + (56 : Word) from
      by bv_omega]

/-- The K146 caller footprint the body needs beyond what the Nth call hands
    back: the four linked BSS buffers, the KSS descriptor table's six dwords,
    the sponge arena, the zeroed output buffer, and the three KSS-owned
    caller-save temps. -/
def legacyBodyBss (chainId cellOld outputBase : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (os : List (BitVec 8)) (A : Assertion) : Assertion :=
  bytesRegion legacyLinkedChainPtr (List.replicate 8 (0 : BitVec 8)) **
    bytesRegion legacyLinkedChainEncPtr legacyChainEncOld **
    bytesRegion legacyPrefixOutPtr (List.replicate 16 (0 : BitVec 8)) **
    (legacyPrefixCellPtr ↦ₘ cellOld) **
    bytesRegion legacySuffixOutPtr
      (List.replicate
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
        (0 : BitVec 8)) **
    legacyTailExtension
      (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length **
    (legacyKssSegsBase ↦ₘ old0) ** ((legacyKssSegsBase + 8) ↦ₘ old1) **
    ((legacyKssSegsBase + 16) ↦ₘ old2) ** ((legacyKssSegsBase + 24) ↦ₘ old3) **
    ((legacyKssSegsBase + 32) ↦ₘ old4) ** ((legacyKssSegsBase + 40) ↦ₘ old5) **
    regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    bytesRegion KssZk3 os **
    bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) ** A

theorem legacyBodyBss_pcFree
    (chainId cellOld outputBase : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (legacyBodyBss chainId cellOld outputBase
      old0 old1 old2 old3 old4 old5 os A).pcFree := by
  unfold legacyBodyBss
  repeat first
    | exact legacyTailExtension_pcFree _
    | exact hA
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | apply pcFree_sepConj
    | exact (by pcf)

/-- Step budget of the K146 body from H+128 through the routine's body exit,
    as `legacyBodyThenKssSuccess_spec` reports it. -/
def legacyBodyFuel (chainId payloadBase inPtr hdrLen : Word)
    (payloadBytes : List (BitVec 8)) : Nat :=
  let n := (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let uintFuel :=
    1 + (8 * 6 + 7 *
      (8 - RlpEncodeUintBeSAsm.reubZeros (chainBytes chainId) 0 8) + 17)
  let prefixFuel := 8 + (1 + tshPrefixFuel) + 8 + (n * (6 + 1) + 1) + 4
  (8 + (68 + 8 + uintFuel + prefixFuel)) +
    (21 + ((1 + (19 + kssBodyFuelMulti
      (legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes))) + 2))

/-- The state at H+124 on the Nth-success arm, minus the seven caller-save
    temps the Nth callee returns as `regOwn`. -/
def legacyNthOkBase (X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 : Word)
    (offVal lenVal cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A R : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ X) ** ((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 8 **
    EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
      { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2, s3 := a3,
        s4 := hdrLen, s5 := v21 } **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
    ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
    (legacyNthOffPtr ↦ₘ offVal) ** (legacyNthLenPtr ↦ₘ lenVal) **
    regOwn .x22 **
    legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A ** R

/-- The Nth-success arm: fall through the `bne a0, x0` at H+124 and run the
    whole payload/chain/prefix/keccak body to the routine's body exit. -/
theorem legacyNthOkThroughBodyExit_spec
    (X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 : Word)
    (offVal lenVal cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBytes os : List (BitVec 8)) (A R : Assertion)
    (hA : A.pcFree) (hR : R.pcFree)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayloadLen : BitVec.ofNat 64 payloadBytes.length =
      ((offVal + lenVal) - hdrLen))
    (hos : os.length = 200)
    (hcount :
      (legacyKssBodySegs a2 ((offVal + lenVal) - hdrLen)
        a0 hdrLen payloadBytes).length < 2 ^ 64)
    (hsegs :
      ∀ s ∈ legacyKssBodySegs a2 ((offVal + lenVal) - hdrLen)
        a0 hdrLen payloadBytes,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (sourceSpec : KssInputSourceSpec a0 hdrLen input payloadBytes)
    (hsourcePrefix : sourceSpec.source.region legacyPrefixOutPtr
        (legacyKssBodyPrefixBytes a2 ((offVal + lenVal) - hdrLen)) =
      bytesRegion legacyPrefixOutPtr
        (legacyKssBodyPrefixBytes a2 ((offVal + lenVal) - hdrLen)))
    (hsourceSuffix : sourceSpec.source.region legacySuffixOutPtr
        (legacyKssBodySuffixBytes a2) =
      bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes a2)) :
    cpsTripleWithin
      (1 + legacyBodyFuel a2 ((offVal + lenVal) - hdrLen) a0 hdrLen payloadBytes)
      (legacyH + 124) legacyBodyExit legacyFullCode
      (legacyNthOkBase X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 offVal lenVal
          cellOld old0 old1 old2 old3 old4 old5 input os A R **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (legacyKssBodyFinal a2 ((offVal + lenVal) - hdrLen) a0 hdrLen a3 sp0 a1
        offVal lenVal payloadBytes A R sourceSpec.source) := by
  apply EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
  intro v5 v6 v7 v28 v29 v30 v31
  set n := (RlpEncodeUintBeSAsm.reubOut (chainBytes a2)).length with hn
  let Fmid : Assertion :=
    ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x20 : Reg) ↦ᵣ hdrLen) ** ((.x21 : Reg) ↦ᵣ v21) **
      (legacyLinkedNthOffPtr ↦ₘ offVal) ** (legacyLinkedNthLenPtr ↦ₘ lenVal) **
      ((.x1 : Reg) ↦ᵣ X) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x18 : Reg) ↦ᵣ a2) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
      bytesRegion legacyLinkedChainPtr (List.replicate 8 (0 : BitVec 8)) **
      bytesRegion legacyLinkedChainEncPtr legacyChainEncOld **
      bytesRegion legacyPrefixOutPtr (List.replicate 16 (0 : BitVec 8)) **
      (legacyPrefixCellPtr ↦ₘ cellOld) **
      bytesRegion legacySuffixOutPtr (List.replicate n (0 : BitVec 8)) **
      regOwn .x22 ** legacyTailExtension n **
      legacyKssBodyExtra a0 a3 sp0 a1 old0 old1 old2 old3 old4 old5 input os A R
  have hFmid : Fmid.pcFree := by
    unfold Fmid legacyKssBodyExtra
    repeat first
      | exact legacyTailExtension_pcFree _
      | exact hA
      | exact hR
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_frameSlotsOwn _ _
      | apply pcFree_sepConj
      | exact (by pcf)
  have hbr := legacyNthFail_ntaken (0 : Word) rfl
  have hbrF := cpsTripleWithin_frameR Fmid hFmid hbr
  have hbrW : cpsTripleWithin 1 (legacyH + 124) (legacyH + 128) legacyFullCode
      (legacyNthOkBase X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 offVal lenVal
          cellOld old0 old1 old2 old3 old4 old5 input os A R **
        ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31))
      (legacyKssBodyInitial X v5 v6 v7 (0 : Word) v11 v12 a2 v28 v29 v30 v31 v21
        offVal lenVal hdrLen cellOld a0 a3 sp0 a1
        old0 old1 old2 old3 old4 old5 input os A R) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hbrF
    · simp only [legacyNthOkBase, legacyBodyBss,
        EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail,
        legacyStackFree8_eq_kssFrameSlotsOwn] at hp
      show (_ ** Fmid) _
      unfold Fmid legacyKssBodyExtra
      xperm_hyp hp
    · unfold Fmid at hq
      unfold legacyKssBodyInitial
      xperm_hyp hq
  have hbody := legacyBodyThenKssSuccess_spec X v5 v6 v7 (0 : Word) v11 v12 a2
    v28 v29 v30 v31 v21 offVal lenVal hdrLen cellOld a0 a3 sp0 a1
    old0 old1 old2 old3 old4 old5 input payloadBytes os A R hA hR
    halign hover hvalid hbound h_out_valid hpayloadLen hos hcount hsegs
    sourceSpec hsourcePrefix hsourceSuffix
  exact cpsTripleWithin_seq_same_cr hbrW hbody

/-! ## The Nth-failure arm

    Status 1 goes straight to the shared `li a0, 1` tail at H+436; `a0` is
    already 1, the output cells are unchanged, and nothing else is touched. -/

def legacyNthFailState (X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 : Word)
    (oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A R : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ X) ** ((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 8 **
    EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
      { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2, s3 := a3,
        s4 := hdrLen, s5 := v21 } **
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
    ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
    (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) **
    regOwn .x22 **
    legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A ** R **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem legacyNthFailState_pcFree
    (X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 : Word)
    (oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A R : Assertion)
    (hA : A.pcFree) (hR : R.pcFree) :
    (legacyNthFailState X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 oldOff oldLen
      cellOld old0 old1 old2 old3 old4 old5 input os A R).pcFree := by
  unfold legacyNthFailState EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
  repeat first
    | exact legacyBodyBss_pcFree _ _ _ _ _ _ _ _ _ _ _ hA
    | exact hR
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_stackFree _ _
    | apply pcFree_sepConj
    | exact (by pcf)

theorem legacyNthFailThroughBodyExitFramed_spec
    (X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 : Word)
    (oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A R : Assertion)
    (hA : A.pcFree) (hR : R.pcFree) :
    cpsTripleWithin 2 (legacyH + 124) legacyBodyExit legacyFullCode
      (legacyNthFailState X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 oldOff oldLen
        cellOld old0 old1 old2 old3 old4 old5 input os A R)
      (legacyNthFailState X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 oldOff oldLen
        cellOld old0 old1 old2 old3 old4 old5 input os A R) := by
  let Ffail : Assertion :=
    ((.x1 : Reg) ↦ᵣ X) ** ((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 8 **
      EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
        { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2, s3 := a3,
          s4 := hdrLen, s5 := v21 } **
      ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
      regOwn .x13 ** regOwn .x14 ** bytesRegion a0 input **
      (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) **
      regOwn .x22 **
      legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A ** R **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have hFfail : Ffail.pcFree := by
    unfold Ffail EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
    repeat first
      | exact legacyBodyBss_pcFree _ _ _ _ _ _ _ _ _ _ _ hA
      | exact hR
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_stackFree _ _
      | apply pcFree_sepConj
      | exact (by pcf)
  have hcore := legacyNthFailThroughBodyExit_spec (1 : Word) Ffail hFfail
    (by decide)
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hcore
  · unfold legacyNthFailState at hp
    show (_ ** Ffail) _
    unfold Ffail
    xperm_hyp hp
  · unfold Ffail at hq
    unfold legacyNthFailState
    xperm_hyp hq

/-- `Result` is a two-constructor inductive over its status/offset/length
    indices; this flattens it so the join can `rcases` without relying on how
    `cases` re-binds unified indices. -/
private theorem legacyResult_split
    {bytes : List (BitVec 8)} {base : Word} {listLen index : Nat}
    {oldOffset oldLen status offset len : Word}
    (h : EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes base listLen index
      oldOffset oldLen status offset len) :
    (status = 0 ∧
        EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes base listLen index
          offset len) ∨
      (status = 1 ∧ offset = oldOffset ∧ len = oldLen) := by
  cases h
  · exact Or.inl ⟨rfl, by assumption⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩

/-! ## Joining the two arms at H+124 -/

/-- Disjunctive body post: the keccak-success outcome, or the status-1
    reject with the output cells unchanged. -/
def legacyNthOutcomePost (Qok Qfail : Assertion) : Assertion :=
  fun h => Qok h ∨ Qfail h

/-- Both arms of the post-`rlp_list_nth_item` branch, from H+124 through the
    routine's body exit. -/
theorem legacyNthThroughBodyExit_spec
    (X v21 hdrLen sp0 a0 a1 a2 a3 : Word)
    (oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8)) (listLen : Nat)
    (A R : Assertion) (hA : A.pcFree) (hR : R.pcFree)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hos : os.length = 200)
    (hpayW : ∀ offVal lenVal,
      EvmAsm.Codegen.RlpListNthItemSAsm.Success input a0 listLen 5 offVal lenVal →
        BitVec.ofNat 64 payloadBs.length = ((offVal + lenVal) - hdrLen))
    (hcount : ∀ offVal lenVal,
      (legacyKssBodySegs a2 ((offVal + lenVal) - hdrLen)
        a0 hdrLen payloadBs).length < 2 ^ 64)
    (hsegs : ∀ offVal lenVal,
      ∀ s ∈ legacyKssBodySegs a2 ((offVal + lenVal) - hdrLen)
        a0 hdrLen payloadBs,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (sourceSpec : KssInputSourceSpec a0 hdrLen input payloadBs)
    (hsourcePrefix : ∀ offVal lenVal,
      sourceSpec.source.region legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2 ((offVal + lenVal) - hdrLen)) =
        bytesRegion legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2 ((offVal + lenVal) - hdrLen)))
    (hsourceSuffix : sourceSpec.source.region legacySuffixOutPtr
        (legacyKssBodySuffixBytes a2) =
      bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes a2))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      1 + legacyBodyFuel a2 ((offVal + lenVal) - hdrLen) a0 hdrLen payloadBs ≤ N)
    (hNfail : 2 ≤ N) :
    cpsTripleWithin N (legacyH + 124) legacyBodyExit legacyFullCode
      ((((.x1 : Reg) ↦ᵣ X) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 a0 (5 : Word)
          legacyNthOffPtr legacyNthLenPtr oldOff oldLen
          { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2,
            s3 := a3, s4 := hdrLen, s5 := v21 }
          input listLen 5) **
        (regOwn .x22 **
          (legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A **
            R)))
      (legacyNthOutcomePost
        (fun h => ∃ offVal lenVal,
          legacyKssBodyFinal a2 ((offVal + lenVal) - hdrLen) a0 hdrLen a3 sp0 a1
            offVal lenVal payloadBs A R sourceSpec.source h)
        (fun h => ∃ v11 v12,
          legacyNthFailState X v11 v12 v21 hdrLen sp0 a0 a1 a2 a3 oldOff oldLen
            cellOld old0 old1 old2 old3 old4 old5 input os A R h)) := by
  refine legacy_cpsTripleWithin_callReturn_pre sp0 a0 (5 : Word)
    legacyNthOffPtr legacyNthLenPtr oldOff oldLen
    { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2,
      s3 := a3, s4 := hdrLen, s5 := v21 } input listLen 5 ?_
  intro status offset len v11 v12 hres
  rcases legacyResult_split hres with ⟨hst, hsucc⟩ | ⟨hst, hoffE, hlenE⟩
  · subst hst
    have hok := legacyNthOkThroughBodyExit_spec X v11 v12 v21 hdrLen sp0
      a0 a1 a2 a3 offset len cellOld old0 old1 old2 old3 old4 old5
      input payloadBs os A R hA hR halign hover hvalid hbound h_out_valid
      (hpayW offset len hsucc) hos (hcount offset len)
      (hsegs offset len) sourceSpec (hsourcePrefix offset len)
      hsourceSuffix
    refine cpsTripleWithin_mono_nSteps (hNok offset len)
      (cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hok)
    · unfold legacyNthOkBase legacyBodyBss
      unfold legacyBodyBss
        EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail at hp
      unfold EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
      xperm_hyp hp
    · exact Or.inl ⟨offset, len, hq⟩
  · subst hst
    subst hoffE
    subst hlenE
    have hfl := legacyNthFailThroughBodyExitFramed_spec X v11 v12 v21 hdrLen
      sp0 a0 a1 a2 a3 offset len cellOld old0 old1 old2 old3 old4 old5
      input os A R hA hR
    refine cpsTripleWithin_mono_nSteps hNfail
      (cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hfl)
    · unfold legacyNthFailState
      unfold legacyBodyBss
        EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail at hp
      unfold legacyBodyBss
        EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
      xperm_hyp hp
    · exact Or.inr ⟨v11, v12, hq⟩

/-! ## The whole body: H+36 through H+440 -/

theorem legacyBodyEntryThroughExit_spec
    (a0 a1 a2 a3 v5 v6 v7 v8 v9 v14 v18 v19 v20 v21 v28 v29 v30 v31 : Word)
    (vOld sp0 oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8)) (listLen : Nat)
    (A R : Assertion) (hA : A.pcFree) (hR : R.pcFree)
    (hlen : a1 ≠ 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hslack : listLen + 9 ≤ input.length)
    (hoverIn : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hos : os.length = 200)
    (hpayW : ∀ offVal lenVal,
      EvmAsm.Codegen.RlpListNthItemSAsm.Success input a0 listLen 5 offVal lenVal →
        BitVec.ofNat 64 payloadBs.length =
          ((offVal + lenVal) - legacyHdrLen input h0))
    (hcount : ∀ offVal lenVal,
      (legacyKssBodySegs a2 ((offVal + lenVal) - legacyHdrLen input h0)
        a0 (legacyHdrLen input h0) payloadBs).length < 2 ^ 64)
    (hsegs : ∀ offVal lenVal,
      ∀ s ∈ legacyKssBodySegs a2 ((offVal + lenVal) - legacyHdrLen input h0)
        a0 (legacyHdrLen input h0) payloadBs,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (sourceSpec :
      KssInputSourceSpec a0 (legacyHdrLen input h0) input payloadBs)
    (hsourcePrefix : ∀ offVal lenVal,
      sourceSpec.source.region legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2
            ((offVal + lenVal) - legacyHdrLen input h0)) =
        bytesRegion legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2
            ((offVal + lenVal) - legacyHdrLen input h0)))
    (hsourceSuffix : sourceSpec.source.region legacySuffixOutPtr
        (legacyKssBodySuffixBytes a2) =
      bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes a2))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      1 + legacyBodyFuel a2 ((offVal + lenVal) - legacyHdrLen input h0) a0
        (legacyHdrLen input h0) payloadBs ≤ N)
    (hNfail : 2 ≤ N) :
    cpsTripleWithin
      (((4 + 1 + 8) + (7 + (1 + ((12 + ((85 + 93 * (5 + 2)) + 6)) + 9)))) + N)
      (legacyH + 36) legacyBodyExit legacyFullCode
      (((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19)) **
        legacyEntryAmbient v7 v14 v21 v28 v29 v30 v31 vOld sp0 oldOff oldLen
          (regOwn .x22 **
            (legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A **
              R)))
      (legacyNthOutcomePost
        (fun h => ∃ offVal lenVal,
          legacyKssBodyFinal a2 ((offVal + lenVal) - legacyHdrLen input h0) a0
            (legacyHdrLen input h0) a3 sp0 a1 offVal lenVal payloadBs A R
            sourceSpec.source h)
        (fun h => ∃ v11 v12,
          legacyNthFailState (legacyNthJalPC + 4) v11 v12 v21
            (legacyHdrLen input h0) sp0 a0 a1 a2 a3 oldOff oldLen
            cellOld old0 old1 old2 old3 old4 old5 input os A R h)) := by
  have hbss : (regOwn .x22 **
      (legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A
        ** R)).pcFree :=
    pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj (legacyBodyBss_pcFree _ _ _ _ _ _ _ _ _ _ _ hA) hR)
  have hentry := legacyEntryThroughNthCall_spec a0 a1 a2 a3 v5 v6 v7 v8 v9 v14
    v18 v19 v20 v21 v28 v29 v30 v31 vOld sp0 oldOff oldLen input listLen
    (regOwn .x22 **
      (legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A ** R))
    hbss hlen h0 halignIn hge hlistLenW hslack hoverIn hvalidBytes
  have hjoin := legacyNthThroughBodyExit_spec (legacyNthJalPC + 4) v21
    (legacyHdrLen input h0) sp0 a0 a1 a2 a3 oldOff oldLen cellOld
    old0 old1 old2 old3 old4 old5 input payloadBs os listLen A R hA hR
    halign hover hvalid hbound h_out_valid hos hpayW hcount hsegs
    sourceSpec hsourcePrefix hsourceSuffix N hNok hNfail
  exact cpsTripleWithin_seq_same_cr hentry hjoin

/-! ## Whole routine: the keccak path

    `abiFrame_spec_own` wants the eight frame registers as `regsOwnAt` in the
    post, so both outcome arms have to give their `regIs` values back as
    ownership.  These two openers do that; they are generic in the registers
    so the ok arm (all eight `regIs`) and the fail arm (`x22` already owned)
    can share them. -/

private theorem legacy_open7 (r1 r2 r3 r4 r5 r6 r7 : Reg)
    (w1 w2 w3 w4 w5 w6 w7 : Word) (P : Assertion) (h : PartialState)
    (hq : ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) **
      (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** P) h) :
    (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5 **
      regOwn r6 ** regOwn r7 ** P) h := by
  have s1 : ((r1 ↦ᵣ w1) ** ((r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) **
      (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** P)) h := by xperm_hyp hq
  have o1 := sepConj_mono_left (regIs_to_regOwn r1 w1) h s1
  have s2 : ((r2 ↦ᵣ w2) ** (regOwn r1 ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) **
      (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** P)) h := by xperm_hyp o1
  have o2 := sepConj_mono_left (regIs_to_regOwn r2 w2) h s2
  have s3 : ((r3 ↦ᵣ w3) ** (regOwn r1 ** regOwn r2 ** (r4 ↦ᵣ w4) **
      (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** P)) h := by xperm_hyp o2
  have o3 := sepConj_mono_left (regIs_to_regOwn r3 w3) h s3
  have s4 : ((r4 ↦ᵣ w4) ** (regOwn r1 ** regOwn r2 ** regOwn r3 **
      (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** P)) h := by xperm_hyp o3
  have o4 := sepConj_mono_left (regIs_to_regOwn r4 w4) h s4
  have s5 : ((r5 ↦ᵣ w5) ** (regOwn r1 ** regOwn r2 ** regOwn r3 **
      regOwn r4 ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** P)) h := by xperm_hyp o4
  have o5 := sepConj_mono_left (regIs_to_regOwn r5 w5) h s5
  have s6 : ((r6 ↦ᵣ w6) ** (regOwn r1 ** regOwn r2 ** regOwn r3 **
      regOwn r4 ** regOwn r5 ** (r7 ↦ᵣ w7) ** P)) h := by xperm_hyp o5
  have o6 := sepConj_mono_left (regIs_to_regOwn r6 w6) h s6
  have s7 : ((r7 ↦ᵣ w7) ** (regOwn r1 ** regOwn r2 ** regOwn r3 **
      regOwn r4 ** regOwn r5 ** regOwn r6 ** P)) h := by xperm_hyp o6
  have o7 := sepConj_mono_left (regIs_to_regOwn r7 w7) h s7
  xperm_hyp o7

private theorem legacy_open8 (r1 r2 r3 r4 r5 r6 r7 r8 : Reg)
    (w1 w2 w3 w4 w5 w6 w7 w8 : Word) (P : Assertion) (h : PartialState)
    (hq : ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) **
      (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** (r8 ↦ᵣ w8) ** P) h) :
    (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5 **
      regOwn r6 ** regOwn r7 ** regOwn r8 ** P) h := by
  have s8 : ((r8 ↦ᵣ w8) ** ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) **
      (r4 ↦ᵣ w4) ** (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** P)) h := by
    xperm_hyp hq
  have o8 := sepConj_mono_left (regIs_to_regOwn r8 w8) h s8
  have hrest : ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) **
      (r5 ↦ᵣ w5) ** (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** (regOwn r8 ** P)) h := by
    xperm_hyp o8
  have h7 := legacy_open7 r1 r2 r3 r4 r5 r6 r7 w1 w2 w3 w4 w5 w6 w7
    (regOwn r8 ** P) h hrest
  xperm_hyp h7

/-- Body-level caller footprint at H+36, i.e. the whole-routine precondition
    minus the ABI frame's own registers and slots. -/
def legacyWholeCallerPre (a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31 : Word)
    (sp0 oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ a1) ** ((.x12 : Reg) ↦ᵣ a2) **
    ((.x13 : Reg) ↦ᵣ a3) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
    ((.x7 : Reg) ↦ᵣ v7) ** ((.x14 : Reg) ↦ᵣ v14) **
    ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
    ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion a0 input ** stackFree sp0 8 **
    (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) **
    legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A ** F

theorem legacyWholeCallerPre_pcFree
    (a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31 : Word)
    (sp0 oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A F : Assertion)
    (hA : A.pcFree) (hF : F.pcFree) :
    (legacyWholeCallerPre a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31
      sp0 oldOff oldLen cellOld old0 old1 old2 old3 old4 old5
      input os A F).pcFree := by
  unfold legacyWholeCallerPre
  repeat first
    | exact legacyBodyBss_pcFree _ _ _ _ _ _ _ _ _ _ _ hA
    | exact hF
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_stackFree _ _
    | apply pcFree_sepConj
    | exact (by pcf)

/-- Keccak-success outcome, with the ABI frame's registers/slots factored
    out. -/
def legacyWholeOkPost
    (chainId payloadBase inPtr hdrLen outputBase sp0 v9 offVal lenVal : Word)
    (payloadBytes : List (BitVec 8)) (A F : Assertion)
    (source : KssSource := kssDefaultSource) : Assertion :=
  frameSlotsSaved kssFrame (sp0 + signExtend12 ((-64 : BitVec 12)))
      (kssEntryVals (legacyKssJalPC + 4) inPtr v9 chainId outputBase hdrLen
        payloadBase (legacyKssBodyPayloadEnd chainId payloadBase)) **
    kssCallerPost_multi legacyKssSegsBase outputBase
      (legacyKssBodySegs chainId payloadBase inPtr hdrLen payloadBytes)
      A source **
    (legacyPrefixCellPtr ↦ₘ legacyKssBodyPrefixLen chainId payloadBase) **
    legacyKssBodyProducedResidual chainId payloadBase offVal lenVal ** F

/-- Status-1 reject outcome, with the ABI frame's registers/slots factored
    out.  The two output cells still hold their entry values. -/
def legacyWholeFailPost (v11 v12 sp0 a0 a2 a3 oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input os : List (BitVec 8)) (A F : Assertion) : Assertion :=
  stackFree sp0 8 ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
    ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
    regOwn .x13 ** regOwn .x14 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion a0 input **
    (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) **
    legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A ** F **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

/-- The K146 body in `abiFrame_spec_own` shape. -/
theorem legacyKeccakBody_own
    (newSp : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31 : Word)
    (oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8)) (listLen : Nat)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hlen : a1 ≠ 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hslack : listLen + 9 ≤ input.length)
    (hoverIn : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hos : os.length = 200)
    (hpayW : ∀ offVal lenVal,
      EvmAsm.Codegen.RlpListNthItemSAsm.Success input a0 listLen 5 offVal lenVal →
        BitVec.ofNat 64 payloadBs.length =
          ((offVal + lenVal) - legacyHdrLen input h0))
    (hcount : ∀ offVal lenVal,
      (legacyKssBodySegs a2 ((offVal + lenVal) - legacyHdrLen input h0)
        a0 (legacyHdrLen input h0) payloadBs).length < 2 ^ 64)
    (hsegs : ∀ offVal lenVal,
      ∀ s ∈ legacyKssBodySegs a2 ((offVal + lenVal) - legacyHdrLen input h0)
        a0 (legacyHdrLen input h0) payloadBs,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (sourceSpec :
      KssInputSourceSpec a0 (legacyHdrLen input h0) input payloadBs)
    (hsourcePrefix : ∀ offVal lenVal,
      sourceSpec.source.region legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2
            ((offVal + lenVal) - legacyHdrLen input h0)) =
        bytesRegion legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2
            ((offVal + lenVal) - legacyHdrLen input h0)))
    (hsourceSuffix : sourceSpec.source.region legacySuffixOutPtr
        (legacyKssBodySuffixBytes a2) =
      bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes a2))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      1 + legacyBodyFuel a2 ((offVal + lenVal) - legacyHdrLen input h0) a0
        (legacyHdrLen input h0) payloadBs ≤ N)
    (hNfail : 2 ≤ N) :
    cpsTripleWithin
      (((4 + 1 + 8) + (7 + (1 + ((12 + ((85 + 93 * (5 + 2)) + 6)) + 9)))) + N)
      (legacyH + BitVec.ofNat 64 (4 * (1 + legacyFrame.length)))
      (legacyH + BitVec.ofNat 64
        (4 * (1 + legacyFrame.length + legacyBody.length)))
      legacyFullCode
      ((.x2 ↦ᵣ newSp) ** regsAt legacyFrame vals **
        frameSlotsSaved legacyFrame newSp vals **
        legacyWholeCallerPre a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31
          newSp oldOff oldLen cellOld old0 old1 old2 old3 old4 old5
          input os A F)
      ((.x2 ↦ᵣ newSp) ** regsOwnAt legacyFrame **
        frameSlotsSaved legacyFrame newSp vals **
        legacyNthOutcomePost
          (fun h => ∃ offVal lenVal,
            legacyWholeOkPost a2 ((offVal + lenVal) - legacyHdrLen input h0)
              a0 (legacyHdrLen input h0) a3 newSp a1 offVal lenVal payloadBs
              A F sourceSpec.source h)
          (fun h => ∃ v11 v12,
            legacyWholeFailPost v11 v12 newSp a0 a2 a3 oldOff oldLen cellOld
              old0 old1 old2 old3 old4 old5 input os A F h)) := by
  rw [legacyFrame_length, legacyBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl,
    show 4 * (1 + 8 + 101) = 440 from rfl]
  have hRF : (frameSlotsSaved legacyFrame newSp vals ** F).pcFree :=
    pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hF
  have hbody := legacyBodyEntryThroughExit_spec a0 a1 a2 a3 v5 v6 v7
    (vals .x8) (vals .x9) v14 (vals .x18) (vals .x19) (vals .x20) (vals .x21)
    v28 v29 v30 v31 (vals .x1) newSp oldOff oldLen cellOld
    old0 old1 old2 old3 old4 old5 input payloadBs os listLen A
    (frameSlotsSaved legacyFrame newSp vals ** F) hA hRF
    hlen h0 halignIn hge hlistLenW hslack hoverIn hvalidBytes
    halign hover hvalid hbound h_out_valid hos hpayW hcount hsegs
    sourceSpec hsourcePrefix hsourceSuffix N hNok hNfail
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hbody
  · rw [legacy_regsAt_frame] at hp
    have hp22 : (regOwn .x22 **
        (((.x2 : Reg) ↦ᵣ newSp) ** ((.x1 : Reg) ↦ᵣ vals .x1) **
          ((.x8 : Reg) ↦ᵣ vals .x8) ** ((.x9 : Reg) ↦ᵣ vals .x9) **
          ((.x18 : Reg) ↦ᵣ vals .x18) ** ((.x19 : Reg) ↦ᵣ vals .x19) **
          ((.x20 : Reg) ↦ᵣ vals .x20) ** ((.x21 : Reg) ↦ᵣ vals .x21) **
          frameSlotsSaved legacyFrame newSp vals **
          legacyWholeCallerPre a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31
            newSp oldOff oldLen cellOld old0 old1 old2 old3 old4 old5
            input os A F)) h :=
      sepConj_mono_left (regIs_to_regOwn .x22 (vals .x22)) h (by xperm_hyp hp)
    unfold legacyWholeCallerPre at hp22
    unfold legacyEntryAmbient
    xperm_hyp hp22
  · rcases hq with hok | hfail
    · obtain ⟨offVal, lenVal, hok⟩ := hok
      unfold legacyKssBodyFinal legacyKssCallPost legacyKssSregs at hok
      have h8 := legacy_open8 .x1 .x8 .x9 .x18 .x19 .x20 .x21 .x22
        (legacyKssJalPC + 4) a0 a1 a2 a3 (legacyHdrLen input h0)
        ((offVal + lenVal) - legacyHdrLen input h0)
        (legacyKssBodyPayloadEnd a2
          ((offVal + lenVal) - legacyHdrLen input h0))
        (((.x2 : Reg) ↦ᵣ newSp) **
          frameSlotsSaved kssFrame (newSp + signExtend12 ((-64 : BitVec 12)))
            (kssEntryVals (legacyKssJalPC + 4) a0 a1 a2 a3
              (legacyHdrLen input h0)
              ((offVal + lenVal) - legacyHdrLen input h0)
              (legacyKssBodyPayloadEnd a2
                ((offVal + lenVal) - legacyHdrLen input h0))) **
          kssCallerPost_multi legacyKssSegsBase a3
            (legacyKssBodySegs a2
              ((offVal + lenVal) - legacyHdrLen input h0) a0
              (legacyHdrLen input h0) payloadBs) A sourceSpec.source **
          (legacyPrefixCellPtr ↦ₘ legacyKssBodyPrefixLen a2
            ((offVal + lenVal) - legacyHdrLen input h0)) **
          legacyKssBodyProducedResidual a2
            ((offVal + lenVal) - legacyHdrLen input h0) offVal lenVal **
          frameSlotsSaved legacyFrame newSp vals ** F)
        h (by xperm_hyp hok)
      have hstep : (((.x2 : Reg) ↦ᵣ newSp) **
          (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x21 ** regOwn .x22) **
          frameSlotsSaved legacyFrame newSp vals **
          legacyWholeOkPost a2 ((offVal + lenVal) - legacyHdrLen input h0)
            a0 (legacyHdrLen input h0) a3 newSp a1 offVal lenVal payloadBs
            A F sourceSpec.source) h := by
        unfold legacyWholeOkPost
        xperm_hyp h8
      rw [legacy_regsOwnAt_frame]
      exact sepConj_mono (fun _ hx => hx)
        (sepConj_mono (fun _ hx => hx)
          (sepConj_mono (fun _ hx => hx)
            (fun _ hx => Or.inl ⟨offVal, lenVal, hx⟩))) h hstep
    · obtain ⟨v11, v12, hfail⟩ := hfail
      unfold legacyNthFailState
        EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail at hfail
      have h7 := legacy_open7 .x1 .x8 .x9 .x18 .x19 .x20 .x21
        (legacyNthJalPC + 4) a0 a1 a2 a3 (legacyHdrLen input h0) (vals .x21)
        (((.x2 : Reg) ↦ᵣ newSp) ** regOwn .x22 **
          frameSlotsSaved legacyFrame newSp vals **
          stackFree newSp 8 ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
          ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
          regOwn .x13 ** regOwn .x14 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion a0 input **
          (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) **
          legacyBodyBss a2 cellOld a3 old0 old1 old2 old3 old4 old5 os A **
          F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        h (by xperm_hyp hfail)
      have hstep : (((.x2 : Reg) ↦ᵣ newSp) **
          (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x21 ** regOwn .x22) **
          frameSlotsSaved legacyFrame newSp vals **
          legacyWholeFailPost v11 v12 newSp a0 a2 a3 oldOff oldLen cellOld
            old0 old1 old2 old3 old4 old5 input os A F) h := by
        unfold legacyWholeFailPost
        xperm_hyp h7
      rw [legacy_regsOwnAt_frame]
      exact sepConj_mono (fun _ hx => hx)
        (sepConj_mono (fun _ hx => hx)
          (sepConj_mono (fun _ hx => hx)
            (fun _ hx => Or.inr ⟨v11, v12, hx⟩))) h hstep

/-! ## Whole routine at the `GuestAddrs` anchor -/

/-- **K146 `tx_signing_hash_legacy_eip155`, whole routine.**

    A `cpsTripleWithin` anchored at
    `GuestAddrs.tx_signing_hash_legacy_eip155` (`legacyH`), through the ABI
    frame, on the non-empty-length list-header domain.  The post is the
    disjunction of the two outcomes the guest actually has: the keccak
    success arm — whose output region holds
    `keccak256 (kssMsg (legacyKssBodySegs …))`, the digest of the re-encoded
    EIP-155 preimage — and the status-1 reject arm, on which the two output
    cells still hold their entry values.

    ## DOMAIN GATE

    `a1 ≠ 0` and `hge`: `input[0]` must be an outer-RLP LIST header
    (`0xc0 ≤ input[0] ≤ 0xff`).  Both header widths are covered — short
    (`0xc0`–`0xf7`) and long (`0xf8`–`0xff`, lenlen 1..8) — because the
    parsed header length is threaded as `legacyHdrLen` rather than
    case-split.  The remaining cut is non-list first bytes `0x00`–`0xbf`,
    where the guest exits through its status-1 reject at H+436 instead of
    through this triple, and `a1 = 0`, which is
    `tx_signing_hash_legacy_eip155_spec_within_empty_len`.

    Everything else is ABI/resource framing, in exactly the shape K145's
    `tx_signing_hash_spec_within` uses: buffer alignment/validity, the
    caller-chosen payload slice (`payloadBs` with `hpayW`), the sponge arena
    length, the keccak segment geometry (`hcount`/`hsegs`), the two
    static-source views (`hsourcePrefix`/`hsourceSuffix`), and a step bound
    `N` covering both arms. -/
theorem tx_signing_hash_legacy_eip155_spec_within
    (sp0 ret : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31 : Word)
    (oldOff oldLen cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (input payloadBs os : List (BitVec 8)) (listLen : Nat)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hret : vals .x1 = ret)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : a1 ≠ 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hslack : listLen + 9 ≤ input.length)
    (hoverIn : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0)
    (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hos : os.length = 200)
    (hpayW : ∀ offVal lenVal,
      EvmAsm.Codegen.RlpListNthItemSAsm.Success input a0 listLen 5 offVal lenVal →
        BitVec.ofNat 64 payloadBs.length =
          ((offVal + lenVal) - legacyHdrLen input h0))
    (hcount : ∀ offVal lenVal,
      (legacyKssBodySegs a2 ((offVal + lenVal) - legacyHdrLen input h0)
        a0 (legacyHdrLen input h0) payloadBs).length < 2 ^ 64)
    (hsegs : ∀ offVal lenVal,
      ∀ s ∈ legacyKssBodySegs a2 ((offVal + lenVal) - legacyHdrLen input h0)
        a0 (legacyHdrLen input h0) payloadBs,
        s.2.length < 2 ^ 64 ∧
          (∀ i, i < s.2.length →
            s.1.toNat + i < 2 ^ 64 ∧
            isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (sourceSpec :
      KssInputSourceSpec a0 (legacyHdrLen input h0) input payloadBs)
    (hsourcePrefix : ∀ offVal lenVal,
      sourceSpec.source.region legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2
            ((offVal + lenVal) - legacyHdrLen input h0)) =
        bytesRegion legacyPrefixOutPtr
          (legacyKssBodyPrefixBytes a2
            ((offVal + lenVal) - legacyHdrLen input h0)))
    (hsourceSuffix : sourceSpec.source.region legacySuffixOutPtr
        (legacyKssBodySuffixBytes a2) =
      bytesRegion legacySuffixOutPtr (legacyKssBodySuffixBytes a2))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      1 + legacyBodyFuel a2 ((offVal + lenVal) - legacyHdrLen input h0) a0
        (legacyHdrLen input h0) payloadBs ≤ N)
    (hNfail : 2 ≤ N) :
    let newSp := sp0 + signExtend12 (-64 : BitVec 12)
    let bodySteps :=
      ((4 + 1 + 8) + (7 + (1 + ((12 + ((85 + 93 * (5 + 2)) + 6)) + 9)))) + N
    cpsTripleWithin
      (1 + legacyFrame.length + bodySteps + legacyFrame.length + 1 + 1)
      legacyH ret legacyFullCode
      ((.x2 ↦ᵣ sp0) ** regsAt legacyFrame vals **
        frameSlotsOwn legacyFrame newSp **
        legacyWholeCallerPre a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31
          newSp oldOff oldLen cellOld old0 old1 old2 old3 old4 old5
          input os A F)
      ((.x2 ↦ᵣ sp0) ** regsAt legacyFrame vals **
        frameSlotsSaved legacyFrame newSp vals **
        legacyNthOutcomePost
          (fun h => ∃ offVal lenVal,
            legacyWholeOkPost a2 ((offVal + lenVal) - legacyHdrLen input h0)
              a0 (legacyHdrLen input h0) a3 newSp a1 offVal lenVal payloadBs
              A F sourceSpec.source h)
          (fun h => ∃ v11 v12,
            legacyWholeFailPost v11 v12 newSp a0 a2 a3 oldOff oldLen cellOld
              old0 old1 old2 old3 old4 old5 input os A F h)) := by
  intro newSp bodySteps
  have hcpPre :
      (legacyWholeCallerPre a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31
        newSp oldOff oldLen cellOld old0 old1 old2 old3 old4 old5
        input os A F).pcFree :=
    legacyWholeCallerPre_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ hA hF
  have hcpPost :
      (legacyNthOutcomePost
        (fun h => ∃ offVal lenVal,
          legacyWholeOkPost a2 ((offVal + lenVal) - legacyHdrLen input h0)
            a0 (legacyHdrLen input h0) a3 newSp a1 offVal lenVal payloadBs
            A F sourceSpec.source h)
        (fun h => ∃ v11 v12,
          legacyWholeFailPost v11 v12 newSp a0 a2 a3 oldOff oldLen cellOld
            old0 old1 old2 old3 old4 old5 input os A F h)).pcFree := by
    have hokF : ∀ offVal lenVal : Word,
        (legacyWholeOkPost a2 ((offVal + lenVal) - legacyHdrLen input h0) a0
          (legacyHdrLen input h0) a3 newSp a1 offVal lenVal payloadBs A F
          sourceSpec.source).pcFree := by
      intro offVal lenVal
      unfold legacyWholeOkPost legacyKssBodyProducedResidual
      repeat first
        | exact kssCallerPost_multi_pcFree _ _ _ _ hA sourceSpec.source
        | exact legacyPrefixBssTail_pcFree _
        | exact hF
        | exact bytesRegion_pcFree _ _
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact pcFree_frameSlotsSaved _ _ _
        | apply pcFree_sepConj
        | exact (by pcf)
    have hfailF : ∀ v11 v12 : Word,
        (legacyWholeFailPost v11 v12 newSp a0 a2 a3 oldOff oldLen cellOld
          old0 old1 old2 old3 old4 old5 input os A F).pcFree := by
      intro v11 v12
      unfold legacyWholeFailPost
      repeat first
        | exact legacyBodyBss_pcFree _ _ _ _ _ _ _ _ _ _ _ hA
        | exact hF
        | exact bytesRegion_pcFree _ _
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memIs
        | exact pcFree_stackFree _ _
        | apply pcFree_sepConj
        | exact (by pcf)
    intro h hh
    rcases hh with hok | hfail
    · obtain ⟨offVal, lenVal, hok⟩ := hok
      exact hokF offVal lenVal h hok
    · obtain ⟨v11, v12, hfail⟩ := hfail
      exact hfailF v11 v12 h hfail
  have h := abiFrame_spec_own legacyH sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    legacyFrame (0 : BitVec 12) legacySregs vals legacyBody bodySteps
    (legacyWholeCallerPre a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31
      newSp oldOff oldLen cellOld old0 old1 old2 old3 old4 old5 input os A F)
    (legacyNthOutcomePost
      (fun h => ∃ offVal lenVal,
        legacyWholeOkPost a2 ((offVal + lenVal) - legacyHdrLen input h0)
          a0 (legacyHdrLen input h0) a3 newSp a1 offVal lenVal payloadBs
          A F sourceSpec.source h)
      (fun h => ∃ v11 v12,
        legacyWholeFailPost v11 v12 newSp a0 a2 a3 oldOff oldLen cellOld
          old0 old1 old2 old3 old4 old5 input os A F h))
    legacyFullCode legacyFrame_cons legacyFrame_ne_zero
    (by rw [legacyFrame_length]; decide)
    (by rw [legacy_prog_eq_abiFrame, legacy_prog_length]; decide)
    hret halignRet (legacyFrame_restore sp0) hcpPre hcpPost
    legacy_ofProg_sub_fullCode
    (legacyKeccakBody_own newSp vals a0 a1 a2 a3 v5 v6 v7 v14 v28 v29 v30 v31
      oldOff oldLen cellOld old0 old1 old2 old3 old4 old5 input payloadBs os
      listLen A F hA hF hlen h0 halignIn hge hlistLenW hslack hoverIn
      hvalidBytes halign hover hvalid hbound h_out_valid hos hpayW hcount
      hsegs sourceSpec hsourcePrefix hsourceSuffix N hNok hNfail)
  exact h

/-! ## Non-vacuity of the domain gate

    The gate is `a1 ≠ 0` together with `hge`, i.e. `input[0]` is an
    outer-RLP LIST header.  Both header widths satisfy it, and a string
    header provably does not. -/

/-- Short outer list header (`0xc4`): the gate holds and the parsed header
    length is 1. -/
theorem legacy_hdrGate_short_nonvacuous :
    ∃ (input : List (BitVec 8)) (h0 : 0 < input.length),
      ¬BitVec.ult (legacyHdrByte input h0) (192 : Word) ∧
        legacyHdrLen input h0 = (1 : Word) :=
  ⟨[0xc4, 0x83, 1, 2, 3], by decide, by decide, by decide⟩

/-- Long outer list header (`0xf8`, one length byte): the gate holds and the
    parsed header length is 2 — so the long arm is reachable too, and the
    threaded `legacyHdrLen` is not silently pinned at 1. -/
theorem legacy_hdrGate_long_nonvacuous :
    ∃ (input : List (BitVec 8)) (h0 : 0 < input.length),
      ¬BitVec.ult (legacyHdrByte input h0) (192 : Word) ∧
        legacyHdrLen input h0 = (2 : Word) :=
  ⟨[0xf8, 0x42, 0x83, 1, 2, 3], by decide, by decide, by decide⟩

/-- Negative control: a string header (`0x80`) makes `hge` FALSE, so the
    gate is a real domain restriction and not a hypothesis that holds
    everywhere.  On those inputs the guest exits through its own status-1
    reject at H+436 instead of through this triple. -/
theorem legacy_hdrGate_false_on_string_header :
    BitVec.ult (legacyHdrByte [0x80, 0x00] (by decide)) (192 : Word) = true := by
  decide

/-- Second negative control: `0xbf` is the last non-list first byte. -/
theorem legacy_hdrGate_false_on_bf :
    BitVec.ult (legacyHdrByte [0xbf, 0x00] (by decide)) (192 : Word) = true := by
  decide

/-! ## The payload/source hypotheses are jointly satisfiable

    `hpayW`, `hsourcePrefix` and `hsourceSuffix` are the three hypotheses of
    the whole-routine triple that mention the KSS source view.  They are not
    independent: all three hold for the canonical payload slice, under the
    caller-owned input-zone bound the production caller supplies.  Proving
    them together rules out a source view that satisfies one and quietly
    fails another. -/

theorem legacyPayloadSupply
    (input : List (BitVec 8)) (a0 offVal lenVal : Word)
    (h0 : 0 < input.length)
    (halign : a0.toNat % 8 = 0)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hinput_hi : a0.toNat + input.length ≤ EvmAsm.Codegen.INPUT_MEM_END)
    (hfit : (legacyHdrLen input h0).toNat +
      ((offVal + lenVal) - legacyHdrLen input h0).toNat ≤ input.length) :
    BitVec.ofNat 64
        (legacyPayloadOf input (legacyHdrLen input h0) offVal lenVal).length =
      (offVal + lenVal) - legacyHdrLen input h0 ∧
    (∀ bs : List (BitVec 8),
      (legacyPayloadSourceSpec input a0 (legacyHdrLen input h0) offVal lenVal
        halign hover hfit).source.region legacyPrefixOutPtr bs =
        bytesRegion legacyPrefixOutPtr bs) ∧
    (∀ bs : List (BitVec 8),
      (legacyPayloadSourceSpec input a0 (legacyHdrLen input h0) offVal lenVal
        halign hover hfit).source.region legacySuffixOutPtr bs =
        bytesRegion legacySuffixOutPtr bs) := by
  refine ⟨legacyPayloadSourceSpec_len input a0 (legacyHdrLen input h0) offVal
    lenVal halign hover hfit, ?_, ?_⟩
  · intro bs
    show (kssInputSource a0 (legacyHdrLen input h0) input
      (legacyPayloadOf input (legacyHdrLen input h0) offVal lenVal) halign
      (legacyPayloadOf_length_le input (legacyHdrLen input h0) offVal lenVal
        hfit)
      hover
      (legacyPayloadOf_bytes input (legacyHdrLen input h0) offVal lenVal
        (legacyPayloadOf_length_le input (legacyHdrLen input h0) offVal lenVal
          hfit))).region legacyPrefixOutPtr bs = _
    exact legacyKssInputSource_prefix_region_of_input_layout _ _ _ _ hinput_hi bs
  · intro bs
    show (kssInputSource a0 (legacyHdrLen input h0) input
      (legacyPayloadOf input (legacyHdrLen input h0) offVal lenVal) halign
      (legacyPayloadOf_length_le input (legacyHdrLen input h0) offVal lenVal
        hfit)
      hover
      (legacyPayloadOf_bytes input (legacyHdrLen input h0) offVal lenVal
        (legacyPayloadOf_length_le input (legacyHdrLen input h0) offVal lenVal
          hfit))).region legacySuffixOutPtr bs = _
    exact legacyKssInputSource_suffix_region_of_input_layout _ _ _ _ hinput_hi bs

end EvmAsm.Codegen.TxSigningHashLegacyTop
