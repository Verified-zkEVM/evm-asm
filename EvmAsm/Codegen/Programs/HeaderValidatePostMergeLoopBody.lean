/-
  EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopBody

  Machine-proof layer for the K67 re-emit (#12461): code plumbing for the
  reshaped `header_validate_post_merge` (166 instructions, one
  `rlp_walk_init` + a 15-iteration `rlp_walk_next` loop) and the
  per-iteration walk step at the loop's `jal` site (instruction [16],
  `K + 64`).

  Layout facts (regenerated GuestAddrs at this commit): K67 at
  `0x8000acdc` (166 instr, range `[0x8000acdc, 0x8000af74)`),
  `rlp_walk_init` at `0x80004c08` (53 instr) and `rlp_walk_next` at
  `0x80004cdc`, both strictly BELOW K67, so all three code regions are
  pairwise disjoint by `CodeReq.Disjoint.ofProg_ranges` with `left`.

  The step lemma `k67WalkNextStep` mirrors
  `HeaderFieldsSpecCommon.hesrNextStep` (the tree's exemplar for composing
  `rlp_walk_next` at a caller `jal`): unpacked callee pre pins, ambient
  `F` framed on the right, caller's `ra` ownership consumed by the `JAL`.
-/

import EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopSpec
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkCallSAsm

/-! ## Linked code and plumbing -/

/-- K67 entry. -/
abbrev K : Word := (Codegen.GuestAddrs.header_validate_post_merge : Word)

/-- The re-emitted routine (166 instructions). -/
abbrev k67Prog : Program := EvmAsm.Codegen.headerValidatePostMerge_prog

set_option maxRecDepth 4000 in
theorem k67_length : k67Prog.length = 166 := by decide

abbrev k67Code : CodeReq := CodeReq.ofProg K k67Prog

/-- Walker entry addresses (both below K67). -/
abbrev initBase : Word := (Codegen.GuestAddrs.rlp_walk_init : Word)
abbrev wnBase : Word := (Codegen.GuestAddrs.rlp_walk_next : Word)

abbrev initCode : CodeReq := rlp_walk_init_code initBase
abbrev nextCode : CodeReq := rlp_walk_next_code wnBase

/-- The full linked closure: the routine plus both walkers. -/
def fullCode : CodeReq := k67Code.union (initCode.union nextCode)

theorem k67_init_disjoint : k67Code.Disjoint initCode := by
  unfold k67Code initCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [k67_length]; decide
  · rw [rlp_walk_init_prog_length]; decide
  · right; rw [rlp_walk_init_prog_length]; decide

theorem k67_next_disjoint : k67Code.Disjoint nextCode := by
  unfold k67Code nextCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [k67_length]; decide
  · rw [rlp_walk_next_prog_length]; decide
  · right; rw [rlp_walk_next_prog_length]; decide

theorem init_next_disjoint : initCode.Disjoint nextCode := by
  unfold initCode nextCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_walk_init_prog_length]; decide
  · rw [rlp_walk_next_prog_length]; decide
  · left; rw [rlp_walk_init_prog_length]; decide

theorem k67_mono : ∀ a i, k67Code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

theorem init_mono : ∀ a i, initCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right k67_init_disjoint
    (fun a i h => CodeReq.union_mono_left a i h) a i hi

theorem next_mono : ∀ a i, nextCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right k67_next_disjoint
    (fun a i h => CodeReq.mono_union_right init_next_disjoint
      (fun _ _ h' => h') a i h) a i hi

/-! ## The per-iteration walk step

    One `rlp_walk_next` call at the loop's call site `K + 64`
    (instruction [16]; return address `K + 68`), lifted into `fullCode`.
    The caller's live state at this point is the loop invariant minus the
    pins the callee consumes (`x10` cursor, `x11` end, `x12` previous
    length, the seven scratch registers); everything else travels in the
    ambient `F`.  The outcome is the raw 6-way `rlp_walk_next` post. -/

/-- The `jal ra, rlp_walk_next` immediate at instruction [16] (`K + 64`). -/
def k67NextOffset : BitVec 21 :=
  jalOff Codegen.GuestAddrs.rlp_walk_next
    (Codegen.GuestAddrs.header_validate_post_merge + 64)

/-- The 6-way `rlp_walk_next` outcome at K67's call site, framed against
    an ambient `F`.  Local copy of `hesrNextOutcome` (K67 does not import
    the header-fields family). -/
def k67NextOutcome (base endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) : Assertion :=
  fun h =>
    rlpWalkNextOk (base + BitVec.ofNat 64 off) endPtr bytes off h ∨
    (((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (2 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ BitVec.ult (base + BitVec.ofNat 64 off) endPtr = true⌝) h) ∨
    (((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (3 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (base + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (4 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (base + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (5 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (base + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (6 : Word)) **
      (.x12 ↦ᵣ (0 : Word)) **
      ⌜¬ ∃ next len, rlpItemDecode bytes off
        (base + BitVec.ofNat 64 off) endPtr next len⌝) h)

set_option maxRecDepth 4000 in
theorem k67WalkNextStep {F : Assertion} (hF : F.pcFree)
    (base endPtr : Word) (bytes : List (BitVec 8)) (off : Nat)
    (oldRa v12 v5 v6 v7 v28 v29 v30 v31 : Word)
    (hsalign : base.toNat % 8 = 0)
    (hoff : off < bytes.length)
    (hss : ¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true →
      BitVec.ult ((bytes[off]'hoff).zeroExtend 64 - (0x80 : Word))
        (endPtr - (base + BitVec.ofNat 64 off)) = true →
      ((bytes[off]'hoff).zeroExtend 64 - (0x80 : Word)) = (1 : Word) →
      off + 1 < bytes.length ∧
      base.toNat + (off + 1) < 2 ^ 64 ∧
      isValidByteAccess (base + BitVec.ofNat 64 (off + 1)) = true)
    (hls : ¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true →
      BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xc0 : Word) = true →
      ¬ BitVec.ult endPtr
        ((base + BitVec.ofNat 64 off) +
          (((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      off + 1 + ((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat ≤
        bytes.length ∧
      base.toNat + (off + 1 +
        ((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
      ∀ k, k < ((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
        isValidByteAccess (base + BitVec.ofNat 64 (off + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult endPtr
        ((base + BitVec.ofNat 64 off) +
          (((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      off + 1 + ((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length ∧
      base.toNat + (off + 1 +
        ((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
      ∀ k, k < ((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (base + BitVec.ofNat 64 (off + 1 + k)) = true)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + 87) (K + 64) (K + 68) fullCode
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) **
         (.x12 ↦ᵣ v12) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F))
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
         (.x1 ↦ᵣ (K + 68)) ** bytesRegion base bytes) **
        k67NextOutcome base endPtr bytes off) ** F) := by
  have hwn := rlp_walk_next_spec_within wnBase base endPtr (K + 68) v12
    v5 v6 v7 v28 v29 v30 v31 bytes off hsalign hoff (by omega)
    (hvalid off hoff) hss hls hll
  have hwnF := cpsTripleWithin_frameR F hF hwn
  have hwn' := cpsTripleWithin_weaken
    (P' := (.x1 ↦ᵣ (K + 68)) **
      ((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ v12) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F))
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwnF
  have hc := rlp_walk_next_call_within (K + 64) wnBase oldRa k67NextOffset
    (by repeat' first
      | exact hF | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
      | exact pcFree_regOwn | apply pcFree_sepConj)
    (by simp only [k67NextOffset, K, wnBase]; decide)
    (by simp only [K]; decide)
    (by
      simp only [K, wnBase]
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (fun a i hi =>
      CodeReq.union_split_mono
        (fun a' i' h' => k67_mono a' i'
          (CodeReq.ofProg_mem_at K (K + 64) k67Prog 16 (.JAL .x1 k67NextOffset)
            (by unfold K; bv_omega)
            (by rw [k67_length]; decide)
            rfl
            (by decide) a' i' h'))
        next_mono a i hi)
    hwn'
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by unfold k67NextOutcome; xperm_hyp hq) hc

/-! ## Init call (prologue piece) -/

/-- Link offset of the prologue `jal rlp_walk_init` (instruction 10, return
    site `K + 44`); spelled to match `headerValidatePostMerge_prog`. -/
def k67InitOffset : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init (GuestAddrs.header_validate_post_merge + 40)

/-- Frame/ambient footprint framed through the calls: the widened 48-byte
    frame, the pass-through registers, and the (abstract) ommers constant. -/
def k67Ambient (sp0 base omConst lenW v18 v19 v20 v21 : Word) : Assertion :=
  (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
  (.x8 ↦ᵣ base) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
  frameSlotsOwn k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) **
  bytesRegion omConst (List.replicate 32 (0 : BitVec 8))

theorem k67Ambient_pcFree (sp0 base omConst lenW v18 v19 v20 v21 : Word) :
    (k67Ambient sp0 base omConst lenW v18 v19 v20 v21).pcFree := by
  unfold k67Ambient
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | exact pcFree_frameSlotsOwn _ _
    | exact bytesRegion_pcFree _ _
    | exact pcFree_emp

/-- Common footprint after the init call returns: the temp registers returned
    to ownership and the header window intact. -/
def k67InitCommon (base : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (K + 44)) ** bytesRegion base bytes

set_option maxRecDepth 4000 in
/-- One init call at `K + 40` over the full closure.  The callee's own
    #12404-shaped long-list gates are carried VERBATIM as premises — no
    window-slack assumption, since the K67 header window is exact-fit. -/
theorem k67InitStep
    (sp0 base omConst oldRa v12 v5 v6 v7 v28 v29 v30 v31 v18 v19 v20 v21 : Word)
    (bytes : List (BitVec 8)) (lenN : Nat)
    (hsalign : base.toNat % 8 = 0)
    (hoff : 0 < bytes.length)
    (_hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true)
    (hll_len : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 lenN)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length)
    (hll_over : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 lenN)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      base.toNat + (0 + 1 +
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 lenN)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      ∀ k, k < ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (base + BitVec.ofNat 64 (0 + 1 + k)) = true) :
    cpsTripleWithin (1 + 81) (K + 40) (K + 44) fullCode
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x12 ↦ᵣ v12) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
          k67Ambient sp0 base omConst (BitVec.ofNat 64 lenN) v18 v19 v20 v21))
      (((k67InitCommon base bytes ** (.x0 ↦ᵣ (0 : Word))) **
          EvmAsm.Codegen.RlpListNthItemSAsm.initOutcome base bytes lenN hoff) **
        k67Ambient sp0 base omConst (BitVec.ofNat 64 lenN) v18 v19 v20 v21) := by
  have hwi := rlp_walk_init_spec_within initBase base (K + 44)
    (BitVec.ofNat 64 lenN) v12 v5 v6 v7 v28 v29 v30 v31 bytes 0
    hsalign hoff (by omega) (hvalid 0 hoff) hll_len hll_over hll_valid
  rw [show base + BitVec.ofNat 64 0 = base from by bv_omega] at hwi
  have hwiF := cpsTripleWithin_frameR
    (k67Ambient sp0 base omConst (BitVec.ofNat 64 lenN) v18 v19 v20 v21)
    (k67Ambient_pcFree sp0 base omConst _ v18 v19 v20 v21) hwi
  have hwi' := cpsTripleWithin_weaken
    (P' := (.x1 ↦ᵣ (K + 44)) **
      ((.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        k67Ambient sp0 base omConst (BitVec.ofNat 64 lenN) v18 v19 v20 v21))
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwiF
  have hc := rlp_walk_init_call_within (K + 40) initBase oldRa k67InitOffset
    (by repeat' first
      | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
      | exact pcFree_regOwn | apply pcFree_sepConj | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_memOwn)
    (by simp only [k67InitOffset, K, initBase]; decide)
    (by simp only [K]; decide)
    (by
      simp only [K, initBase]
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (fun a i hi =>
      CodeReq.union_split_mono
        (fun a' i' h' => k67_mono a' i'
          (CodeReq.ofProg_mem_at K (K + 40) k67Prog 10 (.JAL .x1 k67InitOffset)
            (by unfold K; bv_omega)
            (by rw [k67_length]; decide)
            rfl
            (by decide) a' i' h'))
        init_mono a i hi)
    hwi'
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold k67InitCommon EvmAsm.Codegen.RlpListNthItemSAsm.initOutcome
      xperm_hyp hq) hc

/-- Entry values spilled by the K67 prologue, as a `Reg -> Word` function for
    `frameSlotsSaved`. -/
private def k67PrologueVals (ret v8 v9 v18 v19 v20 : Word) : Reg -> Word :=
  fun r =>
    match r with
    | .x1 => ret | .x8 => v8 | .x9 => v9 | .x18 => v18 | .x19 => v19 | .x20 => v20
    | _ => 0

set_option maxRecDepth 4000 in
/-- Instructions 0-9 (frame allocation, six spills, input saves, index reset)
    followed by the `rlp_walk_init` call at [10].  Ends at the init return
    site K+44 with the spilled slots regrouped as the loop frame, the loop
    index reset, the header base/length saved in `x8/x9`, and the walk-init
    outcome exposed. -/
theorem k67PrologueSetup (sp0 spC base omConst ret v8 v9 v18 v19 v20 v21 v12 v5 v6
    v7 v28 v29 v30 v31 : Word) (bytes : List (BitVec 8)) (lenN : Nat)
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hsalign : base.toNat % 8 = 0) (hoff : 0 < bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length → isValidByteAccess (base + BitVec.ofNat 64 k) = true)
    (hll_len : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 lenN)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length)
    (hll_over : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 lenN)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      base.toNat + (0 + 1 +
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult ((base + BitVec.ofNat 64 0) + BitVec.ofNat 64 lenN)
        ((base + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      ∀ k, k < ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (base + BitVec.ofNat 64 (0 + 1 + k)) = true)
    : cpsTripleWithin (10 + (1 + 81)) K (K + 44) fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 8) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 16) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 24) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 32) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 40))
      (k67InitCommon base bytes ** (.x0 ↦ᵣ (0 : Word)) **
        EvmAsm.Codegen.RlpListNthItemSAsm.initOutcome base bytes lenN hoff **
        k67Ambient sp0 base omConst (BitVec.ofNat 64 lenN) v18 v19 (0 : Word) v21 **
        regOwn .x13 ** regOwn .x14) := by
  subst hspC
  have h0 : cpsTripleWithin 1 K (K + 4)
      (CodeReq.singleton K (.ADDI .x2 .x2 (-48 : BitVec 12)))
      (.x2 ↦ᵣ sp0) (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) :=
    addi_spec_gen_same_within .x2 sp0 (-48 : BitVec 12) K (by decide)
  have h0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K K k67Prog 0 (.ADDI .x2 .x2 (-48 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h0

  have h1 : cpsTripleWithin 1 (K + 4) (K + 4 + 4)
      (CodeReq.singleton (K + 4) (.SD .x2 .x1 (0 : BitVec 12)))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x1 ↦ᵣ ret) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (0 : BitVec 12)))
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x1 ↦ᵣ ret) **
      (((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ ret)) :=
    sd_spec_gen_own_within .x2 .x1 (sp0 + signExtend12 (-48 : BitVec 12)) ret (0 : BitVec 12) (K + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-48 : BitVec 12)) + (0 : Word) = (sp0 + signExtend12 (-48 : BitVec 12)) from by bv_omega] at h1
  have h1C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 4) k67Prog 1 (.SD .x2 .x1 (0 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h1

  have h2 : cpsTripleWithin 1 (K + 8) (K + 8 + 4)
      (CodeReq.singleton (K + 8) (.SD .x2 .x8 (8 : BitVec 12)))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ v8) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (8 : BitVec 12)))
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ v8) **
      (((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ v8)) :=
    sd_spec_gen_own_within .x2 .x8 (sp0 + signExtend12 (-48 : BitVec 12)) v8 (8 : BitVec 12) (K + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at h2
  have h2C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 8) k67Prog 2 (.SD .x2 .x8 (8 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h2

  have h3 : cpsTripleWithin 1 (K + 12) (K + 12 + 4)
      (CodeReq.singleton (K + 12) (.SD .x2 .x9 (16 : BitVec 12)))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x9 ↦ᵣ v9) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (16 : BitVec 12)))
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x9 ↦ᵣ v9) **
      (((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ v9)) :=
    sd_spec_gen_own_within .x2 .x9 (sp0 + signExtend12 (-48 : BitVec 12)) v9 (16 : BitVec 12) (K + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at h3
  have h3C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 12) k67Prog 3 (.SD .x2 .x9 (16 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h3

  have h4 : cpsTripleWithin 1 (K + 16) (K + 16 + 4)
      (CodeReq.singleton (K + 16) (.SD .x2 .x18 (24 : BitVec 12)))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x18 ↦ᵣ v18) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (24 : BitVec 12)))
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x18 ↦ᵣ v18) **
      (((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ v18)) :=
    sd_spec_gen_own_within .x2 .x18 (sp0 + signExtend12 (-48 : BitVec 12)) v18 (24 : BitVec 12) (K + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at h4
  have h4C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 16) k67Prog 4 (.SD .x2 .x18 (24 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h4

  have h5 : cpsTripleWithin 1 (K + 20) (K + 20 + 4)
      (CodeReq.singleton (K + 20) (.SD .x2 .x19 (32 : BitVec 12)))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x19 ↦ᵣ v19) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (32 : BitVec 12)))
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x19 ↦ᵣ v19) **
      (((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ v19)) :=
    sd_spec_gen_own_within .x2 .x19 (sp0 + signExtend12 (-48 : BitVec 12)) v19 (32 : BitVec 12) (K + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at h5
  have h5C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 20) k67Prog 5 (.SD .x2 .x19 (32 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h5

  have h6 : cpsTripleWithin 1 (K + 24) (K + 28)
      (CodeReq.singleton (K + 24) (.SD .x2 .x20 (40 : BitVec 12)))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x20 ↦ᵣ v20) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (40 : BitVec 12)))
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x20 ↦ᵣ v20) **
      (((sp0 + signExtend12 (-48 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ v20)) :=
    sd_spec_gen_own_within .x2 .x20 (sp0 + signExtend12 (-48 : BitVec 12)) v20 (40 : BitVec 12) (K + 24)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at h6
  have h6C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 24) k67Prog 6 (.SD .x2 .x20 (40 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h6

  have h7 : cpsTripleWithin 1 (K + 28) (K + 28 + 4)
      (CodeReq.singleton (K + 28) (.MV .x8 .x10))
      ((.x10 ↦ᵣ base) ** (.x8 ↦ᵣ v8)) ((.x10 ↦ᵣ base) ** (.x8 ↦ᵣ base)) :=
    mv_spec_gen_within .x8 .x10 base v8 (K + 28) (by decide)
  have h7C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 28) k67Prog 7 (.MV .x8 .x10)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h7
  have h8 : cpsTripleWithin 1 (K + 32) (K + 32 + 4)
      (CodeReq.singleton (K + 32) (.MV .x9 .x11))
      ((.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x9 ↦ᵣ v9))
      ((.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x9 ↦ᵣ (BitVec.ofNat 64 lenN))) :=
    mv_spec_gen_within .x9 .x11 (BitVec.ofNat 64 lenN) v9 (K + 32) (by decide)
  have h8C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 32) k67Prog 8 (.MV .x9 .x11)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h8
  have h9 : cpsTripleWithin 1 (K + 36) (K + 36 + 4)
      (CodeReq.singleton (K + 36) (.LI .x20 (0 : Word)))
      (.x20 ↦ᵣ v20) (.x20 ↦ᵣ (0 : Word)) :=
    li_spec_gen_within .x20 v20 (0 : Word) (K + 36) (by decide)
  have h9C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 36) k67Prog 9 (.LI .x20 (0 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h9

  have hblk : cpsTripleWithin 10 K (K + 40) k67Code
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 8) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 16) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 24) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 32) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 40))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) ** (.x9 ↦ᵣ (BitVec.ofNat 64 lenN)) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) **
        ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ ret) ** ((sp0 + signExtend12 (-48 : BitVec 12)) + 8 ↦ₘ v8) ** ((sp0 + signExtend12 (-48 : BitVec 12)) + 16 ↦ₘ v9) **
        ((sp0 + signExtend12 (-48 : BitVec 12)) + 24 ↦ₘ v18) ** ((sp0 + signExtend12 (-48 : BitVec 12)) + 32 ↦ₘ v19) ** ((sp0 + signExtend12 (-48 : BitVec 12)) + 40 ↦ₘ v20)) := by
    runBlock h0C h1C h2C h3C h4C h5C h6C h7C h8C h9C
  have hblk' : cpsTripleWithin 10 K (K + 40) k67Code
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 8) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 16) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 24) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 32) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 40))
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) **
        (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        k67Ambient sp0 base omConst (BitVec.ofNat 64 lenN) v18 v19 (0 : Word) v21 **
        regOwn .x13 ** regOwn .x14) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) hblk
    have hs : (((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) **
      (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) ** (.x9 ↦ᵣ (BitVec.ofNat 64 lenN)) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ v21) **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) **
      regOwn .x13 ** regOwn .x14) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) (k67PrologueVals ret v8 v9 v18 v19 v20)) s := by
      unfold frameSlotsSaved k67Frame k67PrologueVals
      simp only [List.foldr_cons, List.foldr_nil, sepConj_emp_right']
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-48 : BitVec 12)) + (0 : Word) = (sp0 + signExtend12 (-48 : BitVec 12)) from by bv_omega,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show (sp0 + signExtend12 (-48 : BitVec 12)) + (8 : Word) = (sp0 + signExtend12 (-48 : BitVec 12)) + 8 from by bv_omega,
      show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show (sp0 + signExtend12 (-48 : BitVec 12)) + (16 : Word) = (sp0 + signExtend12 (-48 : BitVec 12)) + 16 from by bv_omega,
      show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show (sp0 + signExtend12 (-48 : BitVec 12)) + (24 : Word) = (sp0 + signExtend12 (-48 : BitVec 12)) + 24 from by bv_omega,
      show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show (sp0 + signExtend12 (-48 : BitVec 12)) + (32 : Word) = (sp0 + signExtend12 (-48 : BitVec 12)) + 32 from by bv_omega,
      show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
    show (sp0 + signExtend12 (-48 : BitVec 12)) + (40 : Word) = (sp0 + signExtend12 (-48 : BitVec 12)) + 40 from by bv_omega]
      xperm_hyp hq
    have hqF : (((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) **
      (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ base) ** (.x9 ↦ᵣ (BitVec.ofNat 64 lenN)) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ v21) **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) **
      regOwn .x13 ** regOwn .x14) ** frameSlotsOwn k67Frame (sp0 + signExtend12 (-48 : BitVec 12))) s :=
      sepConj_mono_right
        (EvmAsm.Codegen.ChainValidateExtraDataLengthSpec.frameSlotsSaved_implies_frameSlotsOwn
          k67Frame _ (k67PrologueVals ret v8 v9 v18 v19 v20)) s hs
    unfold k67Ambient at ⊢
    xperm_hyp hqF
  have hG : (regOwn .x13 ** regOwn .x14).pcFree := by
    repeat' first | apply pcFree_sepConj | exact pcFree_regOwn
  have hins := k67InitStep sp0 base omConst ret v12 v5 v6 v7 v28 v29 v30 v31
    v18 v19 (0 : Word) v21 bytes lenN hsalign hoff hover hvalid
    hll_len hll_over hll_valid
  have hinsG := cpsTripleWithin_frameR (regOwn .x13 ** regOwn .x14) hG hins
  have hblk'F : cpsTripleWithin 10 K (K + 40) fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 8) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 16) **
        memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 24) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 32) ** memOwn ((sp0 + signExtend12 (-48 : BitVec 12)) + 40))
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ base) ** (.x11 ↦ᵣ (BitVec.ofNat 64 lenN)) **
        (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        k67Ambient sp0 base omConst (BitVec.ofNat 64 lenN) v18 v19 (0 : Word) v21 **
        regOwn .x13 ** regOwn .x14) :=
    cpsTripleWithin_extend_code k67_mono hblk'
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      first
        | exact hp
        | rw [← sepConj_assoc] at hp; exact hp
        | rw [sepConj_assoc] at hp; exact hp
        | xperm_hyp hp) hblk'F hinsG
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      first
        | exact hq
        | rw [← sepConj_assoc] at hq; exact hq
        | rw [sepConj_assoc] at hq; exact hq
        | xperm_hyp hq) hseq

end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
