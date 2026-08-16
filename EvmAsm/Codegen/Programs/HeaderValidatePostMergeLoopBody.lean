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

end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
