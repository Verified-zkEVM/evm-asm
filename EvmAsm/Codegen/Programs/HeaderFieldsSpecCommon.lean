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

/-- The two global scratch cells the success tail round-trips the decoded field
    offset and length through (`la ; sd ; … ; la ; ld`). -/
abbrev hesrOffAddr : Word := (Codegen.GuestAddrs.hesr_offset : Word)
abbrev hesrLenAddr : Word := (Codegen.GuestAddrs.hesr_length : Word)

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

/-! ## Outer dispatch foundations

    The five status-dispatch `BNE`s (init `[11]` + four nexts `[17]/[22]/[27]/[32]`)
    all route a nonzero status to the shared status-1 return (`+236`), and a zero
    status to the next straight-line block.  We handle each `BNE` by
    `cpsBranchWithin_merge_same_cr` to a *single* exit — the function return —
    with a *single* 3-way postcondition `hesrRetPost`.  The taken (fail) arm
    reaches it via `hesrStatus1Return` (a0 = 1, `Failure`); the not-taken (ok)
    arm continues the walk spine and reaches it via `hesrSuccessTail`
    (a0 ∈ {0,2}, `Success`).  These foundations set up the pieces shared by all
    five stages. -/

/-- Disjunction in the precondition: prove a triple for each disjunct. -/
theorem cpsTripleWithin_or_pre {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P1 P2 R : Assertion}
    (h1 : cpsTripleWithin n entry exit_ cr P1 R)
    (h2 : cpsTripleWithin n entry exit_ cr P2 R) :
    cpsTripleWithin n entry exit_ cr (fun h => P1 h ∨ P2 h) R := by
  intro F hF s hcr hPF hpc
  obtain ⟨hp, hcompat, s1, s2, hd, hu, hOr, hFs⟩ := hPF
  rcases hOr with hP | hP
  · exact h1 F hF s hcr ⟨hp, hcompat, s1, s2, hd, hu, hP, hFs⟩ hpc
  · exact h2 F hF s hcr ⟨hp, hcompat, s1, s2, hd, hu, hP, hFs⟩ hpc

/-- The 2-way normalized `rlp_walk_next` outcome: status-0 success
    (`rlpWalkNextOk`, so `x11 = 0`) or a nonzero-status failure carrying the
    generic `WalkFailure`.  Collapsing the raw 6-way `hesrNextOutcome` to this
    form is what the following `BNE x11, x0` dispatch reads. -/
def hesrNextNorm (listBase endPtr : Word) (bytes : List (BitVec 8)) (off : Nat) : Assertion :=
  fun h =>
    rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
    (∃ status : Word,
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜status ≠ (0 : Word) ∧
          RlpListNthItemSAsm.WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h))

/-- Every raw outcome disjunct implies the 2-way normalized form. -/
theorem hesrNextOutcome_to_norm (listBase endPtr : Word) (bytes : List (BitVec 8)) (off : Nat) :
    ∀ h, hesrNextOutcome listBase endPtr bytes off h → hesrNextNorm listBase endPtr bytes off h := by
  intro h hout
  unfold hesrNextOutcome at hout
  rcases hout with hOk | hb2 | hb3 | hb4 | hb5 | hb6
  · exact Or.inl hOk
  · refine Or.inr ⟨2, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb2
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inl hP⟩
  · refine Or.inr ⟨3, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb3
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩
  · refine Or.inr ⟨4, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb4
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩
  · refine Or.inr ⟨5, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb5
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩
  · refine Or.inr ⟨6, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb6
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩


/-! ## Stage 4 — the selected item (`next4`, `BNE[32]` @+128 → ret)

    The fourth `rlp_walk_next` at [31] (`+124`) decodes the zero-based 3rd child.
    `BNE x11, x0, 108`[32] routes a nonzero status to the shared status-1 exit
    (fail, `Failure.walk`) and status-0 to `hesrSuccessTail` (`+132`), where
    `StrictPrefix.select` upgrades the accumulated 3-item prefix to
    `StrictNthItem 3` = the selected field, and thence to `Success`. -/

/-- The caller-ambient registers the tail-block epilogues consume, folded to a
    single atom so the dispatch permutations count them as one (the WHNF/atom
    wall fix): stack pointer, `s0`/`s1`/`s2` and the saved frame. -/
def hesrAmbRegs (newSp listBase v9 outPtr : Word) (saved : Saved) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ outPtr) **
  savedFrame newSp saved

/-- Those same registers after the epilogue restores them, folded to one atom. -/
def hesrAmbRegsRestored (newSp : Word) (saved : Saved) : Assertion :=
  (.x2 ↦ᵣ (newSp + 48)) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** savedFrame newSp saved

/-- The two written global scratch cells, folded to one atom (both stay `memOwn`
    in the return post — `hesr_offset` is only written on the success tail, which
    `hesrRetPost` weakens back to `memOwn`). -/
def hesrScratchConst : Assertion := memOwn hesrOffAddr ** memOwn hesrLenAddr

theorem pcFree_hesrScratchConst : hesrScratchConst.pcFree := by
  unfold hesrScratchConst
  exact pcFree_sepConj pcFree_memOwn pcFree_memOwn

/-- The pass-through carry the walk and dispatch never write: the two global
    scratch cells (`hesrScratchConst`) and the output buffer.  Folded to one atom. -/
def hesrAmbConst (outPtr : Word) (outBytes : List (BitVec 8)) : Assertion :=
  hesrScratchConst ** bytesRegion outPtr outBytes

/-- The caller ambient the `rlp_walk_next` calls do not touch = `hesrAmbRegs`
    (consumed by the epilogue) followed by `hesrAmbConst` (pass-through). -/
def hesrWalkAmbient (newSp outPtr listBase v9 : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) : Assertion :=
  hesrAmbRegs newSp listBase v9 outPtr saved ** hesrAmbConst outPtr outBytes

theorem pcFree_hesrAmbRegs (newSp listBase v9 outPtr : Word) (saved : Saved) :
    (hesrAmbRegs newSp listBase v9 outPtr saved).pcFree := by
  unfold hesrAmbRegs savedFrame
  repeat' first
    | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs

theorem pcFree_hesrAmbRegsRestored (newSp : Word) (saved : Saved) :
    (hesrAmbRegsRestored newSp saved).pcFree := by
  unfold hesrAmbRegsRestored savedFrame
  repeat' first
    | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs

theorem pcFree_hesrAmbConst (outPtr : Word) (outBytes : List (BitVec 8)) :
    (hesrAmbConst outPtr outBytes).pcFree := by
  unfold hesrAmbConst
  exact pcFree_sepConj pcFree_hesrScratchConst (bytesRegion_pcFree _ _)

theorem pcFree_hesrWalkAmbient (newSp outPtr listBase v9 : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) :
    (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes).pcFree := by
  unfold hesrWalkAmbient
  exact pcFree_sepConj (pcFree_hesrAmbRegs _ _ _ _ _) (pcFree_hesrAmbConst _ _)

/-- Peel five owned scratch registers at once (local mirror of the committed
    `cpsTripleWithin_of_forall_regIs_to_regOwn7`). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn5
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 r4 r5 : Reg} {P Q : Assertion}
    (hspec : ∀ v1 v2 v3 v4 v5, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, ⟨v5, hv5⟩⟩ := hO4
  exact hspec v1 v2 v3 v4 v5 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, hv5⟩, hRb⟩ hpc

/-- Peel two owned scratch memory cells at once. -/
theorem cpsTripleWithin_of_forall_memIs_to_memOwn2
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {a1 a2 : Word} {P Q : Assertion}
    (hspec : ∀ v1 v2, cpsTripleWithin n entry exit_ cr
      (P ** (a1 ↦ₘ v1) ** (a2 ↦ₘ v2)) Q) :
    cpsTripleWithin n entry exit_ cr (P ** memOwn a1 ** memOwn a2) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, ⟨v2, hv2⟩⟩ := hO1
  exact hspec v1 v2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1, hv2⟩, hRb⟩ hpc

/-! ## Stages 1-3 — walk-and-recurse dispatch around a non-selected item

    Each of the first three `rlp_walk_next` calls decodes the zero-based child
    `K-1`, and on a zero status *continues* the walk (marshal the fresh cursor,
    recurse into the next stage) rather than selecting.  The FAIL arm is
    identical to stage 4's (route a nonzero status to the shared status-1
    return with `Failure.walk`); the OK arm replaces the success tail with
    `hesrMarshalNext ;; hesrStage(K+1)`, advancing the walked prefix by one via
    `StrictPrefix.step_bounds`. -/

/-- The two spill cells around a walker call, folded to one atom so the
    dispatch permutations count them as one (the atom-wall discipline). -/
def hesrSpill (newSp cursor endPtr : Word) : Assertion :=
  ((newSp + 32) ↦ₘ cursor) ** ((newSp + 40) ↦ₘ endPtr)

theorem pcFree_hesrSpill (newSp cursor endPtr : Word) :
    (hesrSpill newSp cursor endPtr).pcFree := by
  unfold hesrSpill
  exact pcFree_sepConj pcFree_memIs pcFree_memIs

/-- Peel seven owned scratch registers at once (local mirror of the committed
    `cpsTripleWithin_of_forall_regIs_to_regOwn7`). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn7
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 r4 r5 r6 r7 : Reg} {P Q : Assertion}
    (hspec : ∀ v1 v2 v3 v4 v5 v6 v7, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact hspec v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc


end EvmAsm.Codegen.HeaderFieldsSpec
