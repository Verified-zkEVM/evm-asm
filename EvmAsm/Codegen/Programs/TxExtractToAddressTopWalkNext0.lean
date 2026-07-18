/-
  Extract mid: first type234 walk_next ambient defs + BNE OK framed.
  Residual: walk_next0 call under ambient (of_forall peels) + OkFail normalize.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopType234

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

/-- Stable ambient walk_next0 does not touch. -/
def wn0Stable (txBase lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

private theorem wn0Stable_pcFree (txBase lenW typeW innerW endPtr cursor : Word) :
    (wn0Stable txBase lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn0Stable; pcf

/-- Common after walk_next (temps regOwn + ra link + bytes). -/
def wn0Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext0) **
    bytesRegion txBase txBytes

/-- OK arm: a1=0 with advanced cursor/len. -/
def wn0Ok (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    Assertion :=
  rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff

set_option maxRecDepth 8000 in
/-- BNE a1=0 not-taken under stable + common + concrete OK regs. -/
theorem extractWalkNext0BneOk_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      (wn0Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len))
      (wn0Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)) := by
  have h0 := extractWalkNext0BneOk
  have hF := cpsTripleWithin_frameR
    (wn0Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn0Stable, wn0Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn0Stable, wn0Common] at hq ⊢
    xperm_hyp hq) hF

#print axioms extractWalkNext0BneOk_framed

end EvmAsm.Codegen.TxExtractToAddressSpec
