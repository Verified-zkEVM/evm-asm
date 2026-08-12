/-
  Named residual hypotheses for `mpt_walk` (#11799 / #12144).

  Coord rule (2026-08-11): unproven-callee residuals are DEPENDENCIES, not
  input-domain gates. They do not force `.conditional` and need no coverRef.
  They MUST be named in the statement and registered in Progress.Obligations
  so they cannot go invisible one level up.

  Residual inventory:

  1. `witness_lookup_by_hash` — empty-section miss triple EXISTS and is
     consumed at three walk sites via the GENERIC `wlCallWithinShape` after
     #12144 ambient repair (six telemetry cells in entry/return). Hit/general
     domain still DEPENDENCY until a hit triple lands.

  2. `hp_decode_nibbles` — RETIRED (registered `.proven`).

  3. Setup + root resolve after residual success — RETIRED
     (SetupBody + RootResolve).

  Ambient design (#12144 half-2):
  - Entry carries ABI + telemetry + section/hash bytes + out cells + x5/x6
    scratch values (machine empty-section needs concrete x5/x6).
  - Return carries status/off/len/telemetry-post + owns for clobbered ABI
    temps (x5,x6,x11–x14). Callee-saved s-regs and x7/x28–x31 live in the
    framed `F` (preserved / pass-through owns) so pre/post share one F.
-/

import EvmAsm.Codegen.Programs.MptWalkMachine
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-- GuestAddrs of the residual callee. -/
abbrev WlB : Word := BitVec.ofNat 64 GuestAddrs.witness_lookup_by_hash

/-- Six `.data` cells `witness_lookup_by_hash` always touches (#12144 Blocker 2). -/
abbrev WlCallsLoc : Word := BitVec.ofNat 64 GuestAddrs.wlh_lookup_calls
abbrev WlWidxEnLoc : Word := BitVec.ofNat 64 GuestAddrs.widx_enabled
abbrev WlLinCallsLoc : Word := BitVec.ofNat 64 GuestAddrs.wlh_linear_calls
abbrev WlLinLastLoc : Word := BitVec.ofNat 64 GuestAddrs.wlh_linear_last_section_len
abbrev WlLinMaxLoc : Word := BitVec.ofNat 64 GuestAddrs.wlh_linear_max_section_len
abbrev WlLinMissLoc : Word := BitVec.ofNat 64 GuestAddrs.wlh_linear_misses

/-- Telemetry footprint — must appear in residual entry/return so a
    universally quantified frame cannot own these cells under the residual. -/
def wlTelemetry (nCalls nLin nLast nMax nMiss widxEn : Word) : Assertion :=
  (WlCallsLoc ↦ₘ nCalls) ** (WlWidxEnLoc ↦ₘ widxEn) **
  (WlLinCallsLoc ↦ₘ nLin) ** (WlLinLastLoc ↦ₘ nLast) **
  (WlLinMaxLoc ↦ₘ nMax) ** (WlLinMissLoc ↦ₘ nMiss)

theorem wlTelemetry_pcFree (nCalls nLin nLast nMax nMiss widxEn : Word) :
    (wlTelemetry nCalls nLin nLast nMax nMiss widxEn).pcFree := by
  unfold wlTelemetry
  repeat' first
    | exact pcFree_memIs | apply pcFree_sepConj

/-- Call-site entry ambient for `witness_lookup_by_hash`.
    Includes x5/x6 scratch values so empty-section machine pre matches
    without putting clobbered regs in the shared frame F. -/
def wlCallEntry (sp0 secPtr secLenW hashPtr oldOff oldLen : Word)
    (secBytes hashBytes : List (BitVec 8))
    (v5 v6 : Word)
    (nCalls nLin nLast nMax nMiss widxEn : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ secPtr) ** (.x11 ↦ᵣ secLenW) ** (.x12 ↦ᵣ hashPtr) **
  (.x13 ↦ᵣ MwLookupOff) ** (.x14 ↦ᵣ MwLookupLen) **
  (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  (MwLookupOff ↦ₘ oldOff) ** (MwLookupLen ↦ₘ oldLen) **
  wlTelemetry nCalls nLin nLast nMax nMiss widxEn

/-- Call-site return ambient after residual. Status in a0; owns for temps the
    empty-section miss path leaves concrete (weakened to owns). Out cells at
    post values. Telemetry at post values. Does NOT own x7/x28–x31 or
    callee-saved s-regs — those live in framed F. -/
def wlCallReturn (sp0 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (status off len : Word)
    (nCalls nLin nLast nMax nMiss widxEn : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ status) **
  regOwn .x5 ** regOwn .x6 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  (MwLookupOff ↦ₘ off) ** (MwLookupLen ↦ₘ len) **
  wlTelemetry nCalls nLin nLast nMax nMiss widxEn

/-- Existential return (status/off/len/telemetry-post unknown until residual). -/
def wlCallReturnEx (sp0 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8)) : Assertion :=
  fun h => ∃ status off len nCalls nLin nLast nMax nMiss widxEn,
    wlCallReturn sp0 secPtr hashPtr secBytes hashBytes status off len
      nCalls nLin nLast nMax nMiss widxEn h

/-- Residual hit return: status=0, off/len known; telemetry concrete. -/
def wlHitReturn (sp0 secPtr hashPtr off len : Word)
    (secBytes hashBytes : List (BitVec 8))
    (nCalls nLin nLast nMax nMiss widxEn : Word) : Assertion :=
  wlCallReturn sp0 secPtr hashPtr secBytes hashBytes (0 : Word) off len
    nCalls nLin nLast nMax nMiss widxEn

/-- Shape a residual `h_wl` must satisfy at one callWithin site.
    `F` must be preserved across the call (callee-saved s-regs, x7/x28–x31
    owns, user ambient). Entry/return carry telemetry + ABI + bytes/out. -/
def wlCallWithinShape (cr : CodeReq) (callerPC vOld sp0 secPtr secLenW hashPtr
    oldOff oldLen : Word) (secBytes hashBytes : List (BitVec 8))
    (v5 v6 : Word)
    (nCalls nLin nLast nMax nMiss widxEn : Word)
    (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  F.pcFree ∧
  (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = WlB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
    cr a = some i) ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) ** wlCallEntry sp0 secPtr secLenW hashPtr oldOff oldLen
      secBytes hashBytes v5 v6 nCalls nLin nLast nMax nMiss widxEn) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) ** wlCallReturnEx sp0 secPtr hashPtr
      secBytes hashBytes) ** F)

/-! ## Enable=1 residual (#12183 step 4)

    Production walk ambient after successful `witness_index_build` has
    `widx_enabled = 1`. Nested indexed call needs `stackFree sp0 16`
    (parent Own 8 + nested Own 8 — SAY SO). Linear telemetry (Lin*) is
    NOT bumped; Idx* is. Out cells stay at MwLookupOff/Len.
-/

/-- Extra BSS cells the enable path touches (section match + idx counters).
    Shape `wlCallWithinShapeEn` lives next to `wlhCallWithin_enabled_empty`
    in WitnessLookupByHashEnabledWrap (same ambient; not redefined here). -/
abbrev WlSecPtrLoc : Word := BitVec.ofNat 64 GuestAddrs.widx_section_ptr
abbrev WlSecLenLoc : Word := BitVec.ofNat 64 GuestAddrs.widx_section_len
abbrev WlWidxCountLoc : Word := BitVec.ofNat 64 GuestAddrs.widx_count
abbrev WlIdxCallsLoc : Word := BitVec.ofNat 64 GuestAddrs.wlh_indexed_calls
abbrev WlIdxMissLoc : Word := BitVec.ofNat 64 GuestAddrs.wlh_indexed_misses

/-- Obligation retirement note (rendered into Progress.Obligations). -/
def witnessLookupResidualNote : String :=
  "PRODUCTION empty-miss: wlCallWithinShapeEn (enable=1, stackFree 16) \
in EnabledWrap; discharged at three walk sites via MptWalkWlEnabledEmpty \
(#12183). LEGACY enable=0: wlCallWithinShape via MptWalkWlEmpty (#12144). \
Hit/general: still need hit-domain triple + callWithin (wlCallWithinShapeHit)"
def hpDecodeResidualNote : String :=
  "RETIRED: `hp_decode_nibbles_spec` already exists \
(HpDecodeNibblesSAsmPaths); registered `.proven` under #11799 and consumed \
via HpDecodeNibblesCallSAsm callWithin. No residual."

def setupRootResidualNote : String :=
  "RETIRED: MptWalkSetupBody (ABI+hash-copy+wl-ABI) + MptWalkRootResolve \
(after residual success → kind ABI at pc47). Only the JAL to \
witness_lookup_by_hash remains (empty miss via generic shape; hit DEPENDENCY)."

end EvmAsm.Codegen.MptWalkSpec
