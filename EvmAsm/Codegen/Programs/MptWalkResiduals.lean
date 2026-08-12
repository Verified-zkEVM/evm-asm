/-
  Named residual hypotheses for `mpt_walk` (#11799).

  Coord rule (2026-08-11): unproven-callee residuals are DEPENDENCIES, not
  input-domain gates. They do not force `.conditional` and need no coverRef.
  They MUST be named in the statement and registered in Progress.Obligations
  so they cannot go invisible one level up.

  Residual inventory after this branch's arm work:

  1. `witness_lookup_by_hash` — empty-section miss triple EXISTS
     (`witness_lookup_by_hash_spec_within_empty_section`). After #12144
     walk `fullCode` includes `wlhCr`; three sites discharge empty-section
     miss via `MptWalkWlEmpty` (no free `h_wl`). Hit-domain residual
     (`wlCallWithinShapeHit`) remains a DEPENDENCY until a hit triple
     lands. Generic `wlCallWithinShape` still omits telemetry cells
     (Blocker 2) — prefer empty-section lemmas for miss.

  2. `hp_decode_nibbles` — ALREADY has `hp_decode_nibbles_spec`
     (HpDecodeNibblesSAsmPaths, abiFrame). Was unregistered. Consumed via
     callWithin adapter (HpDecodeNibblesCallSAsm); registered `.proven`.
     NOT a residual.

  3. Setup + root resolve after residual lookup success — RETIRED by
     MptWalkSetupBody + MptWalkRootResolve (proved through JAL ABI /
     pc36→pc47 kind entry). Only the JAL itself is residual (1).

  A residual bounds what you can CONCLUDE, not what you CLAIM about the
  parts already proved. Posts of proved pieces stay full-strength
  (path-preserve free strengthen on kind is the worked example).
-/

import EvmAsm.Codegen.Programs.MptWalkMachine
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-- GuestAddrs of the residual callee. -/
abbrev WlB : Word := BitVec.ofNat 64 GuestAddrs.witness_lookup_by_hash

/-- Call-site entry ambient for `witness_lookup_by_hash` (guest ABI at every
    walk JAL): a0=section, a1=len, a2=hash ptr, a3/a4=out cells,
    stack free ≥ 8 dwords for the callee frame. -/
def wlCallEntry (sp0 secPtr secLenW hashPtr oldOff oldLen : Word)
    (secBytes hashBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ secPtr) ** (.x11 ↦ᵣ secLenW) ** (.x12 ↦ᵣ hashPtr) **
  (.x13 ↦ᵣ MwLookupOff) ** (.x14 ↦ᵣ MwLookupLen) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  (MwLookupOff ↦ₘ oldOff) ** (MwLookupLen ↦ₘ oldLen)

/-- Call-site return ambient after residual `witness_lookup_by_hash`.
    Status in a0 (0 hit / 1 miss); on hit out cells hold matched
    (offset, length). Scratch owns. Future machine must also pin pure
    `witnessLookupSpec` alignment — that pure bridge is part of what
    retires the residual, not a silent walk-post weaken. -/
def wlCallReturn (sp0 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (status off len : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ status) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  (MwLookupOff ↦ₘ off) ** (MwLookupLen ↦ₘ len)

/-- Existential return (status/off/len unknown until residual fires). -/
def wlCallReturnEx (sp0 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8)) : Assertion :=
  fun h => ∃ status off len,
    wlCallReturn sp0 secPtr hashPtr secBytes hashBytes status off len h

/-- Residual hit return: status=0, off/len known. -/
def wlHitReturn (sp0 secPtr hashPtr off len : Word)
    (secBytes hashBytes : List (BitVec 8)) : Assertion :=
  wlCallReturn sp0 secPtr hashPtr secBytes hashBytes (0 : Word) off len

/-- Shape a residual `h_wl` must satisfy at one callWithin site.
    Compose lemmas take `h_wl` of this shape (instantiated at the site's
    callerPC / F / bytes) rather than building the machine. -/
def wlCallWithinShape (cr : CodeReq) (callerPC vOld sp0 secPtr secLenW hashPtr
    oldOff oldLen : Word) (secBytes hashBytes : List (BitVec 8))
    (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  F.pcFree ∧
  (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = WlB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
    cr a = some i) ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) ** wlCallEntry sp0 secPtr secLenW hashPtr oldOff oldLen
      secBytes hashBytes) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) ** wlCallReturnEx sp0 secPtr hashPtr
      secBytes hashBytes) ** F)

/-- Obligation retirement note (rendered into Progress.Obligations). -/
def witnessLookupResidualNote : String :=
  "empty-section miss: discharged at three walk sites via MptWalkWlEmpty \
applying witness_lookup_by_hash_spec_within_empty_section (#12144; fullCode \
includes wlhCr). Hit/general domain: still need \
witness_lookup_by_hash_spec_within + callWithin (wlCallWithinShapeHit)"

def hpDecodeResidualNote : String :=
  "RETIRED: `hp_decode_nibbles_spec` already exists \
(HpDecodeNibblesSAsmPaths); registered `.proven` under #11799 and consumed \
via HpDecodeNibblesCallSAsm callWithin. No residual."

def setupRootResidualNote : String :=
  "RETIRED: MptWalkSetupBody (ABI+hash-copy+wl-ABI) + MptWalkRootResolve \
(after residual success → kind ABI at pc47). Only the JAL to \
witness_lookup_by_hash remains, covered by wlCallWithinShape."

end EvmAsm.Codegen.MptWalkSpec
