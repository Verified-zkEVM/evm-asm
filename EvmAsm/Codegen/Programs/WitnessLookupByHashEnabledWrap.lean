/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledWrap

  #12183 — body core enable=1 empty-miss under nested stack.

  Composes body_to_call + call_to_bodyExit. abiFrame whole-routine wrap follows.
  Domain: widx_enabled=1, widx_count=0, section_len=0 (REACHABLE).
  Nested stack: `stackFree newSp 8` below parent frame (walk needs sp0 16 — SAY SO).

  Ambient split at call:
  * CallP owns ABI + nested Own + WidxCount (from Empty)
  * Extra owns counters/cells + parent frameSlotsSaved + temps not in CallP
  BodyF must NOT pin x10 (Aregs owns it after ABI restore).
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledBody
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledEmpty
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec (WidxCountLoc indexedFrame)
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty (IndexedSaved indexedSavedVals)

set_option maxRecDepth 8000

/-- Nested stack free below parent SP. -/
def wlhEnNestedStack (spC : Word) : Assertion :=
  frameSlotsOwn indexedFrame (spC + signExtend12 (-64 : BitVec 12))

theorem wlhEnNestedStack_pcFree (spC : Word) :
    (wlhEnNestedStack spC).pcFree := by
  unfold wlhEnNestedStack; pcf

/-- Body ambient F through setup→call: parent frame + nested stack + x1/x2/x21/x22.
    No x10 — Aregs owns a0 after ABI restore (would double-own). -/
def wlhEnBodyF (newSp : Word) (vals : Reg → Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x2 : Reg) ↦ᵣ newSp) **
  ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
  frameSlotsSaved wlhFrame newSp vals **
  wlhEnNestedStack newSp

theorem wlhEnBodyF_pcFree (newSp : Word) (vals : Reg → Word) :
    (wlhEnBodyF newSp vals).pcFree := by
  unfold wlhEnBodyF wlhEnNestedStack; pcf

/-- +36 → +580 body under nested stack. Fuel 68 = 32+36.
    Entry s-regs a8..a20 are overwritten by arg moves to secPtr/0/hash/outOff/outLen.
    After call path, x10=1 (indexed miss), outs written only on hit (empty keeps a3/a4). -/
theorem wlhEn_body_core
    (newSp : Word) (vals : Reg → Word)
    (v5 v6 : Word)
    (a8 a9 a18 a19 a20 : Word)
    (secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    let s := wlhEnIdxSaved (vals .x1) secPtr hashPtr outOff outLen
      (vals .x21) (vals .x22)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 68 (wlhB + 36) (wlhB + 580) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) **
        ((.x20 : Reg) ↦ᵣ a20) **
        wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss **
        wlhEnBodyF newSp vals)
      (wlhEnBodyExit newSp retCall s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr
        (frameSlotsSaved wlhFrame newSp vals)) := by
  intro s retCall
  have hF := wlhEnBodyF_pcFree newSp vals
  -- setup → call entry (+36 → +164)
  have h1 := wlhEn_body_to_call v5 v6 a8 a9 a18 a19 a20
    secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
    (wlhEnBodyF newSp vals) hF
  -- Reshape body_to_call post → (x1 ** CallP ** Extra)
  -- body_to_call post:
  --   x0, x5=IdxCallsLoc, x6=nIdx+1, Aregs, Sregs, Cells, BodyF
  -- CallP: x2, s0-s6, x12-14, x5, x10, nested Own, WidxCount
  --   with s0=secPtr,s1=0,s2=hash,s3=outOff,s4=outLen,s5=x21,s6=x22
  --   v5=IdxCallsLoc, v10=secPtr (a0 after ABI)
  -- Extra: x0, x6, x11, cells sans WidxCount, parent Saved
  have h1' : cpsTripleWithin 32 (wlhB + 36) (wlhB + 164) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) **
        ((.x20 : Reg) ↦ᵣ a20) **
        wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss **
        wlhEnBodyF newSp vals)
      ((.x1 ↦ᵣ vals .x1) **
        wlhIdxCallP newSp s hashPtr outOff outLen IdxCallsLoc secPtr **
        wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr
          (frameSlotsSaved wlhFrame newSp vals)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h1
    dsimp [wlhEnAregs, wlhEnSregs, wlhEnCells, wlhEnBodyF, wlhEnNestedStack,
      wlhIdxCallP, wlhEnCallExtra, wlhEnIdxSaved, indexedSavedVals, s] at hq ⊢
    xperm_chunked hq
  -- call → body exit (+164 → +580)
  have h2 := wlhEn_call_to_bodyExit newSp (vals .x1) (vals .x21) (vals .x22)
    secPtr hashPtr outOff outLen IdxCallsLoc secPtr
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
    (frameSlotsSaved wlhFrame newSp vals) (by pcf)
  have c := cpsTripleWithin_seq_same_cr h1' h2
  exact cpsTripleWithin_mono_nSteps (by decide : 32 + 36 ≤ 68) c

/-! ## Remaining (next commit / follow-on)

abiFrame whole-routine wrap under enable=1:
* Reshape body_core ↔ abiFrame body (regsAt/regsOwnAt + callerPre/Post)
* Peel concrete s-regs → owns at body exit (ent_own8 pattern from empty_section)
* Nested stack Own at newSp-64 in pre; Saved after nested epi in post
* Fuel 87 = 1+8+68+8+1+1; CR = enableFullCode via wlh_in_enableFull

Then: MptWalkWlEmpty three sites + WlCall docs + Routines row onto enable=1.
-/

end EvmAsm.Codegen.WitnessLookupByHashSpec
