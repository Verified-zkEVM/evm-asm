/-
  Extension arm: callWithin `hp_decode_nibbles` at pc147 (#11799).

  Consumes `hp_decode_nibbles_call_spec_within` (adapter over the pre-existing
  whole-routine triple in HpDecodeNibblesSAsmPaths). Frame match confirmed:
  standard abiFrame sp-48, ra-factor via regsAt_hdnFrame_factor; walk stack
  free below newSp already ≥8 dwords (nth), hp needs 6.

  Precondition at call: `extHpAbi` (built by `ext_after_nth_ok_to_hp_abi`).
-/

import EvmAsm.Codegen.Programs.MptWalkExtHp
import EvmAsm.Codegen.Programs.HpDecodeNibblesCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HpDecodeNibblesSAsm

set_option maxRecDepth 8000

private theorem ext_hp_jal_target :
    pc 147 + signExtend21
      (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 588)) =
      HpDecodeB := by
  unfold pc walkB HpDecodeB; decide

private theorem ext_hp_ret_even :
    ((pc 147 + 4) &&& ~~~(1 : Word)) = pc 147 + 4 := by
  unfold pc walkB; decide

private theorem ext_hp_pc :
    pc 147 = walkB + BitVec.ofNat 64 (4 * 147) := by
  unfold pc; rfl

/-- Saved-reg map for hp frame at the ext call: link in ra; free values
    for the five callee-saved slots (restored on return). -/
def extHpVals (link s0 s1 s2 s3 s4 : Word) : Reg → Word
  | .x1 => link
  | .x8 => s0
  | .x9 => s1
  | .x18 => s2
  | .x19 => s3
  | .x20 => s4
  | _ => 0

/-- Fuel: 1 JAL + hp whole-routine. -/
def extHpCallFuel (srcLen : Nat) : Nat :=
  1 + hdnFuel srcLen

/-- Walk ambient framed through the hp call.
    Path/nibble bytes live in `hdnCallEntry` (no double-own). -/
def extHpCallFrame (newSp : Word) (ws : WalkSaved)
    (nodeBase pathOff pathLen : Word) : Assertion :=
  walkSavedFrame newSp ws **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x23 ↦ᵣ nodeBase) **
  (MwPathOff ↦ₘ pathOff) ** (MwPathLen ↦ₘ pathLen) **
  stackFree newSp 8

theorem extHpCallFrame_pcFree (newSp : Word) (ws : WalkSaved)
    (nodeBase pathOff pathLen : Word) :
    (extHpCallFrame newSp ws nodeBase pathOff pathLen).pcFree := by
  unfold extHpCallFrame walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _
    | apply pcFree_sepConj

/-! Ext arm JAL hp_decode_nibbles at pc147. -/
theorem ext_hp_call_spec_within
    (newSp : Word) (ws : WalkSaved)
    (nodeBase pathOff pathLenW : Word)
    (pathBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (s0 s1 s2 s3 s4 raVal : Word)
    (hlen : pathLenW = BitVec.ofNat 64 pathBytes.length)
    (halign : (nodeBase + pathOff).toNat % 8 = 0)
    (hover : (nodeBase + pathOff).toNat + pathBytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < pathBytes.length →
      isValidByteAccess (nodeBase + pathOff + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 pathBytes + 2 * (pathBytes.length - 1) ≤ bufOrig.length)
    (hdalign : MwNibbleBuf.toNat % 8 = 0)
    (hdover : MwNibbleBuf.toNat + bufOrig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < bufOrig.length →
      isValidByteAccess (MwNibbleBuf + BitVec.ofNat 64 j) = true) :
    let vals := extHpVals (pc 147 + 4) s0 s1 s2 s3 s4
    let src := nodeBase + pathOff
    cpsTripleWithin (extHpCallFuel pathBytes.length) (pc 147) (pc 147 + 4) fullCode
      (((.x1 ↦ᵣ raVal) **
        hdnCallEntry newSp vals src MwNibbleBuf MwNibbleCount MwIsLeaf
          pathBytes bufOrig v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl) **
        extHpCallFrame newSp ws nodeBase pathOff pathLenW)
      (((.x1 ↦ᵣ (pc 147 + 4)) **
        hdnCallReturn newSp vals src MwNibbleBuf MwNibbleCount MwIsLeaf
          pathBytes bufOrig oldCnt oldIsl) **
        extHpCallFrame newSp ws nodeBase pathOff pathLenW) := by
  intro vals src
  have _ := hlen  -- pathLenW ↔ ofNat pathBytes.length for callers
  have hcall0 := hp_decode_nibbles_call_spec_within (cr := fullCode)
    (pc 147) HpDecodeB raVal newSp vals
    src MwNibbleBuf MwNibbleCount MwIsLeaf pathBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl
    (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 588))
    (extHpCallFrame newSp ws nodeBase pathOff pathLenW)
    (extHpCallFrame_pcFree newSp ws nodeBase pathOff pathLenW)
    (by simp only [vals, extHpVals])
    ext_hp_ret_even
    halign hover hvalid hbuf hdalign hdover hdvalid
    ext_hp_jal_target
    (by rfl)
    (walkMem (pc 147) 147
      (.JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 588)))
      (by decide) (by unfold pc walkB; decide) (by rfl))
    hpCalleeMem
  simpa [extHpCallFuel, src] using hcall0

end EvmAsm.Codegen.MptWalkSpec
