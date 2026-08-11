/-
  Leaf arm: callWithin `hp_decode_nibbles` at pc242 (#11799).

  Mirror of MptWalkExtHpCall. Consumes
  `hp_decode_nibbles_call_spec_within`. Frame match same as ext.
-/

import EvmAsm.Codegen.Programs.MptWalkLeafHp
import EvmAsm.Codegen.Programs.HpDecodeNibblesCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HpDecodeNibblesSAsm

set_option maxRecDepth 8000

private theorem leaf_hp_jal_target :
    pc 242 + signExtend21
      (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 968)) =
      HpDecodeB := by
  unfold pc walkB HpDecodeB; decide

private theorem leaf_hp_ret_even :
    ((pc 242 + 4) &&& ~~~(1 : Word)) = pc 242 + 4 := by
  unfold pc walkB; decide

/-- Saved-reg map for hp frame at the leaf call. -/
def leafHpVals (link s0 s1 s2 s3 s4 : Word) : Reg → Word
  | .x1 => link
  | .x8 => s0
  | .x9 => s1
  | .x18 => s2
  | .x19 => s3
  | .x20 => s4
  | _ => 0

def leafHpCallFuel (srcLen : Nat) : Nat :=
  1 + hdnFuel srcLen

/-- Walk ambient framed through the leaf hp call. -/
def leafHpCallFrame (newSp : Word) (ws : WalkSaved)
    (nodeBase pathOff pathLen : Word) : Assertion :=
  walkSavedFrame newSp ws **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x23 ↦ᵣ nodeBase) **
  (MwPathOff ↦ₘ pathOff) ** (MwPathLen ↦ₘ pathLen) **
  stackFree newSp 8

theorem leafHpCallFrame_pcFree (newSp : Word) (ws : WalkSaved)
    (nodeBase pathOff pathLen : Word) :
    (leafHpCallFrame newSp ws nodeBase pathOff pathLen).pcFree := by
  unfold leafHpCallFrame walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _
    | apply pcFree_sepConj

/-! Leaf arm JAL hp_decode_nibbles at pc242. -/
theorem leaf_hp_call_spec_within
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
    let vals := leafHpVals (pc 242 + 4) s0 s1 s2 s3 s4
    let src := nodeBase + pathOff
    cpsTripleWithin (leafHpCallFuel pathBytes.length) (pc 242) (pc 242 + 4) fullCode
      (((.x1 ↦ᵣ raVal) **
        hdnCallEntry newSp vals src MwNibbleBuf MwNibbleCount MwIsLeaf
          pathBytes bufOrig v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl) **
        leafHpCallFrame newSp ws nodeBase pathOff pathLenW)
      (((.x1 ↦ᵣ (pc 242 + 4)) **
        hdnCallReturn newSp vals src MwNibbleBuf MwNibbleCount MwIsLeaf
          pathBytes bufOrig oldCnt oldIsl) **
        leafHpCallFrame newSp ws nodeBase pathOff pathLenW) := by
  intro vals src
  have _ := hlen
  have hcall0 := hp_decode_nibbles_call_spec_within (cr := fullCode)
    (pc 242) HpDecodeB raVal newSp vals
    src MwNibbleBuf MwNibbleCount MwIsLeaf pathBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl
    (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 968))
    (leafHpCallFrame newSp ws nodeBase pathOff pathLenW)
    (leafHpCallFrame_pcFree newSp ws nodeBase pathOff pathLenW)
    (by simp only [vals, leafHpVals])
    leaf_hp_ret_even
    halign hover hvalid hbuf hdalign hdover hdvalid
    leaf_hp_jal_target
    (by rfl)
    (walkMem (pc 242) 242
      (.JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 968)))
      (by decide) (by unfold pc walkB; decide) (by rfl))
    hpCalleeMem
  simpa [leafHpCallFuel, src] using hcall0

end EvmAsm.Codegen.MptWalkSpec
