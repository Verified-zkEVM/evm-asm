/-
  Pure honesty substrate for ExtractAssumed packaging.

  Connects `extractSuccess` (EL decode model) toward walk-machine residuals
  (`hcre` / `hlen20` / `rlpItemDecode` at field offsets). Full machine bridge
  (hdrop / hok* / hnext* universal packaging) remains residual.
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressModel

namespace EvmAsm.Codegen.TxExtractToAddressHonesty

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen.TxExtractToAddressModel

/-- Empty short string `0x80` at `off` with fit ⇒ `rlpItemDecode` len=0
    (hcre pure half for creation). `hfit`: `0 < end-cursor` i.e. room for header. -/
theorem rlpItemDecode_empty_short
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x80 : BitVec 8))
    (hfit : BitVec.ult (0 : Word) (endPtr - cursor) = true) :
    rlpItemDecode bytes off cursor endPtr
      (cursor + signExtend12 (1 : BitVec 12)) (0 : Word) := by
  refine ⟨(0x80 : BitVec 8), ?_, Or.inr (Or.inl ?_)⟩
  · rw [List.getElem?_eq_getElem hoff, hb]
  · have hge : ¬ BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0x80 : Word) = true := by
      decide
    have hlt : BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := by
      decide
    have hlen0 : (0x80 : BitVec 8).zeroExtend 64 - (0x80 : Word) = (0 : Word) := by
      decide
    refine ⟨hge, hlt, ?_, ?_, ?_, ?_⟩
    · intro h1
      rw [hlen0] at h1
      exact absurd h1 (by decide)
    · rwa [hlen0]
    · rw [hlen0]
      exact (BitVec.add_zero _).symm
    · exact hlen0

/-- Empty short string at `off` ⇒ walk_next OK assertion on matching regs. -/
theorem rlpWalkNextOk_empty_short
    (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hoff : srcOff < srcBytes.length)
    (hb : srcBytes[srcOff]'hoff = (0x80 : BitVec 8))
    (hfit : BitVec.ult (0 : Word)
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true) :
    ∀ h,
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word))) h →
      rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  intro h hp
  refine ⟨(srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12),
    (0 : Word), ?_⟩
  have hdec := rlpItemDecode_empty_short srcBytes srcOff
    (srcBase + BitVec.ofNat 64 srcOff) endPtr hoff hb hfit
  have hleft :
      (((((Reg.x10 ↦ᵣ
            (srcBase + BitVec.ofNat 64 srcOff + signExtend12 (1 : BitVec 12))) **
          (Reg.x11 ↦ᵣ (0 : Word))) ** (Reg.x12 ↦ᵣ (0 : Word))) **
        ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
          (srcBase + BitVec.ofNat 64 srcOff + signExtend12 (1 : BitVec 12))
          (0 : Word)⌝) h) :=
    (sepConj_pure_right h).2 ⟨by xperm_hyp hp, hdec⟩
  xperm_hyp hleft

/-- 20-byte short string prefix `0x94` (= 0x80+20) with fit ⇒ `rlpItemDecode` len=20.
    (hlen20 pure half when field is 20-byte address; canonicity vacuous since len≠1.) -/
theorem rlpItemDecode_addr20_short
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x94 : BitVec 8))
    (hfit : BitVec.ult (20 : Word) (endPtr - cursor) = true) :
    rlpItemDecode bytes off cursor endPtr
      ((cursor + signExtend12 (1 : BitVec 12)) + (20 : Word)) (20 : Word) := by
  refine ⟨(0x94 : BitVec 8), ?_, Or.inr (Or.inl ?_)⟩
  · rw [List.getElem?_eq_getElem hoff, hb]
  · have hge : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0x80 : Word) = true := by
      decide
    have hlt : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := by
      decide
    have hlen20 : (0x94 : BitVec 8).zeroExtend 64 - (0x80 : Word) = (20 : Word) := by
      decide
    refine ⟨hge, hlt, ?_, ?_, ?_, ?_⟩
    · intro h1
      rw [hlen20] at h1
      exact absurd h1 (by decide)
    · rwa [hlen20]
    · rw [hlen20]
    · exact hlen20

#print axioms rlpItemDecode_empty_short
#print axioms rlpWalkNextOk_empty_short
#print axioms rlpItemDecode_addr20_short

end EvmAsm.Codegen.TxExtractToAddressHonesty
