/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterReloadPointerPures

  Pure extractors for fixed x19 reload-pointer framed case splits.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTwoMulFixedIterReloadCondPointerScratchFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterSkipCondRestScratchPrefix
    expTwoMulFixedIterScratchIs
    expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
    expTwoMulFixedIterSkipCondRestScratchSuffix
    expTwoMulFixedIterReloadPointerFrame at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffix, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffix⟩ := hTail
  obtain ⟨_psRet, _psX19Tail, _hDisjointRet, _hUnionRet,
    _hRet, hX19Tail⟩ := hSuffix
  obtain ⟨_psX19, _psX18Tail, _hDisjointX19, _hUnionX19,
    _hX19, hX20Tail⟩ := hX19Tail
  obtain ⟨_psX20, _psX18Tail2, _hDisjointX20, _hUnionX20,
    _hX20, hX18Tail⟩ := hX20Tail
  obtain ⟨_psX18, _psC6Tail, _hDisjointX18, _hUnionX18,
    _hX18, hC6Tail⟩ := hX18Tail
  obtain ⟨_psC6, _psPtrTail, _hDisjointC6, _hUnionC6,
    hC6Pure, hPtrTail⟩ := hC6Tail
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) = 0 := hC6Pure.2
  obtain ⟨_psPtr, _psBit, _hDisjointPtr, _hUnionPtr,
    _hPtr, hBitPure⟩ := hPtrTail
  have h_bit :
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 :=
    hBitPure.2
  exact ⟨h_exit, h_c6, h_bit⟩

theorem expTwoMulFixedIterReloadSkipPointerScratchFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterSkipRestScratchPrefix
    expTwoMulFixedIterScratchIs
    expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
    expTwoMulFixedIterBaseFrame
    expTwoMulFixedIterReloadPointerFrame at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffix, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffix⟩ := hTail
  obtain ⟨_psRet, _psX19Tail, _hDisjointRet, _hUnionRet,
    _hRet, hX19Tail⟩ := hSuffix
  obtain ⟨_psX19, _psX18Tail, _hDisjointX19, _hUnionX19,
    _hX19, hX20Tail⟩ := hX19Tail
  obtain ⟨_psX20, _psX18Tail2, _hDisjointX20, _hUnionX20,
    _hX20, hX18Tail⟩ := hX20Tail
  obtain ⟨_psX18, _psC6Tail, _hDisjointX18, _hUnionX18,
    _hX18, hC6Tail⟩ := hX18Tail
  obtain ⟨_psC6, _psPtrTail, _hDisjointC6, _hUnionC6,
    hC6Pure, hPtrTail⟩ := hC6Tail
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) = 0 := hC6Pure.2
  obtain ⟨_psPtr, _psBitBase, _hDisjointPtr, _hUnionPtr,
    _hPtr, hBitBase⟩ := hPtrTail
  obtain ⟨_psBit, _psBase, _hDisjointBit, _hUnionBit,
    hBitPure, _hBase⟩ := hBitBase
  have h_bit :
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 :=
    hBitPure.2
  exact ⟨h_exit, h_c6, h_bit⟩

end EvmAsm.Evm64.Exp.Compose
