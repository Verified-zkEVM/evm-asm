/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecJoin

  Call-return peel helpers and fail-arm glue for K145 `tx_signing_hash`
  Spec (#12038); multi-rate segments. Lives outside `TxSigningHashSpecSuccess` to stay
  under the Programs 1500-line cap.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecPrefixGate

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Codegen.MptSpliceSlotSpec
open EvmAsm.Rv64.Tactics

/-! ## Fail arm: post-nth `bne` taken → `li a0,1` → `bodyExit` -/

/-- Fail arm: `bne` taken then `li a0,1`. `H+160 → bodyExit`. -/
theorem tshNthFailThroughBodyExit_spec
    (st : Word) (F : Assertion) (hF : F.pcFree) (hnz : st ≠ 0) :
    cpsTripleWithin (1 + 1) (H + 160) tshBodyExit fullCode
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr := tshNthFail_taken st hnz
  have hbrF := cpsTripleWithin_frameR F hF hbr
  have hli := tshFailLi_spec st
  have hliF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** F) (pcFree_sepConj pcFree_regIs hF) hli
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hbrF hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c

/-! ## Type-prefix dword ↔ one-byte `bytesRegion` -/

/-- Bridge: one-byte `bytesRegion` is the packed dword cell. -/
theorem tsh_typeByte_bytesRegion (b : BitVec 8) :
    bytesRegion TshBuf [b] = (TshBuf ↦ₘ packBytes [b]) := by
  simp only [bytesRegion, List.length_singleton, Nat.reduceAdd, Nat.reduceDiv,
    bytesRegionAux, sepConj_emp_right']
  rfl

/-- `TshBuf` is dword-aligned (`GuestAddrs.tsh_buf` ends in `0`). -/
theorem tshBuf_byteOffset_zero : byteOffset TshBuf = 0 := by
  decide

/-- Packing a singleton is just the zero-extended byte. -/
theorem tsh_packBytes_singleton (b : BitVec 8) :
    packBytes [b] = b.zeroExtend 64 := by
  unfold packBytes packDword getByteAt
  simp [List.getElem_cons_zero, BitVec.or_zero]

/-- When the high bytes of the dword are clear, `SB` matches `packBytes [b]`. -/
theorem tsh_replaceByte_eq_packBytes (wordOld : Word) (b : BitVec 8)
    (hhi : wordOld &&& ~~~(0xFF#64) = 0) :
    replaceByte wordOld (byteOffset TshBuf) b = packBytes [b] := by
  rw [tshBuf_byteOffset_zero, tsh_packBytes_singleton]
  unfold replaceByte
  have hmul : (0 : Nat) * 8 = 0 := rfl
  simp only [hmul]
  have hff : 0xFF#64 <<< (0 : Nat) = 0xFF#64 := rfl
  rw [hff, BitVec.shiftLeft_zero, hhi]
  change (0#64) ||| BitVec.zeroExtend 64 b = BitVec.zeroExtend 64 b
  rw [BitVec.zero_or]

/-- Reshape the nth call-frame type dword into a one-byte region. -/
theorem tshNthCallFrame_eq_typeBytes
    (v22 wordBuf a3 : Word)
    (hhi : wordBuf &&& ~~~(0xFF#64) = 0) :
    tshNthCallFrame v22 wordBuf a3 =
      ((.x22 ↦ᵣ v22) ** bytesRegion TshBuf [a3.truncate 8]) := by
  unfold tshNthCallFrame
  rw [tsh_replaceByte_eq_packBytes wordBuf (a3.truncate 8) hhi,
    tsh_typeByte_bytesRegion]

/-! ## Disjunctive post helper for peel outcomes -/

/-- Disjunctive post at `tshBodyExit` after the post-nth status check. -/
def tshNthOutcomePost (Qok Qfail : Assertion) : Assertion :=
  fun h => Qok h ∨ Qfail h

/-! The payload-length equation is a property of the item returned by the
    preceding list lookup, not of arbitrary `Word` pairs.  Keeping the header
    length explicit lets the CPS post carry the fact to the SpecRef bridge
    without baking the one-byte K145 prefix into a universally quantified
    premise. -/
def tshPayloadLenEq (payloadBs : List (BitVec 8))
    (hdrLen offVal lenVal : Word) : Prop :=
  ((offVal + lenVal) - hdrLen) = BitVec.ofNat 64 payloadBs.length

/-! A non-degenerate concrete success witnesses that the scoped relation is
    inhabited: a five-byte short list with a three-byte child payload. -/
theorem tshPayloadLenEq_nonvacuous :
    ∃ offVal lenVal,
      RlpListNthItemSAsm.Success
          [0xc4, 0x83, 0x01, 0x02, 0x03] (0x1000 : Word) 5 0
          offVal lenVal ∧
        tshPayloadLenEq [0x83, 0x01, 0x02, 0x03]
          (1 : Word) offVal lenVal := by
  refine ⟨2, 3, ?_, ?_⟩
  · refine ⟨1, (0x1000 : Word) + (5 : Word), (0x1000 : Word) + (5 : Word), ?_, ?_, ?_⟩
    · exact .short 5 1 (0xc4 : BitVec 8)
        (by decide) (by decide) (by decide) rfl (by decide)
    · refine .zero 1 ((0x1000 : Word) + (5 : Word)) (3 : Word) ?_
      refine ⟨0x83, by decide, Or.inr (Or.inl ?_)⟩
      all_goals decide
    · decide
  · simp [tshPayloadLenEq]

/-! The source-aware call-return result keeps the caller's input ownership in
    one place.  Its pure `Result` still records the original list bytes, while
    the linear byte resource is represented by the KSS source contract. -/
def tshCallReturnResultSource
    (sp0 listBase _indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (sourcePtr : Word) (payloadBs : List (BitVec 8))
    (source : KssSource) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    ((((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail saved) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
       (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
      ⌜RlpListNthItemSAsm.Result bytes listBase listLen index oldOffset oldLen
        status offset len⌝) h

theorem callReturnResult_to_source
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (sourcePtr : Word) (payloadBs : List (BitVec 8)) (source : KssSource)
    (hsource : source.region sourcePtr payloadBs =
      bytesRegion listBase bytes) :
    callReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
      saved bytes listLen index =
      tshCallReturnResultSource sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index sourcePtr payloadBs source := by
  funext h
  simp only [callReturnResult, tshCallReturnResultSource]
  rw [hsource]

theorem tshNthOutcomePost_inl {Qok Qfail : Assertion} {h : PartialState}
    (hq : Qok h) : tshNthOutcomePost Qok Qfail h :=
  Or.inl hq

theorem tshNthOutcomePost_inr {Qok Qfail : Assertion} {h : PartialState}
    (hq : Qfail h) : tshNthOutcomePost Qok Qfail h :=
  Or.inr hq

/-- Peel `callReturnResult` then case on `Result`.

    * `ok`: obligation is the concrete nth-success scratch (status 0, off/len,
      `regOwn` temps, `savedRegTail`, …) under caller ambient `F`.
    * `fail`: obligation is the same ambient with status 1 and unchanged
      off/len cells. -/
theorem tsh_cpsTripleWithin_callReturn_cases
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hok : ∀ offset len v11 v12,
        Success bytes listBase listLen index offset len →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q)
    (hfail : ∀ v11 v12,
        Failure bytes listBase listLen index →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
              (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen)))) ** F) Q) :
    cpsTripleWithin N (H + 160) ret fullCode
      (((.x1 ↦ᵣ X) **
        callReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
          csaved bytes listLen index) ** F) Q := by
  apply tsh_cpsTripleWithin_callReturn_pre sp0 listBase indexW offsetPtr lenPtr
    oldOffset oldLen csaved bytes listLen index
  intro status offset len v11 v12 hResult
  cases hResult with
  | ok _ _ hSucc => exact hok offset len v11 v12 hSucc
  | fail hFail => exact hfail v11 v12 hFail

theorem tsh_cpsTripleWithin_callReturn_pre_source_impl
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (sourcePtr : Word) (payloadBs : List (BitVec 8)) (source : KssSource)
    (h : ∀ status offset len v11 v12,
        RlpListNthItemSAsm.Result bytes listBase listLen index
          oldOffset oldLen status offset len →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q) :
    cpsTripleWithin N (H + 160) ret fullCode
      (((.x1 ↦ᵣ X) **
        tshCallReturnResultSource sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
          csaved bytes listLen index sourcePtr payloadBs source) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold tshCallReturnResultSource at hcRR
  obtain ⟨status, offset, len, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status offset len v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

theorem tsh_cpsTripleWithin_callReturn_cases_source
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (sourcePtr : Word) (payloadBs : List (BitVec 8)) (source : KssSource)
    (hok : ∀ offset len v11 v12,
        Success bytes listBase listLen index offset len →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q)
    (hfail : ∀ v11 v12,
        Failure bytes listBase listLen index →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
              (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen)))) ** F) Q) :
    cpsTripleWithin N (H + 160) ret fullCode
      (((.x1 ↦ᵣ X) **
        tshCallReturnResultSource sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
          csaved bytes listLen index sourcePtr payloadBs source) ** F) Q := by
  apply tsh_cpsTripleWithin_callReturn_pre_source_impl sp0 listBase indexW
    offsetPtr lenPtr oldOffset oldLen csaved bytes listLen index sourcePtr payloadBs source
  intro status offset len v11 v12 hResult
  cases hResult with
  | ok _ _ hSucc => exact hok offset len v11 v12 hSucc
  | fail hFail => exact hfail v11 v12 hFail

theorem tsh_cpsTripleWithin_callReturn_pre_source_impl_late
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (sourcePtr : Word) (payloadBs : List (BitVec 8)) (source : KssSource)
    (h : ∀ status offset len v11 v12,
        RlpListNthItemSAsm.Result bytes listBase listLen index
          oldOffset oldLen status offset len →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q) :
    cpsTripleWithin N (H + 160) ret fullCode
      (((.x1 ↦ᵣ X) **
        tshCallReturnResultSource sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
          csaved bytes listLen index sourcePtr payloadBs source) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold tshCallReturnResultSource at hcRR
  obtain ⟨status, offset, len, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status offset len v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

theorem tsh_cpsTripleWithin_callReturn_pre_source
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (sourcePtr : Word) (payloadBs : List (BitVec 8)) (source : KssSource)
    (h : ∀ status offset len v11 v12,
        RlpListNthItemSAsm.Result bytes listBase listLen index
          oldOffset oldLen status offset len →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q) :
    cpsTripleWithin N (H + 160) ret fullCode
      (((.x1 ↦ᵣ X) **
        tshCallReturnResultSource sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
          csaved bytes listLen index sourcePtr payloadBs source) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold tshCallReturnResultSource at hcRR
  obtain ⟨status, offset, len, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status offset len v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

/-- Fail case of `tsh_cpsTripleWithin_callReturn_cases`: run
    `tshNthFailThroughBodyExit_spec` under the peeled fail scratch. -/
theorem tshCallReturnFail_throughBodyExit
    (sp0 listBase oldOff oldLen : Word)
    (csaved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (sourcePtr : Word) (payloadBs : List (BitVec 8)) (source : KssSource)
    (F : Assertion) (hF : F.pcFree)
    (v11 v12 : Word)
    (_hFail : Failure bytes listBase listLen index) :
    cpsTripleWithin (1 + 1) (H + 160) tshBodyExit fullCode
      (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
         ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
          (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) ** F)
      (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
         ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** source.region sourcePtr payloadBs **
          (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) ** F) := by
  let Rest : Assertion :=
    ((.x1 ↦ᵣ (tshNthJalPC + 4)) **
      (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
       (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        source.region sourcePtr payloadBs **
        (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) ** F
  have hRest : Rest.pcFree := by
    unfold Rest savedRegTail
    repeat first
      | exact hF
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_stackFree _ _
      | exact source.pcFree _ _
      | exact bytesRegion_pcFree _ _
      | exact (by pcf)
  have h := tshNthFailThroughBodyExit_spec (1 : Word) Rest hRest (by decide)
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Rest] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [Rest] at hq ⊢
      xperm_hyp hq) h

/-! ## Ok arm: peeled nth-success → typed gather → bodyExit -/

/-- Reshape peeled nth-success scratch (`savedRegTail` + status 0) plus gather
    ambient into `tshNthOkThroughTypedSuccess_any_spec` (total prefix cover,
    zero-init 16-byte BSS, `segs` = bare `rlpListPrefix`).

    Expects `x28..x31` already as `regOwn`. Leftover `stackFree` / input bytes /
    `regOwn .x13/.x14` ride in `F`. -/
theorem tshCallReturnOk_throughTypedSuccess_spec
    (sp0 _listBase : Word) (csaved : Saved) (_input : List (BitVec 8))
    (v11 v12 v22 cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (typeBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (offVal lenVal : Word)
    (hnz : csaved.s3 ≠ 0)
    (htypeLen : typeBs.length = 1)
    (hhdr : csaved.s5 = (1 : Word))
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ((offVal + lenVal) - (1 : Word)) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ s ∈ tshTypedSegs typeBs
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs csaved.s0 (1 : Word),
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource)
    (hsourceTsh : source.region TshBuf typeBs = bytesRegion TshBuf typeBs)
    (hsourcePrefix : source.region tshPrefixOutPtr
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat) =
      bytesRegion tshPrefixOutPtr
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)) :
    let hdrLen : Word := 1
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let payloadLen := (offVal + lenVal) - hdrLen
    let prefixBs := rlpListPrefix payloadLen.toNat
    let cellVal := BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)
    let segs := tshTypedSegs typeBs prefixBs payloadBs csaved.s0 hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := ((1 + 8 + 6) + (1 + tshPrefixFuel)) +
      ((6 + 3 + 4 + 5 + 3 + 3) + (1 + (19 + kssBodyFuelMulti segs) + 2))
    let Fok : Assertion :=
      stackFree sp0 8 ** regOwn .x13 ** regOwn .x14 ** F
    cpsTripleWithin fuel (H + 160) tshBodyExit fullCode
      ((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        (.x2 ↦ᵣ sp0) ** savedRegTail csaved **
        (.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x0 ↦ᵣ (0 : Word)) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        (.x22 ↦ᵣ v22) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
        frameSlotsOwn kssFrame newSp **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
        bytesRegion TshBuf typeBs **
        source.region (csaved.s0 + hdrLen) payloadBs **
        bytesRegion KssZk3 os **
        bytesRegion csaved.s4 (List.replicate 32 (0 : BitVec 8)) **
        regOwns kssFreeTemps ** A ** Fok)
      ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
        tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase csaved.s4 segs
          csaved.s0 csaved.s1 csaved.s2 csaved.s3 csaved.s4 hdrLen
          payloadLen A source **
        ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
          (.x31 ↦ᵣ (csaved.s0 + hdrLen)) **
          (tshPrefixCellPtr ↦ₘ cellVal) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          regOwn .x28 ** (tshPrefixBssTail payloadLen ** Fok))) := by
  intro hdrLen outBytes payloadLen prefixBs cellVal segs newSp fuel Fok
  have hFok : Fok.pcFree := by
    unfold Fok
    repeat first
      | exact hF
      | apply pcFree_sepConj
      | exact pcFree_regOwn
      | exact pcFree_stackFree _ _
      | exact source.pcFree _ _
      | exact bytesRegion_pcFree _ _
      | exact (by pcf)
  have hs5 : csaved.s5 = hdrLen := by simp only [hdrLen]; exact hhdr
  have h := tshNthOkThroughTypedSuccess_any_spec v11 v12 v22 offVal lenVal
    hdrLen cellOld csaved.s3 csaved.s0 csaved.s4
    old0 old1 old2 old3 old4 old5 sp0 csaved.s1 csaved.s2
    typeBs payloadBs os A Fok hA hFok hnz htypeLen
    h_out_align h_out_valid hpayW hos hsegsOk source hsourceTsh hsourcePrefix
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [savedRegTail, Fok, hdrLen, hs5, outBytes] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [Fok, payloadLen, prefixBs, cellVal, segs, hdrLen,
        tshPrefixBssTail] at hq ⊢
      exact hq) h

/-- Alias: CallReturnOk already takes `regOwn` on `x28..x31`. -/
theorem tshCallReturnOk_throughTypedSuccess_regOwn_spec
    (sp0 listBase : Word) (csaved : Saved) (input : List (BitVec 8))
    (v11 v12 v22 cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (typeBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (offVal lenVal : Word)
    (hnz : csaved.s3 ≠ 0)
    (htypeLen : typeBs.length = 1)
    (hhdr : csaved.s5 = (1 : Word))
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ((offVal + lenVal) - (1 : Word)) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ s ∈ tshTypedSegs typeBs
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs csaved.s0 (1 : Word),
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource)
    (hsourceTsh : source.region TshBuf typeBs = bytesRegion TshBuf typeBs)
    (hsourcePrefix : source.region tshPrefixOutPtr
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat) =
      bytesRegion tshPrefixOutPtr
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)) :
    let hdrLen : Word := 1
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let payloadLen := (offVal + lenVal) - hdrLen
    let prefixBs := rlpListPrefix payloadLen.toNat
    let cellVal := BitVec.ofNat 64 (tshPrefixNH payloadLen.toNat)
    let segs := tshTypedSegs typeBs prefixBs payloadBs csaved.s0 hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := ((1 + 8 + 6) + (1 + tshPrefixFuel)) +
      ((6 + 3 + 4 + 5 + 3 + 3) + (1 + (19 + kssBodyFuelMulti segs) + 2))
    let Fok : Assertion :=
      stackFree sp0 8 ** regOwn .x13 ** regOwn .x14 ** F
    let Rest : Assertion :=
      (.x1 ↦ᵣ (tshNthJalPC + 4)) **
        (.x2 ↦ᵣ sp0) ** savedRegTail csaved **
        (.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x0 ↦ᵣ (0 : Word)) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        (.x22 ↦ᵣ v22) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
        frameSlotsOwn kssFrame newSp **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
        bytesRegion TshBuf typeBs **
        source.region (csaved.s0 + hdrLen) payloadBs **
        bytesRegion KssZk3 os **
        bytesRegion csaved.s4 (List.replicate 32 (0 : BitVec 8)) **
        regOwns kssFreeTemps ** A ** Fok
    let Post : Assertion :=
      (.x1 ↦ᵣ (tshKssJalPC + 4)) **
        tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase csaved.s4 segs
          csaved.s0 csaved.s1 csaved.s2 csaved.s3 csaved.s4 hdrLen
          payloadLen A source **
        ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
          (.x31 ↦ᵣ (csaved.s0 + hdrLen)) **
          (tshPrefixCellPtr ↦ₘ cellVal) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          regOwn .x28 ** (tshPrefixBssTail payloadLen ** Fok))
    cpsTripleWithin fuel (H + 160) tshBodyExit fullCode
      (Rest ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) Post := by
  intro hdrLen outBytes payloadLen prefixBs cellVal segs newSp fuel Fok Rest Post
  have h := tshCallReturnOk_throughTypedSuccess_spec sp0 listBase csaved input
    v11 v12 v22 cellOld old0 old1 old2 old3 old4 old5
    typeBs payloadBs os A F hA hF offVal lenVal hnz htypeLen hhdr
    h_out_align h_out_valid hpayW hos hsegsOk source hsourceTsh hsourcePrefix
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Rest, Fok, hdrLen, outBytes] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [Post, Fok, payloadLen, prefixBs, cellVal, segs, hdrLen,
        tshPrefixBssTail] at hq ⊢
      exact hq) h

/-! ## `callReturnResult` → bodyExit (ok / fail) -/

/-- Gather ambient framed through the post-nth status check. -/
abbrev tshPostNthGatherAmb
    (v22 cellOld : Word) (csaved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (outBytes typeBs _payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion)
    (_source : KssSource := kssDefaultSource) : Assertion :=
  let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
  (.x22 ↦ᵣ v22) **
    bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
    frameSlotsOwn kssFrame newSp **
    (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
    ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
    ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
    bytesRegion TshBuf typeBs **
    bytesRegion KssZk3 os **
    bytesRegion csaved.s4 (List.replicate 32 (0 : BitVec 8)) **
    regOwns kssFreeTemps ** A ** F

theorem tshPostNthGatherAmb_pcFree
    (v22 cellOld : Word) (csaved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (outBytes typeBs payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (source : KssSource := kssDefaultSource) :
    (tshPostNthGatherAmb v22 cellOld csaved old0 old1 old2 old3 old4 old5
      outBytes typeBs payloadBs os sp0 A F source).pcFree := by
  unfold tshPostNthGatherAmb
  repeat first
    | exact hA
    | exact hF
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_frameSlotsOwn _ _
    | exact source.pcFree _ _
    | exact bytesRegion_pcFree _ _
    | exact (by pcf)

/-- Gather ambient without the type-prefix cell (`x22` + `TshBuf`). -/
abbrev tshPostNthGatherAmbRest
    (cellOld : Word) (csaved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (outBytes _payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion)
    (_source : KssSource := kssDefaultSource) : Assertion :=
  let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
  bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
    frameSlotsOwn kssFrame newSp **
    (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
    ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
    ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
    bytesRegion KssZk3 os **
    bytesRegion csaved.s4 (List.replicate 32 (0 : BitVec 8)) **
    regOwns kssFreeTemps ** A ** F

theorem tshPostNthGatherAmbRest_pcFree
    (cellOld : Word) (csaved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (outBytes payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (source : KssSource := kssDefaultSource) :
    (tshPostNthGatherAmbRest cellOld csaved old0 old1 old2 old3 old4 old5
      outBytes payloadBs os sp0 A F source).pcFree := by
  unfold tshPostNthGatherAmbRest
  repeat first
    | exact hA
    | exact hF
    | apply pcFree_sepConj
    | exact pcFree_memIs
    | exact pcFree_frameSlotsOwn _ _
    | exact source.pcFree _ _
    | exact bytesRegion_pcFree _ _
    | exact (by pcf)

/-- Reassemble gather ambient from the nth call-frame + rest. -/
theorem tshPostNthGatherAmb_of_callFrame
    (v22 wordBuf a3 cellOld : Word) (csaved : Saved)
    (old0 old1 old2 old3 old4 old5 : Word)
    (outBytes payloadBs os : List (BitVec 8))
    (sp0 : Word) (A F : Assertion)
    (hhi : wordBuf &&& ~~~(0xFF#64) = 0)
    (source : KssSource := kssDefaultSource) :
    (tshNthCallFrame v22 wordBuf a3 **
        tshPostNthGatherAmbRest cellOld csaved old0 old1 old2 old3 old4 old5
          outBytes payloadBs os sp0 A F source) =
      tshPostNthGatherAmb v22 cellOld csaved old0 old1 old2 old3 old4 old5
        outBytes [a3.truncate 8] payloadBs os sp0 A F source := by
  rw [tshNthCallFrame_eq_typeBytes v22 wordBuf a3 hhi]
  simp only [tshPostNthGatherAmb, tshPostNthGatherAmbRest]
  ac_rfl

/-- Fuel of the typed-success arm after a concrete nth `(offVal, lenVal)`. -/
abbrev tshTypedSuccessFuel (csaved : Saved)
    (typeBs payloadBs : List (BitVec 8))
    (offVal lenVal : Word) : Nat :=
  let segs := tshTypedSegs typeBs
    (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
    payloadBs csaved.s0 (1 : Word)
  ((1 + 8 + 6) + (1 + tshPrefixFuel)) +
    ((6 + 3 + 4 + 5 + 3 + 3) + (1 + (19 + kssBodyFuelMulti segs) + 2))

/-- Peel `callReturnResult` → `bodyExit` with typed-success or fail status.

    `N` must bound both arms: fail is `1+1`, and every success
    offset/len must satisfy `tshTypedSuccessFuel … ≤ N`. -/
theorem tshCallReturnThroughBodyExit_typed_spec
    (sp0 listBase indexW oldOff oldLen : Word)
    (csaved : Saved) (input : List (BitVec 8)) (listLen index : Nat)
    (v22 cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (typeBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hnz : csaved.s3 ≠ 0)
    (htypeLen : typeBs.length = 1)
    (hhdr : csaved.s5 = (1 : Word))
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ∀ offVal lenVal,
      RlpListNthItemSAsm.Success input listBase listLen index offVal lenVal →
        tshPayloadLenEq payloadBs (1 : Word) offVal lenVal)
    (hos : os.length = 200)
    (hsegsOk : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs typeBs
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs csaved.s0 (1 : Word),
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource)
    (hsourceTsh : ∀ (_offVal _lenVal : Word),
      source.region TshBuf typeBs = bytesRegion TshBuf typeBs)
    (hsourcePrefix : ∀ (offVal lenVal : Word),
      source.region tshPrefixOutPtr
          (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat) =
        bytesRegion tshPrefixOutPtr
          (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      tshTypedSuccessFuel csaved typeBs payloadBs offVal lenVal ≤ N)
    (hNfail : 1 + 1 ≤ N) :
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let Amb := tshPostNthGatherAmb v22 cellOld csaved old0 old1 old2 old3 old4 old5
      outBytes typeBs payloadBs os sp0 A F source
    cpsTripleWithin N (H + 160) tshBodyExit fullCode
      (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        tshCallReturnResultSource sp0 listBase indexW tshNthOffPtr tshNthLenPtr
          oldOff oldLen csaved input listLen index (csaved.s0 + (1 : Word)) payloadBs source) ** Amb)
      (tshNthOutcomePost
        (fun h => ∃ offVal lenVal,
          (⌜tshPayloadLenEq payloadBs (1 : Word) offVal lenVal⌝ **
            ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
            tshKssCallPost sp0
              (sp0 + signExtend12 ((-64 : BitVec 12)))
              (tshKssJalPC + 4) tshSegsBase csaved.s4
              (tshTypedSegs typeBs
                (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
                payloadBs csaved.s0 (1 : Word))
              csaved.s0 csaved.s1 csaved.s2 csaved.s3 csaved.s4 (1 : Word)
              ((offVal + lenVal) - (1 : Word)) A source **
            ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
              (.x30 ↦ᵣ tshSegsBase) **
              (.x31 ↦ᵣ (csaved.s0 + (1 : Word))) **
              (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
                (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
              (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
              (stackFree sp0 8 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
                (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F))))) h)
        (fun h => ∃ v11 v12,
          (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region (csaved.s0 + (1 : Word)) payloadBs **
              (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) ** Amb) h)) := by
  intro outBytes Amb
  have hAmb : Amb.pcFree :=
    tshPostNthGatherAmb_pcFree v22 cellOld csaved old0 old1 old2 old3 old4 old5
      outBytes typeBs payloadBs os sp0 A F hA hF source
  refine tsh_cpsTripleWithin_callReturn_cases_source sp0 listBase indexW
    tshNthOffPtr tshNthLenPtr oldOff oldLen csaved input listLen index
    (csaved.s0 + (1 : Word)) payloadBs source ?hok ?hfail
  · intro offset len v11 v12 hSucc
    have hok := tshCallReturnOk_throughTypedSuccess_regOwn_spec sp0 listBase
      csaved input v11 v12 v22 cellOld old0 old1 old2 old3 old4 old5
      typeBs payloadBs os A F hA hF offset len hnz htypeLen hhdr
      h_out_align h_out_valid (hpayW offset len hSucc) hos
      (hsegsOk offset len) source (hsourceTsh offset len) (hsourcePrefix offset len)
    refine cpsTripleWithin_mono_nSteps (hNok offset len) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Amb, tshPostNthGatherAmb] at hp ⊢
        xperm_hyp hp)
      (fun h hq => tshNthOutcomePost_inl ⟨offset, len,
        (sepConj_pure_left h).2 ⟨hpayW offset len hSucc, by xperm_hyp hq⟩⟩) hok
  · intro v11 v12 hFail
    have hfail := tshCallReturnFail_throughBodyExit sp0 listBase oldOff oldLen
      csaved input listLen index (csaved.s0 + (1 : Word)) payloadBs source
      Amb hAmb v11 v12 hFail
    refine cpsTripleWithin_mono_nSteps hNfail ?_
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => tshNthOutcomePost_inr ⟨v11, v12, hq⟩) hfail

/-! ## Call-frame shape → typed bodyExit (reshape + peel) -/

/-- Same as `tshCallReturnThroughBodyExit_typed_spec`, but the ambient is the
    nth `tshNthCallFrame` dword plus `tshPostNthGatherAmbRest` (the shape left
    by `tshSetupThroughNthCall_spec`). Reshapes via
    `tshPostNthGatherAmb_of_callFrame` with `typeBs = [a3.truncate 8]`. -/
theorem tshCallReturnFrameThroughBodyExit_typed_spec
    (sp0 listBase indexW oldOff oldLen : Word)
    (csaved : Saved) (input : List (BitVec 8)) (listLen index : Nat)
    (wordBuf a3 cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hnz : csaved.s3 ≠ 0)
    (hhdr : csaved.s5 = (1 : Word))
    (hhi : wordBuf &&& ~~~(0xFF#64) = 0)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ∀ offVal lenVal,
      RlpListNthItemSAsm.Success input listBase listLen index offVal lenVal →
        tshPayloadLenEq payloadBs (1 : Word) offVal lenVal)
    (hos : os.length = 200)
    (hsegsOk : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs [a3.truncate 8]
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs csaved.s0 (1 : Word),
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource)
    (hsourceTsh : ∀ (_offVal _lenVal : Word),
      source.region TshBuf [a3.truncate 8] =
        bytesRegion TshBuf [a3.truncate 8])
    (hsourcePrefix : ∀ (offVal lenVal : Word),
      source.region tshPrefixOutPtr
          (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat) =
        bytesRegion tshPrefixOutPtr
          (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      tshTypedSuccessFuel csaved [a3.truncate 8] payloadBs offVal lenVal ≤ N)
    (hNfail : 1 + 1 ≤ N) :
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let AmbRest := tshPostNthGatherAmbRest cellOld csaved old0 old1 old2 old3 old4 old5
      outBytes payloadBs os sp0 A F source
    let typeBs : List (BitVec 8) := [a3.truncate 8]
    let Amb := tshPostNthGatherAmb (0 : Word) cellOld csaved old0 old1 old2 old3 old4 old5
      outBytes typeBs payloadBs os sp0 A F source
    cpsTripleWithin N (H + 160) tshBodyExit fullCode
      (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        tshCallReturnResultSource sp0 listBase indexW tshNthOffPtr tshNthLenPtr
          oldOff oldLen csaved input listLen index (csaved.s0 + (1 : Word)) payloadBs source) **
        tshNthCallFrame (0 : Word) wordBuf a3 ** AmbRest)
      (tshNthOutcomePost
        (fun h => ∃ offVal lenVal,
          (⌜tshPayloadLenEq payloadBs (1 : Word) offVal lenVal⌝ **
            ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
            tshKssCallPost sp0
              (sp0 + signExtend12 ((-64 : BitVec 12)))
              (tshKssJalPC + 4) tshSegsBase csaved.s4
              (tshTypedSegs typeBs
                (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
                payloadBs csaved.s0 (1 : Word))
              csaved.s0 csaved.s1 csaved.s2 csaved.s3 csaved.s4 (1 : Word)
              ((offVal + lenVal) - (1 : Word)) A source **
            ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
              (.x30 ↦ᵣ tshSegsBase) **
              (.x31 ↦ᵣ (csaved.s0 + (1 : Word))) **
              (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
                (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
              (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
              (stackFree sp0 8 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
                (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F))))) h)
        (fun h => ∃ v11 v12,
          (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail csaved) **
             ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region (csaved.s0 + (1 : Word)) payloadBs **
              (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) ** Amb) h)) := by
  intro outBytes AmbRest typeBs Amb
  have h := tshCallReturnThroughBodyExit_typed_spec sp0 listBase indexW oldOff oldLen
    csaved input listLen index (0 : Word) cellOld old0 old1 old2 old3 old4 old5
    typeBs payloadBs os A F hA hF hnz
    (by simp only [typeBs, List.length_singleton]) hhdr
    h_out_align h_out_valid hpayW hos hsegsOk source hsourceTsh hsourcePrefix N hNok hNfail
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [AmbRest, typeBs, outBytes, tshPostNthGatherAmb, tshPostNthGatherAmbRest] at hp ⊢
      rw [tshNthCallFrame_eq_typeBytes (0 : Word) wordBuf a3 hhi] at hp
      xperm_hyp hp)
    (fun _ hq => by
      simp only [typeBs] at hq ⊢
      exact hq) h

/-! ## Setup → nth call → typed bodyExit (`H+36 → bodyExit`) -/

/-- Frame gather ambient through `tshSetupThroughNthCall_spec`, then peel via
    `tshCallReturnFrameThroughBodyExit_typed_spec`.

    `typeBs = [a3.truncate 8]`; requires high bytes of `wordOld` clear so the
    type-prefix `SB` matches `packBytes`. -/
theorem tshSetupThroughNthThenBodyExit_typed_spec
    (a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20 v21 wordOld : Word)
    (sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen : Word)
    (input : List (BitVec 8)) (listLen index : Nat)
    (cellOld : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (hnzFields : a2 ≠ 0)
    (hnzType : a3 ≠ 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hindexW : tshNthIndexW a2 = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true)
    (hhi : wordOld &&& ~~~(0xFF#64) = 0)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_valid : ∀ k, k < 16 →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ∀ offVal lenVal,
      RlpListNthItemSAsm.Success input a0 listLen index offVal lenVal →
        tshPayloadLenEq payloadBs (1 : Word) offVal lenVal)
    (hos : os.length = 200)
    (hsegsOk : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs [a3.truncate 8]
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs a0 (1 : Word),
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource)
    (hsourceInput : source.region (a0 + (1 : Word)) payloadBs =
      bytesRegion a0 input)
    (hsourceTsh : ∀ (_offVal _lenVal : Word),
      source.region TshBuf [a3.truncate 8] = bytesRegion TshBuf [a3.truncate 8])
    (hsourcePrefix : ∀ (offVal lenVal : Word),
      source.region tshPrefixOutPtr
          (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat) =
        bytesRegion tshPrefixOutPtr
          (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat))
    (N : Nat)
    (hNok : ∀ offVal lenVal,
      tshTypedSuccessFuel (tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4)
        [a3.truncate 8] payloadBs offVal lenVal ≤ N)
    (hNfail : 1 + 1 ≤ N) :
    let setupFuel := 5 + 3 + 1 + 7 + (1 + 1 + 1 + 3 + 6)
    let callFuel := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let saved := tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4
    let outBytes := List.replicate 16 (0 : BitVec 8)
    let AmbRest := tshPostNthGatherAmbRest cellOld saved old0 old1 old2 old3 old4 old5
      outBytes payloadBs os sp0 A F source
    let typeBs : List (BitVec 8) := [a3.truncate 8]
    let Amb := tshPostNthGatherAmb (0 : Word) cellOld saved old0 old1 old2 old3 old4 old5
      outBytes typeBs payloadBs os sp0 A F source
    cpsTripleWithin (setupFuel + callFuel + N) (H + 36) tshBodyExit fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld) ** source.region (a0 + (1 : Word)) payloadBs **
        tshNthCallAmbient sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen ** AmbRest)
      (tshNthOutcomePost
        (fun h => ∃ offVal lenVal,
          (⌜tshPayloadLenEq payloadBs (1 : Word) offVal lenVal⌝ **
            ((.x1 ↦ᵣ (tshKssJalPC + 4)) **
            tshKssCallPost sp0
              (sp0 + signExtend12 ((-64 : BitVec 12)))
              (tshKssJalPC + 4) tshSegsBase saved.s4
              (tshTypedSegs typeBs
                (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
                payloadBs saved.s0 (1 : Word))
              saved.s0 saved.s1 saved.s2 saved.s3 saved.s4 (1 : Word)
              ((offVal + lenVal) - (1 : Word)) A source **
            ((.x29 ↦ᵣ BitVec.ofNat 64 (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
              (.x30 ↦ᵣ tshSegsBase) **
              (.x31 ↦ᵣ (saved.s0 + (1 : Word))) **
              (tshPrefixCellPtr ↦ₘ BitVec.ofNat 64
                (tshPrefixNH ((offVal + lenVal) - (1 : Word)).toNat)) **
              (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
              (stackFree sp0 8 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
                (tshPrefixBssTail ((offVal + lenVal) - (1 : Word)) ** F))))) h)
        (fun h => ∃ v11 v12,
          (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail saved) **
             ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** source.region (a0 + (1 : Word)) payloadBs **
              (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)))) ** Amb) h)) := by
  intro setupFuel callFuel saved outBytes AmbRest typeBs Amb
  have hRest : AmbRest.pcFree :=
    tshPostNthGatherAmbRest_pcFree cellOld saved old0 old1 old2 old3 old4 old5
      outBytes payloadBs os sp0 A F hA hF source
  have hsetup := tshSetupThroughNthCall_spec a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19
    v20 v21 wordOld sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen input listLen index
    halignBuf hvalidBuf hlen hnzFields h0 halignIn hoverIn hvalidIn hge hult
    hlistLenW hindexW hindex hslack hover hvalidBytes
  have hsetupF := cpsTripleWithin_frameR AmbRest hRest hsetup
  have hcallEq := callReturnResult_to_source sp0 a0 (tshNthIndexW a2)
    tshNthOffPtr tshNthLenPtr oldOff oldLen saved input listLen index
    (a0 + (1 : Word)) payloadBs source hsourceInput
  let Psrc : Assertion :=
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
      (.x14 ↦ᵣ a4) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (TshBuf ↦ₘ wordOld) ** source.region (a0 + (1 : Word)) payloadBs **
      tshNthCallAmbient sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen) ** AmbRest
  let Qsrc : Assertion :=
    (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
      tshCallReturnResultSource sp0 a0 (tshNthIndexW a2) tshNthOffPtr tshNthLenPtr
        oldOff oldLen saved input listLen index (a0 + (1 : Word)) payloadBs source) **
      tshNthCallFrame (0 : Word) wordOld a3) ** AmbRest
  have hpre : ∀ h, Psrc h →
      (((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input **
        tshNthCallAmbient sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen) ** AmbRest) h := by
    intro h hp
    simp only [Psrc] at hp
    rw [hsourceInput] at hp
    exact hp
  let Qold : Assertion :=
    (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
      callReturnResult sp0 a0 (tshNthIndexW a2) tshNthOffPtr tshNthLenPtr
        oldOff oldLen saved input listLen index) **
      tshNthCallFrame (0 : Word) wordOld a3) ** AmbRest
  have hpost : ∀ h, Qold h → Qsrc h := by
    intro h hq
    simp only [Qold, Qsrc] at hq ⊢
    rw [← hcallEq]
    exact hq
  have hsetupSrc := cpsTripleWithin_weaken hpre hpost hsetupF
  have hnz : saved.s3 ≠ 0 := by
    simp only [saved, tshNthSaved]; exact hnzType
  have hhdr : saved.s5 = (1 : Word) := by
    simp only [saved, tshNthSaved]
  have hsegsOk' : ∀ offVal lenVal,
      ∀ s ∈ tshTypedSegs [a3.truncate 8]
        (rlpListPrefix ((offVal + lenVal) - (1 : Word)).toNat)
        payloadBs saved.s0 (1 : Word),
      s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true) := by
    intro offVal lenVal
    simpa [saved, tshNthSaved] using hsegsOk offVal lenVal
  have hNok' : ∀ offVal lenVal,
      tshTypedSuccessFuel saved [a3.truncate 8] payloadBs offVal lenVal ≤ N :=
    hNok
  have hexit := tshCallReturnFrameThroughBodyExit_typed_spec sp0 a0 (tshNthIndexW a2)
    oldOff oldLen saved input listLen index wordOld a3 cellOld
    old0 old1 old2 old3 old4 old5 payloadBs os A F hA hF
    hnz hhdr hhi h_out_align h_out_valid hpayW hos
    hsegsOk' source hsourceTsh hsourcePrefix N hNok' hNfail
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [saved, tshNthSaved, Qsrc, AmbRest, outBytes] at hp ⊢
      xperm_hyp hp) hsetupSrc hexit
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [AmbRest, outBytes] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [saved, Amb, typeBs, outBytes] at hq ⊢
      exact hq) c


end EvmAsm.Codegen.TxSigningHashSpec
