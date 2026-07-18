/-
  Ambient dual of extract type_dispatch setup+call+BEQ (E+72 → E+112).

  Reuses setup/BEQ leaves (register-only). Call uses ambient values-carrying
  type_dispatch (teer of txSlice; bytesRegion regionBase bs).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeCall
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nTypeSteps extractToBufOwn teaScratchOwn)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

private def typeJalOffAmb : BitVec 21 :=
  jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_extract_to_address + 96)

/-- Ambient callee pre: a0=loadPtr, ambient region, tea cells. -/
def extractTypeCalleePAmbient (loadPtr lenW : Word) (regionBase : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ TeaTypeAddr) ** (.x13 ↦ᵣ TeaInnerAddr) **
  bytesRegion regionBase bs **
  memOwn TeaTypeAddr ** memOwn TeaInnerAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Ambient value-carrying post: tea cells hold teer(slice) type/inner. -/
def extractTypeCalleeQAmbient (regionBase : Word) (bs : List (BitVec 8))
    (off len : Nat) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion regionBase bs **
  (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
  (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem extractTypeCalleePAmbient_pcFree (loadPtr lenW regionBase : Word)
    (bs : List (BitVec 8)) :
    (extractTypeCalleePAmbient loadPtr lenW regionBase bs).pcFree := by
  unfold extractTypeCalleePAmbient; pcf

set_option maxRecDepth 8000 in
/-- JAL type_dispatch ambient under success domain on txSlice. -/
theorem extractTypeCallAmbient
    (regionBase loadPtr lenW : Word) (bs : List (BitVec 8)) (off len : Nat)
    (old1 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (1 + nTypeSteps) TypeJalPc LinkType extractLinkedCode
      ((.x1 ↦ᵣ old1) ** extractTypeCalleePAmbient loadPtr lenW regionBase bs)
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQAmbient regionBase bs off len) := by
  have hret : (LinkType &&& ~~~(1 : Word)) = LinkType := by
    simp only [LinkType, E]; decide
  have hcallee0 :=
    typeDispatch_success_values_ambient_flat_typeCode
      LinkType regionBase loadPtr lenW TeaTypeAddr TeaInnerAddr bs off len
      hret hptr hlen hsuccess halign hbound hover hvalid
  have hcalleeD : cpsTripleWithin nTypeSteps TxTypeDispatchSpec.D LinkType
      TxTypeDispatchSpec.typeCode
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleePAmbient loadPtr lenW regionBase bs)
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQAmbient regionBase bs off len) := by
    simpa only [extractTypeCalleePAmbient, extractTypeCalleeQAmbient] using hcallee0
  have hentry : TxTypeDispatchSpec.D = TypeEntry := by
    simp only [TxTypeDispatchSpec.D, TypeEntry]
  have hcallee0' : cpsTripleWithin nTypeSteps TypeEntry LinkType
      TxTypeDispatchSpec.typeCode
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleePAmbient loadPtr lenW regionBase bs)
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQAmbient regionBase bs off len) := by
    rw [← hentry]; exact hcalleeD
  have hcallee := cpsTripleWithin_extend_code type_in_extractLinked hcallee0'
  have hcall := callWithin_spec TypeJalPc TypeEntry old1 typeJalOffAmb nTypeSteps
    (by show TypeJalPc + signExtend21 typeJalOffAmb = TypeEntry
        simp only [TypeJalPc, TypeEntry, typeJalOffAmb, E]; decide)
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E TypeJalPc extractProg 24
        (.JAL .x1 typeJalOffAmb) (by simp only [TypeJalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractTypeCalleePAmbient_pcFree loadPtr lenW regionBase bs)
    hcallee
  rw [show (TypeJalPc + 4 : Word) = LinkType from by
    simp only [TypeJalPc, LinkType]; bv_omega] at hcall
  exact hcall

set_option maxRecDepth 8000 in
/-- Setup + ambient call + BEQ success: AfterPreZero → AfterTypeBeqz. -/
theorem extractTypeSuccessAmbient
    (regionBase loadPtr lenW : Word) (bs : List (BitVec 8)) (off len : Nat)
    (old1 v10 v11 v12 v13 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterPreZero AfterTypeBeqz
      extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        bytesRegion regionBase bs **
        teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  -- Setup reuses slice leaf with loadPtr as "txBase" (s0→a0 copy only)
  have hsetup := extractTypeSetup loadPtr lenW v10 v11 v12 v13
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** bytesRegion regionBase bs **
      memOwn TeaTypeAddr ** memOwn TeaInnerAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hsetup
  have hcall := extractTypeCallAmbient regionBase loadPtr lenW bs off len old1
    hptr hlen hsuccess halign hbound hover hvalid
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW)) (by pcf) hcall
  have hb := extractTypeBeqzOk
  have hbF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      bytesRegion regionBase bs **
      (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
      (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hb
  have hsetupW : cpsTripleWithin 6 AfterPreZero TypeJalPc extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        bytesRegion regionBase bs ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        extractTypeCalleePAmbient loadPtr lenW regionBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teaScratchOwn_eq_typeInner, extractTypeCalleePAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teaScratchOwn_eq_typeInner, extractTypeCalleePAmbient] at hq ⊢
      xperm_hyp hq) hsetupF
  have hcallW : cpsTripleWithin (1 + nTypeSteps) TypeJalPc LinkType extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        extractTypeCalleePAmbient loadPtr lenW regionBase bs)
      ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        extractTypeCalleeQAmbient regionBase bs off len) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallF
  have hbW : cpsTripleWithin 1 LinkType AfterTypeBeqz extractLinkedCode
      ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        extractTypeCalleeQAmbient regionBase bs off len)
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractTypeCalleeQAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hbF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupW hcallW
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hbW
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms extractTypeCallAmbient
#print axioms extractTypeSuccessAmbient

end EvmAsm.Codegen.TxExtractToAddressSpec
