/-
  `accountDecode_prog` caller-contract composition, part 2 — the four per-field
  "stages": each field's K20 call composed with its post-call status dispatch
  (`adFieldNCall ;; adK20Dispatch`), yielding a `cpsBranchWithin` from the call
  entry with the shared failure edge (`AB+504`) and the field's continue edge
  (the length-check entry `dispatchPC + 4`).

  Mirrors `WithdrawalDecodeSpec.wdFieldNStage` (uniform here: all four fields
  are K20, so the four stages share one shape).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeClose
import EvmAsm.Codegen.Programs.AccountDecodeDispatch

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved flatReturnResult)

/-- The shared field-call precondition, parameterised by the call entry and the
    field's saved-`s2` slot value.  Identical register/memory footprint across
    all four fields (only the `ra`/index differ, tracked in the call/dispatch
    lemmas). -/
def adCallPre (raIn spW listBase len s2v s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 : Word) (bytes : List (BitVec 8)) : Assertion :=
  ((.x1 : Reg) ↦ᵣ raIn) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) **
  (.x18 ↦ᵣ s2v) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
  (.x14 ↦ᵣ v14) ** stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen)

set_option maxRecDepth 8000 in
/-- Field-0 stage [14]-[22] (`AB+56 → 504/92`): the nonce K20 call composed with
    its post-call dispatch.  Fail edge `AB+504`, continue edge `AB+92` (nonce
    length check). -/
theorem adField0Stage
    (spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 88, s0 := listBase, s1 := len, s2 := nonceOut, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (0 + 2)) + 6)) + 9
    cpsBranchWithin ((7 + (1 + n20)) + 1) (AB + 56) fullCode
      (adCallPre raIn spW listBase len nonceOut s3 s4 s5 oldOffset oldLen
        v10 v11 v12 v13 v14 bytes)
      (AB + 504) (adK20FailPost spW listBase oldOffset oldLen 0 saved bytes listLen)
      (AB + 92) (adK20ContPost spW listBase 0 saved bytes listLen) := by
  intro saved n20
  have hcall := adField0Call spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hdisp := adK20Dispatch spW listBase oldOffset oldLen (AB + 88) (416 : BitVec 13) 0
    saved bytes listLen
    (by rw [show signExtend13 (416 : BitVec 13) = (416 : Word) from by decide]; bv_omega)
    (fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 88) accountDecode_prog 22
        (.BNE .x10 .x0 (416 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide) rfl
        (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 88 : Word) + 4 = AB + 92 from by bv_omega] at hdisp
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun _ hq => hq) hcall hdisp

#print axioms adField0Stage

set_option maxRecDepth 8000 in
/-- Field-1 stage [41]-[49] (`AB+164 → 504/200`): the balance K20 call composed
    with its dispatch.  Fail edge `AB+504`, continue edge `AB+200`. -/
theorem adField1Stage
    (spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 196, s0 := listBase, s1 := len, s2 := nonceOut, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (1 + 2)) + 6)) + 9
    cpsBranchWithin ((7 + (1 + n20)) + 1) (AB + 164) fullCode
      (adCallPre raIn spW listBase len nonceOut s3 s4 s5 oldOffset oldLen
        v10 v11 v12 v13 v14 bytes)
      (AB + 504) (adK20FailPost spW listBase oldOffset oldLen 1 saved bytes listLen)
      (AB + 200) (adK20ContPost spW listBase 1 saved bytes listLen) := by
  intro saved n20
  have hcall := adField1Call spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hdisp := adK20Dispatch spW listBase oldOffset oldLen (AB + 196) (308 : BitVec 13) 1
    saved bytes listLen
    (by rw [show signExtend13 (308 : BitVec 13) = (308 : Word) from by decide]; bv_omega)
    (fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 196) accountDecode_prog 49
        (.BNE .x10 .x0 (308 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide) rfl
        (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 196 : Word) + 4 = AB + 200 from by bv_omega] at hdisp
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun _ hq => hq) hcall hdisp

#print axioms adField1Stage

set_option maxRecDepth 8000 in
/-- Field-2 stage [72]-[80] (`AB+288 → 504/324`): the storage-root K20 call
    composed with its dispatch.  Fail edge `AB+504`, continue edge `AB+324`. -/
theorem adField2Stage
    (spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 320, s0 := listBase, s1 := len, s2 := nonceOut, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (2 + 2)) + 6)) + 9
    cpsBranchWithin ((7 + (1 + n20)) + 1) (AB + 288) fullCode
      (adCallPre raIn spW listBase len nonceOut s3 s4 s5 oldOffset oldLen
        v10 v11 v12 v13 v14 bytes)
      (AB + 504) (adK20FailPost spW listBase oldOffset oldLen 2 saved bytes listLen)
      (AB + 324) (adK20ContPost spW listBase 2 saved bytes listLen) := by
  intro saved n20
  have hcall := adField2Call spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hdisp := adK20Dispatch spW listBase oldOffset oldLen (AB + 320) (184 : BitVec 13) 2
    saved bytes listLen
    (by rw [show signExtend13 (184 : BitVec 13) = (184 : Word) from by decide]; bv_omega)
    (fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 320) accountDecode_prog 80
        (.BNE .x10 .x0 (184 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide) rfl
        (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 320 : Word) + 4 = AB + 324 from by bv_omega] at hdisp
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun _ hq => hq) hcall hdisp

#print axioms adField2Stage

set_option maxRecDepth 8000 in
/-- Field-3 stage [98]-[106] (`AB+392 → 504/428`): the code-hash K20 call
    composed with its dispatch.  Fail edge `AB+504`, continue edge `AB+428`. -/
theorem adField3Stage
    (spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen v10 v11 v12 v13 v14 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : Saved :=
      { ra := AB + 424, s0 := listBase, s1 := len, s2 := nonceOut, s3 := s3, s4 := s4,
        s5 := s5 }
    let n20 := (12 + ((85 + 93 * (3 + 2)) + 6)) + 9
    cpsBranchWithin ((7 + (1 + n20)) + 1) (AB + 392) fullCode
      (adCallPre raIn spW listBase len nonceOut s3 s4 s5 oldOffset oldLen
        v10 v11 v12 v13 v14 bytes)
      (AB + 504) (adK20FailPost spW listBase oldOffset oldLen 3 saved bytes listLen)
      (AB + 428) (adK20ContPost spW listBase 3 saved bytes listLen) := by
  intro saved n20
  have hcall := adField3Call spW raIn listBase len nonceOut s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hdisp := adK20Dispatch spW listBase oldOffset oldLen (AB + 424) (80 : BitVec 13) 3
    saved bytes listLen
    (by rw [show signExtend13 (80 : BitVec 13) = (80 : Word) from by decide]; bv_omega)
    (fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 424) accountDecode_prog 106
        (.BNE .x10 .x0 (80 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide) rfl
        (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 424 : Word) + 4 = AB + 428 from by bv_omega] at hdisp
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun _ hq => hq) hcall hdisp

#print axioms adField3Stage

end EvmAsm.Codegen.AccountDecodeSpec
