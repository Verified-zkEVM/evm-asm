/-
  EvmAsm.Codegen.Programs.ValidateHeaderParentHashCorrespondence

  Call-site adapter for conjunct 11 of SpecRef-shaped `validate_header`:
  `parent_hash` field equals `keccak256(parent_rlp)`.

  Objdump / Program check (do not substitute a different keccak entry):
  - `validate_header + 244` (instr 61) `jal` → `header_validate_parent_hash`
  - Inside that callee, `header_validate_parent_hash + 68` `jal` →
    **`zkvm_keccak256`** (one-shot at GuestAddrs.zkvm_keccak256),
    **not** `zkvm_keccak256_segments`.
  - Sibling extract: `header_validate_parent_hash + 36` → `headers_parent_hash`.

  There is no whole-routine machine triple for `header_validate_parent_hash`
  yet.  This module therefore makes that missing triple an explicit premise
  (same shape as the K67 post-merge adapter), while recording that the
  one-shot `zkvm_keccak256_spec_within` is the proven leaf the callee
  actually calls — the composition shortcut for this conjunct.

  Status: any nonzero `a0` from the callee is mapped by the caller to
  validate_header status **11** (distinct from 1/3/5/6/7/…).

  EMPTY_OMMER_HASH vs empty-trie-root conflation (#12081) is a different
  conjunct (ommers / post-merge); not used here.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCorrespondence
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.ValidateHeaderParentHashCorrespondence

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Linked call at `H + 244` and the HVPH premise shape -/

abbrev H : Word := EvmAsm.Codegen.ValidateHeaderCorrespondence.H
abbrev A : Word := H + 244
abbrev Ret : Word := H + 248
abbrev Callee : Word := (GuestAddrs.header_validate_parent_hash : Word)
abbrev Keccak : Word := (GuestAddrs.zkvm_keccak256 : Word)

abbrev callerCode : CodeReq := EvmAsm.Codegen.ValidateHeaderCorrespondence.callerCode

/-- 32-byte ABI frame used by `headerValidateParentHash_prog`. -/
def hvphFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]

def hvphSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24)]

def hvphFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

/- Entry under the linked `jal`: caller has placed this/parent RLP in
   `a0..a3` (`x10..x13`).  `header_validate_parent_hash` allocates its own
   32-byte frame; the validate_header 56-byte frame and s0..s5 live values
   stay in the ambient `F`. -/
def hvphEntryRest
    (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn hvphFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
  (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes

def hvphCalleePost
    (sp0 thisPtr parentPtr ret status : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved hvphFrame (sp0 + signExtend12 (-32 : BitVec 12))
    (hvphFrameVals ret vals) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ status) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes

theorem hvphEntryRest_pcFree
    (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) :
    (hvphEntryRest sp0 thisPtr thisLen parentPtr parentLen vals
      thisBytes parentBytes).pcFree := by
  unfold hvphEntryRest hvphFrame hvphSavedFrame
  pcf

theorem validateHeader_length : EvmAsm.Codegen.validateHeader_prog.length = 97 := by
  exact EvmAsm.Codegen.ValidateHeaderCorrespondence.validateHeader_length

theorem validateHeader_parentHash_jal_mem :
    ∀ a i, CodeReq.singleton A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244))) a = some i → callerCode a = some i := by
  exact CodeReq.ofProg_mem_at
    (GuestAddrs.validate_header : Word) A EvmAsm.Codegen.validateHeader_prog 61 _
    (by bv_omega) (by rw [validateHeader_length]; decide) rfl
    (by rw [validateHeader_length]; decide)

/-! ## Objdump / Program pins: which keccak entry is live -/

/-- Kernel-checked: instr 17 at callee+68 is `jal zkvm_keccak256` (one-shot),
    and that symbol is not the segments entry (matches objdump). -/
theorem headerValidateParentHash_keccak_jal_is_oneshot :
    (∀ a i, CodeReq.singleton
        (GuestAddrs.header_validate_parent_hash + 68 : Word)
        (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.header_validate_parent_hash + 68))) a = some i →
      CodeReq.ofProg (GuestAddrs.header_validate_parent_hash : Word)
        headerValidateParentHash_prog a = some i) ∧
    (GuestAddrs.zkvm_keccak256 : Nat) ≠ GuestAddrs.zkvm_keccak256_segments := by
  refine ⟨?_, by decide⟩
  exact CodeReq.ofProg_mem_at
    (GuestAddrs.header_validate_parent_hash : Word)
    (GuestAddrs.header_validate_parent_hash + 68 : Word)
    headerValidateParentHash_prog 17 _
    (by bv_omega) (by decide) rfl (by decide)

/-!
The theorem below is the machine half of the parent-hash correspondence at the
real `validate_header` call site.  `hcallee` is intentionally undischarged:
proving it is the missing whole-routine triple for
`header_validate_parent_hash`.  That triple can (and should) discharge its
inner `jal` at callee+68 with the proven `zkvm_keccak256_spec_within`
(one-shot) — verified above and by objdump on `stateless_guest.elf`
(`jal` → `zkvm_keccak256`, not `zkvm_keccak256_segments`).
-/
set_option maxRecDepth 8000 in
theorem validate_header_parent_hash_call_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (sp0 thisPtr thisLen parentPtr parentLen oldRa status : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hdisj : (CodeReq.singleton A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)))).Disjoint calleeCode)
    (hcallerDisj : callerCode.Disjoint calleeCode)
    (hcode : ∀ a i, (callerCode.union calleeCode) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n Callee Ret calleeCode
      ((.x1 ↦ᵣ Ret) **
        hvphEntryRest sp0 thisPtr thisLen parentPtr parentLen vals
          thisBytes parentBytes)
      (hvphCalleePost sp0 thisPtr parentPtr Ret status vals
        thisBytes parentBytes)) :
    cpsTripleWithin (1 + n) A Ret cr
      (((.x1 ↦ᵣ oldRa) **
        hvphEntryRest sp0 thisPtr thisLen parentPtr parentLen vals
          thisBytes parentBytes) ** F)
      (hvphCalleePost sp0 thisPtr parentPtr Ret status vals
        thisBytes parentBytes ** F) := by
  have htarget : A + signExtend21 (jalOff GuestAddrs.header_validate_parent_hash
      (GuestAddrs.validate_header + 244)) = Callee := by
    change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 244 + _ =
      BitVec.ofNat 64 GuestAddrs.header_validate_parent_hash
    exact jalOff_correct_add GuestAddrs.header_validate_parent_hash
      GuestAddrs.validate_header 244 (by decide) (by decide) (by decide) (by decide)
  have hret' : (A + 4) &&& ~~~(1 : Word) = A + 4 := by decide
  have hpre := hvphEntryRest_pcFree sp0 thisPtr thisLen parentPtr parentLen vals
    thisBytes parentBytes
  have hRet : A + 4 = Ret := by decide
  have hcallee' : cpsTripleWithin n Callee ((A + 4) &&& ~~~(1 : Word)) calleeCode
      ((.x1 ↦ᵣ Ret) **
        hvphEntryRest sp0 thisPtr thisLen parentPtr parentLen vals
          thisBytes parentBytes)
      (hvphCalleePost sp0 thisPtr parentPtr Ret status vals
        thisBytes parentBytes) := by
    rw [hret', hRet]
    exact hcallee
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := A) (calleeEntry := Callee) (vOld := oldRa)
    (calleeCode := calleeCode)
    (Prest := hvphEntryRest sp0 thisPtr thisLen parentPtr parentLen vals
      thisBytes parentBytes)
    (Q := hvphCalleePost sp0 thisPtr parentPtr Ret status vals
      thisBytes parentBytes)
    (jalOff GuestAddrs.header_validate_parent_hash (GuestAddrs.validate_header + 244))
    htarget hret' hpre hdisj hcallee'
  have hcallCode : ∀ a i,
      ((CodeReq.singleton A (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)))).union calleeCode) a = some i →
      (callerCode.union calleeCode) a = some i := by
    exact CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i
        (validateHeader_parentHash_jal_mem a i h))
      (fun a i h => CodeReq.mono_union_right hcallerDisj
        (fun _ _ h' => h') a i h)
  have hcallC := cpsTripleWithin_extend_code hcallCode hcall
  have hcallCr := cpsTripleWithin_extend_code hcode hcallC
  have hcallF := cpsTripleWithin_frameR F hF hcallCr
  simpa [hRet] using hcallF

end EvmAsm.Codegen.ValidateHeaderParentHashCorrespondence
