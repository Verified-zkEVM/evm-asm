/-
  EvmAsm.Codegen.Programs.ValidateHeaderStep2ParentHashAmbient

  Step-2 caller plumbing for the unified parent-hash route (#12346 item 9).

  The parent-hash continuation resources are available at the whole-verdict
  entry, but x20 is not: validate_header's prologue installs x20 from the
  a4 parent-RLP argument.  This module gives that distinction a named
  assertion, carries it through the prologue, and specializes the existing
  whole-header composition to the resulting hcore contract.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderWhole
import EvmAsm.Codegen.Programs.HeaderValidateParentHashUnifiedCover

namespace EvmAsm.Codegen.ValidateHeaderStep2ParentHashAmbient

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderWhole
open EvmAsm.Codegen.HeaderValidateParentHashSpec
open EvmAsm.Codegen.Proofs

noncomputable section

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
      | exact bytesRegion_pcFree _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_regOwns _)

/-- The stack cells reserved for the keccak child are below the prologue
    frame.  At entry `sp0` is live; after the prologue `spC = sp0 - 56`, so
    this is `spC - 32`, the child frame base used by the parent-hash route. -/
abbrev step2ParentHashChildSp (sp0 : Word) : Word :=
  sp0 + signExtend12 (-88 : BitVec 12)

/-- Resources which Step 2 carries from its entry to the parent-hash seam.

    `claimedOwn`, the 200-byte `zk3_state` arena and the 32-byte computed
    output are genuine byte resources.  The four temporary registers and the
    four free child-stack dwords are ordinary caller-owned resources.  x20 is
    intentionally absent: the validate-header prologue establishes it from
    the a4 parent-RLP pointer before the route uses it. -/
def step2ParentHashAmbient
    (sp0 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  claimedOwn C0 **
  stackFree (step2ParentHashChildSp sp0) 4 **
  regOwns [.x14, .x15, .x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F

theorem step2ParentHashAmbient_pcFree
    (sp0 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) : (step2ParentHashAmbient sp0 C0 os out0 F).pcFree := by
  unfold step2ParentHashAmbient claimedOwn
  pcf
  exact hF

theorem step2ParentHashChildSp_eq_post_prologue
    (sp0 spC : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    step2ParentHashChildSp sp0 =
      spC + signExtend12 (BitVec.ofNat 12 4064) := by
  have h56 : signExtend12 (-56 : BitVec 12) =
      (0xFFFFFFFFFFFFFFC8 : Word) := by decide
  have h88 : signExtend12 (-88 : BitVec 12) =
      (0xFFFFFFFFFFFFFFA8 : Word) := by decide
  have h32 : signExtend12 (BitVec.ofNat 12 4064) =
      (0xFFFFFFFFFFFFFFE0 : Word) := by decide
  simp only [step2ParentHashChildSp]
  rw [hspC, h56, h88, h32]
  bv_omega

/-- The exact precondition handed to the first checker after threading the
    Step-2 ambient.  Keeping this as a named carrier makes the later hcore
    proof consume the same assertion that the prologue theorem preserves. -/
def step2ParentHashProloguePre
    (sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21 : Word)
    (sp2 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  (regIs .x1 raIn) ** (regIs .x2 sp0) **
  (regIs .x8 o8) ** (regIs .x9 o9) ** (regIs .x18 o18) **
  (regIs .x19 o19) ** (regIs .x20 o20) ** (regIs .x21 o21) **
  (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
  (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
  memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) **
  memOwn (spC + 24) ** memOwn (spC + 32) ** memOwn (spC + 40) **
  memOwn (spC + 48) ** step2ParentHashAmbient sp2 C0 os out0 F

def step2ParentHashProloguePost
    (_sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21 : Word)
    (sp2 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  (regIs .x1 raIn) ** (regIs .x2 spC) **
  (regIs .x8 a0) ** (regIs .x9 a1) ** (regIs .x18 a2) **
  (regIs .x19 a3) ** (regIs .x20 a4) ** (regIs .x21 a5) **
  (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
  (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
  ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
  ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
  step2ParentHashAmbient sp2 C0 os out0 F

/-! The ambient is carried unchanged by the actual 14-step prologue.  The
    theorem is intentionally stated at the same boundary as hcore (H+56),
    rather than claiming that x20 existed at the entry point. -/
theorem validate_header_prologue_preserves_step2_parent_hash_ambient
    (sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21 : Word)
    (sp2 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hsp2 : sp2 = sp0) :
    cpsTripleWithin 14 ValidateHeaderWhole.H (ValidateHeaderWhole.H + 56)
      ValidateHeaderWhole.callerCode
      (step2ParentHashProloguePre sp0 spC raIn a0 a1 a2 a3 a4 a5
        o8 o9 o18 o19 o20 o21 sp2 C0 os out0 F)
      (step2ParentHashProloguePost sp0 spC raIn a0 a1 a2 a3 a4 a5
        o8 o9 o18 o19 o20 o21 sp2 C0 os out0 F) := by
  subst sp2
  have hA := step2ParentHashAmbient_pcFree sp0 C0 os out0 F hF
  have hpro := validateHeader_prologue_spec
    sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21
    (step2ParentHashAmbient sp0 C0 os out0 F) hA hspC
  simpa only [step2ParentHashProloguePre, step2ParentHashProloguePost] using hpro

/-- hcore specialized to the ambient that has actually been threaded from
    Step 2.  The existing core contract remains parametric for other callers;
    this alias is the one a parent-hash consumer can instantiate. -/
abbrev validateHeaderCoreContractWithStep2ParentHashAmbient
    (nCore : Nat) (cr : CodeReq)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (C0 os out0 : List (BitVec 8)) (F : Assertion) : Prop :=
  validateHeaderCoreContract nCore cr parentSpec headerSpec
    spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
    rawBytes parentRawBytes headerStruct parentStruct
    o1 o8 o9 o18 o19 o20 o21
    (step2ParentHashAmbient sp0 C0 os out0 F)

def validateHeaderWholePreWithStep2ParentHashAmbient
    (sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (_o1 o8 o9 o18 o19 o20 o21 : Word)
    (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  (regIs .x1 raIn) ** (regIs .x2 sp0) **
  (regIs .x8 o8) ** (regIs .x9 o9) ** (regIs .x18 o18) **
  (regIs .x19 o19) ** (regIs .x20 o20) ** (regIs .x21 o21) **
  (regIs .x10 header) ** (regIs .x11 headerLen) **
  (regIs .x12 thisStruct) ** (regIs .x13 parentStructPtr) **
  (regIs .x14 parentRlpPtr) ** (regIs .x15 parentRlpLen) **
  memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) **
  memOwn (spC + 24) ** memOwn (spC + 32) ** memOwn (spC + 40) **
  memOwn (spC + 48) **
  validateHeaderCoreFrame parentSpec headerSpec header parentRlpPtr headerLen parentRlpLen
    rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct **
  step2ParentHashAmbient sp0 C0 os out0 F

/-! This is the actual whole-header consumer of the threaded ambient.  It is
    deliberately a wrapper around `validate_header_cps_compose`: the middle
    hcore proof remains an explicit premise, but it now has the same concrete
    claimed/computed/zk3/stack/register resources that the unified route needs. -/
set_option maxRecDepth 8000 in
theorem validate_header_cps_compose_with_step2_parent_hash_ambient
    {cr : CodeReq} {nCore : Nat}
    (sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (C0 os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hdecode : EvmAsm.Stateless.SpecRef._decode_header rawBytes = .ok headerSpec)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hcaller : ∀ a i, ValidateHeaderWhole.callerCode a = some i → cr a = some i)
    (hcore : validateHeaderCoreContractWithStep2ParentHashAmbient
      nCore cr parentSpec headerSpec sp0 spC raIn header headerLen thisStruct
      parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes
      headerStruct parentStruct o1 o8 o9 o18 o19 o20 o21 C0 os out0 F) :
    cpsTripleWithin (14 + nCore + 9) ValidateHeaderWhole.H raIn cr
      (validateHeaderWholePreWithStep2ParentHashAmbient
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        parentSpec headerSpec rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 C0 os out0 F)
      (validateHeaderFinalPost parentSpec headerSpec sp0 spC raIn header headerLen
        thisStruct parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes
        headerStruct parentStruct o8 o9 o18 o19 o20 o21
        (step2ParentHashAmbient sp0 C0 os out0 F)) := by
  have hA := step2ParentHashAmbient_pcFree sp0 C0 os out0 F hF
  exact validate_header_cps_compose
    (G := step2ParentHashAmbient sp0 C0 os out0 F)
    sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
    o1 o8 o9 o18 o19 o20 o21 parentSpec headerSpec rawBytes parentRawBytes
    headerStruct parentStruct hA hdecode hspC hret hcaller hcore

/-! The side-condition envelope carried by the unified parent-hash adapter is
    independently inhabited on the same shape used by the hcore caller.  This
    is a named projection of the existing match cover, not a new decoder claim:
    it records that real lengths, alignment, byte validity and keccak bounds
    can all be supplied together. -/
def step2ParentHashEnvelope
    (sp0 spC : Word) (F : Assertion) (ret : Word)
    (thisPtr thisLen parentPtr parentLen : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) : Prop :=
  F.pcFree ∧
  ret &&& ~~~(1 : Word) = ret ∧
  spC = sp0 + signExtend12 (-32 : BitVec 12) ∧
  thisBytes.length = thisLen.toNat ∧
  3 ≤ thisBytes.length ∧ C0.length = 32 ∧
  thisPtr.toNat % 8 = 0 ∧ thisPtr.toNat + thisBytes.length ≤ 2 ^ 64 ∧
  (∀ k, k < thisBytes.length →
    isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true) ∧
  (headersParentHash_out thisBytes C0).length = 32 ∧
  parentLen = BitVec.ofNat 64
    (EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem) ∧
  parentBytes.length = EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem ∧ rem ≤ 135 ∧
  os.length = 200 ∧
  (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0 ∧
  (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64 ∧
  EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem < 2 ^ 63 ∧ rem < 2 ^ 64 ∧
  (EvmAsm.Codegen.Proofs.keccakAbsorbCursor parentPtr N).toNat % 8 = 0 ∧
  (∀ n, n < rem →
    (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
  (∀ n, n < rem →
    (EvmAsm.Codegen.Proofs.keccakAbsorbCursor parentPtr N).toNat +
      (rem - (n + 1)) < 2 ^ 64) ∧
  (∀ n, n < rem →
    isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
  (∀ n, n < rem →
    isValidByteAccess
      (EvmAsm.Codegen.Proofs.keccakAbsorbCursor parentPtr N +
        BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
  isValidByteAccess
    (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true ∧
  isValidByteAccess
    (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true ∧
  (∀ j, j < 200 →
    isValidMemAddr
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) ∧
  headersParentHash_status thisBytes = 0 ∧
  (∀ q, q < 4 →
    dwordAt (headersParentHash_out thisBytes C0) q =
      dwordAt (keccakBodyDigest parentBytes N rem) q)

theorem step2ParentHashEnvelope_inhabited :
    ∃ (sp0 spC : Word) (ret thisPtr thisLen parentPtr parentLen : Word)
        (thisBytes parentBytes C0 : List (BitVec 8))
        (N rem : Nat) (os : List (BitVec 8)) (F : Assertion),
      step2ParentHashEnvelope sp0 spC F ret thisPtr thisLen parentPtr parentLen
        thisBytes parentBytes C0 N rem os := by
  rcases header_validate_parent_hash_match_cover with
    ⟨sp0, spC, ret, thisPtr, thisLen, parentPtr, parentLen, vals, v20,
      thisBytes, parentBytes, C0, N, rem, os, F, h⟩
  exact ⟨sp0, spC, ret, thisPtr, thisLen, parentPtr, parentLen, thisBytes,
    parentBytes, C0, N, rem, os, F, by
      simpa [step2ParentHashEnvelope] using h⟩

end
end EvmAsm.Codegen.ValidateHeaderStep2ParentHashAmbient
