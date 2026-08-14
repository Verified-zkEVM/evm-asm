/-
  EvmAsm.Codegen.Programs.ValidateHeaderPostMergeCorrespondence

  Call-site adapter for the post-merge trio in `validate_header`.

  The K67 `header_validate_post_merge` Program exists, but its machine triple
  does not.  This module therefore makes that missing triple an explicit
  premise instead of treating the old `chain_validate_post_merge_full`
  theorem as if it described K67.  The adapter fixes the exact ABI/frame
  contract that a future K67 proof must consume; the pure byte and constant
  bridges remain usable independently of the deleted dead routine.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCorrespondence
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.ChainValidatePostMergeFullSpec
import EvmAsm.Codegen.Programs.SpecRefConstantPins
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.ValidateHeaderPostMergeCorrespondence

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-! ## The linked call and the K67 premise shape -/

abbrev H : Word := EvmAsm.Codegen.ValidateHeaderCorrespondence.H
abbrev A : Word := H + 192
abbrev Ret : Word := H + 196
abbrev K : Word := (GuestAddrs.header_validate_post_merge : Word)

abbrev callerCode : CodeReq := EvmAsm.Codegen.ValidateHeaderCorrespondence.callerCode

def postMergeFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32)]

def postMergeSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32)]

def postMergeFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

/- The assertion immediately below is the exact K67 machine entry, with the
   linking `x1` factored out for `WP.cpsCallWithin`.  K67 owns the 40-byte
   frame it allocates, reads the caller-owned header byte region, preserves
   x8/x9/x18/x19 through that frame, leaves x20/x21 untouched, and uses the
   listed scratch registers. -/
def postMergeEntryRest
    (sp0 header headerLen s4 s5 : Word) (vals : Reg → Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn postMergeFrame (sp0 + signExtend12 (-40 : BitVec 12)) **
  regsAt postMergeSavedFrame vals **
  (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ headerLen) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion header bytes

/- The future K67 machine triple must return this shape: linked `ra`, original
   `sp`, restored saved registers and stack slots, status in `x10`, the
   untouched x20/x21 values, the input bytes, and ownership of the registers
   K67 uses as temporaries.  The status-to-SpecRef relation is deliberately
   not hidden here; the pure bridges below cover only the specification half. -/
def postMergeCalleePost
    (sp0 header s4 s5 ret status : Word) (vals : Reg → Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved postMergeFrame (sp0 + signExtend12 (-40 : BitVec 12))
    (postMergeFrameVals ret vals) **
  regsAt postMergeSavedFrame vals **
  (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ status) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion header bytes

theorem postMergeEntryRest_pcFree
    (sp0 header headerLen s4 s5 : Word) (vals : Reg → Word)
    (bytes : List (BitVec 8)) :
    (postMergeEntryRest sp0 header headerLen s4 s5 vals bytes).pcFree := by
  unfold postMergeEntryRest postMergeFrame postMergeSavedFrame
  pcf

theorem validateHeader_length : EvmAsm.Codegen.validateHeader_prog.length = 97 := by
  exact EvmAsm.Codegen.ValidateHeaderCorrespondence.validateHeader_length

theorem validateHeader_postMerge_jal_mem :
    ∀ a i, CodeReq.singleton A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_post_merge
        (GuestAddrs.validate_header + 192))) a = some i → callerCode a = some i := by
  exact CodeReq.ofProg_mem_at
    (GuestAddrs.validate_header : Word) A EvmAsm.Codegen.validateHeader_prog 48 _
    (by bv_omega) (by rw [validateHeader_length]; decide) rfl
    (by rw [validateHeader_length]; decide)

/-!
The theorem below is the machine half of the post-merge correspondence.  Its
`hcallee` premise is intentionally undischarged: proving that premise is the
missing machine triple for K67 `header_validate_post_merge`.  A future proof
must instantiate `calleeCode` with K67 plus its RLP-walker closure and must
expose the exact `postMergeCalleePost` status; no old full-routine theorem can
be substituted because `chain_validate_post_merge_full` is a different
Program and was removed as dead code.
-/
set_option maxRecDepth 8000 in
theorem validate_header_post_merge_call_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (sp0 header headerLen s4 s5 oldRa : Word) (vals : Reg → Word)
    (bytes : List (BitVec 8)) (status : Word) (F : Assertion)
    (hF : F.pcFree)
    (hdisj : (CodeReq.singleton A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_post_merge
        (GuestAddrs.validate_header + 192)))).Disjoint calleeCode)
    (hcallerDisj : callerCode.Disjoint calleeCode)
    (hcode : ∀ a i, (callerCode.union calleeCode) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n K Ret calleeCode
      ((.x1 ↦ᵣ Ret) ** postMergeEntryRest sp0 header headerLen s4 s5 vals bytes)
      (postMergeCalleePost sp0 header s4 s5 Ret status vals bytes)) :
    cpsTripleWithin (1 + n) A Ret cr
      (((.x1 ↦ᵣ oldRa) **
        postMergeEntryRest sp0 header headerLen s4 s5 vals bytes) ** F)
      (postMergeCalleePost sp0 header s4 s5 Ret status vals bytes ** F) := by
  have htarget : A + signExtend21 (jalOff GuestAddrs.header_validate_post_merge
      (GuestAddrs.validate_header + 192)) = K := by
    change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 192 + _ =
      BitVec.ofNat 64 GuestAddrs.header_validate_post_merge
    exact jalOff_correct_add GuestAddrs.header_validate_post_merge
      GuestAddrs.validate_header 192 (by decide) (by decide) (by decide) (by decide)
  have hret' : (A + 4) &&& ~~~(1 : Word) = A + 4 := by decide
  have hpre := postMergeEntryRest_pcFree sp0 header headerLen s4 s5 vals bytes
  have hRet : A + 4 = Ret := by decide
  have hcallee' : cpsTripleWithin n K ((A + 4) &&& ~~~(1 : Word)) calleeCode
      ((.x1 ↦ᵣ Ret) ** postMergeEntryRest sp0 header headerLen s4 s5 vals bytes)
      (postMergeCalleePost sp0 header s4 s5 Ret status vals bytes) := by
    rw [hret', hRet]
    exact hcallee
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := A) (calleeEntry := K) (vOld := oldRa)
    (calleeCode := calleeCode) (Prest := postMergeEntryRest sp0 header headerLen s4 s5 vals bytes)
    (Q := postMergeCalleePost sp0 header s4 s5 Ret status vals bytes)
    (jalOff GuestAddrs.header_validate_post_merge (GuestAddrs.validate_header + 192))
    htarget hret' hpre hdisj hcallee'
  have hcallCode : ∀ a i,
      ((CodeReq.singleton A (.JAL .x1 (jalOff GuestAddrs.header_validate_post_merge
        (GuestAddrs.validate_header + 192)))).union calleeCode) a = some i →
      (callerCode.union calleeCode) a = some i := by
    exact CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i
        (validateHeader_postMerge_jal_mem a i h))
      (fun a i h => CodeReq.mono_union_right hcallerDisj
        (fun _ _ h' => h') a i h)
  have hcallC := cpsTripleWithin_extend_code hcallCode hcall
  have hcallCr := cpsTripleWithin_extend_code hcode hcallC
  have hcallF := cpsTripleWithin_frameR F hF hcallCr
  simpa [hRet] using hcallF

/-! ## Pure specification-side bridges

These are the surviving mathematical pieces from `ChainValidatePostMergeFullSpec`.
They do not certify K67's emitted machine code.  They become usable by a future
K67 triple: the difficulty bridge identifies byte-level scalar zero, the nonce
bridge uses the fixed eight-byte field width, and the constant pin keeps
`EMPTY_OMMER_HASH = keccak256(0xc0)` distinct from the empty-trie root
`keccak256(0x80)`. -/

theorem difficulty_zero_bytes_bridge (bs : List EvmAsm.EL.RLP.Byte) :
    EvmAsm.EL.RLP.Nat.fromBytesBE bs = 0 ↔
      bs = List.replicate bs.length 0 :=
  EvmAsm.Codegen.ChainValidatePostMergeFullSpec.fromBytesBE_eq_zero_iff bs

theorem nonce_zero_bytes_bridge (bs : List EvmAsm.EL.RLP.Byte) (hlen : bs.length = 8) :
    EvmAsm.EL.RLP.Nat.fromBytesBE bs = 0 ↔
      bs = List.replicate 8 (0 : EvmAsm.EL.RLP.Byte) :=
  EvmAsm.Codegen.ChainValidatePostMergeFullSpec.nonce_rule_agrees bs hlen

theorem empty_ommer_hash_pin_and_trie_root_distinction :
    EvmAsm.Codegen.SpecRefConstantPins.hexNat?
        EvmAsm.Stateless.Constants.emptyOmmerHashHex
        = some 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
      ∧ EvmAsm.Codegen.SpecRefConstantPins.hexNat?
        EvmAsm.Stateless.Constants.emptyTrieRootHex
        = some 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421
      ∧ EvmAsm.Codegen.SpecRefConstantPins.hexNat?
        EvmAsm.Stateless.Constants.emptyOmmerHashHex ≠
        EvmAsm.Codegen.SpecRefConstantPins.hexNat?
          EvmAsm.Stateless.Constants.emptyTrieRootHex :=
  EvmAsm.Codegen.SpecRefConstantPins.fix_emptyOmmerHashHex

end EvmAsm.Codegen.ValidateHeaderPostMergeCorrespondence
