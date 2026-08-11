/-
  EvmAsm.Codegen.TxSigningHashResidual

  The signing-hash routines have a live code consumer (`tx_pubkey_signature_material`)
  but their segment-hash callee is not yet machine-proven.  This file records the
  caller contract at that seam explicitly.  It is a dependency residual, not an
  input-domain gate: the RLP parse result is an outcome of the routine.

  The interim digest is expressed with `keccakBodyDigest`, the same guest-side
  digest relation used by the Keccak bridge.  Once the segment bridge lands, the
  single replacement is the pure bridge from that relation to `SpecRef.keccak256`.
  The message definitions below are independent of that replacement.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBody
import EvmAsm.EL.RLP.FullDecode
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.TxSigningHashResidual

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.EL.RLP
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef

abbrev TxSigningHashB : Word := BitVec.ofNat 64 GuestAddrs.tx_signing_hash
abbrev TxSigningHashLegacyB : Word :=
  BitVec.ofNat 64 GuestAddrs.tx_signing_hash_legacy_eip155
abbrev Eip7702SigningHashB : Word :=
  BitVec.ofNat 64 GuestAddrs.eip7702_authorization_signing_hash

def interimKeccak (message : Bytes) : Bytes :=
  keccakBodyDigest message (message.length / keccakRateBytes) (message.length % keccakRateBytes)

/- The operational HashBridge post is `interimKeccak`; #12037 supplies this
   pure equality to the function named by the execution specs. -/
def keccakBodyDigestBridge (message : Bytes) : Prop :=
  interimKeccak message = keccak256 message

def prefixBytes (typePrefix : Word) : Bytes :=
  if typePrefix = 0 then [] else [typePrefix.truncate 8]

def genericSigningMessage (input : Bytes) (nFields typePrefix : Word) : Option Bytes :=
  match decodeFully input with
  | some (.list items) =>
      some (prefixBytes typePrefix ++ encode (.list (items.take nFields.toNat)))
  | _ => none

def legacyEip155SigningMessage (input : Bytes) (chainId : Word) : Option Bytes :=
  match decodeFully input with
  | some (.list items) =>
      some (encode (.list
        (items.take 6 ++
          [.bytes (Nat.toBytesBE chainId.toNat), .bytes [], .bytes []])))
  | _ => none

def signingHashBytesOperational (message : Option Bytes) (oldOut : Bytes) : Bytes :=
  match message with
  | some msg => interimKeccak msg
  | none => oldOut

def signingHashBytes (message : Option Bytes) (oldOut : Bytes) : Bytes :=
  match message with
  | some msg => keccak256 msg
  | none => oldOut

def signingHashStatus (message : Option Bytes) : Word :=
  match message with
  | some _ => 0
  | none => 1

/-- Entry footprint shared by the two 64-byte-frame signing-hash routines. -/
def signingHashCallEntry (sp0 inPtr lenW nFields typePrefix outPtr : Word)
    (input outOld : Bytes) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ nFields) **
  (.x13 ↦ᵣ typePrefix) ** (.x14 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inPtr input ** bytesRegion outPtr outOld

/-- Return footprint.  The status and output relation are explicit; the
    parse result is not smuggled into a precondition. -/
def signingHashCallReturn (sp0 inPtr lenW nFields typePrefix outPtr : Word)
    (input outOld : Bytes) (message : Option Bytes) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ signingHashStatus message) **
  (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ nFields) ** (.x13 ↦ᵣ typePrefix) **
  (.x14 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion inPtr input ** bytesRegion outPtr (signingHashBytes message outOld)

def signingHashOperationalCallReturn (sp0 inPtr lenW nFields typePrefix outPtr : Word)
    (input outOld : Bytes) (message : Option Bytes) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ signingHashStatus message) **
  (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ nFields) ** (.x13 ↦ᵣ typePrefix) **
  (.x14 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion inPtr input ** bytesRegion outPtr (signingHashBytesOperational message outOld)

def legacySigningHashCallEntry (sp0 inPtr lenW chainId outPtr : Word)
    (input outOld : Bytes) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ chainId) **
  (.x13 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inPtr input ** bytesRegion outPtr outOld

def legacySigningHashCallReturn (sp0 inPtr lenW chainId outPtr : Word)
    (input outOld : Bytes) (message : Option Bytes) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ (if message.isSome then (0 : Word) else 1)) **
  (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ chainId) ** (.x13 ↦ᵣ outPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion inPtr input ** bytesRegion outPtr (signingHashBytes message outOld)

def legacySigningHashOperationalCallReturn (sp0 inPtr lenW chainId outPtr : Word)
    (input outOld : Bytes) (message : Option Bytes) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ (if message.isSome then (0 : Word) else 1)) **
  (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ chainId) ** (.x13 ↦ᵣ outPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion inPtr input **
  bytesRegion outPtr (signingHashBytesOperational message outOld)

theorem signingHashOperationalReturn_to_spec
    (sp0 inPtr lenW nFields typePrefix outPtr : Word)
    (input outOld : Bytes) (message : Option Bytes)
    (hbridge : ∀ msg, message = some msg → keccakBodyDigestBridge msg) :
    signingHashOperationalCallReturn sp0 inPtr lenW nFields typePrefix outPtr
        input outOld message =
      signingHashCallReturn sp0 inPtr lenW nFields typePrefix outPtr
        input outOld message := by
  cases message with
  | none =>
      rfl
  | some msg =>
      have h_msg := hbridge msg rfl
      change interimKeccak msg = keccak256 msg at h_msg
      simp only [signingHashOperationalCallReturn, signingHashCallReturn,
        signingHashBytesOperational, signingHashBytes]
      rw [h_msg]

theorem legacySigningHashOperationalReturn_to_spec
    (sp0 inPtr lenW chainId outPtr : Word)
    (input outOld : Bytes) (message : Option Bytes)
    (hbridge : ∀ msg, message = some msg → keccakBodyDigestBridge msg) :
    legacySigningHashOperationalCallReturn sp0 inPtr lenW chainId outPtr
        input outOld message =
      legacySigningHashCallReturn sp0 inPtr lenW chainId outPtr
        input outOld message := by
  cases message with
  | none =>
      rfl
  | some msg =>
      have h_msg := hbridge msg rfl
      change interimKeccak msg = keccak256 msg at h_msg
      simp only [legacySigningHashOperationalCallReturn,
        legacySigningHashCallReturn, signingHashBytesOperational,
        signingHashBytes]
      rw [h_msg]

/-- Machine contract still owed for `zkvm_keccak256_segments`.  This is the
    load-bearing dependency used by both signing-hash routines. -/
def segmentHashCallWithinShape (cr : CodeReq) (callerPC vOld sp0 table countW outPtr : Word)
    (message : Bytes) (outOld : Bytes) (offset : BitVec 21) (fuel : Nat)
    (F : Assertion) : Prop :=
  F.pcFree ∧
  (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = (GuestAddrs.zkvm_keccak256_segments : Word) ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i) ∧
  countW.toNat = 3 ∧
  outOld.length = 32 ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) **
      ((.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
       (.x10 ↦ᵣ table) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outPtr) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion outPtr outOld)) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) **
      ((.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outPtr) **
       (.x0 ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       bytesRegion outPtr (interimKeccak message))) ** F)

/-- Generic K145 contract, with the exact RLP-derived message in the outcome.
    The separate `txSigningHashSegmentResidual` records the only unproven
    machine dependency. -/
def txSigningHashCallWithinShape (cr : CodeReq)
    (callerPC vOld sp0 inPtr lenW nFields typePrefix outPtr : Word)
    (input outOld : Bytes) (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  F.pcFree ∧ lenW.toNat = input.length ∧
  outOld.length = 32 ∧
  (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = TxSigningHashB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i) ∧
  ∃ message, message = genericSigningMessage input nFields typePrefix ∧
    (match message with
     | some msg => keccakBodyDigestBridge msg
     | none => True) ∧
    cpsTripleWithin fuel callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ vOld) **
        (signingHashCallEntry sp0 inPtr lenW nFields typePrefix outPtr input outOld)) ** F)
      (((.x1 ↦ᵣ (callerPC + 4)) **
        signingHashOperationalCallReturn sp0 inPtr lenW nFields typePrefix outPtr input outOld message) ** F)

theorem txSigningHashCallWithinShape_to_spec
    (cr : CodeReq)
    (callerPC vOld sp0 inPtr lenW nFields typePrefix outPtr : Word)
    (input outOld : Bytes) (offset : BitVec 21) (fuel : Nat) (F : Assertion)
    (hshape : txSigningHashCallWithinShape cr callerPC vOld sp0 inPtr lenW
      nFields typePrefix outPtr input outOld offset fuel F) :
    F.pcFree ∧ lenW.toNat = input.length ∧
    outOld.length = 32 ∧
    (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
    callerPC + signExtend21 offset = TxSigningHashB ∧
    (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i) ∧
    ∃ message, message = genericSigningMessage input nFields typePrefix ∧
      (match message with
       | some msg => keccakBodyDigestBridge msg
       | none => True) ∧
      cpsTripleWithin fuel callerPC (callerPC + 4) cr
        (((.x1 ↦ᵣ vOld) **
          signingHashCallEntry sp0 inPtr lenW nFields typePrefix outPtr input outOld) ** F)
        (((.x1 ↦ᵣ (callerPC + 4)) **
          signingHashCallReturn sp0 inPtr lenW nFields typePrefix outPtr input outOld message) ** F) := by
  rcases hshape with ⟨hF, hlen, hout, hret, htarget, hmem, message, hmessage, hbridge, htrip⟩
  refine ⟨hF, hlen, hout, hret, htarget, hmem, message, hmessage, hbridge, ?_⟩
  cases message with
  | none =>
      exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => hq) htrip
  | some msg =>
      have heq := signingHashOperationalReturn_to_spec
        sp0 inPtr lenW nFields typePrefix outPtr input outOld (some msg)
        (fun msg' hmsg' => by cases hmsg'; exact hbridge)
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (fun _ hq => by simpa only [heq] using hq) htrip

/-- Generic K145 contract with the segment-hash residual named separately.
    This makes the dependency visible to a caller proof instead of treating it
    as a domain restriction. -/
def txSigningHashSegmentResidual (cr : CodeReq)
    (sp0 outPtr : Word) (message outOld : Bytes)
    (offset : BitVec 21) (segmentFuel : Nat)
    (F : Assertion) : Prop :=
  keccakBodyDigestBridge message ∧
  segmentHashCallWithinShape cr (TxSigningHashB + 316) (TxSigningHashB + 320) sp0
    (GuestAddrs.tsh_buf : Word) (3 : Word) outPtr message outOld
    offset segmentFuel F

/-- Legacy K146 contract, with `(chain_id, 0, 0)` in the modelled RLP list. -/
def txSigningHashLegacyCallWithinShape (cr : CodeReq)
    (callerPC vOld sp0 inPtr lenW chainId outPtr : Word)
    (input outOld : Bytes) (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  F.pcFree ∧ lenW.toNat = input.length ∧ outOld.length = 32 ∧
  (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = TxSigningHashLegacyB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i) ∧
  ∃ message, message = legacyEip155SigningMessage input chainId ∧
    (match message with
     | some msg => keccakBodyDigestBridge msg
     | none => True) ∧
    cpsTripleWithin fuel callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ vOld) **
        (legacySigningHashCallEntry sp0 inPtr lenW chainId outPtr input outOld)) ** F)
      (((.x1 ↦ᵣ (callerPC + 4)) **
        legacySigningHashOperationalCallReturn sp0 inPtr lenW chainId outPtr
          input outOld message) ** F)

theorem txSigningHashLegacyCallWithinShape_to_spec
    (cr : CodeReq)
    (callerPC vOld sp0 inPtr lenW chainId outPtr : Word)
    (input outOld : Bytes) (offset : BitVec 21) (fuel : Nat) (F : Assertion)
    (hshape : txSigningHashLegacyCallWithinShape cr callerPC vOld sp0 inPtr lenW
      chainId outPtr input outOld offset fuel F) :
    F.pcFree ∧ lenW.toNat = input.length ∧ outOld.length = 32 ∧
    (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
    callerPC + signExtend21 offset = TxSigningHashLegacyB ∧
    (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i) ∧
    ∃ message, message = legacyEip155SigningMessage input chainId ∧
      (match message with
       | some msg => keccakBodyDigestBridge msg
       | none => True) ∧
      cpsTripleWithin fuel callerPC (callerPC + 4) cr
        (((.x1 ↦ᵣ vOld) **
          legacySigningHashCallEntry sp0 inPtr lenW chainId outPtr input outOld) ** F)
        (((.x1 ↦ᵣ (callerPC + 4)) **
          legacySigningHashCallReturn sp0 inPtr lenW chainId outPtr input outOld message) ** F) := by
  rcases hshape with ⟨hF, hlen, hout, hret, htarget, hmem, message, hmessage, hbridge, htrip⟩
  refine ⟨hF, hlen, hout, hret, htarget, hmem, message, hmessage, hbridge, ?_⟩
  cases message with
  | none =>
      exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => hq) htrip
  | some msg =>
      have heq := legacySigningHashOperationalReturn_to_spec
        sp0 inPtr lenW chainId outPtr input outOld (some msg)
        (fun msg' hmsg' => by cases hmsg'; exact hbridge)
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (fun _ hq => by simpa only [heq] using hq) htrip

def txSigningHashResidualNote : String :=
  "K145/K146 caller contracts expose the RLP-derived signing message and the " ++
  "interim keccakBodyDigest output.  Their remaining machine dependency is " ++
  "zkvm_keccak256_segments; discharge it with the segment bridge, then replace " ++
  "interimKeccak by the pure SpecRef.keccak256 bridge.  This is a dependency, " ++
  "not an input-domain gate."

end EvmAsm.Codegen.TxSigningHashResidual
