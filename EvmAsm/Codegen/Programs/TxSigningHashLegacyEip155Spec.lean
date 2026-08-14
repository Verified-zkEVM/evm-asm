/-
  EvmAsm.Codegen.Programs.TxSigningHashLegacyEip155Spec

  Whole-routine machine contract for `tx_signing_hash_legacy_eip155` (K146,
  issue 12038).  This file deliberately stops at the machine-level contract:
  its successful post uses the operational segment-hash bytes.  The later
  correspondence file will replace that digest relation with
  `SpecRef.signing_hash_155`.

  The post is unified.  A parse/header/callee failure is the `none` arm; a
  successful parse is the `some message` arm.  No branch condition is admitted
  as a precondition.

  The four calls are existing machine contracts, not new domain assumptions:

  * `rlpListNthItem_spec_within` at `+120`;
  * `RlpEncodeUintBeSAsm.reub_spec_within_of_length_le` at `+224` (the source
    is the fixed eight-byte chain-id slot, so `8 ≤ 55` is arithmetic);
  * `tsh_prefix_any_callWithin` at `+260`;
  * `zkvm_keccak256_segments_spec_within` at `+424`, specifically the
    multi-rate segment theorem rather than the short one-shot theorem.
-/

import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.TxSigningHashResidual
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Programs.TxSigningHashSpecPrefix
import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTop
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Codegen.TxSigningHashLegacyEip155Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashResidual
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Codegen.RlpEncodeUintBeSAsm

/-! ## Linked image and frame -/

abbrev LegacyB : Word :=
  BitVec.ofNat 64 GuestAddrs.tx_signing_hash_legacy_eip155

abbrev NthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
abbrev UintB : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_uint_be
abbrev PrefixB : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_list_prefix

def legacyFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]

abbrev legacyRoutineCode : CodeReq :=
  CodeReq.ofProg LegacyB txSigningHashLegacyEip155_prog

abbrev legacyFullCode : CodeReq :=
  legacyRoutineCode.union
    (EvmAsm.Codegen.RlpListNthItemSAsm.code.union
      ((CodeReq.ofProg PrefixB rlpEncodeListPrefix_prog).union
        (RlpEncodeUintBeSAsm.reubCode.union kssCr)))

/-! ## Caller-facing footprints -/

def legacyCallerPre (inPtr lenW chainId outPtr : Word)
    (input outOld : List (BitVec 8)) (newSp : Word)
    (A F : Assertion) : Assertion :=
  (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ chainId) **
  (.x13 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
  stackFree newSp 8 ** bytesRegion inPtr input ** bytesRegion outPtr outOld ** A ** F

def legacyCallerPostFor (inPtr lenW chainId outPtr : Word)
    (input outOld : List (BitVec 8)) (newSp : Word)
    (message : Option (List (BitVec 8)))
    (A F : Assertion) : Assertion :=
  stackFree newSp 8 **
  (.x10 ↦ᵣ signingHashStatus message) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ chainId) ** (.x13 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion inPtr input **
  bytesRegion outPtr (signingHashBytesOperational message outOld) ** A ** F

/- The `none` arm is the complete failure post.  The `some` arm carries the
   exact legacy EIP-155 signing message derived from the input. -/
def legacyCallerPost (inPtr lenW chainId outPtr : Word)
    (input outOld : List (BitVec 8)) (newSp : Word)
    (A F : Assertion) : Assertion :=
  fun h =>
    legacyCallerPostFor inPtr lenW chainId outPtr input outOld newSp none A F h ∨
    ∃ message,
      legacyEip155SigningMessage input chainId = some message ∧
      legacyCallerPostFor inPtr lenW chainId outPtr input outOld newSp
        (some message) A F h

/-! ## Fuel envelope -/

/- The exact composed bound is a later proof obligation.  Keeping it as an
   explicit parameter makes the machine statement reusable by a caller while
   leaving the four callee bounds visible to the eventual proof.  It is a
   static termination budget, not a premise selecting a machine outcome. -/
def legacyEip155Fuel (input : List (BitVec 8)) : Nat :=
  120 + 1 + 2 * (input.length + 1) + 200000

/-! ## Whole-routine machine statement -/

/-- `tx_signing_hash_legacy_eip155`, all outcomes, at its linked guest PC.

    Hypotheses are ABI/resource facts only: ambient pc-freedom, the saved
    return address, input/output alignment and bounds, byte validity, and a
    fuel envelope.  In particular there is no hypothesis on the first RLP
    byte, input length being nonzero, field count, header class, or any callee
    status.  Those are represented by the `none`/`some message` post arms.

    The output is intentionally `signingHashBytesOperational`; the later
    SpecRef correspondence theorem is a separate K146 step. -/
theorem tx_signing_hash_legacy_eip155_spec_within
    (sp0 ret : Word) (vals : Reg → Word)
    (inPtr lenW chainId outPtr : Word)
    (input outOld : List (BitVec 8)) (A F : Assertion) (fuel : Nat)
    (hA : A.pcFree) (hF : F.pcFree)
    (hret : vals .x1 = ret)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hlenW : lenW.toNat = input.length)
    (halign_in : inPtr.toNat % 8 = 0)
    (hover_in : inPtr.toNat + input.length < 2 ^ 64)
    (hvalid_in : ∀ k, k < input.length →
      isValidByteAccess (inPtr + BitVec.ofNat 64 k) = true)
    (halign_out : outPtr.toNat % 8 = 0)
    (hover_out : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hvalid_out : ∀ k, k < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hlegacy_buf :
      ∀ k, k < 131072 →
        isValidByteAccess
          ((BitVec.ofNat 64 GuestAddrs.t155_buf) + BitVec.ofNat 64 k) = true)
    (hlegacy_chain :
      ∀ k, k < 8 →
        isValidByteAccess
          ((BitVec.ofNat 64 GuestAddrs.t155_chain_be) + BitVec.ofNat 64 k) = true)
    (hlegacy_chain_enc :
      ∀ k, k < 9 →
        isValidByteAccess
          ((BitVec.ofNat 64 GuestAddrs.t155_chain_enc) + BitVec.ofNat 64 k) = true)
    (hlegacy_prefix :
      isValidByteAccess (BitVec.ofNat 64 GuestAddrs.t155_prefix_len) = true)
    (hfuel : legacyEip155Fuel input ≤ fuel) :
    let newSp := sp0 + signExtend12 (-64 : BitVec 12)
    cpsTripleWithin fuel LegacyB ret legacyFullCode
      ((.x2 ↦ᵣ sp0) ** regsAt legacyFrame vals **
        frameSlotsOwn legacyFrame newSp **
        legacyCallerPre inPtr lenW chainId outPtr input outOld newSp A F)
      ((.x2 ↦ᵣ sp0) ** regsAt legacyFrame vals **
        frameSlotsSaved legacyFrame newSp vals **
        legacyCallerPost inPtr lenW chainId outPtr input outOld newSp A F) := by
  sorry

end EvmAsm.Codegen.TxSigningHashLegacyEip155Spec
