/-
  Machine contract scaffold for `block_header_ssz_to_rlp`.

  This file deliberately starts with the two facts on which the whole caller
  composition depends: the linked 356-instruction program is an ABI frame,
  and the result buffer bound is derived from the Amsterdam field widths.  The
  byte-producing body contract is built below these facts; keeping the frame
  and capacity lemmas separate makes it impossible to hide an incorrect
  capacity assumption in a later `xperm` proof.
-/

import EvmAsm.Codegen.Programs.BlockHeaderSszToRlp
import EvmAsm.Codegen.Programs.RlpEncodeBytesComposeSAsm
import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong2Spec
import EvmAsm.Codegen.Programs.BhrRevLeBeSAsm
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.BlockHeaderSszToRlpSpec

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-! ## Linked program and ABI frame -/

def bhrB : Word := (GuestAddrs.block_header_ssz_to_rlp : Word)

def bhrCr : CodeReq := CodeReq.ofProg bhrB blockHeaderSszToRlp_prog

/-- `ra` plus the nine callee-saved registers written by the prologue. -/
def bhrFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)),
   (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
   (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)),
   (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12)),
   (.x23, (64 : BitVec 12)), (.x24, (72 : BitVec 12))]

/-- The instructions between the eleventh prologue instruction and the first
    epilogue load.  The two counts are part of the contract, not comments. -/
def bhrBody : List Instr := (blockHeaderSszToRlp_prog.drop 11).take 333

theorem bhrFrame_length : bhrFrame.length = 10 := by decide

set_option maxRecDepth 8000 in
theorem bhrBody_length : bhrBody.length = 333 := by decide

set_option maxRecDepth 8000 in
theorem bhr_abiFrame_byte_tie :
    abiFrameProg (-96 : BitVec 12) (96 : BitVec 12) bhrFrame bhrBody =
      blockHeaderSszToRlp_prog := by
  decide

/-! ## Capacity derived from the 23 field-width constraints -/

/-- Widths that are fixed by the Amsterdam header schema.  The only variable
    field is `extra_data`; all seven scalar u64 fields are bounded by eight
    bytes and the bloom is the fixed 256-byte SSZ field. -/
structure BhrFieldWidths where
  extraData : Nat
  extraData_le : extraData ≤ 32

/-- Maximum RLP byte length of one byte-string field.  For the widths used by
    this routine, every non-empty fixed field is below the 56-byte boundary
    except the 256-byte bloom, whose canonical prefix is three bytes. -/
def bhrBytesEncodedMax (n : Nat) : Nat :=
  if n < 56 then n + 1 else if n < 256 then n + 2 else n + 3

/-- The uint encoder strips leading zeroes.  Eight input bytes therefore have
    at most a nine-byte RLP encoding (`0x88` plus eight data bytes); zero is
    already included in this upper bound. -/
def bhrUintEncodedMax (n : Nat) : Nat :=
  if n = 0 then 1 else if n ≤ 55 then n + 1 else n + 2

def bhrPayloadEncodedMax (w : BhrFieldWidths) : Nat :=
  bhrBytesEncodedMax 32 + bhrBytesEncodedMax 32 +
  bhrBytesEncodedMax 20 + bhrBytesEncodedMax 32 +
  bhrBytesEncodedMax 32 + bhrBytesEncodedMax 32 +
  bhrBytesEncodedMax 256 + bhrUintEncodedMax 0 +
  bhrUintEncodedMax 8 + bhrUintEncodedMax 8 +
  bhrUintEncodedMax 8 + bhrUintEncodedMax 8 +
  bhrBytesEncodedMax w.extraData + bhrBytesEncodedMax 32 +
  bhrBytesEncodedMax 8 + bhrUintEncodedMax 32 +
  bhrBytesEncodedMax 32 + bhrUintEncodedMax 8 +
  bhrUintEncodedMax 8 + bhrBytesEncodedMax 32 +
  bhrBytesEncodedMax 32 + bhrBytesEncodedMax 32 +
  bhrUintEncodedMax 8

def bhrResultEncodedMax (w : BhrFieldWidths) : Nat :=
  bhrPayloadEncodedMax w + 3

theorem bhr_field_width_maximum (w : BhrFieldWidths) :
    bhrPayloadEncodedMax w ≤ 749 := by
  have hle := w.extraData_le
  have hextra : w.extraData < 56 := by omega
  simp [bhrPayloadEncodedMax, bhrBytesEncodedMax, bhrUintEncodedMax, hextra]
  omega

theorem bhr_field_width_maximum_attained :
    bhrPayloadEncodedMax {
      extraData := 32
      extraData_le := by decide } = 749 := by
  decide

theorem bhr_result_capacity_bound (w : BhrFieldWidths) :
    bhrResultEncodedMax w ≤ 1024 := by
  have h := bhr_field_width_maximum w
  simp [bhrResultEncodedMax]
  omega

theorem bhr_documented_627_is_not_the_23_field_maximum :
    ¬ (∀ w : BhrFieldWidths, bhrResultEncodedMax w ≤ 627) := by
  intro h
  have h32 : bhrResultEncodedMax {
      extraData := 32
      extraData_le := by decide } ≤ 627 := h _
  norm_num [bhrResultEncodedMax, bhrPayloadEncodedMax,
    bhrBytesEncodedMax, bhrUintEncodedMax] at h32

/-! A concrete non-empty width witness.  This is intentionally kept at the
    capacity layer for now; the producer post below reuses it to show that the
    output-region precondition is not empty. -/

def bhrSampleWidths : BhrFieldWidths := {
  extraData := 32
  extraData_le := by decide }

theorem bhrSampleWidths_result_capacity :
    bhrResultEncodedMax bhrSampleWidths = 752 := by decide

/-! ## Alignment residual exposed by the existing callee contracts

    `rlp_encode_bytes` only emits byte stores, so its machine path is valid at
    an arbitrary byte address.  Its current compose theorem nevertheless asks
    for an 8-byte-aligned output window.  The producer's packed accumulator
    reaches the next field after the 33-byte encoding of a 32-byte hash, so a
    caller cannot discharge that hypothesis at the second field.  Keep this
    as a checked fact rather than smuggling a false alignment premise into the
    producer theorem. -/

theorem bhr_payload_is_dword_aligned :
    ((GuestAddrs.bhr_payload : Word).toNat % 8) = 0 := by decide

theorem bhr_after_parent_hash_is_not_dword_aligned :
    (((GuestAddrs.bhr_payload : Word) + BitVec.ofNat 64 33).toNat % 8) = 1 := by
  decide

end EvmAsm.Codegen.BlockHeaderSszToRlpSpec
