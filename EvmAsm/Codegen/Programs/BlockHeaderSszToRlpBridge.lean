/-
  EvmAsm.Codegen.Programs.BlockHeaderSszToRlpBridge

  Bridges the SSZ schema constant `MAX_EXTRA_DATA_BYTES = 32` into the
  `BhrFieldWidths` capacity facts (`#13233`).

  The capacity theorems in `BlockHeaderSszToRlpSpec` (`bhr_field_width_maximum`,
  `bhr_result_capacity_bound`) are conditional on `BhrFieldWidths.extraData_le`,
  a hand-carried width hypothesis.  Every guest-accepted header is narrower:
  `validate_header` itself rejects `header.extraData.length > 32`
  (`SpecRef/SeamShell.lean` ~:257), and the SSZ schema declares the payload's
  extraData field as `.byteList MAX_EXTRA_DATA_BYTES`
  (`SpecRef/Ssz.lean:86`, codec enforcement at `SszCodec.lean:207-208`).
  This file makes those two sources of the 32-byte bound usable at the capacity
  layer.  `MAX_EXTRA_DATA_BYTES` is definitionally `32`, so the bridge is a
  construction, not a new bound; it simply changes where the bound comes from.

  It does NOT change the hcore pre (the hslack option-(a) pre-shape remains a
  maintainer decision).  The payload-field extraction that reaches
  `extraData ≤ 32` from a successful container `deserialize` is a separate,
  larger piece of SSZ plumbing and is NOT included here.
-/

import EvmAsm.Codegen.Programs.BlockHeaderSszToRlpSpec
import EvmAsm.Stateless.SpecRef.Ssz

namespace EvmAsm.Codegen.BlockHeaderSszToRlpSpec

open EvmAsm.Stateless.SpecRef

/-- Construct the capacity-width record from an SSZ-side length fact.  This is
    the bridge coord's ask: `bhr_field_width_maximum` /
    `bhr_result_capacity_bound` become applicable whenever the decoder (or
    `validate_header`) proves `extraData.length ≤ MAX_EXTRA_DATA_BYTES`. -/
@[reducible] def bhrWidthsOfExtraDataLe (n : Nat) (hn : n ≤ MAX_EXTRA_DATA_BYTES) :
    BhrFieldWidths :=
  { extraData := n
    extraData_le := by simpa [MAX_EXTRA_DATA_BYTES] using hn }

/-- The capacity bound, now derived purely from the SSZ width constant
    `MAX_EXTRA_DATA_BYTES` instead of a hand-carried `extraData_le`. -/
theorem bhr_capacity_bound_of_extra_data_le (n : Nat)
    (hn : n ≤ MAX_EXTRA_DATA_BYTES) :
    bhrResultEncodedMax (bhrWidthsOfExtraDataLe n hn) ≤ 1024 := by
  exact bhr_result_capacity_bound (bhrWidthsOfExtraDataLe n hn)

/-- Non-vacuity witness: at the SSZ maximum `n = 32` the worst-case encoding
    is attained at 752 bytes (not 0), so the ≤ 1024 bound is genuinely
    exercised. -/
theorem bhr_capacity_bound_of_extra_data_le_nonvacuous (n : Nat)
    (_hn : n ≤ MAX_EXTRA_DATA_BYTES) :
    bhrResultEncodedMax (bhrWidthsOfExtraDataLe 32 (by decide)) = 752 := by
  simpa [bhrWidthsOfExtraDataLe, bhrSampleWidths] using bhrSampleWidths_result_capacity

/-- The slack fact the hslack option-(a) pre-shape rests on: even at the SSZ
    worst case (752-byte RLP), a 1024-byte input region always leaves at least
    nine bytes of spare room after the produced RLP. -/
theorem bhr_slack_at_least_9 (n : Nat) (_hn : n ≤ MAX_EXTRA_DATA_BYTES) :
    bhrResultEncodedMax (bhrWidthsOfExtraDataLe 32 (by decide)) + 9 ≤ 1024 := by
  change bhrResultEncodedMax bhrSampleWidths + 9 ≤ 1024
  rw [bhrSampleWidths_result_capacity]
  norm_num

#print axioms bhr_capacity_bound_of_extra_data_le

end EvmAsm.Codegen.BlockHeaderSszToRlpSpec