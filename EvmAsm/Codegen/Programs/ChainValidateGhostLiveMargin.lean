/-
  EvmAsm.Codegen.Programs.ChainValidateGhostLiveMargin

  PREDICTIVE GUARD for the ghost/live address margin (GH #12488).

  The `ChainValidate*` offline proofs compose a **ghost** self-code (a frozen
  `ChainValidateOfflineAddrs` base — the routine's last linked entry before it
  was retired from the guest image) with a **live** callee (a `GuestAddrs` base
  that moves on every `.text` layout change). Each composition needs the two
  code windows to be disjoint, discharged by `CodeReq.Disjoint.ofProg_ranges`
  whose `hsep` argument is an `Or` — and every one of those proofs picks its
  side by hand (`left`/`right`).

  Two ways that breaks, both silent until the build stops:

  1. **Overlap.** A `.text` insertion below a live window pushes it into a
     frozen ghost range. Both `hsep` branches then go false, `decide` closes
     nothing, and the failure surfaces deep inside an unrelated disjointness
     proof. Worse, if such a union were ever admitted it would describe an
     image that cannot exist, making every triple over it vacuous.
  2. **Ordering swap.** Even a *non-overlapping* shift that changes which
     window is lower falsifies the hardcoded `left`/`right` without any
     overlap, because the proof text names the side rather than deriving it.

  This module makes both failure modes fire early, from one place, with the
  actual byte counts in the message — instead of as a `decide` that closes
  nothing several files away. It is the cheap mitigation from #12488; it is
  deliberately NOT the structural fix (ghost-twinning the callee, or
  parameterising over an abstract callee base, is a design decision that has
  not been made).

  `compositions` mirrors the proof texts one-for-one, ordering included, so a
  swap is caught as a negative margin under the *declared* order.
-/

import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ChainValidateOfflineAddrs
import EvmAsm.Codegen.Programs.ChainValidate
import EvmAsm.Codegen.Programs.ChainValidateBlob
import EvmAsm.Codegen.Programs.ChainValidatePostMerge
import EvmAsm.Codegen.Programs.ChainValidateProgs
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.RlpFieldToU64StrictProgram
import EvmAsm.Rv64.RLP.ContentToU64Strict

namespace EvmAsm.Codegen.ChainValidateGhostLiveMargin

open EvmAsm.Codegen

/-! ## Code windows -/

/-- A code window: an entry address and an instruction count (4 bytes each). -/
structure Window where
  name : String
  base : Nat
  instrs : Nat

/-- One past the last byte of the window. -/
def Window.limit (w : Window) : Nat := w.base + 4 * w.instrs

/-! ### Ghost windows (frozen; `ChainValidateOfflineAddrs`)

    These do NOT move with layout — that is the whole point of a ghost base. -/

def ghostPostMergeFull : Window :=
  ⟨"chain_validate_post_merge_full",
   ChainValidateOfflineAddrs.chain_validate_post_merge_full, 149⟩

/- `chain_validate_extra_data_length` (also `0x80002f38`) is deliberately
   absent: #12484 deleted its `fullCode`/`cvedl_disjoint` closure, so the ghost
   constant survives but is no longer composed against any live callee. It has
   no margin to guard. -/

def ghostGasUsedUnderLimit : Window :=
  ⟨"chain_validate_gas_used_under_limit",
   ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit, 83⟩

def ghostBlobGasUsedMultiple : Window :=
  ⟨"chain_validate_blob_gas_used_multiple",
   ChainValidateOfflineAddrs.chain_validate_blob_gas_used_multiple, 68⟩

def ghostBlobGasUsedUnderMax : Window :=
  ⟨"chain_validate_blob_gas_used_under_max",
   ChainValidateOfflineAddrs.chain_validate_blob_gas_used_under_max, 66⟩

def ghostIncreasingTimestamps : Window :=
  ⟨"chain_validate_increasing_timestamps",
   ChainValidateOfflineAddrs.chain_validate_increasing_timestamps, 92⟩

def ghostConsecutiveNumbers : Window :=
  ⟨"chain_validate_consecutive_numbers",
   ChainValidateOfflineAddrs.chain_validate_consecutive_numbers, 93⟩

/-! ### Live windows (`GuestAddrs`; move on any `.text` layout change) -/

def liveNthItem : Window :=
  ⟨"rlp_list_nth_item", GuestAddrs.rlp_list_nth_item, 194⟩

def liveFieldToU64Strict : Window :=
  ⟨"rlp_field_to_u64_strict", GuestAddrs.rlp_field_to_u64_strict, 37⟩

def liveContentToU64Strict : Window :=
  ⟨"rlp_content_to_u64_strict", GuestAddrs.rlp_content_to_u64_strict, 22⟩

/-! ### Instruction counts are tied to the actual programs

    Without these the guard could drift from the code it claims to describe,
    which is worse than no guard: it would keep reporting a healthy margin for
    a window whose real size had changed. -/

set_option maxRecDepth 8000 in
theorem ghostPostMergeFull_instrs :
    chainValidatePostMergeFull_prog.length = ghostPostMergeFull.instrs := by decide

theorem ghostGasUsedUnderLimit_instrs :
    chainValidateGasUsedUnderLimit_prog.length = ghostGasUsedUnderLimit.instrs := by decide

theorem ghostBlobGasUsedMultiple_instrs :
    chainValidateBlobGasUsedMultiple_prog.length = ghostBlobGasUsedMultiple.instrs := by decide

theorem ghostBlobGasUsedUnderMax_instrs :
    chainValidateBlobGasUsedUnderMax_prog.length = ghostBlobGasUsedUnderMax.instrs := by decide

theorem ghostIncreasingTimestamps_instrs :
    chainValidateIncreasingTimestamps_prog.length = ghostIncreasingTimestamps.instrs := by decide

theorem ghostConsecutiveNumbers_instrs :
    chainValidateConsecutiveNumbers_prog.length = ghostConsecutiveNumbers.instrs := by decide

theorem liveNthItem_instrs :
    rlpListNthItem_prog.length = liveNthItem.instrs :=
  EvmAsm.Codegen.RlpListNthItemSAsm.total_length

theorem liveFieldToU64Strict_instrs :
    rlpFieldToU64Strict_prog.length = liveFieldToU64Strict.instrs := by decide

theorem liveContentToU64Strict_instrs :
    EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog.length
      = liveContentToU64Strict.instrs := by decide

/-! ## Compositions -/

/-- Which window the proof text asserts is the lower one. This mirrors the
    `left`/`right` picked at each `CodeReq.Disjoint.ofProg_ranges` call site:
    `ofProg_ranges`' `hsep` is
    `ghost.limit ≤ live.base ∨ live.limit ≤ ghost.base`, so `left` is
    `ghostBelowLive` and `right` is `liveBelowGhost`. -/
inductive Order where
  | ghostBelowLive
  | liveBelowGhost

/-- One ghost/live disjointness obligation, as written in the proof text. -/
structure Composition where
  ghost : Window
  live : Window
  order : Order

/-- Free bytes between the two windows, under the DECLARED order. Negative
    means the proof text's `hsep` side is false — either because the windows
    now overlap, or because the ordering swapped. -/
def Composition.margin (c : Composition) : Int :=
  match c.order with
  | .ghostBelowLive => (c.live.base : Int) - (c.ghost.limit : Int)
  | .liveBelowGhost => (c.ghost.base : Int) - (c.live.limit : Int)

/-- The margin after `.text` grows by `delta` bytes at an address below every
    live window. Ghost bases are frozen, so only the live side moves. -/
def Composition.marginAfterTextGrowth (c : Composition) (delta : Nat) : Int :=
  match c.order with
  | .ghostBelowLive => ((c.live.base + delta : Nat) : Int) - (c.ghost.limit : Int)
  | .liveBelowGhost => (c.ghost.base : Int) - ((c.live.limit + delta : Nat) : Int)

/-- The six ghosts whose proofs compose against the whole K34 closure
    (`rlp_field_to_u64_strict` wrapper, `rlp_list_nth_item`,
    `rlp_content_to_u64_strict`), in the three-bullet `left`/`right`/`left`
    shape.

    Six, not the five #12488 lists: `ChainValidateIncreasingTimestampsSpec`
    (lines 97/101/106) has the same shape and the same exposure. That issue
    says its file list is a grep and therefore a bound; this is the re-derived
    census. -/
def k34Ghosts : List Window :=
  [ghostPostMergeFull, ghostGasUsedUnderLimit, ghostBlobGasUsedMultiple,
   ghostBlobGasUsedUnderMax, ghostIncreasingTimestamps, ghostConsecutiveNumbers]

/-- Every ghost/live disjointness obligation in the `ChainValidate*` proofs:
    six ghosts against the three-member K34 closure, 18 in all. -/
def compositions : List Composition :=
  k34Ghosts.flatMap (fun g =>
    [⟨g, liveFieldToU64Strict, .ghostBelowLive⟩,
     ⟨g, liveNthItem, .liveBelowGhost⟩,
     ⟨g, liveContentToU64Strict, .ghostBelowLive⟩])

/-- Tripwire: a margin at or below this many bytes is reported as too close,
    before it becomes an overlap.

    It must sit under today's minimum (468 bytes, `rlp_list_nth_item` against
    `chain_validate_post_merge_full` at `0x80002f38`) or the guard would fire
    on a healthy tree. Be
    honest about the lead time this buys: the insertions that actually move
    this needle are routine-sized (#12477 is 1320 bytes), so a real change
    will usually cross the floor and the overlap in one step. The value here
    is a failure that names the routine and the byte count, not a slow-creep
    alarm. -/
def marginFloor : Int := 256

/-! ## Elaboration-time report

    Mirrors `FileSizeGuard`: silent while healthy, and on failure throws with
    the offending ranges and byte counts spelled out, so the message itself is
    the diagnosis.

    This deliberately precedes the `decide` facts below. Both catch the same
    drift, but a failing `decide` reports only that it closed nothing, which
    is the very diagnosis-free failure #12488 asks us to replace. Elaboration
    is top-to-bottom, so putting the report first means the numbers are what
    the reader sees. -/

private def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

private def Composition.describe (c : Composition) : String :=
  let lower := match c.order with | .ghostBelowLive => c.ghost | .liveBelowGhost => c.live
  let upper := match c.order with | .ghostBelowLive => c.live | .liveBelowGhost => c.ghost
  s!"  {c.ghost.name} vs {c.live.name}: margin {c.margin} bytes " ++
    s!"(lower {lower.name} [{hex lower.base}, {hex lower.limit}), " ++
    s!"upper {upper.name} base {hex upper.base})"

#eval show IO Unit from do
  let overlapping := compositions.filter (fun c => c.margin < 0)
  let tooClose := compositions.filter (fun c => 0 ≤ c.margin && c.margin < marginFloor)
  unless overlapping.isEmpty do
    throw <| IO.userError <|
      "ghost/live OVERLAP (GH #12488): a frozen ChainValidateOfflineAddrs " ++
      "range now intersects a live GuestAddrs callee, so the composed image " ++
      "cannot exist and every triple over it would be vacuous.\n" ++
      String.intercalate "\n" (overlapping.map Composition.describe) ++
      "\nA negative margin means the ofProg_ranges `hsep` side named in the " ++
      "proof text is false — the windows overlap, or the ordering swapped. " ++
      "Do not silence this by flipping left/right: check whether the subject " ++
      "is retired AND unconsumed before deleting, and see #12488 for the " ++
      "structural options."
  unless tooClose.isEmpty do
    throw <| IO.userError <|
      s!"ghost/live margin below the {marginFloor}-byte tripwire (GH #12488). " ++
      "Still disjoint, but the next .text insertion below the live window " ++
      "may overlap a frozen ghost range.\n" ++
      String.intercalate "\n" (tooClose.map Composition.describe)

/-! ## The kernel-checked backstop

    The report above is an `#eval`, so it is only as trustworthy as the
    elaborator running it. These restate the same properties as `decide`
    facts, which the kernel checks. -/

/-- Every composition's declared ordering still holds and the windows are
    disjoint. This is the property the `ofProg_ranges` `hsep` arguments need. -/
theorem compositions_disjoint :
    compositions.all (fun c => decide (0 ≤ c.margin)) = true := by decide

/-- Every composition additionally clears the tripwire. -/
theorem compositions_above_floor :
    compositions.all (fun c => decide (marginFloor ≤ c.margin)) = true := by decide

/-- Pins the minimum margin quoted in `marginFloor`'s docstring, so that
    figure cannot rot: today's tightest is 468 bytes, `rlp_list_nth_item`
    ending at `0x80002d64` against the lowest live-composed ghost base,
    `chain_validate_post_merge_full` at `0x80002f38`.

    Worth stating explicitly because it is NOT the number #12488 works from:
    the 1348 bytes it quotes for `chain_validate_blob_gas_used_under_max` is
    the loosest of the six margins, not the binding one. -/
theorem minimum_margin_today :
    compositions.all (fun c => decide (468 ≤ c.margin)) = true := by decide

/-- #12477 inserts `0x528` = 1320 bytes below `rlp_list_nth_item`.

    At that delta THREE compositions go negative — `post_merge_full`,
    `gas_used_under_limit` and `blob_gas_used_multiple` genuinely overlap the
    live window, rather than merely running close to it.
    `blob_gas_used_under_max`, the case #12488 names, is the last one still
    disjoint, at 28 bytes. Recorded as a checked fact so the scope of that
    landing is not re-derived from a grep. -/
theorem projected_after_12477 :
    (compositions.filter (fun c => decide (c.marginAfterTextGrowth 0x528 < 0))).length = 3 := by
  decide

#print axioms compositions_disjoint
#print axioms compositions_above_floor
#print axioms minimum_margin_today
#print axioms projected_after_12477

end EvmAsm.Codegen.ChainValidateGhostLiveMargin
