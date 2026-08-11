/-
  Pure layer for `mpt_node_kind` (#11799 dep / #11347 machine hole).

  Guest semantics (arity-exact after #11347):
    count items; fail → 3;
    count = 17 → branch 0;
    count ≠ 2 → fail 3;
    else nth item 0 path; empty path → 3;
    high nibble 0/1 → extension 1; 2/3 → leaf 2; else 3.

  ⚠️ The pure `mptNodeKindSpec` in MptAssertions is LOOSER (`2 < length → branch`)
  and does NOT match the guest after the arity fix. Machine posts use the guest
  mirror below. Under `MptNode.WF` both agree (branch is always 17 children + value).
-/

import EvmAsm.Evm64.MptAssertions
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmBase
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.MptNodeKindSpec

open EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- Guest-faithful kind discriminator (arity-exact).

    Kept for coverRef / `#guard`s only. Result→`kindTag` under WF is
    `MptNodeKindWire.mptNodeKindResult_eq_kindTag` (#12027) — that path does
    **not** go through this def (the pure `mptNodeKindGuest_eq_kindTag` /
    `mptNodeKindSpec_eq_guest_of_WF` bridges were deleted as unused supersedes). -/
def mptNodeKindGuest (node : List (BitVec 8)) : Nat :=
  match decodeFully node with
  | some (.list items) =>
    if items.length = 17 then 0
    else if items.length ≠ 2 then 3
    else
      match items with
      | [.bytes path, _] =>
        match path with
        | [] => 3
        | b0 :: _ =>
          let hn := b0.toNat / 16
          if hn < 2 then 1 else if hn < 4 then 2 else 3
      | _ => 3
  | _ => 3

/-! ## coverRef — all three success tags + fail, decide-closed -/

private def coverBranch : List (BitVec 8) :=
  (MptNode.branch (List.replicate 16 []) []).rlp

private def coverLeaf : List (BitVec 8) :=
  (MptNode.leaf [1, 2, 3] [0xaa]).rlp

private def coverExt : List (BitVec 8) :=
  (MptNode.extension [5] (List.replicate 32 0)).rlp

#guard mptNodeKindGuest coverBranch = 0
#guard mptNodeKindGuest coverLeaf = 2
#guard mptNodeKindGuest coverExt = 1
#guard mptNodeKindGuest ([] : List (BitVec 8)) = 3

/-- Non-vacuity: guest kind hits branch / extension / leaf / fail on concrete bytes. -/
theorem mpt_node_kind_precondition_reachable :
    mptNodeKindGuest coverBranch = 0 ∧
    mptNodeKindGuest coverExt = 1 ∧
    mptNodeKindGuest coverLeaf = 2 ∧
    mptNodeKindGuest [] = 3 := by
  decide

/-! ## Strict operational result (machine post)

    The guest classifies via `rlp_list_count_items` / `rlp_list_nth_item`
    (strict walk), not `decodeFully`. The machine triple posts this relation;
    under `MptNode.WF`, `MptNodeKindWire.mptNodeKindResult_eq_kindTag` recovers
    `kindTag` for walk callers (success arms `kind < 3`). -/

/-- HP high-nibble → kind tag (1 ext / 2 leaf / 3 fail). -/
def hpKind (b : BitVec 8) : Nat :=
  let hn := b.toNat / 16
  if hn < 2 then 1 else if hn < 4 then 2 else 3

/-- Operational kind result matching guest control flow on strict Results. -/
inductive MptNodeKindResult (bytes : List (BitVec 8)) (base : Word)
    (listLen : Nat) (oldCount oldOff oldLen : Word) : Nat → Prop
  /-- count failed → kind 3 -/
  | countFail
      (h : RlpListCountItemsSAsm.Result bytes base listLen (1 : Word) (0 : Word)) :
      MptNodeKindResult bytes base listLen oldCount oldOff oldLen 3
  /-- count = 17 → branch 0 -/
  | branch
      (h : RlpListCountItemsSAsm.Result bytes base listLen (0 : Word)
        (BitVec.ofNat 64 17)) :
      MptNodeKindResult bytes base listLen oldCount oldOff oldLen 0
  /-- count success, not 17 and not 2 → kind 3 -/
  | badArity (c : Nat) (hc : c < 2 ^ 64)
      (h : RlpListCountItemsSAsm.Result bytes base listLen (0 : Word)
        (BitVec.ofNat 64 c))
      (hne17 : c ≠ 17) (hne2 : c ≠ 2) :
      MptNodeKindResult bytes base listLen oldCount oldOff oldLen 3
  /-- count = 2, nth failed → kind 3 -/
  | nthFail
      (hc : RlpListCountItemsSAsm.Result bytes base listLen (0 : Word)
        (BitVec.ofNat 64 2))
      (hn : RlpListNthItemSAsm.Result bytes base listLen 0 oldOff oldLen
        (1 : Word) oldOff oldLen) :
      MptNodeKindResult bytes base listLen oldCount oldOff oldLen 3
  /-- count = 2, nth ok, path length 0 → kind 3 -/
  | emptyPath (off : Word)
      (hc : RlpListCountItemsSAsm.Result bytes base listLen (0 : Word)
        (BitVec.ofNat 64 2))
      (hn : RlpListNthItemSAsm.Result bytes base listLen 0 oldOff oldLen
        (0 : Word) off (0 : Word)) :
      MptNodeKindResult bytes base listLen oldCount oldOff oldLen 3
  /-- count = 2, nth ok, path non-empty → HP classify -/
  | path (off len : Word) (b : BitVec 8) (kind : Nat)
      (hc : RlpListCountItemsSAsm.Result bytes base listLen (0 : Word)
        (BitVec.ofNat 64 2))
      (hn : RlpListNthItemSAsm.Result bytes base listLen 0 oldOff oldLen
        (0 : Word) off len)
      (hlen : 0 < len.toNat)
      (hb : bytes[off.toNat]? = some b)
      (hk : kind = hpKind b) :
      MptNodeKindResult bytes base listLen oldCount oldOff oldLen kind

end EvmAsm.Codegen.MptNodeKindSpec
