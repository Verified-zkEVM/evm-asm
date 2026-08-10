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
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.MptNodeKindSpec

open EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- Guest-faithful kind discriminator (arity-exact). -/
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

/-- Under `MptNode.WF`, guest kind equals the structural tag. -/
theorem mptNodeKindGuest_eq_kindTag (n : MptNode) (hwf : n.WF) :
    mptNodeKindGuest n.rlp = n.kindTag := by
  have hdec := decodeFully_encode n.rlpItem (n.rlp_length_lt hwf)
  unfold mptNodeKindGuest
  rw [show n.rlp = encode n.rlpItem from rfl, hdec]
  cases n with
  | branch cs v =>
    obtain ⟨hcs, -, -⟩ := hwf
    show (if (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).length = 17 then (0 : Nat)
      else _) = 0
    rw [if_pos (by simp [hcs])]
  | leaf p v =>
    obtain ⟨hp, -, -⟩ := hwf
    obtain ⟨b0, tl, heq, hdiv⟩ := hpEncodeAux_head_div 2 (by omega) p hp
    show (if ([RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length = 17
        then (0 : Nat)
      else if ([RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length ≠ 2 then 3
      else match hpEncode true p with
        | [] => 3
        | b0 :: _ =>
          if b0.toNat / 16 < 2 then 1 else if b0.toNat / 16 < 4 then 2 else 3) = 2
    have hne17 : ¬ ([RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length = 17 := by
      simp
    have heq2 : ([RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length = 2 := by
      simp
    rw [if_neg hne17, if_neg (by simp [heq2])]
    rw [show hpEncode true p = hpEncodeAux 2 p from rfl, heq]
    show (if b0.toNat / 16 < 2 then (1 : Nat)
      else if b0.toNat / 16 < 4 then 2 else 3) = 2
    have hmod2 : p.length % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [if_neg (by omega), if_pos (by omega)]
  | extension p c =>
    obtain ⟨hp, -, -⟩ := hwf
    obtain ⟨b0, tl, heq, hdiv⟩ := hpEncodeAux_head_div 0 (by omega) p hp
    show (if ([RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length = 17
        then (0 : Nat)
      else if ([RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length ≠ 2 then 3
      else match hpEncode false p with
        | [] => 3
        | b0 :: _ =>
          if b0.toNat / 16 < 2 then 1 else if b0.toNat / 16 < 4 then 2 else 3) = 1
    have hne17 : ¬ ([RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length = 17 := by
      simp
    have heq2 : ([RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length = 2 := by
      simp
    rw [if_neg hne17, if_neg (by simp [heq2])]
    rw [show hpEncode false p = hpEncodeAux 0 p from rfl, heq]
    show (if b0.toNat / 16 < 2 then (1 : Nat)
      else if b0.toNat / 16 < 4 then 2 else 3) = 1
    have hmod2 : p.length % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [if_pos (by omega)]

/-- Pure `mptNodeKindSpec` agrees with guest on every well-formed node. -/
theorem mptNodeKindSpec_eq_guest_of_WF (n : MptNode) (hwf : n.WF) :
    mptNodeKindSpec n.rlp = mptNodeKindGuest n.rlp := by
  rw [mptNodeKindSpec_rlp n hwf, mptNodeKindGuest_eq_kindTag n hwf]

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

end EvmAsm.Codegen.MptNodeKindSpec
