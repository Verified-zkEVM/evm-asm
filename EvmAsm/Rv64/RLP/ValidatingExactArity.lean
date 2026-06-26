/-
  EvmAsm.Rv64.RLP.ValidatingExactArity

  Exact-arity end check for the fixed-schema untrusted RLP decoders (#9373). After a single-pass
  field walk over a list's payload, the cursor `x13` must land *exactly* on the list's end pointer:
  if it is short, the list had fewer fields than the schema; if the walk somehow over-ran (or the
  list claimed more bytes than the fields consume) the cursor misses the end. This is the issue's
  core "abort on the wrong number of elements / trailing bytes" — `withdrawal_decode` (exactly 4
  fields), `header_minimal_decode`, and the tx decoders all need it.

  `rlp_exact_arity_check` is a single `BNE x13, rEnd, fail`: the cursor `x13 = regionBase + cursor`
  and the saved list-end pointer `rEnd = regionBase + listEnd` are compared; equal (fall-through) ⇒
  SUCCESS with `⌜cursor = listEnd⌝`, unequal (taken) ⇒ FAIL with `⌜cursor ≠ listEnd⌝`. The pointer
  comparison is reflected to the underlying byte offsets via `ptr_eq_iff_ofNat`.
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- Two region pointers are equal iff their byte offsets are (for in-range offsets): the `regionBase`
    base cancels. -/
theorem ptr_eq_iff_ofNat (regionBase : Word) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (regionBase + BitVec.ofNat 64 a = regionBase + BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h
    have h2 : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by bv_omega
    have h3 := congrArg BitVec.toNat h2
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h3
    exact h3
  · intro h; rw [h]

/-- **Exact-arity end check**: `BNE x13, rEnd, fail`. With the cursor `x13 = regionBase + cursor` and
    the saved list-end pointer `rEnd = regionBase + listEnd`, the fall-through (SUCCESS) exit carries
    `⌜cursor = listEnd⌝` (the walk consumed the list exactly) and the taken (FAIL) exit carries
    `⌜cursor ≠ listEnd⌝` (wrong element count / trailing bytes). -/
theorem rlp_exact_arity_check (b regionBase : Word) (rEnd : Reg) (cursor listEnd : Nat)
    (failOff : BitVec 13) (hc : cursor < 2 ^ 64) (hl : listEnd < 2 ^ 64) :
    cpsBranchWithin 1 b (CodeReq.singleton b (.BNE .x13 rEnd failOff))
      ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 cursor)) **
       (rEnd ↦ᵣ (regionBase + BitVec.ofNat 64 listEnd)))
      -- FAIL (taken): cursor ≠ list end.
      (b + signExtend13 failOff)
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 cursor)) **
         (rEnd ↦ᵣ (regionBase + BitVec.ofNat 64 listEnd)) ** ⌜cursor ≠ listEnd⌝)
      -- SUCCESS (fall): cursor = list end (exact arity).
      (b + 4)
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 cursor)) **
         (rEnd ↦ᵣ (regionBase + BitVec.ofNat 64 listEnd)) ** ⌜cursor = listEnd⌝) := by
  have raw := bne_spec_gen_within .x13 rEnd failOff
    (regionBase + BitVec.ofNat 64 cursor) (regionBase + BitVec.ofNat 64 listEnd) b
  refine cpsBranchWithin_weaken (fun _ hp => hp) ?taken ?fall raw
  case taken =>
    intro h hp
    rw [show ((regionBase + BitVec.ofNat 64 cursor ≠ regionBase + BitVec.ofNat 64 listEnd))
          = (cursor ≠ listEnd) from by
        rw [ne_eq, ne_eq, ptr_eq_iff_ofNat regionBase cursor listEnd hc hl]] at hp
    exact hp
  case fall =>
    intro h hp
    rw [show ((regionBase + BitVec.ofNat 64 cursor = regionBase + BitVec.ofNat 64 listEnd))
          = (cursor = listEnd) from propext (ptr_eq_iff_ofNat regionBase cursor listEnd hc hl)] at hp
    exact hp

end EvmAsm.Rv64.RLP
