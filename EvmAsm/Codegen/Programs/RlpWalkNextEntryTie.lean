/-
  EvmAsm.Codegen.Programs.RlpWalkNextEntryTie

  Whole-routine contract for the `rlp_walk_next` THUNK (GH #12799,
  ownership-table row 3).

  ## The naming hazard this module exists to close

  Two nearly-identical names denote DIFFERENT routines:

  * `rlpWalkNext_prog`  (camelCase, `Codegen/Programs/RlpWalk.lean:105`) is the
    13-instruction thunk at `GuestAddrs.rlp_walk_next` (`0x80004cdc`, 52 B).
  * `rlp_walk_next_prog` (snake_case, `Rv64/RLP/WalkNext.lean`) is the
    103-instruction CORE at `GuestAddrs.rlp_walk_next_core` (`0x80004e34`,
    412 B); `rlp_walk_next_prog_length = 103`.

  The three registry rows labelled `routine "rlp_walk_next"` cite theorems over
  `rlp_walk_next_code base` — free base, and the CORE's program.  None of them
  says anything about the routine actually entered at
  `GuestAddrs.rlp_walk_next`, which is what the 19 `rlp_walk_next` call sites in
  `header_extended_decode` reach.

  ## The chain

  ```
  rlp_walk_next          0x80004cdc   52 B   13 insns  --jal--> rlp_walk_next_shared
    rlp_walk_next_shared 0x80004d10  208 B   52 insns  --jal--> rlp_walk_next_core
                                                       --jal--> rlp_validate_payload
      rlp_walk_next_core 0x80004e34  412 B  103 insns  (no callees)
  ```

  The thunk, read off the linked image (and matching `rlpWalkNext_prog`
  index-for-index):

  ```
  idx  0  addi sp,sp,-32        idx  7  jal  ra, rlp_walk_next_shared
  idx  1  sd   ra,0(sp)         idx  8  ld   s0,8(sp)
  idx  2  sd   s0,8(sp)         idx  9  ld   s1,16(sp)
  idx  3  sd   s1,16(sp)        idx 10  ld   ra,0(sp)
  idx  4  sub  t0,a1,a0         idx 11  addi sp,sp,32
  idx  5  slli s0,t0,1          idx 12  ret
  idx  6  li   s1,0
  ```

  It computes the recursion budget `s0 = 2 * (a1 - a0)`, zeroes `s1`, and does
  nothing else.  Every register pinned in the frame below is read off exactly
  one of those thirteen lines — see `entryPre`'s docstring for the line-by-line
  attribution.

  ## What is COMPOSED and what SURVIVES

  `rlp_walk_next_shared`'s contract
  (`RlpWalkNextStrictTie.rlp_walk_next_shared_nonlist_strict_spec_within`) is
  genuinely COMPOSED here, not assumed: it is applied as a term, and its own
  callee (`rlp_walk_next_core`) was already composed inside it.  Nothing in this
  module hypothesises a callee triple.

  What survives is that contract's INPUT-DOMAIN gate, which this module carries
  rather than discharges:

  * `hnotlist` — the prefix byte at the cursor is `< 0xc0`, i.e. the item is a
    byte string.  The LIST arms (the runs that enter `rlp_validate_payload`) are
    NOT covered.
  * the four readability premises `hoff`/`hover`/`hvalid`/`hss`/`hls`/`hll`,
    unchanged.

  ## The `s0 ≥ 2` translation — the substantive content of row 3

  `rlp_walk_next_shared_nonlist_strict_spec_within` gates on
  `hbudget : ¬ BitVec.ult budget 2`, a raw condition on the callee-saved
  register `s0` that a caller has no direct way to establish.  The thunk is
  exactly where that gate is translated, because idx 4/5 SET `s0`:

  ```
  s0 = (a1 - a0) <<< 1
  ```

  so `s0 ≥ 2` iff `a1 - a0 ≥ 1` (and the doubling does not wrap).  Both halves
  follow from two facts a caller already has about its own cursor/end pair:

  * `hlt  : BitVec.ult cursor endPtr = true` — the cursor is strictly before the
    end, i.e. `a1 - a0 ≥ 1`;
  * `hend : isValidByteAccess endPtr = true` — the end pointer is a guest
    address.  Together with `hvalid` (already a premise of the shared contract)
    this bounds both endpoints by `RAM_MEM_END = 0xc0000000`, so
    `a1 - a0 < 2 ^ 63` and `2 * (a1 - a0)` cannot wrap.

  ⇒ the machine-level gate `s0 ≥ 2` becomes the caller-level gate
  **"the end pointer is a valid guest byte address and the cursor is strictly
  before it"**.  `no_wrap_of_valid_span` below is the arithmetic bridge and
  `budget_ge_two` is the translation itself.
-/
import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie

namespace EvmAsm.Codegen.RlpWalkNextEntryTie

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-- Guest entry of the 13-instruction `rlp_walk_next` thunk (`0x80004cdc`). -/
abbrev T : Word := (GuestAddrs.rlp_walk_next : Word)

/-- The linked image of the thunk, anchored at its own `GuestAddrs` entry.
    Paired with `GuestAddrs.rlp_walk_next` in `guestImageEntries:212`. -/
abbrev entryCode : CodeReq := CodeReq.ofProg T rlpWalkNext_prog

/-- Thunk ∪ shared body ∪ lenient core: the three linked extents the call chain
    executes, and nothing else. -/
abbrev wholeCode : CodeReq := entryCode.union RlpWalkNextStrictTie.fullCode

theorem entry_length : rlpWalkNext_prog.length = 13 := rfl

/-! ## Code-requirement plumbing. -/

theorem entry_shared_disjoint :
    CodeReq.Disjoint entryCode RlpWalkNextStrictTie.sharedCode :=
  CodeReq.ofProg_disjoint_range_len T rlpWalkNext_prog 13
    RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52 entry_length (by decide) (by
      intro k1 k2 h1 h2 heq
      have hT : T.toNat = GuestAddrs.rlp_walk_next := by decide
      have hS : RlpWalkNextStrictTie.S.toNat = GuestAddrs.rlp_walk_next_shared := by decide
      simp only [GuestAddrs.rlp_walk_next, GuestAddrs.rlp_walk_next_shared] at hT hS
      have h := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hT, hS] at h
      omega)

theorem entry_core_disjoint :
    CodeReq.Disjoint entryCode RlpWalkNextStrictTie.coreCode :=
  CodeReq.ofProg_disjoint_range_len T rlpWalkNext_prog 13
    RlpWalkNextStrictTie.C rlpWalkNextCore_prog 103 entry_length (by decide) (by
      intro k1 k2 h1 h2 heq
      have hT : T.toNat = GuestAddrs.rlp_walk_next := by decide
      have hC : RlpWalkNextStrictTie.C.toNat = GuestAddrs.rlp_walk_next_core := by decide
      simp only [GuestAddrs.rlp_walk_next, GuestAddrs.rlp_walk_next_core] at hT hC
      have h := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hT, hC] at h
      omega)

theorem entry_full_disjoint :
    CodeReq.Disjoint entryCode RlpWalkNextStrictTie.fullCode :=
  CodeReq.Disjoint.union_right entry_shared_disjoint entry_core_disjoint

theorem entry_sub : ∀ a i, entryCode a = some i → wholeCode a = some i :=
  CodeReq.union_mono_left

theorem full_sub :
    ∀ a i, RlpWalkNextStrictTie.fullCode a = some i → wholeCode a = some i := by
  intro a i h
  rcases entry_full_disjoint a with h1 | h2
  · simp only [wholeCode, CodeReq.union, h1, h]
  · rw [h2] at h; exact absurd h (by simp)

/-! ## The `s0 ≥ 2` translation.

    `budget_ge_two` is the whole substance of ownership-table row 3: it turns
    the shared body's raw register gate into a condition on the caller's own
    cursor/end pair. -/

/-- Every guest byte address is bounded by `RAM_MEM_END`.  `isValidByteAccess`
    is `isValidMemAddr` with no alignment conjunct (`Rv64/Word.lean:151`), and
    all three admitted ranges end at or below `0xc0000000`. -/
theorem toNat_le_of_validByte {a : Word} (h : isValidByteAccess a = true) :
    a.toNat ≤ 0xc0000000 := by
  simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩
  · rw [show EvmAsm.Rv64.MEM_END = 0x78000000 from rfl] at h; omega
  · rw [show EvmAsm.Rv64.INPUT_MEM_END = 0x40002000 from rfl] at h; omega
  · rw [show EvmAsm.Rv64.RAM_MEM_END = 0xc0000000 from rfl] at h; omega

/-- `slli s0,t0,1` (idx 5) does not wrap: both endpoints are guest addresses, so
    their difference is below `2 ^ 63`. -/
theorem span_lt_two_pow_63 {cursor endPtr : Word}
    (hlt : BitVec.ult cursor endPtr = true)
    (hc : isValidByteAccess cursor = true) (he : isValidByteAccess endPtr = true) :
    (endPtr - cursor).toNat < 2 ^ 63 := by
  have hcb := toNat_le_of_validByte hc
  have heb := toNat_le_of_validByte he
  have hlt' : cursor.toNat < endPtr.toNat := by
    simpa [BitVec.ult, decide_eq_true_eq] using hlt
  have : (endPtr - cursor).toNat = endPtr.toNat - cursor.toNat := by
    rw [BitVec.toNat_sub]
    have : endPtr.toNat < 2 ^ 64 := endPtr.isLt
    have : cursor.toNat < 2 ^ 64 := cursor.isLt
    omega
  omega

/-- **The translation.**  `s0` after idx 4/5 is `(a1 - a0) <<< 1`; the shared
    body's `hbudget : ¬ BitVec.ult s0 2` therefore holds exactly when the
    cursor is strictly before the end pointer and both are guest addresses. -/
theorem budget_ge_two {cursor endPtr : Word}
    (hlt : BitVec.ult cursor endPtr = true)
    (hc : isValidByteAccess cursor = true) (he : isValidByteAccess endPtr = true) :
    ¬ BitVec.ult ((endPtr - cursor) <<< (1 : Nat)) (2 : Word) = true := by
  have hspan := span_lt_two_pow_63 hlt hc he
  have hcb := toNat_le_of_validByte hc
  have heb := toNat_le_of_validByte he
  have hlt' : cursor.toNat < endPtr.toNat := by
    simpa [BitVec.ult, decide_eq_true_eq] using hlt
  have hsub : (endPtr - cursor).toNat = endPtr.toNat - cursor.toNat := by
    rw [BitVec.toNat_sub]
    have h1 : endPtr.toNat < 2 ^ 64 := endPtr.isLt
    have h2 : cursor.toNat < 2 ^ 64 := cursor.isLt
    omega
  have hsl : ((endPtr - cursor) <<< (1 : Nat)).toNat = (endPtr - cursor).toNat * 2 % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt, hsl]
  have h2 : (2 : Word).toNat = 2 := by decide
  omega

end EvmAsm.Codegen.RlpWalkNextEntryTie
