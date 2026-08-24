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

/-! ## Straight-line blocks.

    `q` is the thunk's own frame base — the value of `sp` AFTER `addi sp,sp,-32`
    (idx 0).  The caller enters with `sp = q + 32`. -/

/-- `pcf` closes `P.pcFree` for the atoms used in this module. -/
local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

/-- Prologue (idx 0..3): open the 32-byte frame and spill `ra`/`s0`/`s1`.
    `addi sp,sp,-32` ⨾ `sd ra,0(sp)` ⨾ `sd s0,8(sp)` ⨾ `sd s1,16(sp)`. -/
theorem prologue_block (q raIn s0Old s1Old : Word) :
    cpsTripleWithin 4 T (T + 16) entryCode
      ((.x2 ↦ᵣ (q + 32)) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
       memOwn q ** memOwn (q + 8) ** memOwn (q + 16))
      ((.x2 ↦ᵣ q) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
       (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0Old) ** ((q + 16) ↦ₘ s1Old)) := by
  have h0 := addi_spec_gen_same_within .x2 (q + 32) (-32 : BitVec 12) T (by decide)
  rw [show (q + 32) + signExtend12 (-32 : BitVec 12) = q from by
        rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide]; bv_omega] at h0
  have h1 := sd_spec_gen_own_within .x2 .x1 q raIn (0 : BitVec 12) (T + 4)
  have h2 := sd_spec_gen_own_within .x2 .x8 q s0Old (8 : BitVec 12) (T + 8)
  have h3 := sd_spec_gen_own_within .x2 .x9 q s1Old (16 : BitVec 12) (T + 12)
  runBlock h0 h1 h2 h3

/-- Budget block (idx 4..6): `sub t0,a1,a0` ⨾ `slli s0,t0,1` ⨾ `li s1,0`.
    This is the only computation the thunk performs. -/
theorem budget_block (cursor endPtr t0Old s0v s1v : Word) :
    cpsTripleWithin 3 (T + 16) (T + 28) entryCode
      ((.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x5 ↦ᵣ t0Old) **
       (.x8 ↦ᵣ s0v) ** (.x9 ↦ᵣ s1v))
      ((.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x5 ↦ᵣ (endPtr - cursor)) **
       (.x8 ↦ᵣ ((endPtr - cursor) <<< (1 : BitVec 6).toNat)) ** (.x9 ↦ᵣ (0 : Word))) := by
  have h4 := sub_spec_gen_within .x5 .x11 .x10 endPtr cursor t0Old (T + 16) (by decide)
  have h5 := slli_spec_gen_within .x8 .x5 s0v (endPtr - cursor) (1 : BitVec 6) (T + 20) (by decide)
  have h6 := li_spec_gen_within .x9 s1v (0 : Word) (T + 24) (by decide)
  runBlock h4 h5 h6

/-- Epilogue (idx 8..12): reload `s0`/`s1`/`ra`, close the frame, `ret`. -/
theorem epilogue_block (q raIn s0Old s1Old w1 w8 w9 : Word) :
    cpsTripleWithin 5 (T + 32) (raIn &&& ~~~1) entryCode
      ((.x2 ↦ᵣ q) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x1 ↦ᵣ w1) **
       (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0Old) ** ((q + 16) ↦ₘ s1Old))
      ((.x2 ↦ᵣ (q + 32)) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x1 ↦ᵣ raIn) **
       (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0Old) ** ((q + 16) ↦ₘ s1Old)) := by
  have h8 := ld_spec_gen_within .x8 .x2 q w8 s0Old (8 : BitVec 12) (T + 32) (by decide)
  have h9 := ld_spec_gen_within .x9 .x2 q w9 s1Old (16 : BitVec 12) (T + 36) (by decide)
  have h10 := ld_spec_gen_within .x1 .x2 q w1 raIn (0 : BitVec 12) (T + 40) (by decide)
  have h11 := addi_spec_gen_same_within .x2 q (32 : BitVec 12) (T + 44) (by decide)
  rw [show q + signExtend12 (32 : BitVec 12) = q + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]] at h11
  have h12 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (T + 48)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show raIn + (0 : Word) = raIn from by bv_omega] at h12
  runBlock h8 h9 h10 h11 h12

/-! ## Call block (idx 7): `jal ra, rlp_walk_next_shared`.

    Mirrors `RlpWalkNextStrictTie.call_core`.  The callee code requirement is
    the shared body UNIONED WITH the lenient core, because the shared body's own
    contract already composes the core. -/

theorem singleton_disjoint_of_none {a : Word} {i : Instr} {cr : CodeReq} (h : cr a = none) :
    CodeReq.Disjoint (CodeReq.singleton a i) cr := by
  intro a'
  by_cases hb : (a' == a) = true
  · rw [beq_iff_eq] at hb; subst hb; right; exact h
  · left; simp [CodeReq.singleton, hb]

theorem shared_none_at_call :
    RlpWalkNextStrictTie.fullCode (T + 28) = none := by
  have hs : RlpWalkNextStrictTie.sharedCode (T + 28) = none :=
    CodeReq.ofProg_none_range_len RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52 (T + 28)
      (by decide) (by
        intro k hk heq
        have hT28 : (T + 28).toNat = GuestAddrs.rlp_walk_next + 28 := by decide
        have hS : RlpWalkNextStrictTie.S.toNat = GuestAddrs.rlp_walk_next_shared := by decide
        simp only [GuestAddrs.rlp_walk_next, GuestAddrs.rlp_walk_next_shared] at hT28 hS
        have h := congrArg BitVec.toNat heq
        rw [hT28] at h
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hS] at h
        omega)
  have hc : RlpWalkNextStrictTie.coreCode (T + 28) = none :=
    CodeReq.ofProg_none_range_len RlpWalkNextStrictTie.C rlpWalkNextCore_prog 103 (T + 28)
      (by decide) (by
        intro k hk heq
        have hT28 : (T + 28).toNat = GuestAddrs.rlp_walk_next + 28 := by decide
        have hC : RlpWalkNextStrictTie.C.toNat = GuestAddrs.rlp_walk_next_core := by decide
        simp only [GuestAddrs.rlp_walk_next, GuestAddrs.rlp_walk_next_core] at hT28 hC
        have h := congrArg BitVec.toNat heq
        rw [hT28] at h
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hC] at h
        omega)
  simp only [RlpWalkNextStrictTie.fullCode, CodeReq.union, hs, hc]

theorem call_shared {n : Nat} {Prest Q : Assertion} (oldRa : Word)
    (h_pre : Prest.pcFree)
    (h_callee : cpsTripleWithin n RlpWalkNextStrictTie.S ((T + 32) &&& ~~~(1 : Word))
      RlpWalkNextStrictTie.fullCode ((.x1 ↦ᵣ (T + 32)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (T + 28) (T + 32) wholeCode ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  rw [show (T + 32 : Word) = T + 28 + 4 from by bv_omega] at h_callee ⊢
  have h_call := cpsCallWithin
    (nSteps := n) (callerPC := T + 28) (calleeEntry := RlpWalkNextStrictTie.S) (vOld := oldRa)
    (calleeCode := RlpWalkNextStrictTie.fullCode) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next_shared (GuestAddrs.rlp_walk_next + 28))
    (by decide) (by decide) h_pre
    (singleton_disjoint_of_none shared_none_at_call)
    h_callee
  refine cpsTripleWithin_extend_code (CodeReq.union_split_mono ?_ full_sub) h_call
  exact fun a i h_code => entry_sub a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr T rlpWalkNext_prog 7 (T + 28)
      (by rw [entry_length]; norm_num) (by rw [entry_length]; norm_num) (by bv_omega))
      a i h_code)

/-! ## `regOwn` variants of the two blocks that meet the shared body's frame. -/

/-- After `li s1,0` the machine holds `x9 = 0`; the shared body only asks to OWN
    `x9`, so weaken the post accordingly. -/
theorem budget_block_own (cursor endPtr t0Old s0v s1v : Word) :
    cpsTripleWithin 3 (T + 16) (T + 28) entryCode
      ((.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x5 ↦ᵣ t0Old) **
       (.x8 ↦ᵣ s0v) ** (.x9 ↦ᵣ s1v))
      ((.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x5 ↦ᵣ (endPtr - cursor)) **
       (.x8 ↦ᵣ ((endPtr - cursor) <<< (1 : BitVec 6).toNat)) ** regOwn .x9) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (regIs_implies_regOwn .x9)))) h hq)
    (budget_block cursor endPtr t0Old s0v s1v)

/-- The shared body returns `x8`/`x9` merely OWNED (it clobbers both), which is
    all the epilogue's two `ld`s need. -/
theorem epilogue_block_own (q raIn s0Old s1Old w1 : Word) :
    cpsTripleWithin 5 (T + 32) (raIn &&& ~~~1) entryCode
      ((.x2 ↦ᵣ q) ** (.x1 ↦ᵣ w1) **
       (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0Old) ** ((q + 16) ↦ₘ s1Old) **
       regOwn .x8 ** regOwn .x9)
      ((.x2 ↦ᵣ (q + 32)) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x1 ↦ᵣ raIn) **
       (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0Old) ** ((q + 16) ↦ₘ s1Old)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x2 ↦ᵣ q) ** (.x1 ↦ᵣ w1) **
        (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0Old) ** ((q + 16) ↦ₘ s1Old) ** regOwn .x8)
      (r := .x9) (fun w9 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x2 ↦ᵣ q) ** (.x1 ↦ᵣ w1) **
        (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0Old) ** ((q + 16) ↦ₘ s1Old) ** (.x9 ↦ᵣ w9))
      (r := .x8) (fun w8 => ?_))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (epilogue_block q raIn s0Old s1Old w1 w8 w9)

/-! ## The thunk's postcondition. -/

/-- Post of the thunk contract.  `a0/st/a2` are the wrapper's three return
    registers, exactly as `RlpWalkNextStrictTie.sharedPost` reports them.  The
    thunk restores `sp`, `ra`, `s0` and `s1` from its own 32-byte frame
    (`sp+64 .. sp+80`) and leaves everything else as the shared body left it.

    On an accepting run (`st = 0`) the post carries the STRICT wrapper relation
    `rlpItemDecodeStrictW`, inherited unchanged from the shared body. -/
def entryPost (sp raIn s0Old s1Old srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff floor : Nat) : Assertion := fun h => ∃ a0 st a2 : Word,
  ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
   (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
   regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
   regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
   (sp ↦ₘ (T + 32)) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
   ((sp + 16) ↦ₘ endPtr) **
   ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ st) ** ((sp + 40) ↦ₘ a2) **
   ((sp + 64) ↦ₘ raIn) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old) **
   bytesRegion srcBase srcBytes) h ∧
  ((st = 0 ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
      (endPtr - srcBase).toNat a2 floor) ∨ st ≠ 0)

/-- The epilogue consuming the shared body's existential post.  This is the only
    place the thunk touches `sharedPost`'s internal shape; the three cells
    `sp+64 / sp+72 / sp+80` are the thunk's OWN frame, framed around the call and
    untouched by the shared body. -/
theorem epilogue_from_sharedPost (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat) :
    cpsTripleWithin 5 (T + 32) (raIn &&& ~~~1) entryCode
      (RlpWalkNextStrictTie.sharedPost sp (T + 32) srcBase endPtr srcBytes srcOff floor **
        (((sp + 64) ↦ₘ raIn) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old)))
      (entryPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
  have hepi := epilogue_block_own (sp + 64) raIn s0Old s1Old (T + 32)
  rw [show (sp + 64 : Word) + 8 = sp + 72 from by bv_omega,
      show (sp + 64 : Word) + 16 = sp + 80 from by bv_omega,
      show (sp + 64 : Word) + 32 = sp + 96 from by bv_omega] at hepi
  have key : ∀ a0 st a2 : Word,
      ((st = (0 : Word) ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
          (endPtr - srcBase).toNat a2 floor) ∨ st ≠ (0 : Word)) →
      cpsTripleWithin 5 (T + 32) (raIn &&& ~~~1) entryCode
        (((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ (T + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 **
          regOwn .x9 ** regOwn .x13 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (sp ↦ₘ (T + 32)) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((sp + 16) ↦ₘ endPtr) **
          ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ st) ** ((sp + 40) ↦ₘ a2) **
          bytesRegion srcBase srcBytes) **
         (((sp + 64) ↦ₘ raIn) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old)))
        (entryPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
    intro a0 st a2 hpure
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         (sp ↦ₘ (T + 32)) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
         ((sp + 16) ↦ₘ endPtr) **
         ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ st) ** ((sp + 40) ↦ₘ a2) **
         bytesRegion srcBase srcBytes) (by pcf) hepi)
    exact ⟨a0, st, a2, by xperm_hyp hq, hpure⟩
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, g1, g2, hd, hu, hP, hR2⟩ := hPR
  obtain ⟨f1, f2, fd, fu, hSP, hFr⟩ := hP
  obtain ⟨a0, st, a2, hBIG, hpure⟩ := hSP
  exact key a0 st a2 hpure R hR s hcr
    ⟨hp, hcompat, g1, g2, hd, hu, ⟨f1, f2, fd, fu, hBIG, hFr⟩, hR2⟩ hpc

/-! ## The whole-routine contract at `GuestAddrs.rlp_walk_next`.

    ⚠️ TIER: `.conditional`.  The gate is inherited from
    `RlpWalkNextStrictTie.rlp_walk_next_shared_nonlist_strict_spec_within` and
    is NOT discharged here: the prefix byte at the cursor must be `< 0xc0`
    (byte-string items only).  The LIST arms — the runs that enter
    `rlp_validate_payload` — are not covered.

    What IS discharged here is the shared body's OTHER gate, `s0 ≥ 2`.  See
    `budget_ge_two`. -/

/-- **Whole-routine machine triple for the `rlp_walk_next` THUNK**, entered at
    `GuestAddrs.rlp_walk_next` over the linked image `rlpWalkNext_prog`, unioned
    with the shared body and the lenient core it calls.

    Frame, with the disassembly line each register is read from:

    | reg   | role                        | read from            |
    |-------|-----------------------------|----------------------|
    | `x2`  | stack pointer, `sp + 96` in | idx 0 `addi sp,sp,-32`, idx 11 `addi sp,sp,32` |
    | `x1`  | caller return address       | idx 1 `sd ra,0(sp)`, idx 10 `ld ra,0(sp)`, idx 12 `ret` |
    | `x8`  | callee-saved `s0`, spilled  | idx 2 `sd s0,8(sp)`, idx 5 `slli s0,t0,1`, idx 8 `ld s0,8(sp)` |
    | `x9`  | callee-saved `s1`, spilled  | idx 3 `sd s1,16(sp)`, idx 6 `li s1,0`, idx 9 `ld s1,16(sp)` |
    | `x10` | `a0`, item cursor           | idx 4 `sub t0,a1,a0` |
    | `x11` | `a1`, end pointer           | idx 4 `sub t0,a1,a0` |
    | `x5`  | `t0`, scratch               | idx 4 `sub t0,a1,a0`, idx 5 `slli s0,t0,1` |

    `x12`, `x6`, `x7`, `x13` and `x28..x31` appear only because the CALLEE
    (`rlp_walk_next_shared`) requires or clobbers them; no thunk instruction
    mentions them, and none is pinned to a value the thunk does not set.

    Frame layout: `sp` is the SHARED body's frame base.  The caller enters with
    `x2 = sp + 96`; the thunk's own 32-byte frame is `sp+64 .. sp+88` (`ra` at
    `sp+64`, `s0` at `sp+72`, `s1` at `sp+80`), and the shared body's 64-byte
    frame is `sp .. sp+56`.  The two are disjoint by construction.

    Step bound `122 = 8 (thunk prologue + budget + jal) + 109 (shared body)
    + 5 (thunk epilogue)`. -/
theorem rlp_walk_next_entry_nonlist_strict_spec_within
    (sp raIn s0Old s1Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true →
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)) = (1 : Word) →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    -- The `s0 ≥ 2` gate, translated: the end pointer is a guest byte address
    -- and the cursor is strictly before it, i.e. `a1 - a0 ≥ 1`.
    (hend : isValidByteAccess endPtr = true)
    (hlt : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 122 T (raIn &&& ~~~1) wholeCode
      ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ a2Old) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x13 **
       (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       memOwn (sp + 64) ** memOwn (sp + 72) ** memOwn (sp + 80) **
       bytesRegion srcBase srcBytes)
      (entryPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
  -- idx 0..3: open the thunk frame and spill ra/s0/s1.
  have hpro0 := prologue_block (sp + 64) raIn s0Old s1Old
  rw [show (sp + 64 : Word) + 32 = sp + 96 from by bv_omega,
      show (sp + 64 : Word) + 8 = sp + 72 from by bv_omega,
      show (sp + 64 : Word) + 16 = sp + 80 from by bv_omega] at hpro0
  have hpro := cpsTripleWithin_extend_code entry_sub
    (cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x13 **
       (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       bytesRegion srcBase srcBytes) (by pcf) hpro0)
  -- idx 4..6: compute the recursion budget.
  have hbud := cpsTripleWithin_extend_code entry_sub
    (cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) **
       (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x13 **
       (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       ((sp + 64) ↦ₘ raIn) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old) **
       bytesRegion srcBase srcBytes) (by pcf)
      (budget_block_own (srcBase + BitVec.ofNat 64 srcOff) endPtr t0Old s0Old s1Old))
  -- idx 7: the shared body's contract, COMPOSED (not assumed).
  have hwn := RlpWalkNextStrictTie.rlp_walk_next_shared_nonlist_strict_spec_within
    sp (T + 32) srcBase endPtr
    ((endPtr - (srcBase + BitVec.ofNat 64 srcOff)) <<< (1 : BitVec 6).toNat)
    a2Old (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) t1Old t2Old
    t3Old t4Old t5Old t6Old srcBytes srcOff floor hsalign hoff hover hvalid hss hls hll
    (budget_ge_two hlt hvalid hend) hnotlist
  have hwnF := cpsTripleWithin_frameR
    (((sp + 64) ↦ₘ raIn) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old)) (by pcf) hwn
  have hwn' := cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hwnF
    (P' := (.x1 ↦ᵣ (T + 32)) **
      ((.x2 ↦ᵣ (sp + 64)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x8 ↦ᵣ ((endPtr - (srcBase + BitVec.ofNat 64 srcOff)) <<< (1 : BitVec 6).toNat)) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ a2Old) **
       (.x5 ↦ᵣ (endPtr - (srcBase + BitVec.ofNat 64 srcOff))) **
       (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x9 ** regOwn .x13 **
       (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       bytesRegion srcBase srcBytes **
       ((sp + 64) ↦ₘ raIn) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old)))
  have hcall := call_shared raIn (by pcf) hwn'
  -- idx 8..12: restore and return.
  have hepi := cpsTripleWithin_extend_code entry_sub
    (epilogue_from_sharedPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro hbud
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hcall
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hepi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) c3)

end EvmAsm.Codegen.RlpWalkNextEntryTie
