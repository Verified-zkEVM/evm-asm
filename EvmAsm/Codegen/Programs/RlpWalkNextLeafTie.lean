/-
  EvmAsm.Codegen.Programs.RlpWalkNextLeafTie

  Whole-routine contract for `rlp_walk_next_leaf` (GH #12799, ownership-table
  row 4).

  ## Extent, derived from the linked image

  `nm gen-out/regionmap/stateless_guest.elf`, sorted, next symbol as `hi`:

  ```
  000000008000bb28 t rlp_walk_next_leaf
  000000008000bb64 t header_extended_decode        <- next symbol = hi
  ```

  `hi - lo = 0x3c = 60` bytes, and `rlpWalkNextLeaf_prog.length * 4 = 15 * 4 = 60`.
  Cross-check ✅ (`leaf_length` below is the kernel-checked half).

  ## The routine, index-for-index against the linked image

  ```
  idx  0  addi sp,sp,-32          idx  8  lbu  t2,0(t0)
  idx  1  sd   ra,0(sp)           idx  9  li   t3,192
  idx  2  sd   a0,8(sp)           idx 10  bltu t2,t3,+8   -> idx 12
  idx  3  jal  ra, rlp_walk_next  idx 11  li   a1,8
  idx  4  bne  a1,zero,+32 -> 12  idx 12  ld   ra,0(sp)
  idx  5  sub  t0,a0,a2           idx 13  addi sp,sp,32
  idx  6  ld   t1,8(sp)           idx 14  ret
  idx  7  bne  t0,t1,+20  -> 12
  ```

  It saves the ENTRY cursor at `sp+8` (idx 2), calls the walker, and then
  reports status `8` exactly when the walker succeeded, the reported length `a2`
  spans back from the new cursor `a0` to the entry cursor, and the byte there is
  a LIST prefix (`≥ 0xc0`).  Under the RLP ABI the walker reports the content
  length for strings and the full span for lists, so `a0 - a2 = entry cursor`
  holds for lists and for single-byte items; the prefix test at idx 10
  disambiguates those two.

  ## ⭐ Does the idx-10 prefix test DISCHARGE row 3's non-LIST gate?

  **No — the gate is INHERITED, unchanged, and this module carries it.**  Three
  independent reasons, in increasing order of how much they settle the question:

  1. **Ordering.**  `cpsTripleWithin` composition is sequential: the callee's
     precondition must hold in the state at the CALL.  The `jal` is idx 3 and
     the `bltu` is idx 10, so at the moment row 3's contract is applied its
     `hnotlist` premise is simply not available — there is nothing yet to
     discharge it with.  A test that runs after the callee has already executed
     cannot restrict the callee's input domain.

  2. **Different subject.**  Even ignoring the ordering, the two predicates are
     not the same predicate.  Row 3's `hnotlist` is about `srcBytes[srcOff]`,
     the byte at the INPUT cursor.  Idx 10 tests the byte at `t0 = a0 - a2`, an
     address computed from the callee's OUTPUT registers.  The two addresses
     coincide only on the idx-7 fall-through, and that they coincide there is a
     fact about the walker's post — which one only has after assuming the
     walker's precondition.  Discharging the gate this way would be circular.

  3. **Consequence: under the inherited gate the status-8 arm is DEAD.**  This
     is the sharp form of the answer.  If `hnotlist` holds, then on the only
     path that reaches idx 10 we have `t0 = entry cursor` (idx 7 fell through),
     so `lbu t2,0(t0)` loads exactly `srcBytes[srcOff]`, and `hnotlist` says
     that byte is `< 0xc0` — so `bltu t2,t3` is ALWAYS taken and idx 11
     (`li a1,8`) never executes.  `prefix_test_always_taken` is that proof.

  ⇒ composing row 3 here does not weaken its gate; it makes the wrapper's own
  LIST rejection unreachable.  Under the gate this routine is
  **status-transparent**: the `a1` it returns is exactly the `a1` the walker
  returned, never the wrapper's `8`.  Covering the status-8 arm needs the LIST
  arms of the walker, i.e. exactly what row 3 does not cover.

  ## What is COMPOSED and what SURVIVES

  `RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within` is
  genuinely COMPOSED here, applied as a term — not hypothesised.  Its own callee
  chain (`rlp_walk_next_shared` → `rlp_walk_next_core`) was already composed
  inside it.  Nothing in this module hypothesises a callee triple.

  Surviving premises, carried verbatim into this module's statement:
  `hsalign`, `hoff`, `hover`, `hvalid`, `hss`, `hls`, `hll`, `hend`, `hlt`,
  and the non-LIST gate `hnotlist`.  ⚠️ TIER: `.conditional` on `hnotlist`.

  ## Frame

  | reg   | role                              | read from |
  |-------|-----------------------------------|-----------|
  | `x2`  | stack pointer, `sp + 128` in      | idx 0 `addi sp,sp,-32`, idx 13 `addi sp,sp,32` |
  | `x1`  | caller return address             | idx 1 `sd ra,0(sp)`, idx 12 `ld ra,0(sp)`, idx 14 `ret` |
  | `x10` | `a0`, item cursor in / next out   | idx 2 `sd a0,8(sp)`, idx 5 `sub t0,a0,a2` |
  | `x11` | `a1`, walker status               | idx 4 `bne a1,zero`, idx 11 `li a1,8` |
  | `x12` | `a2`, reported length             | idx 5 `sub t0,a0,a2` |
  | `x5`  | `t0`, recomputed item start       | idx 5, idx 7 `bne t0,t1`, idx 8 `lbu t2,0(t0)` |
  | `x6`  | `t1`, reloaded entry cursor       | idx 6 `ld t1,8(sp)`, idx 7 |
  | `x7`  | `t2`, prefix byte                 | idx 8 `lbu t2,0(t0)`, idx 10 `bltu t2,t3` |
  | `x28` | `t3`, the constant `192`          | idx 9 `li t3,192`, idx 10 |

  `x0`, `x8`, `x9`, `x13`, `x29`, `x30`, `x31` appear only because the CALLEE
  requires or clobbers them; no instruction of this routine mentions them.  They
  are pinned in `P` and `Q` precisely because `cpsTripleWithin` quantifies over
  all frames.

  Frame layout: `sp` is the walker's own frame base, as in row 3.  The walker
  needs `x2 = sp + 96` at its entry, which is this routine's frame base after
  idx 0, so the caller enters here with `x2 = sp + 128`.  This routine's own
  32-byte frame is `sp+96 .. sp+120` (`ra` at `sp+96`, the entry cursor at
  `sp+104`); the walker's cells are `sp .. sp+40` and `sp+64 .. sp+80`.  The two
  are disjoint by construction.

  Step bound `136 = 3 (prologue) + 1 + 122 (jal + walker) + 10 (longest tail:
  idx 4,5,6,7,8,9,10 then the three-instruction epilogue)`.
-/
import EvmAsm.Codegen.Programs.RlpWalkNextEntryTie
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Codegen.RlpWalkNextLeafTie

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-- Guest entry of the 15-instruction `rlp_walk_next_leaf` routine
    (`GuestAddrs.rlp_walk_next_leaf = 0x8000bb28`). -/
abbrev L : Word := (GuestAddrs.rlp_walk_next_leaf : Word)

/-- The linked image of the wrapper, anchored at its own `GuestAddrs` entry.
    Paired with `GuestAddrs.rlp_walk_next_leaf` in `guestImageEntries:268`. -/
abbrev leafCode : CodeReq := CodeReq.ofProg L rlpWalkNextLeaf_prog

/-- Wrapper ∪ (thunk ∪ shared body ∪ lenient core): the four linked extents the
    call chain executes, and nothing else. -/
abbrev wholeCode : CodeReq := leafCode.union RlpWalkNextEntryTie.wholeCode

/-- Kernel-checked half of the extent cross-check: `15 * 4 = 60 = 0x8000bb64 -
    0x8000bb28`. -/
theorem leaf_length : rlpWalkNextLeaf_prog.length = 15 := rfl

/-! ## Code-requirement plumbing. -/

private theorem leaf_disjoint_ofProg (base2 : Word) (prog2 : List Instr) (n2 : Nat)
    (hlen2 : prog2.length = n2) (b2 : Nat) (hb2 : base2.toNat = b2)
    (hn2 : 4 * n2 ≤ 0x8000bb28 - b2 ∨ 0x8000bb28 + 60 ≤ b2) (hsmall : b2 + 4 * n2 < 2 ^ 64) :
    CodeReq.Disjoint leafCode (CodeReq.ofProg base2 prog2) :=
  CodeReq.ofProg_disjoint_range_len L rlpWalkNextLeaf_prog 15 base2 prog2 n2
    leaf_length hlen2 (by
      intro k1 k2 h1 h2 heq
      have hL : L.toNat = GuestAddrs.rlp_walk_next_leaf := by decide
      simp only [GuestAddrs.rlp_walk_next_leaf] at hL
      have h := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hL, hb2] at h
      omega)

theorem leaf_entry_disjoint :
    CodeReq.Disjoint leafCode RlpWalkNextEntryTie.entryCode :=
  leaf_disjoint_ofProg RlpWalkNextEntryTie.T rlpWalkNext_prog 13
    RlpWalkNextEntryTie.entry_length 0x80004cdc (by decide) (by norm_num) (by norm_num)

theorem leaf_shared_disjoint :
    CodeReq.Disjoint leafCode RlpWalkNextStrictTie.sharedCode :=
  leaf_disjoint_ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52
    (by rfl) 0x80004d10 (by decide) (by norm_num) (by norm_num)

theorem leaf_core_disjoint :
    CodeReq.Disjoint leafCode RlpWalkNextStrictTie.coreCode :=
  leaf_disjoint_ofProg RlpWalkNextStrictTie.C rlpWalkNextCore_prog 103
    (by rfl) 0x80004e34 (by decide) (by norm_num) (by norm_num)

theorem leaf_walk_disjoint :
    CodeReq.Disjoint leafCode RlpWalkNextEntryTie.wholeCode :=
  CodeReq.Disjoint.union_right leaf_entry_disjoint
    (CodeReq.Disjoint.union_right leaf_shared_disjoint leaf_core_disjoint)

theorem leaf_sub : ∀ a i, leafCode a = some i → wholeCode a = some i :=
  CodeReq.union_mono_left

theorem walk_sub :
    ∀ a i, RlpWalkNextEntryTie.wholeCode a = some i → wholeCode a = some i := by
  intro a i h
  rcases leaf_walk_disjoint a with h1 | h2
  · simp only [wholeCode, CodeReq.union, h1, h]
  · rw [h2] at h; exact absurd h (by simp)

/-! ## Address arithmetic for the three branch targets and the call. -/

private theorem se13_32 : signExtend13 (32 : BitVec 13) = (32 : Word) := by decide
private theorem se13_20 : signExtend13 (20 : BitVec 13) = (20 : Word) := by decide
private theorem se13_8 : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide

private theorem br1_target : (L + 16) + signExtend13 (32 : BitVec 13) = L + 48 := by
  rw [se13_32]; bv_omega
private theorem br2_target : (L + 28) + signExtend13 (20 : BitVec 13) = L + 48 := by
  rw [se13_20]; bv_omega
private theorem br3_target : (L + 40) + signExtend13 (8 : BitVec 13) = L + 48 := by
  rw [se13_8]; bv_omega

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

/-! ## The frame carried across the whole tail.

    `frameCore` is everything the tail neither reads nor writes, plus the two
    argument/result registers.  The four scratch registers `x5`/`x6`/`x7`/`x28`
    are kept OUTSIDE it because the tail cycles them between `regOwn` (as the
    callee returns them) and `regIs` (as each instruction spec needs them). -/
abbrev frameCore (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (a0 st a2 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
  (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
  regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (sp ↦ₘ (RlpWalkNextEntryTie.T + 32)) **
  ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
  ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ st) ** ((sp + 40) ↦ₘ a2) **
  ((sp + 64) ↦ₘ (L + 16)) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old) **
  ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
  bytesRegion srcBase srcBytes

/-- State at the epilogue entry `L + 48`, uniform across all three paths that
    reach it: the four scratch registers are merely OWNED, because path A leaves
    them untouched while paths B and C overwrite some of them. -/
abbrev epiPre (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (a0 st a2 : Word) : Assertion :=
  (.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
  frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28

/-- Post of the whole-routine contract.  `a0/st/a2` are the walker's three
    return registers, passed through unchanged — see the module docstring for
    why the wrapper's own status `8` is unreachable under `hnotlist`. -/
def leafPost (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat) : Assertion := fun h =>
  ∃ a0 st a2 : Word,
  ((.x2 ↦ᵣ (sp + 128)) ** (.x1 ↦ᵣ raIn) **
   frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
   regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) h ∧
  ((st = 0 ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
      (endPtr - srcBase).toNat a2 floor) ∨ st ≠ 0)

/-! ## Straight-line blocks. -/

/-- Prologue (idx 0..2): open the 32-byte frame, spill `ra`, and save the ENTRY
    cursor at `sp+8` of the new frame — the value idx 6 reloads. -/
theorem prologue_block (q raIn cursor : Word) :
    cpsTripleWithin 3 L (L + 12) leafCode
      ((.x2 ↦ᵣ (q + 32)) ** (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ cursor) **
       memOwn q ** memOwn (q + 8))
      ((.x2 ↦ᵣ q) ** (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ cursor) **
       (q ↦ₘ raIn) ** ((q + 8) ↦ₘ cursor)) := by
  have h0 := addi_spec_gen_same_within .x2 (q + 32) (-32 : BitVec 12) L (by decide)
  rw [show (q + 32) + signExtend12 (-32 : BitVec 12) = q from by
        rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide]; bv_omega] at h0
  have h1 := sd_spec_gen_own_within .x2 .x1 q raIn (0 : BitVec 12) (L + 4)
  have h2 := sd_spec_gen_own_within .x2 .x10 q cursor (8 : BitVec 12) (L + 8)
  runBlock h0 h1 h2

/-- Recompute block (idx 5..6): `sub t0,a0,a2` ⨾ `ld t1,8(sp)`.  `t0` is the
    item start implied by the walker's outputs; `t1` is the saved entry cursor. -/
theorem recompute_block (q a0 a2 cursor v5 v6 : Word) :
    cpsTripleWithin 2 (L + 20) (L + 28) leafCode
      ((.x2 ↦ᵣ q) ** (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       ((q + 8) ↦ₘ cursor))
      ((.x2 ↦ᵣ q) ** (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (a0 - a2)) **
       (.x6 ↦ᵣ cursor) ** ((q + 8) ↦ₘ cursor)) := by
  have h5 := sub_spec_gen_within .x5 .x10 .x12 a0 a2 v5 (L + 20) (by decide)
  have h6 := ld_spec_gen_within .x6 .x2 q v6 cursor (8 : BitVec 12) (L + 24) (by decide)
  runBlock h5 h6

/-- Prefix-load block (idx 8..9): `lbu t2,0(t0)` ⨾ `li t3,192`.  The load is the
    keystone: `t0` is the entry cursor on this path, so the byte read is
    `srcBytes[srcOff]` — the very byte `hnotlist` constrains. -/
theorem prefix_block (srcBase v7 v28 : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin 2 (L + 32) (L + 40) leafCode
      ((.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x7 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) ** (.x28 ↦ᵣ (192 : Word)) **
       bytesRegion srcBase srcBytes) := by
  have h8 := bytesRegion_lbu_within .x7 .x5 srcBase v7 (L + 32) srcBytes srcOff
    (by decide) hsalign hoff hover hvalid
  have h9 := li_spec_gen_within .x28 v28 (192 : Word) (L + 36) (by decide)
  runBlock h8 h9

/-- Epilogue (idx 12..14): reload `ra`, close the frame, `ret`. -/
theorem epilogue_block (q raIn w1 : Word) :
    cpsTripleWithin 3 (L + 48) (raIn &&& ~~~1) leafCode
      ((.x2 ↦ᵣ q) ** (.x1 ↦ᵣ w1) ** (q ↦ₘ raIn))
      ((.x2 ↦ᵣ (q + 32)) ** (.x1 ↦ᵣ raIn) ** (q ↦ₘ raIn)) := by
  have h12 := ld_spec_gen_within .x1 .x2 q w1 raIn (0 : BitVec 12) (L + 48) (by decide)
  have h13 := addi_spec_gen_same_within .x2 q (32 : BitVec 12) (L + 52) (by decide)
  rw [show q + signExtend12 (32 : BitVec 12) = q + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]] at h13
  have h14 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (L + 56)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show raIn + (0 : Word) = raIn from by bv_omega] at h14
  runBlock h12 h13 h14

/-! ## Call block (idx 3): `jal ra, rlp_walk_next`. -/

private theorem singleton_disjoint_of_none {a : Word} {i : Instr} {cr : CodeReq}
    (h : cr a = none) : CodeReq.Disjoint (CodeReq.singleton a i) cr := by
  intro a'
  by_cases hb : (a' == a) = true
  · rw [beq_iff_eq] at hb; subst hb; right; exact h
  · left; simp [CodeReq.singleton, hb]

private theorem walk_none_at (b : Word) (prog : List Instr) (n : Nat)
    (hlen : prog.length = n) (bn : Nat) (hb : b.toNat = bn)
    (hgap : ∀ k, k < n → bn + 4 * k ≠ 0x8000bb34) (hsmall : bn + 4 * n < 2 ^ 64) :
    CodeReq.ofProg b prog (L + 12) = none :=
  CodeReq.ofProg_none_range_len b prog n (L + 12) hlen (by
    intro k hk heq
    have hL : (L + 12).toNat = 0x8000bb34 := by decide
    have h := congrArg BitVec.toNat heq
    rw [hL] at h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hb] at h
    exact hgap k hk (by omega))

theorem walk_none_at_call : RlpWalkNextEntryTie.wholeCode (L + 12) = none := by
  have he : RlpWalkNextEntryTie.entryCode (L + 12) = none :=
    walk_none_at RlpWalkNextEntryTie.T rlpWalkNext_prog 13
      RlpWalkNextEntryTie.entry_length 0x80004cdc (by decide) (by omega) (by norm_num)
  have hs : RlpWalkNextStrictTie.sharedCode (L + 12) = none :=
    walk_none_at RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52 (by rfl)
      0x80004d10 (by decide) (by omega) (by norm_num)
  have hc : RlpWalkNextStrictTie.coreCode (L + 12) = none :=
    walk_none_at RlpWalkNextStrictTie.C rlpWalkNextCore_prog 103 (by rfl)
      0x80004e34 (by decide) (by omega) (by norm_num)
  simp only [RlpWalkNextEntryTie.wholeCode, RlpWalkNextStrictTie.fullCode,
    CodeReq.union, he, hs, hc]

theorem call_walk {n : Nat} {Prest Q : Assertion} (oldRa : Word)
    (h_pre : Prest.pcFree)
    (h_callee : cpsTripleWithin n RlpWalkNextEntryTie.T ((L + 16) &&& ~~~(1 : Word))
      RlpWalkNextEntryTie.wholeCode ((.x1 ↦ᵣ (L + 16)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (L + 12) (L + 16) wholeCode ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  rw [show (L + 16 : Word) = L + 12 + 4 from by bv_omega] at h_callee ⊢
  have h_call := cpsCallWithin
    (nSteps := n) (callerPC := L + 12) (calleeEntry := RlpWalkNextEntryTie.T) (vOld := oldRa)
    (calleeCode := RlpWalkNextEntryTie.wholeCode) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.rlp_walk_next_leaf + 12))
    (by decide) (by decide) h_pre
    (singleton_disjoint_of_none walk_none_at_call)
    h_callee
  refine cpsTripleWithin_extend_code (CodeReq.union_split_mono ?_ walk_sub) h_call
  exact fun a i h_code => leaf_sub a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr L rlpWalkNextLeaf_prog 3 (L + 12)
      (by rw [leaf_length]; norm_num) (by rw [leaf_length]; norm_num) (by bv_omega))
      a i h_code)

/-! ## Introducing a pure fact carried in a precondition. -/

private theorem intro_pure {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop}
    (h : fact → cpsTripleWithin n entry exit_ cr P Q) :
    cpsTripleWithin n entry exit_ cr (P ** ⌜fact⌝) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, g1, g2, hd, hu, hPf, hR2⟩ := hPR
  have hf := (sepConj_pure_right g1).1 hPf
  exact h hf.2 R hR s hcr ⟨hp, hcompat, g1, g2, hd, hu, hf.1, hR2⟩ hpc

/-! ## ⭐ The status-8 arm is dead under the inherited non-LIST gate. -/

/-- **The deadness proof.**  At `L + 40` the machine holds `t2 =
    srcBytes[srcOff]` (idx 8 loaded it from the entry cursor) and `t3 = 192`.
    `hnotlist` says that byte is `< 0xc0 = 192`, so `bltu t2,t3` is taken and
    control jumps straight to the epilogue: idx 11 (`li a1,8`) is unreachable.

    This is what makes the wrapper status-transparent under row 3's gate, and it
    is the reason the gate is INHERITED rather than discharged — see the module
    docstring. -/
theorem prefix_test_always_taken (v : BitVec 8)
    (hnotlist : BitVec.ult (v.zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 1 (L + 40) (L + 48) leafCode
      ((.x7 ↦ᵣ (v.zeroExtend 64)) ** (.x28 ↦ᵣ (192 : Word)))
      ((.x7 ↦ᵣ (v.zeroExtend 64)) ** (.x28 ↦ᵣ (192 : Word))) := by
  have hbr := bltu_spec_gen_within .x7 .x28 (8 : BitVec 13)
    (v.zeroExtend 64) (192 : Word) (L + 40)
  rw [br3_target] at hbr
  have hbr' := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr L rlpWalkNextLeaf_prog 10 (L + 40)
      (by rw [leaf_length]; norm_num) (by rw [leaf_length]; norm_num) (by bv_omega))) hbr
  refine cpsTripleWithin_weaken (fun _ hp => hp) sepConj_strip_pure_end2
    (cpsBranchWithin_takenPath hbr' (fun hh hq => ?_))
  have hq2 := (sepConj_pure_right hh).1 hq
  exact hq2.2 hnotlist

end EvmAsm.Codegen.RlpWalkNextLeafTie
