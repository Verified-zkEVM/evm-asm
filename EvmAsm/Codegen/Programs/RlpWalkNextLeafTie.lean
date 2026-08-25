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
abbrev inert (sp s0Old s1Old srcBase endPtr : Word) (srcOff : Nat)
    (a0 st a2 : Word) : Assertion :=
  (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
  regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (sp ↦ₘ (RlpWalkNextEntryTie.T + 32)) **
  ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
  ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ st) ** ((sp + 40) ↦ₘ a2) **
  ((sp + 64) ↦ₘ (L + 16)) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old)

/-- The callee's return registers, this routine's own two frame cells, and the
    source region: everything the tail carries but only `x11` is ever read. -/
abbrev frameCore (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (a0 st a2 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
  inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
  ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
  bytesRegion srcBase srcBytes

/-- State inside the tail with the four scratch registers pinned to concrete
    values — the shape every instruction spec in the tail needs. -/
abbrev atTail (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (a0 st a2 v5 v6 v7 v28 : Word) : Assertion :=
  (.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
  frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)

/-- State at the epilogue entry `L + 48`, uniform across all three paths that
    reach it: the four scratch registers are merely OWNED, because path A leaves
    them untouched while paths B and C overwrite some of them. -/
abbrev epiPre (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (a0 st a2 : Word) : Assertion :=
  (.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
  frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28

/-- The only weakening the three paths need in common: forget the four scratch
    values.  Path A never writes them, paths B and C do. -/
theorem atTail_to_epiPre (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (a0 st a2 v5 v6 v7 v28 : Word) :
    ∀ h, atTail sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 v5 v6 v7 v28 h →
      epiPre sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 h :=
  sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7) (regIs_implies_regOwn .x28))))))

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
  refine cpsBranchWithin_takenStripPure2 hbr' (fun hh hq => ?_)
  obtain ⟨_, g2, _, _, _, hrest⟩ := hq
  exact ((sepConj_pure_right g2).1 hrest).2 hnotlist

/-! ## The three paths through the tail. -/

/-- Path to the epilogue closes the routine: reload `ra`, close the frame,
    return, and report the walker's three registers unchanged. -/
theorem epi_to_leafPost (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat) (a0 st a2 : Word)
    (hdisj : (st = 0 ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
        (endPtr - srcBase).toNat a2 floor) ∨ st ≠ 0) :
    cpsTripleWithin 3 (L + 48) (raIn &&& ~~~1) wholeCode
      (epiPre sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2)
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
  have he := epilogue_block (sp + 96) raIn (L + 16)
  rw [show (sp + 96 : Word) + 32 = sp + 128 from by bv_omega] at he
  have hef := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
     inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
     ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     bytesRegion srcBase srcBytes **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) (by pcf)
    (cpsTripleWithin_extend_code leaf_sub he)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => ⟨a0, st, a2, by xperm_hyp hq, hdisj⟩) hef

/-- **Path C** (`L + 32 → L + 48`): the item start `t0` coincides with the entry
    cursor, so idx 8 loads `srcBytes[srcOff]` and idx 10 always branches — see
    `prefix_test_always_taken`.  Idx 11 is never reached. -/
theorem pathC (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (a0 st a2 v7 v28 : Word)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 3 (L + 32) (L + 48) wholeCode
      (atTail sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2
        (srcBase + BitVec.ofNat 64 srcOff) (srcBase + BitVec.ofNat 64 srcOff) v7 v28)
      (epiPre sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2) := by
  have hpf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
     inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
     ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff))) (by pcf)
    (cpsTripleWithin_extend_code leaf_sub
      (prefix_block srcBase v7 v28 srcBytes srcOff hsalign hoff hover hvalid))
  have htf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
     inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
     ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     bytesRegion srcBase srcBytes **
     (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
     (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff))) (by pcf)
    (cpsTripleWithin_extend_code leaf_sub
      (prefix_test_always_taken (srcBytes[srcOff]'hoff) hnotlist))
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpf htf
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => atTail_to_epiPre sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff
        a0 st a2 (srcBase + BitVec.ofNat 64 srcOff) (srcBase + BitVec.ofNat 64 srcOff)
        ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word) h (by xperm_hyp hq)) hseq)

/-- **Branch 2** (idx 7, `L + 28`): `bne t0,t1`.  Taken — the reported length
    does NOT span back to the entry cursor, so the item carries a header and is
    a byte string — falls straight through to the epilogue with `a1` unchanged.
    Not taken — path C, where the prefix test runs and is always taken. -/
theorem branch2 (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat) (a0 st a2 v7 v28 : Word)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hdisj : (st = 0 ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
        (endPtr - srcBase).toNat a2 floor) ∨ st ≠ 0) :
    cpsTripleWithin 7 (L + 28) (raIn &&& ~~~1) wholeCode
      (atTail sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2
        (a0 - a2) (srcBase + BitVec.ofNat 64 srcOff) v7 v28)
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
  have hsub : ∀ a i, CodeReq.singleton (L + 28) (.BNE .x5 .x6 (20 : BitVec 13)) a = some i →
      wholeCode a = some i := fun a i h => leaf_sub a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr L rlpWalkNextLeaf_prog 7 (L + 28)
      (by rw [leaf_length]; norm_num) (by rw [leaf_length]; norm_num) (by bv_omega)) a i h)
  have hbr := bne_spec_gen_within .x5 .x6 (20 : BitVec 13) (a0 - a2)
    (srcBase + BitVec.ofNat 64 srcOff) (L + 28)
  rw [br2_target, show (L + 28 : Word) + 4 = L + 32 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
     frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
     (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) (by pcf)
    (cpsBranchWithin_extend_code hsub hbr)
  have harmT : cpsTripleWithin 6 (L + 48) (raIn &&& ~~~1) wholeCode
      (((.x5 ↦ᵣ (a0 - a2)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        ⌜(a0 - a2) ≠ srcBase + BitVec.ofNat 64 srcOff⌝) **
       ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
        frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)))
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (intro_pure (fact := (a0 - a2) ≠ srcBase + BitVec.ofNat 64 srcOff) (fun _ =>
        cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken
            (atTail_to_epiPre sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2
              (a0 - a2) (srcBase + BitVec.ofNat 64 srcOff) v7 v28)
            (fun _ hp => hp)
            (epi_to_leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor
              a0 st a2 hdisj))))
  have harmF : cpsTripleWithin 6 (L + 32) (raIn &&& ~~~1) wholeCode
      (((.x5 ↦ᵣ (a0 - a2)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        ⌜(a0 - a2) = srcBase + BitVec.ofNat 64 srcOff⌝) **
       ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
        frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)))
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (intro_pure (P := atTail sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2
        (a0 - a2) (srcBase + BitVec.ofNat 64 srcOff) v7 v28)
        (fact := (a0 - a2) = srcBase + BitVec.ofNat 64 srcOff) (fun heq => ?_))
    rw [heq]
    exact cpsTripleWithin_seq_same_cr
      (pathC sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 v7 v28
        hsalign hoff hover hvalid hnotlist)
      (epi_to_leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor
        a0 st a2 hdisj)
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (cpsBranchWithin_merge_same_cr hbrf harmT harmF))

/-- **Branch 1** (idx 4, `L + 16`) and the recompute block (idx 5..6).  Taken —
    the walker failed, so its status is passed through untouched.  Not taken —
    recompute `t0 = a0 - a2`, reload the saved entry cursor, and hand off to
    `branch2`. -/
theorem branch1 (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat) (a0 st a2 v5 v6 v7 v28 : Word)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hdisj : (st = 0 ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
        (endPtr - srcBase).toNat a2 floor) ∨ st ≠ 0) :
    cpsTripleWithin 10 (L + 16) (raIn &&& ~~~1) wholeCode
      (atTail sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 v5 v6 v7 v28)
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
  -- idx 5..6, then branch 2: the whole `st = 0` path, nine steps from `L + 20`.
  have hrb := recompute_block (sp + 96) a0 a2 (srcBase + BitVec.ofNat 64 srcOff) v5 v6
  rw [show (sp + 96 : Word) + 8 = sp + 104 from by bv_omega] at hrb
  have hrbf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (L + 16)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ st) **
     inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
     ((sp + 96) ↦ₘ raIn) ** bytesRegion srcBase srcBytes **
     (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) (by pcf)
    (cpsTripleWithin_extend_code leaf_sub hrb)
  have hpathB : cpsTripleWithin 9 (L + 20) (raIn &&& ~~~1) wholeCode
      (atTail sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 v5 v6 v7 v28)
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) :=
    cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hrbf)
        (branch2 sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor a0 st a2 v7 v28
          hsalign hoff hover hvalid hnotlist hdisj))
  have hsub : ∀ a i, CodeReq.singleton (L + 16) (.BNE .x11 .x0 (32 : BitVec 13)) a = some i →
      wholeCode a = some i := fun a i h => leaf_sub a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr L rlpWalkNextLeaf_prog 4 (L + 16)
      (by rw [leaf_length]; norm_num) (by rw [leaf_length]; norm_num) (by bv_omega)) a i h)
  have hbr := bne_spec_gen_within .x11 .x0 (32 : BitVec 13) st (0 : Word) (L + 16)
  rw [br1_target, show (L + 16 : Word) + 4 = L + 20 from by bv_omega] at hbr
  have hbrf := cpsBranchWithin_frameR
    ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) ** (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) **
     inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
     ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     bytesRegion srcBase srcBytes **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) (by pcf)
    (cpsBranchWithin_extend_code hsub hbr)
  have harmT : cpsTripleWithin 9 (L + 48) (raIn &&& ~~~1) wholeCode
      (((.x11 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) **
       ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) ** (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) **
        inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
        ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
        bytesRegion srcBase srcBytes **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)))
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (intro_pure (fact := st ≠ (0 : Word)) (fun _ =>
        cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken
            (atTail_to_epiPre sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2
              v5 v6 v7 v28)
            (fun _ hp => hp)
            (epi_to_leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor
              a0 st a2 hdisj))))
  have harmF : cpsTripleWithin 9 (L + 20) (raIn &&& ~~~1) wholeCode
      (((.x11 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜st = (0 : Word)⌝) **
       ((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) ** (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) **
        inert sp s0Old s1Old srcBase endPtr srcOff a0 st a2 **
        ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
        bytesRegion srcBase srcBytes **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)))
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (intro_pure (P := atTail sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff
        a0 st a2 v5 v6 v7 v28) (fact := st = (0 : Word)) (fun _ => hpathB))
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (cpsBranchWithin_merge_same_cr hbrf harmT harmF))

/-- The whole tail (`L + 16` onwards), consuming the walker's existential post.
    This is the only place this module touches `entryPost`'s internal shape; the
    two cells `sp+96 / sp+104` are this routine's OWN frame, framed around the
    call and untouched by the walker. -/
theorem tail_from_entryPost (sp raIn s0Old s1Old srcBase endPtr : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 10 (L + 16) (raIn &&& ~~~1) wholeCode
      (RlpWalkNextEntryTie.entryPost sp (L + 16) s0Old s1Old srcBase endPtr
          srcBytes srcOff floor **
        ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)))
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
  have key : ∀ a0 st a2 : Word,
      ((st = (0 : Word) ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
          (endPtr - srcBase).toNat a2 floor) ∨ st ≠ (0 : Word)) →
      cpsTripleWithin 10 (L + 16) (raIn &&& ~~~1) wholeCode
        (((.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
          (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (sp ↦ₘ (RlpWalkNextEntryTie.T + 32)) **
          ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((sp + 16) ↦ₘ endPtr) **
          ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ st) ** ((sp + 40) ↦ₘ a2) **
          ((sp + 64) ↦ₘ (L + 16)) ** ((sp + 72) ↦ₘ s0Old) ** ((sp + 80) ↦ₘ s1Old) **
          bytesRegion srcBase srcBytes) **
         (((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff))))
        (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
    intro a0 st a2 hdisj
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (cpsTripleWithin_of_forall_regIs_to_regOwn
        (P := (.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
          frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7)
        (r := .x28) (fun v28 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (cpsTripleWithin_of_forall_regIs_to_regOwn
        (P := (.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
          frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
          regOwn .x5 ** regOwn .x6 ** (.x28 ↦ᵣ v28))
        (r := .x7) (fun v7 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (cpsTripleWithin_of_forall_regIs_to_regOwn
        (P := (.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
          frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
          regOwn .x5 ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28))
        (r := .x6) (fun v6 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (cpsTripleWithin_of_forall_regIs_to_regOwn
        (P := (.x2 ↦ᵣ (sp + 96)) ** (.x1 ↦ᵣ (L + 16)) **
          frameCore sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff a0 st a2 **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28))
        (r := .x5) (fun v5 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (branch1 sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor a0 st a2
        v5 v6 v7 v28 hsalign hoff hover hvalid hnotlist hdisj)
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, g1, g2, hd, hu, hP, hR2⟩ := hPR
  obtain ⟨f1, f2, fd, fu, hSP, hFr⟩ := hP
  obtain ⟨a0, st, a2, hBIG, hdisj⟩ := hSP
  exact key a0 st a2 hdisj R hR s hcr
    ⟨hp, hcompat, g1, g2, hd, hu, ⟨f1, f2, fd, fu, hBIG, hFr⟩, hR2⟩ hpc

/-! ## The whole-routine contract at `GuestAddrs.rlp_walk_next_leaf`.

    ⚠️ TIER: `.conditional`.  The gate is inherited from
    `RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within` (row 3)
    and is NOT discharged here: the prefix byte at the INPUT cursor must be
    `< 0xc0`.  See the module docstring for why the routine's own idx-10 prefix
    test cannot discharge it, and `prefix_test_always_taken` for what that test
    does buy — the wrapper's status-8 arm is dead under the gate. -/

/-- **Whole-routine machine triple for `rlp_walk_next_leaf`**, entered at
    `GuestAddrs.rlp_walk_next_leaf` over the linked image `rlpWalkNextLeaf_prog`,
    unioned with the walker thunk, the shared body and the lenient core.

    Under the inherited non-LIST gate the wrapper is **status-transparent**: the
    `(a0, a1, a2)` it returns are exactly what `rlp_walk_next` returned, and the
    strict wrapper relation `rlpItemDecodeStrictW` is inherited unchanged on the
    accepting run.  See the module docstring for the frame attribution.

    Step bound `136 = 3 (prologue) + 1 + 122 (jal + walker) + 10 (tail)`. -/
theorem rlp_walk_next_leaf_entry_nonlist_strict_spec_within
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
    (hend : isValidByteAccess endPtr = true)
    (hlt : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 136 L (raIn &&& ~~~1) wholeCode
      ((.x2 ↦ᵣ (sp + 128)) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ a2Old) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x13 **
       (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       memOwn (sp + 64) ** memOwn (sp + 72) ** memOwn (sp + 80) **
       memOwn (sp + 96) ** memOwn (sp + 104) **
       bytesRegion srcBase srcBytes)
      (leafPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor) := by
  -- idx 0..2: open the frame, spill `ra`, save the ENTRY cursor.
  have hpro0 := prologue_block (sp + 96) raIn (srcBase + BitVec.ofNat 64 srcOff)
  rw [show (sp + 96 : Word) + 32 = sp + 128 from by bv_omega,
      show (sp + 96 : Word) + 8 = sp + 104 from by bv_omega] at hpro0
  have hpro := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
     (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
     (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x13 **
     (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
     memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
     memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
     memOwn (sp + 64) ** memOwn (sp + 72) ** memOwn (sp + 80) **
     bytesRegion srcBase srcBytes) (by pcf)
    (cpsTripleWithin_extend_code leaf_sub hpro0)
  -- idx 3: row 3's whole-routine contract, COMPOSED (not assumed).
  have hwn := RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within
    sp (L + 16) s0Old s1Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff floor hsalign hoff hover hvalid hss hls hll hend hlt hnotlist
  have hwnF := cpsTripleWithin_frameR
    (((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)))
    (by pcf) hwn
  have hwn' := cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hwnF
    (P' := (.x1 ↦ᵣ (L + 16)) **
      ((.x2 ↦ᵣ (sp + 96)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ a2Old) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x13 **
       (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       memOwn (sp + 64) ** memOwn (sp + 72) ** memOwn (sp + 80) **
       bytesRegion srcBase srcBytes **
       ((sp + 96) ↦ₘ raIn) ** ((sp + 104) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff))))
  have hcall := call_walk raIn (by pcf) hwn'
  -- idx 4..14: the three-way tail.
  have htail := tail_from_entryPost sp raIn s0Old s1Old srcBase endPtr srcBytes srcOff floor
    hsalign hoff hover hvalid hnotlist
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro hcall
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 htail
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) c2)

/-! ## Non-vacuity.

    Discipline (#12799): a satisfiable instance AND a negative control in which
    the same hypotheses are provably FALSE.  Two instances are given, because
    the two structurally different tail paths deserve separate witnesses:

    * `rlp_walk_next_leaf_entry_instance` — the canonical three-byte short
      string, the same input `RlpWalkNextEntryTie.rlp_walk_next_entry_instance`
      uses, so row 3's anchor and this one are exercised on one witness.  Its
      header is one byte long, so `a0 - a2 ≠ entry cursor` and the run takes
      path B (idx 7 branches).
    * `rlp_walk_next_leaf_single_byte_instance` — a single-byte item, where
      `a0 - a2 = entry cursor` and the run takes path C, the path that actually
      executes the prefix test.  Without it the whole `prefix_test_always_taken`
      argument could be about an unreachable block. -/

/-- Closed instantiation on the canonical three-byte short string: every
    hypothesis discharged by `decide`, hence a hypothesis-free machine triple at
    `GuestAddrs.rlp_walk_next_leaf`. -/
theorem rlp_walk_next_leaf_entry_instance :
    cpsTripleWithin 136 L ((0xa0000000 : Word) &&& ~~~1) wholeCode
      ((.x2 ↦ᵣ ((0xa0000100 : Word) + 128)) ** (.x1 ↦ᵣ (0xa0000000 : Word)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0x40000000 : Word) + BitVec.ofNat 64 0)) **
       (.x11 ↦ᵣ ((0x40000000 : Word) + 4)) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
       regOwn .x13 **
       (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (0 : Word)) **
       (.x31 ↦ᵣ (0 : Word)) **
       memOwn (0xa0000100 : Word) ** memOwn ((0xa0000100 : Word) + 8) **
       memOwn ((0xa0000100 : Word) + 16) ** memOwn ((0xa0000100 : Word) + 24) **
       memOwn ((0xa0000100 : Word) + 32) ** memOwn ((0xa0000100 : Word) + 40) **
       memOwn ((0xa0000100 : Word) + 64) ** memOwn ((0xa0000100 : Word) + 72) **
       memOwn ((0xa0000100 : Word) + 80) ** memOwn ((0xa0000100 : Word) + 96) **
       memOwn ((0xa0000100 : Word) + 104) **
       bytesRegion (0x40000000 : Word) [0x83, 0x01, 0x02, 0x03])
      (leafPost (0xa0000100 : Word) (0xa0000000 : Word) (0 : Word) (0 : Word)
        (0x40000000 : Word) ((0x40000000 : Word) + 4) [0x83, 0x01, 0x02, 0x03] 0 9) :=
  rlp_walk_next_leaf_entry_nonlist_strict_spec_within
    (0xa0000100 : Word) (0xa0000000 : Word) (0 : Word) (0 : Word)
    (0x40000000 : Word) ((0x40000000 : Word) + 4)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    [0x83, 0x01, 0x02, 0x03] 0 9 (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ => ⟨by decide, by decide, by decide⟩)
    (fun h1 _ _ => absurd (by decide) h1) (fun h1 _ => absurd (by decide) h1)
    (by decide) (by decide) (by decide)

/-- Closed instantiation on a SINGLE-BYTE item (`0x05`), the shape whose header
    is empty, so the walker's reported length spans the whole item and
    `a0 - a2 = entry cursor` — the run that actually reaches idx 8..10 and
    exercises `prefix_test_always_taken`. -/
theorem rlp_walk_next_leaf_single_byte_instance :
    cpsTripleWithin 136 L ((0xa0000000 : Word) &&& ~~~1) wholeCode
      ((.x2 ↦ᵣ ((0xa0000100 : Word) + 128)) ** (.x1 ↦ᵣ (0xa0000000 : Word)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0x40000000 : Word) + BitVec.ofNat 64 0)) **
       (.x11 ↦ᵣ ((0x40000000 : Word) + 1)) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
       regOwn .x13 **
       (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (0 : Word)) **
       (.x31 ↦ᵣ (0 : Word)) **
       memOwn (0xa0000100 : Word) ** memOwn ((0xa0000100 : Word) + 8) **
       memOwn ((0xa0000100 : Word) + 16) ** memOwn ((0xa0000100 : Word) + 24) **
       memOwn ((0xa0000100 : Word) + 32) ** memOwn ((0xa0000100 : Word) + 40) **
       memOwn ((0xa0000100 : Word) + 64) ** memOwn ((0xa0000100 : Word) + 72) **
       memOwn ((0xa0000100 : Word) + 80) ** memOwn ((0xa0000100 : Word) + 96) **
       memOwn ((0xa0000100 : Word) + 104) **
       bytesRegion (0x40000000 : Word) [0x05])
      (leafPost (0xa0000100 : Word) (0xa0000000 : Word) (0 : Word) (0 : Word)
        (0x40000000 : Word) ((0x40000000 : Word) + 1) [0x05] 0 9) :=
  rlp_walk_next_leaf_entry_nonlist_strict_spec_within
    (0xa0000100 : Word) (0xa0000000 : Word) (0 : Word) (0 : Word)
    (0x40000000 : Word) ((0x40000000 : Word) + 1)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    [0x05] 0 9 (by decide) (by decide) (by decide) (by decide)
    (fun h1 _ _ _ => absurd (by decide) h1)
    (fun h1 _ _ => absurd (by decide) h1) (fun h1 _ => absurd (by decide) h1)
    (by decide) (by decide) (by decide)

/-- Closed instantiation of the deadness lemma itself, so the claim "idx 11 is
    unreachable" is witnessed and not merely asserted in prose. -/
theorem rlp_walk_next_leaf_prefix_test_instance :
    cpsTripleWithin 1 (L + 40) (L + 48) leafCode
      ((.x7 ↦ᵣ ((0x05 : BitVec 8).zeroExtend 64)) ** (.x28 ↦ᵣ (192 : Word)))
      ((.x7 ↦ᵣ ((0x05 : BitVec 8).zeroExtend 64)) ** (.x28 ↦ᵣ (192 : Word))) :=
  prefix_test_always_taken (0x05 : BitVec 8) (by decide)

/-- NEGATIVE CONTROL.  Each of the three premises this module carries beyond the
    plain readability ones is REFUTABLE, so none is a tautology that any
    instantiation satisfies:

    * `hnotlist` fails at a LIST prefix (`0xc3`) — this is exactly the input
      class row 3 does not cover, and exactly the class for which the wrapper's
      status-8 arm would fire.  Its refutability here is the formal statement
      that the gate is INHERITED rather than discharged.
    * `hend` fails at a text-segment address (`0x80000000`), which is not a
      guest data address.
    * `hlt` fails when the cursor is not strictly before the end pointer. -/
theorem rlp_walk_next_leaf_premises_refutable :
    ¬ BitVec.ult ((([0xc3, 0x01, 0x02, 0x03] : List (BitVec 8))[0]'(by decide)).zeroExtend 64)
        (0xc0 : Word) = true ∧
    ¬ isValidByteAccess (0x80000000 : Word) = true ∧
    ¬ BitVec.ult ((0x40000004 : Word)) (0x40000000 : Word) = true :=
  ⟨by decide, by decide, by decide⟩

end EvmAsm.Codegen.RlpWalkNextLeafTie
