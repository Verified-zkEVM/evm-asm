/-
  EvmAsm.Rv64.RLP.Field0ToU64

  First caller-level verification slice composing the verified cursor-walk RLP
  leaves (`rlp_walk_init`, `rlp_walk_next`, `rlp_content_to_u64`) into a small
  wrapper subroutine that decodes the **first field** of an RLP list as a
  canonical `u64`. This is a bounded, intentionally narrow slice: it does not
  attempt arbitrary nth-field walking, and it is not (yet) wired into Codegen's
  unverified `rlp_field_to_u64` (`EvmAsm/Codegen/Programs/Tx.lean`).

  ## Caller-facing contract (LP64)

  Frameless wrapper: reached by `jal ra, rlp_field0_to_u64`, returns via `ret`.

  ### Inputs
  * `a0` (`x10`) — full RLP list bytes pointer.
  * `a1` (`x11`) — full RLP list byte length.

  ### Outputs
  * `a0` (`x10`) — decoded `u64` value on success; `0` on every failure path.
  * `a1` (`x11`) — status: `0` ok · `1` parse/list/item failure while locating
    field 0 · `2` scalar too long (`rlp_content_to_u64` status 2) · `3` scalar
    non-canonical (`rlp_content_to_u64` status 3).

  Scratch `t0..t6` (`x5,x6,x7,x28..x31`) and `a3`/`x13` (used to save the
  caller's `ra` across the three nested calls) are clobbered; `ra` preserved.

  ## Code layout

  Fixed, non-overlapping offsets from the wrapper's own `base`:
    * wrapper body         — `base`
    * `rlp_walk_init`       — `base + 0x100`
    * `rlp_walk_next`       — `base + 0x300`
    * `rlp_content_to_u64`  — `base + 0x600`

  ```
   0  MV   x13 x1            ; save caller ra
   1  JAL  x1  rlp_walk_init  (base+0x100)
   2  BNE  x12 x0  -> idx 11  ; walk_init status != 0 -> parse_fail
   3  JAL  x1  rlp_walk_next  (base+0x300)
   4  BNE  x11 x0  -> idx 11  ; walk_next status != 0 -> parse_fail
   5  SUB  x10 x10 x12        ; content_ptr = advanced - content_len
   6  MV   x11 x12            ; len = content_len
   7  MV   x6  x10            ; pin t1 = content_ptr (rlp_content_to_u64's scratch
                                 register precondition)
   8  JAL  x1  rlp_content_to_u64  (base+0x600)
   9  MV   x1  x13            ; restore caller ra
  10  JALR x0  x1  0          ; ret
  11  LI   x10 0              ; parse_fail: a0 = 0
  12  LI   x11 1              ; a1 = 1
  13  MV   x1  x13
  14  JALR x0  x1  0          ; ret
  ```

  ## Verification status

  This PR lands the **call-composition slice**: a proved theorem
  (`rlp_field0_to_u64_content_call_success_spec_within`) that, starting from a
  state immediately after a successful `rlp_walk_next` (cursor advanced,
  status `0`, content length in `x12`), steps through the `SUB`/`MV`/`MV` glue
  and the `jal ra, rlp_content_to_u64` call via `WP.cpsCallWithin`, and
  concludes the wrapper's overall success postcondition: status `0` and the
  decoded `Nat.fromBytesBE` value, with the caller's `ra` restored.

  **Remaining work** (tracked as a bead, see PR body): lift the `rlp_walk_init`
  and `rlp_walk_next` call compositions (idx 1 and idx 3) the same way, and
  combine all three call compositions plus the two failure branches into one
  unified `rlp_field0_to_u64_spec_within` top theorem with a four-way
  disjunctive postcondition (success / status 1 / 2 / 3), per the
  `AGENTS.md` spec-design convention.
-/

import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.BitAux
import EvmAsm.Rv64.Tactics.WP
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.SeqFrame

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP

/-- Isolated alignment fact for `cpsCallWithin`'s `halign` side condition, kept as a
standalone lemma (rather than inline `bv_omega`, which cannot derive bitwise-AND facts
from arithmetic alone) so the call site can discharge it directly from `hbase0` via
`EvmAsm.Rv64.BitAux.word_add_even_andn_one`. -/
private theorem field0_halign (base : Word) (hbase0 : base &&& (1 : Word) = 0) :
    (base + 32 + 4) &&& ~~~(1 : Word) = base + 32 + 4 := by
  have h36 : (base + 32 + 4 : Word) = base + 36 := by bv_omega
  rw [h36]
  exact EvmAsm.Rv64.BitAux.word_add_even_andn_one hbase0 (by decide)

/-- Isolated jump-target fact for the `jal ra, rlp_content_to_u64` call, kept standalone
for the same reason as `field0_halign`. -/
private theorem field0_hoffset (base : Word) :
    (base + 32) + signExtend21 (1504 : BitVec 21) = base + (1536 : Word) := by
  rw [show signExtend21 (1504 : BitVec 21) = (1504 : Word) from by decide]; bv_omega

/-- The `rlp_field0_to_u64` wrapper body (15 instructions). See the module doc
comment for the annotated listing and register map. -/
def rlp_field0_to_u64_prog : List Instr :=
  [ .MV .x13 .x1,                    -- 0  save caller ra
    .JAL .x1 (252 : BitVec 21),      -- 1  call rlp_walk_init at base+0x100 (256-4)
    .BNE .x12 .x0 (36 : BitVec 13),  -- 2  walk_init status != 0 -> idx 11 (44-8)
    .JAL .x1 (756 : BitVec 21),      -- 3  call rlp_walk_next at base+0x300 (768-12)
    .BNE .x11 .x0 (28 : BitVec 13),  -- 4  walk_next status != 0 -> idx 11 (44-16)
    .SUB .x10 .x10 .x12,             -- 5  content_ptr = advanced - content_len
    .MV .x11 .x12,                   -- 6  len = content_len
    .MV .x6 .x10,                    -- 7  pin t1 = content_ptr
    .JAL .x1 (1504 : BitVec 21),     -- 8  call rlp_content_to_u64 at base+0x600 (1536-32)
    .MV .x1 .x13,                    -- 9  restore caller ra
    .JALR .x0 .x1 0,                 -- 10 ret
    .LI .x10 (0 : Word),             -- 11 parse_fail: a0 = 0
    .LI .x11 (1 : Word),             -- 12 a1 = 1
    .MV .x1 .x13,                    -- 13 restore caller ra
    .JALR .x0 .x1 0 ]                -- 14 ret

theorem rlp_field0_to_u64_prog_length : rlp_field0_to_u64_prog.length = 15 := rfl

/-- The wrapper body as a `CodeReq` rooted at `base`. -/
abbrev rlp_field0_to_u64_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_field0_to_u64_prog

/-- Shared parse-failure tail: zero the value, set wrapper status 1, restore
the caller ra from x13, and return. This is the target of both wrapper
parse-failure branches. -/
def rlp_field0_to_u64_parse_fail_tail_prog : List Instr :=
  [ .LI .x10 (0 : Word),
    .LI .x11 (1 : Word),
    .MV .x1 .x13,
    .JALR .x0 .x1 0 ]

theorem rlp_field0_to_u64_parse_fail_tail_prog_length :
    rlp_field0_to_u64_parse_fail_tail_prog.length = 4 := rfl

def rlp_field0_to_u64_parse_fail_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_field0_to_u64_parse_fail_tail_prog

def rlp_field0_to_u64_parse_fail_exit (savedRa : Word) : Word :=
  savedRa &&& ~~~(1 : Word)

def rlp_field0_to_u64_parse_fail_post (savedRa : Word) : Assertion :=
  ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) **
    (.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa))

/-- WP-synthesized certificate for the common parse-failure tail. The
precondition is computed from the final postcondition by wp_rv64_leaf_synth;
no hand-written instruction sequencing is needed for this straight-line block. -/
def rlp_field0_to_u64_parse_fail_tail_cert (base savedRa : Word) :
    WP.CFG.Cert base (rlp_field0_to_u64_parse_fail_exit savedRa)
      (rlp_field0_to_u64_parse_fail_tail_code base)
      (rlp_field0_to_u64_parse_fail_post savedRa) := by
  unfold rlp_field0_to_u64_parse_fail_exit
    rlp_field0_to_u64_parse_fail_tail_code
    rlp_field0_to_u64_parse_fail_tail_prog
    rlp_field0_to_u64_parse_fail_post
  wp_rv64_leaf_synth

theorem rlp_field0_to_u64_parse_fail_tail_cert_pre (base savedRa : Word) :
    (rlp_field0_to_u64_parse_fail_tail_cert base savedRa).pre =
      (regOwn .x10 ** regOwn .x11 ** (.x13 ↦ᵣ savedRa) ** regOwn .x1) := rfl

/-- The parse-failure tail certificate, lifted from its four-instruction slice
into the full wrapper CodeReq at index 11. -/
def rlp_field0_to_u64_parse_fail_cert (base savedRa : Word) :
    WP.CFG.Cert (base + 44) (rlp_field0_to_u64_parse_fail_exit savedRa)
      (rlp_field0_to_u64_code base) (rlp_field0_to_u64_parse_fail_post savedRa) :=
  WP.CFG.extendCode (rlp_field0_to_u64_parse_fail_tail_cert (base + 44) savedRa)
    (CodeReq.ofProg_mono_sub base (base + 44) rlp_field0_to_u64_prog
      rlp_field0_to_u64_parse_fail_tail_prog 11
      (by bv_omega) (by decide) (by decide) (by decide))

/-- Verified common parse-failure tail of rlp_field0_to_u64. -/
theorem rlp_field0_to_u64_parse_fail_spec_within (base savedRa : Word) :
    cpsTripleWithin (rlp_field0_to_u64_parse_fail_cert base savedRa).nSteps
      (base + 44) (rlp_field0_to_u64_parse_fail_exit savedRa)
      (rlp_field0_to_u64_code base)
      (regOwn .x10 ** regOwn .x11 ** (.x13 ↦ᵣ savedRa) ** regOwn .x1)
      (rlp_field0_to_u64_parse_fail_post savedRa) := by
  rw [← rlp_field0_to_u64_parse_fail_tail_cert_pre (base + 44) savedRa]
  exact (rlp_field0_to_u64_parse_fail_cert base savedRa).sound

/-- The full deployed layout: wrapper plus the three verified callees, at the
fixed offsets documented in the module header. Used for the planned unified
top theorem; the call-composition slice proved in this file works over the
smaller `rlp_field0_to_u64_code base ∪ rlp_content_to_u64_code (base+0x600)`
sub-layout, which is a `CodeReq.union` summand of this full layout. -/
def rlp_field0_to_u64_full_code (base : Word) : CodeReq :=
  ((rlp_field0_to_u64_code base).union (rlp_walk_init_code (base + (256 : Word)))).union
    ((rlp_walk_next_code (base + (768 : Word))).union
      (rlp_content_to_u64_code (base + (1536 : Word))))

/-- Contiguous deployable image for the fixed-offset wrapper layout.

The NOP gaps place the callees at the exact addresses used by the wrapper's
PC-relative JAL instructions: walk_init at +0x100, walk_next at +0x300, and
content_to_u64 at +0x600. -/
def rlp_field0_to_u64_full_prog : List Instr :=
  rlp_field0_to_u64_prog ++
    List.replicate 49 .NOP ++
    rlp_walk_init_prog ++
    List.replicate 75 .NOP ++
    rlp_walk_next_prog ++
    List.replicate 89 .NOP ++
    rlp_content_to_u64_prog

/-! ## Layout sanity: the four fixed-offset regions are pairwise disjoint. -/

theorem rlp_field0_to_u64_wrapper_walkInit_disjoint (base : Word) :
    (rlp_field0_to_u64_code base).Disjoint (rlp_walk_init_code (base + (256 : Word))) := by
  crDisjoint

theorem rlp_field0_to_u64_wrapper_walkNext_disjoint (base : Word) :
    (rlp_field0_to_u64_code base).Disjoint (rlp_walk_next_code (base + (768 : Word))) := by
  crDisjoint

theorem rlp_field0_to_u64_wrapper_content_disjoint (base : Word) :
    (rlp_field0_to_u64_code base).Disjoint (rlp_content_to_u64_code (base + (1536 : Word))) := by
  crDisjoint

theorem rlp_field0_to_u64_walkInit_walkNext_disjoint (base : Word) :
    (rlp_walk_init_code (base + (256 : Word))).Disjoint
      (rlp_walk_next_code (base + (768 : Word))) := by
  crDisjoint

theorem rlp_field0_to_u64_walkInit_content_disjoint (base : Word) :
    (rlp_walk_init_code (base + (256 : Word))).Disjoint
      (rlp_content_to_u64_code (base + (1536 : Word))) := by
  crDisjoint

theorem rlp_field0_to_u64_walkNext_content_disjoint (base : Word) :
    (rlp_walk_next_code (base + (768 : Word))).Disjoint
      (rlp_content_to_u64_code (base + (1536 : Word))) := by
  crDisjoint

/-! ## Call-site adapters for the two cursor-walk callees. -/

private theorem field0_init_halign (base : Word) (hbase0 : base &&& (1 : Word) = 0) :
    (base + 4 + 4) &&& ~~~(1 : Word) = base + 4 + 4 := by
  rw [show (base + 4 + 4 : Word) = base + 8 from by bv_omega]
  exact EvmAsm.Rv64.BitAux.word_add_even_andn_one hbase0 (by decide)

private theorem field0_init_hoffset (base : Word) :
    (base + 4) + signExtend21 (252 : BitVec 21) = base + (256 : Word) := by
  rw [show signExtend21 (252 : BitVec 21) = (252 : Word) from by decide]
  bv_omega

/-- Compose the wrapper's call at index 1 with an arbitrary verified
`rlp_walk_init` postcondition, and lift the local call/callee union into the
complete fixed-offset field-0 image. -/
theorem rlp_field0_to_u64_call_walk_init
    {nSteps : Nat} {Prest Q : Assertion} (base oldRa : Word)
    (hbase0 : base &&& (1 : Word) = 0) (hpre : Prest.pcFree)
    (hcallee : cpsTripleWithin nSteps (base + (256 : Word))
      ((base + 4 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code (base + (256 : Word)))
      ((.x1 ↦ᵣ (base + 4 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + nSteps) (base + 4) (base + 8)
      (rlp_field0_to_u64_full_code base) ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have hdisj : (CodeReq.singleton (base + 4) (.JAL .x1 (252 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + (256 : Word))) := by crDisjoint
  have hcall := WP.cpsCallWithin (offset := (252 : BitVec 21)) (vOld := oldRa)
    (field0_init_hoffset base) (field0_init_halign base hbase0) hpre
    hdisj hcallee
  have hmono : ∀ a i,
      ((CodeReq.singleton (base + 4) (.JAL .x1 (252 : BitVec 21))).union
        (rlp_walk_init_code (base + (256 : Word)))) a = some i →
        rlp_field0_to_u64_full_code base a = some i :=
    CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
        (CodeReq.singleton_mono
          (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 1 (base + 4)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)))
      (fun a i h => CodeReq.union_mono_left a i (CodeReq.mono_union_right
        (rlp_field0_to_u64_wrapper_walkInit_disjoint base) (fun _ _ h' => h') a i h))
  rw [show (base + 4 + 4 : Word) = base + 8 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code hmono hcall

private theorem field0_next_halign (base : Word) (hbase0 : base &&& (1 : Word) = 0) :
    (base + 12 + 4) &&& ~~~(1 : Word) = base + 12 + 4 := by
  rw [show (base + 12 + 4 : Word) = base + 16 from by bv_omega]
  exact EvmAsm.Rv64.BitAux.word_add_even_andn_one hbase0 (by decide)

private theorem field0_next_hoffset (base : Word) :
    (base + 12) + signExtend21 (756 : BitVec 21) = base + (768 : Word) := by
  rw [show signExtend21 (756 : BitVec 21) = (756 : Word) from by decide]
  bv_omega

/-- Compose the wrapper's call at index 3 with an arbitrary verified
`rlp_walk_next` postcondition, lifted into the complete fixed-offset image. -/
theorem rlp_field0_to_u64_call_walk_next
    {nSteps : Nat} {Prest Q : Assertion} (base oldRa : Word)
    (hbase0 : base &&& (1 : Word) = 0) (hpre : Prest.pcFree)
    (hcallee : cpsTripleWithin nSteps (base + (768 : Word))
      ((base + 12 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code (base + (768 : Word)))
      ((.x1 ↦ᵣ (base + 12 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + nSteps) (base + 12) (base + 16)
      (rlp_field0_to_u64_full_code base) ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have hdisj : (CodeReq.singleton (base + 12) (.JAL .x1 (756 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + (768 : Word))) := by crDisjoint
  have hcall := WP.cpsCallWithin (offset := (756 : BitVec 21)) (vOld := oldRa)
    (field0_next_hoffset base) (field0_next_halign base hbase0) hpre
    hdisj hcallee
  have hleftNext : ((rlp_field0_to_u64_code base).union
      (rlp_walk_init_code (base + (256 : Word)))).Disjoint
      (rlp_walk_next_code (base + (768 : Word))) := by crDisjoint
  have hmono : ∀ a i,
      ((CodeReq.singleton (base + 12) (.JAL .x1 (756 : BitVec 21))).union
        (rlp_walk_next_code (base + (768 : Word)))) a = some i →
        rlp_field0_to_u64_full_code base a = some i :=
    CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
        (CodeReq.singleton_mono
          (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 3 (base + 12)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)))
      (fun a i h => CodeReq.mono_union_right hleftNext
        (fun a i h' => CodeReq.union_mono_left a i h') a i h)
  rw [show (base + 12 + 4 : Word) = base + 16 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code hmono hcall

#print axioms rlp_field0_to_u64_call_walk_init
#print axioms rlp_field0_to_u64_call_walk_next

/-! ## Wrapper parse-failure branches. -/

/-- If `rlp_walk_init` returns any nonzero status in `x12`, the wrapper's
index-2 branch reaches the shared tail and normalizes the public result to
`a0 = 0, a1 = 1`, preserving the caller's saved return address. -/
theorem rlp_field0_to_u64_init_failure_spec_within
    (base savedRa cursor endPtr initStatus : Word) (srcBase : Word)
    (srcBytes : List (BitVec 8)) (hstatus : initStatus ≠ 0) :
    cpsTripleWithin 5 (base + 8) (savedRa &&& ~~~(1 : Word))
      (rlp_field0_to_u64_full_code base)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 8)) ** bytesRegion srcBase srcBytes) **
       ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ initStatus) **
        (.x13 ↦ᵣ savedRa)))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ initStatus) ** bytesRegion srcBase srcBytes) **
       rlp_field0_to_u64_parse_fail_post savedRa) := by
  have hbr0 := bne_spec_gen_within .x12 .x0 (36 : BitVec 13) initStatus (0 : Word) (base + 8)
  rw [show (base + 8) + signExtend13 (36 : BitVec 13) = base + 44 from by
    rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]; bv_omega] at hbr0
  have hmono2 : ∀ a i,
      CodeReq.singleton (base + 8) (.BNE .x12 .x0 (36 : BitVec 13)) a = some i →
        rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 2 (base + 8)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hbr := cpsBranchWithin_frameR
    ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (base + 8)) ** bytesRegion srcBase srcBytes) **
     ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x13 ↦ᵣ savedRa)))
    (by pcFree) (cpsBranchWithin_extend_code hmono2 hbr0)
  have htaken := cpsBranchWithin_takenPath hbr (fun h hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, _⟩ := hp
    exact hstatus h_eq)
  have hwrapMono : ∀ a i, rlp_field0_to_u64_code base a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i h)
  have htail0 := cpsTripleWithin_extend_code hwrapMono
    (rlp_field0_to_u64_parse_fail_spec_within base savedRa)
  have htailBase : cpsTripleWithin (rlp_field0_to_u64_parse_fail_cert base savedRa).nSteps
      (base + 44) (rlp_field0_to_u64_parse_fail_exit savedRa)
      (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x13 ↦ᵣ savedRa) **
        (.x1 ↦ᵣ (base + 8)))
      (rlp_field0_to_u64_parse_fail_post savedRa) :=
    cpsTripleWithin_weaken (fun h hp =>
      sepConj_mono (regIs_implies_regOwn .x10)
        (sepConj_mono (regIs_implies_regOwn .x11)
          (sepConj_mono (fun _ x => x) (regIs_implies_regOwn .x1))) h hp)
    (fun _ hp => hp) htail0
  have htail := cpsTripleWithin_frameR
    ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ initStatus) ** bytesRegion srcBase srcBytes) **
     ⌜initStatus ≠ 0⌝)
    (by pcFree) htailBase
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) htaken htail
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      extract_pure_deep hp
      obtain ⟨_, hp'⟩ := hp
      xperm_hyp hp') hseq

#print axioms rlp_field0_to_u64_init_failure_spec_within

/-- If `rlp_walk_next` returns a nonzero status in `x11`, the wrapper's
index-4 branch normalizes it to the public parse-failure result. -/
theorem rlp_field0_to_u64_next_failure_spec_within
    (base savedRa cursor nextStatus contentLen srcBase : Word)
    (srcBytes : List (BitVec 8)) (hstatus : nextStatus ≠ 0) :
    cpsTripleWithin 5 (base + 16) (savedRa &&& ~~~(1 : Word))
      (rlp_field0_to_u64_full_code base)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 16)) ** bytesRegion srcBase srcBytes) **
       ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ nextStatus) ** (.x12 ↦ᵣ contentLen) **
        (.x13 ↦ᵣ savedRa)))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ contentLen) ** bytesRegion srcBase srcBytes) **
       rlp_field0_to_u64_parse_fail_post savedRa) := by
  have hbr0 := bne_spec_gen_within .x11 .x0 (28 : BitVec 13) nextStatus (0 : Word) (base + 16)
  rw [show (base + 16) + signExtend13 (28 : BitVec 13) = base + 44 from by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega] at hbr0
  have hmono4 : ∀ a i,
      CodeReq.singleton (base + 16) (.BNE .x11 .x0 (28 : BitVec 13)) a = some i →
        rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 4 (base + 16)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hbr := cpsBranchWithin_frameR
    ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (base + 16)) ** bytesRegion srcBase srcBytes) **
     ((.x10 ↦ᵣ cursor) ** (.x12 ↦ᵣ contentLen) ** (.x13 ↦ᵣ savedRa)))
    (by pcFree) (cpsBranchWithin_extend_code hmono4 hbr0)
  have htaken := cpsBranchWithin_takenPath hbr (fun h hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, _⟩ := hp
    exact hstatus h_eq)
  have hwrapMono : ∀ a i, rlp_field0_to_u64_code base a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i h)
  have htail0 := cpsTripleWithin_extend_code hwrapMono
    (rlp_field0_to_u64_parse_fail_spec_within base savedRa)
  have htailBase : cpsTripleWithin (rlp_field0_to_u64_parse_fail_cert base savedRa).nSteps
      (base + 44) (rlp_field0_to_u64_parse_fail_exit savedRa)
      (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ nextStatus) ** (.x13 ↦ᵣ savedRa) **
        (.x1 ↦ᵣ (base + 16)))
      (rlp_field0_to_u64_parse_fail_post savedRa) :=
    cpsTripleWithin_weaken (fun h hp =>
      sepConj_mono (regIs_implies_regOwn .x10)
        (sepConj_mono (regIs_implies_regOwn .x11)
          (sepConj_mono (fun _ x => x) (regIs_implies_regOwn .x1))) h hp)
      (fun _ hp => hp) htail0
  have htail := cpsTripleWithin_frameR
    ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ contentLen) ** bytesRegion srcBase srcBytes) **
     ⌜nextStatus ≠ 0⌝)
    (by pcFree) htailBase
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) htaken htail
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      extract_pure_deep hp
      obtain ⟨_, hp'⟩ := hp
      xperm_hyp hp') hseq

#print axioms rlp_field0_to_u64_next_failure_spec_within

/-! ## Call-composition slice: idx 5..10, starting from a successful
`rlp_walk_next` state. -/

/--
**`rlp_field0_to_u64` — success-path call composition** (idx 5..10, `base+20 →
savedRa &&& ~~~1`).

Starting from a state immediately after a successful `rlp_walk_next` call
(`x10` = the advanced cursor, `x11 = 0` status, `x12` = the content length),
this steps through the `SUB`/`MV`/`MV` glue and the `jal ra, rlp_content_to_u64`
call (composed via `WP.cpsCallWithin`), and concludes the wrapper's overall
success outcome: `a0` = the decoded `Nat.fromBytesBE` scalar, `a1 = 0`, with
the caller's `ra` restored from `x13`.

`hbase0` records that the wrapper's own entry `base` is half-word aligned
(its low bit is clear) — true for any real code layout, and needed here
(unlike the leaf-only theorems elsewhere in this development) because this is
the first proof in the repo to compose a real `jal`-based subroutine call via
`WP.cpsCallWithin`, which requires the call's own return address to already
be aligned. -/
theorem rlp_field0_to_u64_content_call_success_spec_within
    (base srcBase savedRa x1Val t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (advanced contentLen : Word) (srcOff len : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hlen0 : 0 < len) (hlen8 : len ≤ 8)
    (hsalign : srcBase.toNat % 8 = 0) (hsoff : srcOff < srcBytes.length)
    (hcanon : srcBytes[srcOff]'hsoff ≠ 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hadvanced : advanced = srcBase + BitVec.ofNat 64 (srcOff + len))
    (hcontentLen : contentLen = BitVec.ofNat 64 len) :
    cpsTripleWithin (7 * len + 17) (base + 20) (savedRa &&& ~~~1)
      ((rlp_field0_to_u64_code base).union (rlp_content_to_u64_code (base + (1536 : Word))))
      ((.x10 ↦ᵣ advanced) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ contentLen) **
        (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ contentLen) ** (.x13 ↦ᵣ savedRa) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes) := by
  subst hadvanced; subst hcontentLen
  set CR := (rlp_field0_to_u64_code base).union (rlp_content_to_u64_code (base + (1536 : Word)))
    with hCR
  -- Re-bind `contentLen` as a local abbreviation for `BitVec.ofNat 64 len` (rather than
  -- leaving the equation as a separate hypothesis) so every later occurrence is the
  -- SAME term syntactically — `xperm_hyp`'s atom matching needs literal/defeq sameness,
  -- not just provable equality.
  set contentLen : Word := BitVec.ofNat 64 len with hcontentLen
  have hcp : (srcBase + BitVec.ofNat 64 (srcOff + len)) - contentLen =
      srcBase + BitVec.ofNat 64 srcOff := by rw [hcontentLen]; bv_omega
  -- idx 5 (base+20): SUB x10 x10 x12.  base+20 → base+24.
  have hsub0 := sub_spec_gen_rd_eq_rs1_within .x10 .x12
    (srcBase + BitVec.ofNat 64 (srcOff + len)) contentLen (base + 20) (by decide)
  rw [hcp] at hsub0
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.SUB .x10 .x10 .x12) a = some i →
      CR a = some i :=
    fun a i h => CodeReq.union_mono_left a i
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 5 (base + 20)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hA := cpsTripleWithin_extend_code hmono5 hsub0
  rw [show (base + 20 + 4 : Word) = base + 24 from by bv_omega] at hA
  have hA' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
      (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
    (by pcFree) hA
  -- idx 6 (base+24): MV x11 x12.  base+24 → base+28.
  have hmv11 := mv_spec_gen_within .x11 .x12 contentLen (0 : Word) (base + 24) (by decide)
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.MV .x11 .x12) a = some i →
      CR a = some i :=
    fun a i h => CodeReq.union_mono_left a i
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 6 (base + 24)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hB := cpsTripleWithin_extend_code hmono6 hmv11
  rw [show (base + 24 + 4 : Word) = base + 28 from by bv_omega] at hB
  have hB' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) **
      (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) **
      bytesRegion srcBase srcBytes)
    (by pcFree) hB
  -- idx 7 (base+28): MV x6 x10 — pin t1 = content_ptr.  base+28 → base+32.
  have hmv6 := mv_spec_gen_within .x6 .x10 (srcBase + BitVec.ofNat 64 srcOff) t1Old (base + 28)
    (by decide)
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.MV .x6 .x10) a = some i →
      CR a = some i :=
    fun a i h => CodeReq.union_mono_left a i
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 7 (base + 28)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hC := cpsTripleWithin_extend_code hmono7 hmv6
  rw [show (base + 28 + 4 : Word) = base + 32 from by bv_omega] at hC
  have hC' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ contentLen) ** (.x12 ↦ᵣ contentLen) ** (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) **
      (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
    (by pcFree) hC
  -- idx 8 (base+32): jal ra, rlp_content_to_u64.  base+32 → base+36.
  have halign := field0_halign base hbase0
  have hoffset := field0_hoffset base
  have hdisj : (CodeReq.singleton (base + 32) (.JAL .x1 (1504 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + (1536 : Word))) := by crDisjoint
  -- The extra frame carried across the call (x0/bytesRegion are already part of
  -- `rlp_content_to_u64_success_spec_within`'s own contract, so they are not repeated here).
  -- The call's own return value is kept as `base + 32 + 4` (not the equal-but-not-
  -- syntactically-identical `base + 36`) so it matches `cpsCallWithin`'s literal
  -- `callerPC + 4` exit expression without needing a defeq/rewrite step.
  have hcallee_raw := rlp_content_to_u64_success_spec_within (base + (1536 : Word)) srcBase
    (base + 32 + 4) t0Old (srcBase + BitVec.ofNat 64 srcOff) t2Old t3Old srcBytes srcOff len
    hlen0 hlen8 hsalign hsoff hcanon hslen hsover hsvalid
  have hcallee_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ contentLen) ** (.x13 ↦ᵣ savedRa) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old))
    (by pcFree) hcallee_raw
  have hPrest : (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
      ((.x12 ↦ᵣ contentLen) ** (.x13 ↦ᵣ savedRa) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old))).pcFree := by pcFree
  have hcall := WP.cpsCallWithin (offset := (1504 : BitVec 21)) (vOld := x1Val) hoffset halign
    hPrest hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee_framed)
  have hmono8 : ∀ a i,
      ((CodeReq.singleton (base + 32) (.JAL .x1 (1504 : BitVec 21))).union
        (rlp_content_to_u64_code (base + (1536 : Word)))) a = some i → CR a = some i :=
    CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.singleton_mono
          (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 8 (base + 32)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
      (CodeReq.mono_union_right (rlp_field0_to_u64_wrapper_content_disjoint base)
        (fun _ _ h => h))
  have hD := cpsTripleWithin_extend_code hmono8 hcall
  rw [show (base + 32 + 4 : Word) = base + 36 from by bv_omega] at hD
  -- idx 9 (base+36): MV x1 x13 — restore caller ra.  base+36 → base+40.
  have hmv1 := mv_spec_gen_within .x1 .x13 savedRa (base + 36) (base + 36) (by decide)
  have hmono9 : ∀ a i, CodeReq.singleton (base + 36) (.MV .x1 .x13) a = some i →
      CR a = some i :=
    fun a i h => CodeReq.union_mono_left a i
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 9 (base + 36)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hE := cpsTripleWithin_extend_code hmono9 hmv1
  rw [show (base + 36 + 4 : Word) = base + 40 from by bv_omega] at hE
  have hE' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ contentLen) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hE
  -- idx 10 (base+40): ret.  base+40 → savedRa &&& ~~~1.
  have hret := jalr_x0_spec_gen_within .x1 savedRa (0 : BitVec 12) (base + 40)
  simp only [signExtend12_0] at hret
  rw [show (savedRa + 0 : Word) = savedRa from by bv_omega] at hret
  have hmono10 : ∀ a i, CodeReq.singleton (base + 40) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      CR a = some i :=
    fun a i h => CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 10 (base + 40)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hF := cpsTripleWithin_extend_code hmono10 hret
  have hF' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ contentLen) ** (.x13 ↦ᵣ savedRa) ** regOwn .x5 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hF
  -- Compose A ⨾ B ⨾ C ⨾ D(call) ⨾ E ⨾ F.
  -- `refine ... ?_ hX hY` unifies `Q1`/`Q2` from the already-concrete `hX`/`hY` before
  -- the leftover permutation goal is handed to `xperm_hyp`.
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hA' hB'; intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hC'; intro h hp; xperm_hyp hp
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hD; intro h hp; xperm_hyp hp
  have s4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s3 hE'; intro h hp; xperm_hyp hp
  have s5 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s4 hF'; intro h hp; xperm_hyp hp
  refine cpsTripleWithin_mono_nSteps (by ring_nf; omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s5)

end EvmAsm.Rv64.RLP
