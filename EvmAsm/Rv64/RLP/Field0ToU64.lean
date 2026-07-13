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
import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.BitAux
import EvmAsm.Rv64.Tactics.WP
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.WP

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

/-- Generic wrapper epilogue (idx 9..10).  Keeping the callee result in an
arbitrary PC-free assertion lets the unified content decoder carry all four
of its semantic outcomes through `ra` restoration without selecting one. -/
theorem rlp_field0_to_u64_restore_ret_spec_within
    (base savedRa : Word) (result : Assertion) (hresult : result.pcFree) :
    cpsTripleWithin 2 (base + 36) (savedRa &&& ~~~1) (rlp_field0_to_u64_code base)
      ((.x1 ↦ᵣ (base + 36)) ** (.x13 ↦ᵣ savedRa) ** result)
      ((.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa) ** result) := by
  have hmv := mv_spec_gen_within .x1 .x13 savedRa (base + 36) (base + 36) (by decide)
  have hmono9 : ∀ a i, CodeReq.singleton (base + 36) (.MV .x1 .x13) a = some i →
      rlp_field0_to_u64_code base a = some i :=
    fun a i h => CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 9 (base + 36)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h
  have hA := cpsTripleWithin_extend_code hmono9 hmv
  rw [show (base + 36 + 4 : Word) = base + 40 from by bv_omega] at hA
  have hA' := cpsTripleWithin_frameR result hresult hA
  have hret := jalr_x0_spec_gen_within .x1 savedRa (0 : BitVec 12) (base + 40)
  simp only [signExtend12_0] at hret
  rw [show (savedRa + 0 : Word) = savedRa from by bv_omega] at hret
  have hmono10 : ∀ a i,
      CodeReq.singleton (base + 40) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      rlp_field0_to_u64_code base a = some i :=
    fun a i h => CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 10 (base + 40)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h
  have hB := cpsTripleWithin_extend_code hmono10 hret
  have hB' := cpsTripleWithin_frameR ((.x13 ↦ᵣ savedRa) ** result)
    (pcFree_sepConj (by pcFree) hresult) hB
  have hs := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hA' hB'
    intro h hp
    xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hp => hp) hs

/-- All semantic outcomes of `rlp_content_to_u64`, together with the wrapper
state that must survive its call.  `x1` is deliberately excluded: the call
rule exposes the return address separately for the generic epilogue above. -/
def rlpField0ContentResult (srcBase contentLen t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion srcBase srcBytes) **
  (fun h =>
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
      ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
    (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
      (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h)) **
  ((.x12 ↦ᵣ contentLen) ** (.x29 ↦ᵣ t4Old) **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))

theorem rlpField0ContentResult_pcFree
    (srcBase contentLen t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) :
    (rlpField0ContentResult srcBase contentLen t4Old t5Old t6Old
      srcBytes srcOff len).pcFree := by
  unfold rlpField0ContentResult
  let outcomes : Assertion := fun h =>
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
      ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
    (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
      (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h)
  have houtcomes : outcomes.pcFree := by
    intro h hp
    rcases hp with hp | hp | hp | hp
    · exact (by pcFree : (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) **
        ⌜8 < len⌝)).pcFree) h hp
    · exact (by pcFree : (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
        ⌜len = 0⌝)).pcFree) h hp
    · exact (by pcFree : (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝)).pcFree) h hp
    · exact (by pcFree : (((.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝)).pcFree) h hp
  change ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) ** outcomes **
    ((.x12 ↦ᵣ contentLen) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))).pcFree
  letI : Assertion.PCFree (bytesRegion srcBase srcBytes) :=
    ⟨bytesRegion_pcFree srcBase srcBytes⟩
  exact pcFree_sepConj (by pcFree) (pcFree_sepConj houtcomes (by pcFree))

/-- Unified content call at idx 8.  Unlike the earlier success-only helper,
this consumes the unified callee theorem and preserves its complete outcome
disjunction for the wrapper epilogue. -/
theorem rlp_field0_to_u64_content_call_unified_spec_within
    (base srcBase savedRa x1Old t0Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hbase0 : base &&& (1 : Word) = 0) (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (7 * len + 12) (base + 32) (base + 36)
      ((rlp_field0_to_u64_code base).union
        (rlp_content_to_u64_code (base + (1536 : Word))))
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ BitVec.ofNat 64 len) **
        (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) **
        (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Old) **
        bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ (base + 36)) ** (.x13 ↦ᵣ savedRa) **
        rlpField0ContentResult srcBase (BitVec.ofNat 64 len)
          t4Old t5Old t6Old srcBytes srcOff len) := by
  have halign := field0_halign base hbase0
  have hoffset := field0_hoffset base
  have hdisj : (CodeReq.singleton (base + 32) (.JAL .x1 (1504 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + (1536 : Word))) := by crDisjoint
  have hcallee := rlp_content_to_u64_spec_within (base + (1536 : Word)) srcBase
    (base + 32 + 4) t0Old (srcBase + BitVec.ofNat 64 srcOff) t2Old t3Old
    srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  have hcallee_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ BitVec.ofNat 64 len) ** (.x13 ↦ᵣ savedRa) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
    (by pcFree) hcallee
  have hPrest : (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x5 ↦ᵣ t0Old) **
      (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
      ((.x12 ↦ᵣ BitVec.ofNat 64 len) ** (.x13 ↦ᵣ savedRa) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))).pcFree := by
    pcFree
  have hcall := WP.cpsCallWithin (offset := (1504 : BitVec 21)) (vOld := x1Old) hoffset halign
    hPrest hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hp => hp) hcallee_framed)
  have hmono : ∀ a i,
      ((CodeReq.singleton (base + 32) (.JAL .x1 (1504 : BitVec 21))).union
        (rlp_content_to_u64_code (base + (1536 : Word)))) a = some i →
      ((rlp_field0_to_u64_code base).union
        (rlp_content_to_u64_code (base + (1536 : Word)))) a = some i :=
    CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.singleton_mono
          (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 8 (base + 32)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
      (CodeReq.mono_union_right (rlp_field0_to_u64_wrapper_content_disjoint base)
        (fun _ _ h => h))
  have hs := cpsTripleWithin_extend_code hmono hcall
  rw [show (base + 32 + 4 : Word) = base + 36 from by bv_omega] at hs
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hs)
  unfold rlpField0ContentResult at hp ⊢
  xperm_hyp hp

/-- Unified successful-walk tail (idx 5..10): derive the content pointer,
invoke the complete content decoder, restore the caller's `ra`, and return.
The walk succeeded, but content decoding may still produce any of its four
genuine outcomes. -/
theorem rlp_field0_to_u64_content_tail_unified_spec_within
    (base srcBase savedRa x1Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hbase0 : base &&& (1 : Word) = 0) (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (7 * len + 17) (base + 20) (savedRa &&& ~~~1)
      ((rlp_field0_to_u64_code base).union
        (rlp_content_to_u64_code (base + (1536 : Word))))
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ BitVec.ofNat 64 len) **
        (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ x1Old) ** bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa) **
        rlpField0ContentResult srcBase (BitVec.ofNat 64 len)
          t4Old t5Old t6Old srcBytes srcOff len) := by
  set CR := (rlp_field0_to_u64_code base).union
    (rlp_content_to_u64_code (base + (1536 : Word)))
  have hcp : (srcBase + BitVec.ofNat 64 (srcOff + len)) - BitVec.ofNat 64 len =
      srcBase + BitVec.ofNat 64 srcOff := by bv_omega
  have hsub := sub_spec_gen_rd_eq_rs1_within .x10 .x12
    (srcBase + BitVec.ofNat 64 (srcOff + len)) (BitVec.ofNat 64 len)
    (base + 20) (by decide)
  rw [hcp] at hsub
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.SUB .x10 .x10 .x12) a = some i →
      CR a = some i := fun a i h => CodeReq.union_mono_left a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 5 (base + 20)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hA := cpsTripleWithin_extend_code hmono5 hsub
  rw [show (base + 20 + 4 : Word) = base + 24 from by bv_omega] at hA
  have hA' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) **
      (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Old) ** bytesRegion srcBase srcBytes)
    (by pcFree) hA
  have hmv11 := mv_spec_gen_within .x11 .x12 (BitVec.ofNat 64 len)
    (0 : Word) (base + 24) (by decide)
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.MV .x11 .x12) a = some i →
      CR a = some i := fun a i h => CodeReq.union_mono_left a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 6 (base + 24)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hB := cpsTripleWithin_extend_code hmono6 hmv11
  rw [show (base + 24 + 4 : Word) = base + 28 from by bv_omega] at hB
  have hB' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x13 ↦ᵣ savedRa) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Old) **
      bytesRegion srcBase srcBytes) (by pcFree) hB
  have hmv6 := mv_spec_gen_within .x6 .x10
    (srcBase + BitVec.ofNat 64 srcOff) t1Old (base + 28) (by decide)
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.MV .x6 .x10) a = some i →
      CR a = some i := fun a i h => CodeReq.union_mono_left a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 7 (base + 28)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hC := cpsTripleWithin_extend_code hmono7 hmv6
  rw [show (base + 28 + 4 : Word) = base + 32 from by bv_omega] at hC
  have hC' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ BitVec.ofNat 64 len) **
      (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Old) **
      bytesRegion srcBase srcBytes) (by pcFree) hC
  have hD := rlp_field0_to_u64_content_call_unified_spec_within
    base srcBase savedRa x1Old t0Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff len hbase0 hlen64 hsalign hslen hsover hsvalid
  have hE0 := rlp_field0_to_u64_restore_ret_spec_within base savedRa
    (rlpField0ContentResult srcBase (BitVec.ofNat 64 len)
      t4Old t5Old t6Old srcBytes srcOff len)
    (rlpField0ContentResult_pcFree srcBase (BitVec.ofNat 64 len)
      t4Old t5Old t6Old srcBytes srcOff len)
  have hE := cpsTripleWithin_extend_code (cr' := CR)
    (fun a i h => CodeReq.union_mono_left a i h) hE0
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hA' hB'; intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hC'; intro h hp; xperm_hyp hp
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hD; intro h hp; xperm_hyp hp
  have s4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s3 hE; intro h hp; exact hp
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hp => hp) s4)

/-! ## Branch composition slice: idx 4..14, starting at the branch immediately
after `rlp_walk_next` returns (`BNE x11 x0 -> parse_fail`), through either the
success-path call composition proved above or the `parse_fail` fallback.

This exercises the `WP.CFG` branch/leaf layer (`docs/agents/wp-framework.md`):
the `BNE` header becomes a `WP.Branch`, the `parse_fail` tail is synthesized
from its postcondition with `wp_rv64_leaf_synth`, and the two continuations
are joined with `WP.CFG.branch`. The starting state is still a generic
post-`rlp_walk_next` state (`x11` is a free status word, not yet produced by
composing the real `jal ra, rlp_walk_next` call) — composing that call is
left to a follow-up, per the module header's "Remaining work" list. -/

/-- The `parse_fail` leaf body (idx 11..14): on a nonzero `rlp_walk_next`
status, set `a0 = 0`, `a1 = 1`, restore `ra` from `x13`, and return. -/
def rlp_field0_to_u64_parse_fail_prog : List Instr :=
  [ .LI .x10 (0 : Word), .LI .x11 (1 : Word), .MV .x1 .x13, .JALR .x0 .x1 0 ]

theorem rlp_field0_to_u64_parse_fail_prog_length :
    rlp_field0_to_u64_parse_fail_prog.length = 4 := rfl

/-- WP-synthesized `parse_fail` leaf certificate. The `LI x10`/`LI x11`/`MV x1
x13` specs are passed explicitly (in forward execution order) so the
synthesized precondition exposes the *named* old values `advancedOld` /
`walkNextStatusOld` / `x1Old` instead of falling back to `regOwn` — this
keeps the certificate composable with the caller's exact pre-branch register
state without an extra `regIs`-to-`regOwn` conversion at the call site. The
trailing `JALR` is resolved automatically: its only atom (`x1`) is already
pinned to `savedRa` by the preceding `MV`. -/
def rlp_field0_to_u64_parse_fail_exact_cert
    (addr savedRa advancedOld walkNextStatusOld x1Old : Word) :
    WP.CFG.Cert addr (savedRa &&& ~~~1)
      (CodeReq.ofProg addr rlp_field0_to_u64_parse_fail_prog)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x13 ↦ᵣ savedRa) **
        (.x1 ↦ᵣ savedRa)) := by
  unfold rlp_field0_to_u64_parse_fail_prog
  let hLi10 := li_spec_gen_within .x10 advancedOld (0 : Word) addr (by decide)
  let hLi11 := li_spec_gen_within .x11 walkNextStatusOld (1 : Word) (addr + 4) (by decide)
  let hMv := mv_spec_gen_within .x1 .x13 savedRa x1Old (addr + 8) (by decide)
  let hJalr := jalr_x0_spec_gen_within .x1 savedRa (0 : BitVec 12) (addr + 12)
  wp_rv64_leaf_synth hLi10 hLi11 hMv hJalr

/-- The `parse_fail` leaf, lifted from its own minimal `CodeReq.ofProg` into
the full `rlp_field0_to_u64_code base` (idx 11, i.e. `base + 44`). -/
def rlp_field0_to_u64_parse_fail_exact_cert_in_code
    (base savedRa advancedOld walkNextStatusOld x1Old : Word) :
    WP.CFG.Cert (base + 44) (savedRa &&& ~~~1) (rlp_field0_to_u64_code base)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x13 ↦ᵣ savedRa) **
        (.x1 ↦ᵣ savedRa)) :=
  WP.CFG.extendCode
    (rlp_field0_to_u64_parse_fail_exact_cert (base + 44) savedRa advancedOld walkNextStatusOld x1Old)
    (CodeReq.ofProg_mono_sub base (base + 44) rlp_field0_to_u64_prog
      rlp_field0_to_u64_parse_fail_prog 11 (by bv_omega) (by rfl)
      (by rw [rlp_field0_to_u64_prog_length, rlp_field0_to_u64_parse_fail_prog_length])
      (by rw [rlp_field0_to_u64_prog_length]; norm_num))

/--
**`rlp_field0_to_u64` — branch composition** (idx 4..14, `base+16 → savedRa
&&& ~~~1`).

Starting at the branch immediately after `rlp_walk_next` returns (`x10` the
advanced cursor, `x11` a free post-walk status word, `x12` the content
length), this composes the `BNE x11 x0 -> parse_fail` header with the two
open continuations:

* not-taken (`x11 = 0`): the success-path call composition proved above
  (`rlp_field0_to_u64_content_call_success_spec_within`), reaching the
  wrapper's overall success outcome (`x11 = 0`, decoded value in `x10`).
* taken (`x11 ≠ 0`): the `parse_fail` leaf, synthesized with
  `wp_rv64_leaf_synth`, reaching status `x11 = 1`, `x10 = 0`.

The two outcomes are already mutually exclusive by their `x10`/`x11` shape
(`x11 = 0` vs. `x11 = 1`), so the postcondition does not need an extra static
guard atom to disambiguate them; a `WP.CFG.branch`-composed postcondition
cannot carry one anyway, since neither continuation certificate is proved
under an assumption about `walkNextStatus`'s value. The static hypotheses
about `srcBytes`/`srcOff`/`len` mirror the precondition the eventual
`rlp_walk_next` call composition would establish on the success path; per the
`AGENTS.md` spec-design convention they stay in the precondition as static
facts rather than gating which disjunct the postcondition selects. -/
theorem rlp_field0_to_u64_branch_spec_within
    (base srcBase savedRa x1Val t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (advanced contentLen walkNextStatus : Word)
    (srcOff len : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hadvanced : advanced = srcBase + BitVec.ofNat 64 (srcOff + len))
    (hcontentLen : contentLen = BitVec.ofNat 64 len) :
    cpsTripleWithin (7 * len + 18) (base + 16) (savedRa &&& ~~~1)
      ((rlp_field0_to_u64_code base).union (rlp_content_to_u64_code (base + (1536 : Word))))
      ((.x10 ↦ᵣ advanced) ** (.x11 ↦ᵣ walkNextStatus) ** (.x12 ↦ᵣ contentLen) **
        (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
      (fun h =>
        (((.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa) **
          rlpField0ContentResult srcBase contentLen t4Old t5Old t6Old
            srcBytes srcOff len) h) ∨
        ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ contentLen) **
            (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
            (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
            (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes) h) := by
  subst hadvanced; subst hcontentLen
  set CR := (rlp_field0_to_u64_code base).union (rlp_content_to_u64_code (base + (1536 : Word)))
    with hCR
  set contentLen : Word := BitVec.ofNat 64 len with hcontentLen
  -- The BNE header (idx 4, base+16): taken (x11 ≠ 0) -> base+44 (parse_fail);
  -- not-taken (x11 = 0) -> base+20 (idx 5, the success-path entry above).
  have hbr0 := bne_spec_gen_within .x11 .x0 (28 : BitVec 13) walkNextStatus (0 : Word) (base + 16)
  simp only [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide] at hbr0
  rw [show (base + 16 + 28 : Word) = base + 44 from by bv_omega,
      show (base + 16 + 4 : Word) = base + 20 from by bv_omega] at hbr0
  have hbrF := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x12 ↦ᵣ contentLen) **
      (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
    (by pcFree) hbr0
  have hmono4 : ∀ a i,
      (CodeReq.singleton (base + 16) (.BNE .x11 .x0 (28 : BitVec 13))) a = some i →
      CR a = some i :=
    fun a i h => CodeReq.union_mono_left a i
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 4 (base + 16)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num)
        (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)
  have hbrCR := cpsBranchWithin_extend_code hmono4 hbrF
  -- Re-state with the pure status fact moved to the very front of each post.
  -- `extract_pure`'s current bubbling rules (`sepConj_pure_mid_left/right`) only
  -- reach a pure atom buried at depth ≤ 1 in a right-associated `**` chain (the
  -- general depth-≥2 case is a documented gap, GH #1435/evm-asm-22a); putting the
  -- pure at depth 0 sidesteps that gap, since `xperm_hyp` itself is depth-agnostic.
  have hbrCR' :
      cpsBranchWithin 1 (base + 16) CR
        ((.x11 ↦ᵣ walkNextStatus) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x12 ↦ᵣ contentLen) **
          (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
        (base + 44)
        (⌜walkNextStatus ≠ (0 : Word)⌝ **
          (.x11 ↦ᵣ walkNextStatus) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x12 ↦ᵣ contentLen) **
          (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
        (base + 20)
        (⌜walkNextStatus = (0 : Word)⌝ **
          (.x11 ↦ᵣ walkNextStatus) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x12 ↦ᵣ contentLen) **
          (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes) :=
    cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) hbrCR
  let br0 : WP.Branch (base + 16) CR := WP.Branch.ofSpec hbrCR'
  -- The shared join postcondition: a content outcome or wrapper parse failure.
  let finalPost : Assertion := fun h =>
    (((.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa) **
        rlpField0ContentResult srcBase contentLen t4Old t5Old t6Old
          srcBytes srcOff len) h ∨
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ contentLen) **
        (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes) h)
  -- Not-taken continuation: all unified content-decoder outcomes.
  have hsuccess := rlp_field0_to_u64_content_tail_unified_spec_within
    base srcBase savedRa x1Val t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff len hbase0 hlen64 hsalign hslen hsover hsvalid
  let successCert : WP.CFG.Cert (base + 20) (savedRa &&& ~~~1) CR finalPost :=
    WP.CFG.weakenPost (WP.CFG.leaf hsuccess) (fun h hp => Or.inl hp)
  -- Taken continuation: the parse_fail leaf, extended into `CR` and framed
  -- with the registers/bytes the leaf does not touch.
  let failCertRaw0 :=
    WP.CFG.extendCode (cr' := CR)
      (rlp_field0_to_u64_parse_fail_cert base savedRa)
      (fun a i h => CodeReq.union_mono_left a i h)
  let failCertRaw : WP.CFG.Cert (base + 44) (savedRa &&& ~~~1) CR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x13 ↦ᵣ savedRa) ** (.x1 ↦ᵣ savedRa)) :=
    WP.CFG.weakenPost failCertRaw0 (by
      intro h hp
      unfold rlp_field0_to_u64_parse_fail_post at hp
      xperm_hyp hp)
  let failCertInCR : WP.CFG.Cert (base + 44) (savedRa &&& ~~~1) CR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x13 ↦ᵣ savedRa) ** (.x1 ↦ᵣ savedRa)) :=
    WP.CFG.weakenPre
      (pre' := ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) **
        (.x11 ↦ᵣ walkNextStatus) ** (.x13 ↦ᵣ savedRa) ** (.x1 ↦ᵣ x1Val)))
      failCertRaw (by
      intro h hp
      change (regOwn .x10 ** regOwn .x11 ** (.x13 ↦ᵣ savedRa) ** regOwn .x1) h
      have hp1 := sepConj_mono_left (regIs_implies_regOwn .x10) h hp
      have hp2 := sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x11)) h hp1
      have hp3 := sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x1))) h hp2
      exact hp3)
  let failCertFramed :=
    WP.CFG.frameR failCertInCR
      ((.x12 ↦ᵣ contentLen) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      (by pcFree)
  let failCert : WP.CFG.Cert (base + 44) (savedRa &&& ~~~1) CR finalPost :=
    WP.CFG.weakenPost failCertFramed (fun h hp => Or.inr (by xperm_hyp hp))
  -- Stated against the explicit (already-reduced) `post_f`/`post_t` shape rather
  -- than the opaque `br0.post_f`/`br0.post_t` projections, so `extract_pure` sees
  -- a literal `sepConj`/`⌜·⌝` term to rewrite; `WP.CFG.branch` below still accepts
  -- these via defeq against `br0`'s fields.
  have hlinkNotTaken :
      WP.Entails
        (⌜walkNextStatus = (0 : Word)⌝ **
          (.x11 ↦ᵣ walkNextStatus) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x12 ↦ᵣ contentLen) **
          (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
        successCert.pre := by
    dsimp only [successCert, WP.CFG.weakenPost, WP.CFG.leaf, WP.CFG.block,
      WP.Triple.weakenPost, WP.Triple.ofSpec]
    intro h hp
    extract_pure hp
    obtain ⟨heq, hp⟩ := hp
    subst heq
    xperm_hyp hp
  have hlinkTaken :
      WP.Entails
        (⌜walkNextStatus ≠ (0 : Word)⌝ **
          (.x11 ↦ᵣ walkNextStatus) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x12 ↦ᵣ contentLen) **
          (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
        failCert.pre := by
    dsimp only [failCert, failCertFramed, failCertInCR, WP.CFG.weakenPost,
      WP.CFG.frameR, WP.CFG.weakenPre, WP.Triple.weakenPost, WP.Triple.frameR,
      WP.Triple.weakenPre]
    intro h hp
    extract_pure hp
    obtain ⟨_hne, hp⟩ := hp
    xperm_hyp hp
  let hcert := WP.CFG.branch br0 failCert successCert hlinkTaken hlinkNotTaken
  have hns : hcert.nSteps = 1 + Nat.max failCert.nSteps successCert.nSteps := rfl
  have hnsFail : failCert.nSteps = 4 := rfl
  have hnsSuccess : successCert.nSteps = 7 * len + 17 := rfl
  have hs : cpsTripleWithin hcert.nSteps (base + 16) (savedRa &&& ~~~1) CR
      ((.x11 ↦ᵣ walkNextStatus) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x12 ↦ᵣ contentLen) **
        (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes) finalPost := hcert.sound
  refine cpsTripleWithin_mono_nSteps (by
    rw [hns, hnsFail, hnsSuccess]
    have hm : Nat.max 4 (7 * len + 17) = 7 * len + 17 := Nat.max_eq_right (by omega)
    rw [hm]
    omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by exact hp) hs)

end EvmAsm.Rv64.RLP
