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
    field 0 · `2` scalar too long (`rlp_content_to_u64` status 2).

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
  unified `rlp_field0_to_u64_spec_within` top theorem with a three-way
  disjunctive postcondition (success / status 1 / 2), per the
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

private theorem field0_ult_lt {a b : Word} (h : BitVec.ult a b = true) :
    a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem field0_not_ult_le {a b : Word} (h : ¬ BitVec.ult a b = true) :
    b.toNat ≤ a.toNat := by
  simp [BitVec.ult] at h
  exact h

private theorem field0_spanStart_longString {base : Word} {off endOff : Nat}
    {next header payload len : Word}
    (hheader1 : 1 ≤ header.toNat) (hheader9 : header.toNat ≤ 9)
    (hfit1 : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
      ((base + BitVec.ofNat 64 off) + header) = true)
    (hfit2 : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff) -
      ((base + BitVec.ofNat 64 off) + header)) payload = true)
    (hnext : next = ((base + BitVec.ofNat 64 off) + header) + payload)
    (hlen : len = payload) (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
      (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit1' := field0_not_ult_le hfit1
  have hfit2' := field0_not_ult_le hfit2
  constructor <;> bv_omega

private theorem field0_spanStart_shortList {base : Word} {off endOff : Nat}
    {next span len : Word}
    (hspan1 : 1 ≤ span.toNat) (hspan56 : span.toNat ≤ 56)
    (hfit : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff) -
      (base + BitVec.ofNat 64 off)) span = true)
    (hnext : next = (base + BitVec.ofNat 64 off) + span)
    (hlen : len = span) (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
      (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit' := field0_not_ult_le hfit
  constructor <;> bv_omega

private theorem field0_spanStart_longList {base : Word} {off endOff : Nat}
    {next header payload len : Word}
    (hheader1 : 1 ≤ header.toNat) (hheader9 : header.toNat ≤ 9)
    (hfit1 : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
      ((base + BitVec.ofNat 64 off) + header) = true)
    (hfit2 : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff) -
      ((base + BitVec.ofNat 64 off) + header)) payload = true)
    (hnext : next = ((base + BitVec.ofNat 64 off) + header) + payload)
    (hlen : len = header + payload) (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
      (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit1' := field0_not_ult_le hfit1
  have hfit2' := field0_not_ult_le hfit2
  constructor <;> bv_omega

private theorem field0_reassocLongList (cursor header payload : Word) :
    cursor + (header + payload + 1) = (cursor + (header + 1)) + payload := by
  bv_omega

private theorem field0_addRotate (header payload : Word) :
    header + payload + 1 = (header + 1) + payload := by
  bv_omega

/-- Core-layer content-window bridge for an accepted walk item.  This is the
pure fact needed to feed `next - len` and `len` to the scalar decoder without
importing the Codegen-layer walk-loop development. -/
theorem rlpItemDecode_field0_content_span {bytes : List (BitVec 8)} {base : Word}
    {off endOff : Nat} {next len : Word}
    (h : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) next len)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    next - len = base + BitVec.ofNat 64 ((next - len - base).toNat) ∧
    off ≤ (next - len - base).toNat ∧
    (next - len - base).toNat + len.toNat ≤ endOff := by
  have hrep : next - len = base + BitVec.ofNat 64 ((next - len - base).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  refine ⟨hrep, ?_⟩
  obtain ⟨b, _hb, hd⟩ := h
  have hb256 : (b.zeroExtend 64).toNat < 256 := by bv_omega
  rcases hd with ⟨_hp80, hin, hnext, hlen⟩ |
      ⟨hge80, _hltb8, _hcanon, hfit, hnext, hlen⟩ |
      ⟨hgeb8, hltc0, _hlead, _hmin, hfit1, hfit2, hnext, hlen⟩ |
      ⟨hgec0, hltf8, hfit, hnext, hlen⟩ |
      ⟨hgef8, _hlead, _hmin, hfit1, hfit2, hnext, hlen⟩
  · have hin' := field0_ult_lt hin
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hnext
    subst hlen
    constructor <;> bv_omega
  · have hfit' := field0_ult_lt hfit
    have hge' := field0_not_ult_le hge80
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hnext
    subst hlen
    constructor <;> bv_omega
  · have hge' := field0_not_ult_le hgeb8
    have hlt' := field0_ult_lt hltc0
    have hheader1 : 1 ≤ ((b.zeroExtend 64 - (0xb7 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    have hheader9 : ((b.zeroExtend 64 - (0xb7 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat ≤ 9 := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    exact field0_spanStart_longString hheader1 hheader9 hfit1 hfit2 hnext hlen hoffle hover
  · have hge' := field0_not_ult_le hgec0
    have hlt' := field0_ult_lt hltf8
    have hspan1 : 1 ≤ ((b.zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    have hspan56 : ((b.zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat ≤ 56 := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    exact field0_spanStart_shortList hspan1 hspan56 hfit hnext hlen hoffle hover
  · have hge' := field0_not_ult_le hgef8
    have hheader1 : 1 ≤ ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word)).toNat := by
      bv_omega
    have hheader9 : ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word)).toNat ≤ 9 := by
      bv_omega
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hnext hlen hfit1 hfit2
    rw [field0_reassocLongList] at hnext
    rw [field0_addRotate] at hlen
    exact field0_spanStart_longList hheader1 hheader9 hfit1 hfit2 hnext hlen hoffle hover

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

/-- Compose the wrapper's index-8 content decoder call with an arbitrary
verified postcondition, lifted into the complete fixed-offset image. -/
theorem rlp_field0_to_u64_call_content
    {nSteps : Nat} {Prest Q : Assertion} (base oldRa : Word)
    (hbase0 : base &&& (1 : Word) = 0) (hpre : Prest.pcFree)
    (hcallee : cpsTripleWithin nSteps (base + (1536 : Word))
      ((base + 32 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code (base + (1536 : Word)))
      ((.x1 ↦ᵣ (base + 32 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + nSteps) (base + 32) (base + 36)
      (rlp_field0_to_u64_full_code base) ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have hdisj : (CodeReq.singleton (base + 32) (.JAL .x1 (1504 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + (1536 : Word))) := by crDisjoint
  have hcall := WP.cpsCallWithin (offset := (1504 : BitVec 21)) (vOld := oldRa)
    (field0_hoffset base) (field0_halign base hbase0) hpre hdisj hcallee
  have hleftContent : ((rlp_field0_to_u64_code base).union
      (rlp_walk_init_code (base + (256 : Word)))).Disjoint
      (rlp_content_to_u64_code (base + (1536 : Word))) := by crDisjoint
  have hmono : ∀ a i,
      ((CodeReq.singleton (base + 32) (.JAL .x1 (1504 : BitVec 21))).union
        (rlp_content_to_u64_code (base + (1536 : Word)))) a = some i →
        rlp_field0_to_u64_full_code base a = some i :=
    CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
        (CodeReq.singleton_mono
          (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 8 (base + 32)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num)
            (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h)))
      (fun a i h => CodeReq.mono_union_right hleftContent
        (CodeReq.mono_union_right (rlp_field0_to_u64_walkNext_content_disjoint base)
          (fun _ _ h' => h')) a i h)
  rw [show (base + 32 + 4 : Word) = base + 36 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code hmono hcall


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


/-! ## Successful list-init handoff to the unified first-item walk. -/

def rlpField0NextCalleeCommon (base srcBase : Word)
    (srcBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 16)) **
  bytesRegion srcBase srcBytes

def rlpField0NextCommon (base srcBase savedRa : Word)
    (srcBytes : List (BitVec 8)) : Assertion :=
  rlpField0NextCalleeCommon base srcBase srcBytes ** (.x13 ↦ᵣ savedRa)

def rlpField0NextOutcome (srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion := fun h =>
  rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
  (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
  (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
      (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
      (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
      (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
      (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h)

/-- A successful `walk_init` status falls through index 2 and calls the
unified `walk_next`, exposing its complete six-way outcome at index 4. -/
theorem rlp_field0_to_u64_walk_next_call_spec_within
    (base srcBase savedRa endPtr v5 v6 v7 v28 v29 v30 v31 oldRa : Word)
    (srcBytes : List (BitVec 8))
    (srcOff listLen : Nat) (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hoff : srcOff ≤ listLen) :
    cpsTripleWithin 89 (base + 8) (base + 16) (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) ** bytesRegion srcBase srcBytes)
      (rlpField0NextCommon base srcBase savedRa srcBytes **
       rlpField0NextOutcome srcBase endPtr srcBytes srcOff) := by
  have hoffb : srcOff < srcBytes.length := by omega
  have hbr0 := bne_spec_gen_within .x12 .x0 (36 : BitVec 13) (0 : Word) (0 : Word) (base + 8)
  have hmono2 : ∀ a i,
      CodeReq.singleton (base + 8) (.BNE .x12 .x0 (36 : BitVec 13)) a = some i →
        rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 2 (base + 8)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hbr := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
      (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (.x1 ↦ᵣ oldRa) **
      bytesRegion srcBase srcBytes)
    (by pcFree) (cpsBranchWithin_extend_code hmono2 hbr0)
  have hfall := cpsBranchWithin_ntakenPath hbr (fun h hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, _⟩ := hp
    exact h_ne rfl)
  rw [show (base + 8 + 4 : Word) = base + 12 from by bv_omega] at hfall
  have hwn0 := rlp_walk_next_spec_within (base + (768 : Word)) srcBase endPtr
    (base + 12 + 4) (0 : Word) v5 v6 v7 v28 v29 v30 v31 srcBytes srcOff hsalign hoffb (by omega)
    (hvalid srcOff hoffb)
    (fun _ _ => ⟨by omega, by omega, hvalid _ (by omega)⟩)
    (fun hb8 hc0 => by
      have hlo : ((srcBytes[srcOff]'hoffb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hb8 hc0
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
    (fun hf8 => by
      have hlo : ((srcBytes[srcOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hf8
        have h_byte := (srcBytes[srcOff]'hoffb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
  rw [show (base + 12 + 4 : Word) = base + 16 from by bv_omega] at hwn0
  change cpsTripleWithin 87 (base + (768 : Word)) ((base + 16) &&& ~~~(1 : Word))
    (rlp_walk_next_code (base + (768 : Word)))
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ (base + 16)) ** bytesRegion srcBase srcBytes)
    (rlpField0NextCalleeCommon base srcBase srcBytes **
      rlpField0NextOutcome srcBase endPtr srcBytes srcOff) at hwn0
  have hwn1 := cpsTripleWithin_frameR ((.x13 ↦ᵣ savedRa)) (by pcFree) hwn0
  have hwn2 : cpsTripleWithin 87 (base + (768 : Word))
      ((base + 16) &&& ~~~(1 : Word))
      (rlp_walk_next_code (base + (768 : Word)))
      ((.x1 ↦ᵣ (base + 16)) **
       ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes))
      (rlpField0NextCommon base srcBase savedRa srcBytes **
       rlpField0NextOutcome srcBase endPtr srcBytes srcOff) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by unfold rlpField0NextCommon; xperm_hyp hp) hwn1
  have hpreCall :
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes)).pcFree := by
    pcFree
  rw [← show (base + 12 + 4 : Word) = base + 16 from by bv_omega] at hwn2
  have hwn : cpsTripleWithin 88 (base + 12) (base + 16)
      (rlp_field0_to_u64_full_code base)
      ((.x1 ↦ᵣ oldRa) **
       ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes))
      (rlpField0NextCommon base srcBase savedRa srcBytes **
       rlpField0NextOutcome srcBase endPtr srcBytes srcOff) :=
    rlp_field0_to_u64_call_walk_next (nSteps := 87)
      (Prest :=
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
         (.x12 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes))
      (Q := rlpField0NextCommon base srcBase savedRa srcBytes **
        rlpField0NextOutcome srcBase endPtr srcBytes srcOff)
      base oldRa hbase0 hpreCall hwn2
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    extract_pure_deep hp
    obtain ⟨_, hp'⟩ := hp
    xperm_hyp hp') hfall hwn
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hp => hp) hseq)


/-! ## Unified content-decoder return path. -/

/-- Resources and three-way scalar outcome that survive the wrapper's final
`ra` restore and `ret`. -/
def rlpField0ContentRest (srcBase contentLen t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
   ((.x12 ↦ᵣ contentLen) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
    (.x31 ↦ᵣ t6Old)) **
   (fun h =>
     (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
     (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
     (((.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) **
        ⌜0 < len ∧ len ≤ 8⌝) h)))

theorem rlpField0ContentRest_pcFree
    (srcBase contentLen t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) :
    (rlpField0ContentRest srcBase contentLen t4Old t5Old t6Old srcBytes srcOff len).pcFree := by
  unfold rlpField0ContentRest
  apply pcFree_sepConj
  · pcFree
  apply pcFree_sepConj
  · pcFree
  intro h hp
  rcases hp with hp | hp | hp
  · exact (by pcFree :
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝).pcFree) h hp
  · exact (by pcFree :
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝).pcFree) h hp
  · exact (by pcFree :
      ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) **
        ⌜0 < len ∧ len ≤ 8⌝).pcFree) h hp

/-- Starting at the content call, cover all scalar outcomes (success, empty,
too long), then restore the caller's `ra` and return. -/
theorem rlp_field0_to_u64_content_call_spec_within
    (base srcBase savedRa x1Val t0Old x6Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (contentLen : Word) (srcOff len : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcontentLen : contentLen = BitVec.ofNat 64 len) :
    cpsTripleWithin (7 * len + 12) (base + 32) (savedRa &&& ~~~(1 : Word))
      (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ contentLen) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
       (.x28 ↦ᵣ t3Old) ** (.x12 ↦ᵣ contentLen) ** (.x13 ↦ᵣ savedRa) **
       (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
      (rlpField0ContentRest srcBase contentLen t4Old t5Old t6Old srcBytes srcOff len **
       (.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa)) := by
  subst hcontentLen
  have hcallee0 := rlp_content_to_u64_spec_within (base + (1536 : Word)) srcBase
    (base + 32 + 4) t0Old x6Old t2Old t3Old srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  have hcallee1 := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ BitVec.ofNat 64 len) ** (.x13 ↦ᵣ savedRa) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
    (by pcFree) hcallee0
  let Prest : Assertion :=
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) **
      (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x12 ↦ᵣ BitVec.ofNat 64 len) **
      (.x13 ↦ᵣ savedRa) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
  let Q : Assertion :=
    ((.x1 ↦ᵣ (base + 36)) ** (.x13 ↦ᵣ savedRa) **
      rlpField0ContentRest srcBase (BitVec.ofNat 64 len) t4Old t5Old t6Old srcBytes srcOff len)
  have hcallee : cpsTripleWithin (7 * len + 9) (base + (1536 : Word))
      ((base + 32 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code (base + (1536 : Word)))
      ((.x1 ↦ᵣ (base + 32 + 4)) ** Prest) Q :=
    cpsTripleWithin_weaken (fun h hp => by dsimp [Prest] at hp ⊢; xperm_hyp hp)
      (fun h hp => by
        rw [show (base + 32 + 4 : Word) = base + 36 from by bv_omega] at hp
        dsimp [Q, rlpField0ContentRest] at hp ⊢
        xperm_hyp hp) hcallee1
  have hcall := rlp_field0_to_u64_call_content base x1Val hbase0 (by pcFree) hcallee
  have hcall' : cpsTripleWithin (1 + (7 * len + 9)) (base + 32) (base + 36)
      (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) **
       (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x12 ↦ᵣ BitVec.ofNat 64 len) **
       (.x13 ↦ᵣ savedRa) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
       (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) **
       bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ (base + 36)) ** (.x13 ↦ᵣ savedRa) **
       rlpField0ContentRest srcBase (BitVec.ofNat 64 len) t4Old t5Old t6Old srcBytes srcOff len) :=
    cpsTripleWithin_weaken (fun h hp => by dsimp [Prest] at hp ⊢; xperm_hyp hp)
      (fun h hp => by dsimp [Q] at hp; exact hp) hcall
  have hmv1 := mv_spec_gen_within .x1 .x13 savedRa (base + 36) (base + 36) (by decide)
  have hmono9 : ∀ a i, CodeReq.singleton (base + 36) (.MV .x1 .x13) a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 9 (base + 36)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hmv := cpsTripleWithin_frameR
    (rlpField0ContentRest srcBase (BitVec.ofNat 64 len) t4Old t5Old t6Old srcBytes srcOff len)
    (rlpField0ContentRest_pcFree srcBase (BitVec.ofNat 64 len) t4Old t5Old t6Old srcBytes srcOff len)
    (cpsTripleWithin_extend_code hmono9 hmv1)
  rw [show (base + 36 + 4 : Word) = base + 40 from by bv_omega] at hmv
  have hret0 := jalr_x0_spec_gen_within .x1 savedRa (0 : BitVec 12) (base + 40)
  simp only [signExtend12_0] at hret0
  rw [show (savedRa + 0 : Word) = savedRa from by bv_omega] at hret0
  have hmono10 : ∀ a i,
      CodeReq.singleton (base + 40) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
        rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 10 (base + 40)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hret := cpsTripleWithin_frameR
    (rlpField0ContentRest srcBase (BitVec.ofNat 64 len) t4Old t5Old t6Old srcBytes srcOff len **
      (.x13 ↦ᵣ savedRa))
    (pcFree_sepConj
      (rlpField0ContentRest_pcFree srcBase (BitVec.ofNat 64 len) t4Old t5Old t6Old
        srcBytes srcOff len) pcFree_regIs)
    (cpsTripleWithin_extend_code hmono10 hret0)
  have hs1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcall' hmv
  have hs2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hs1 hret
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) hs2)


end EvmAsm.Rv64.RLP
