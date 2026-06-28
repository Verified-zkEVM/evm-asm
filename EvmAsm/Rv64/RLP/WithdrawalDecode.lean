/-
  EvmAsm.Rv64.RLP.WithdrawalDecode

  A verified, strict, single-pass walk-based drop-in for the codegen guest
  `withdrawal_decode`: parse an RLP withdrawal `[index, validator_index, address, amount]`
  and write the 48-byte struct. Unlike the existing assembly (four `rlp_list_nth_item`
  re-scans), this makes one left-to-right pass with `rlp_walk_init` + `rlp_walk_next` +
  strict `rlp_content_to_u64`, and is proved to coincide with the strict pure
  `EvmAsm.EL.decodeWithdrawal`.

  `withdrawal_decode` is the first **non-leaf** verified routine: it preserves callee-saved
  registers across the calls, so it uses a stack frame (modeled as `↦ₘ` cells), and invokes
  the verified leaves via `cpsCallWithin`.

  Built block-by-block: each segment is a `cpsTripleWithin` proved here and composed.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.CPSCall
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.WalkDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- **Prologue.** Push a 32-byte frame, save `ra` and callee-saved `s0/s1/s2`, and move the
    output-struct pointer (`a2`) into `s0`. Registers: `sp = x2`, `ra = x1`, `s0 = x8`,
    `s1 = x9`, `s2 = x18`, `a2 = x12`. -/
def wd_prologue : List Instr :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),   -- addi sp, sp, -32
    .SD .x2 .x1 (0 : BitVec 12),        -- sd ra, 0(sp)
    .SD .x2 .x8 (8 : BitVec 12),        -- sd s0, 8(sp)
    .SD .x2 .x9 (16 : BitVec 12),       -- sd s1, 16(sp)
    .SD .x2 .x18 (24 : BitVec 12),      -- sd s2, 24(sp)
    .MV .x8 .x12 ]                       -- mv s0, a2

/-- `CodeReq` of the prologue at `base`. -/
def wd_prologue_code (base : Word) : CodeReq := CodeReq.ofProg base wd_prologue

theorem wd_prologue_length : wd_prologue.length = 6 := rfl

/-- The prologue saves `ra`/`s0`/`s1`/`s2` into the freshly-pushed frame and sets `s0` to the
    output-struct pointer, reaching `base + 24` (the first instruction after the prologue). -/
theorem wd_prologue_spec (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 : Word) :
    cpsTripleWithin 6 base (base + 24) (wd_prologue_code base)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raVal) **
        (.x8 ↦ᵣ structPtr) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) := by
  have hadd := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) base (by decide)
  have hsd0 := sd_spec_gen_within .x2 .x1 (sp0 + signExtend12 (-32 : BitVec 12)) raVal m0
    (0 : BitVec 12) (base + 4)
  have hsd1 := sd_spec_gen_within .x2 .x8 (sp0 + signExtend12 (-32 : BitVec 12)) s0Old m1
    (8 : BitVec 12) (base + 8)
  have hsd2 := sd_spec_gen_within .x2 .x9 (sp0 + signExtend12 (-32 : BitVec 12)) s1Old m2
    (16 : BitVec 12) (base + 12)
  have hsd3 := sd_spec_gen_within .x2 .x18 (sp0 + signExtend12 (-32 : BitVec 12)) s2Old m3
    (24 : BitVec 12) (base + 16)
  have hmv := mv_spec_gen_within .x8 .x12 structPtr s0Old (base + 20) (by decide)
  simp only [signExtend12_0] at hsd0
  runBlock hadd hsd0 hsd1 hsd2 hsd3 hmv

/-- **Call block: `rlp_content_to_u64`.** A `jal ra` at `callerPC` into the verified
    `rlp_content_to_u64` (appended at `calleeEntry = callerPC + sext offset`) decodes the
    `len`-byte content at `srcBase + srcOff` and returns to `callerPC + 4` with the 4-way status
    result. Establishes the `cpsCallWithin` pattern the scalar-field blocks reuse. -/
theorem wd_call_content_to_u64
    (callerPC calleeEntry srcBase vOld t0Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_content_to_u64_code calleeEntry))
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length) (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (1 + (7 * len + 11)) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_content_to_u64_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
         (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (callerPC + 4)) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
            (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) := by
  have hcallee := rlp_content_to_u64_spec_within calleeEntry srcBase (callerPC + 4) t0Old t2Old
    t3Old srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  -- `cpsCallWithin` fixes the expected callee `Pre = (x1 ↦ callerPC+4) ** Prest` from the goal;
  -- reorder the callee's precondition (`x1` is mid-list) to that form via `xperm_hyp`.
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee)

/-! ## The self-contained drop-in program

`withdrawal_decode_prog` is a single-pass, walk-based parse of an RLP withdrawal into the
48-byte output struct, **self-contained**: the verified leaf programs `rlp_walk_init_prog`,
`rlp_walk_next_prog`, `rlp_content_to_u64_prog` are appended after the 83-instruction glue, and
the glue's `JAL`s target them at concrete PC-relative offsets (since `emitProgram` renders
`JAL` as `.+N`). Layout (instruction indices):

  glue            0  .. 82   (83 instrs)
  rlp_walk_init   83 .. 135  (53)
  rlp_walk_next   136 .. 238 (103)
  rlp_content_to_u64  239 .. 260 (22)

Calling convention (drop-in identical to the old `withdrawal_decode`): `a0 = rlp ptr`,
`a1 = rlp len`, `a2 = struct out ptr`; on return `a0 = 0` success / `a0 = 1` failure;
`ra`/`s0`/`s1`/`s2` preserved via a 32-byte frame. Registers: `s0 = struct`, `s1 = cursor`,
`s2 = end`, `t0 = x5`, `t1 = x6` (also the `rlp_content_to_u64` content pointer). -/

/-- The 83-instruction glue: prologue, `walk_init`, four field decodes (`walk_next` →
    reject-list → `content_to_u64`/20-byte copy → store → advance), an exact-arity check
    (a 5th `walk_next` must report end-of-list, status 2), then success/fail epilogue. -/
def withdrawal_decode_glue : List Instr :=
  [ -- prologue (0..5)
    .ADDI .x2 .x2 (-32 : BitVec 12),        -- 0  addi sp, sp, -32
    .SD .x2 .x1 (0 : BitVec 12),             -- 1  sd ra, 0(sp)
    .SD .x2 .x8 (8 : BitVec 12),             -- 2  sd s0, 8(sp)
    .SD .x2 .x9 (16 : BitVec 12),            -- 3  sd s1, 16(sp)
    .SD .x2 .x18 (24 : BitVec 12),           -- 4  sd s2, 24(sp)
    .MV .x8 .x12,                            -- 5  mv s0, a2  (struct out)
    -- walk_init (6..9)
    .JAL .x1 (308 : BitVec 21),              -- 6  jal ra, rlp_walk_init  (→ 83)
    .BNE .x12 .x0 (276 : BitVec 13),         -- 7  bnez a2, fail          (→ 76)
    .MV .x9 .x10,                            -- 8  mv s1, a0  (cursor)
    .MV .x18 .x11,                           -- 9  mv s2, a1  (end)
    -- field 0: index @ struct+0 (10..23)
    .MV .x10 .x9,                            -- 10 mv a0, s1
    .MV .x11 .x18,                           -- 11 mv a1, s2
    .JAL .x1 (496 : BitVec 21),              -- 12 jal ra, rlp_walk_next  (→ 136)
    .BNE .x11 .x0 (252 : BitVec 13),         -- 13 bnez a1, fail          (→ 76)
    .LBU .x5 .x9 (0 : BitVec 12),            -- 14 lbu t0, 0(s1)  (prefix)
    .LI .x6 (192 : Word),                    -- 15 li t1, 0xc0
    .BGEU .x5 .x6 (240 : BitVec 13),         -- 16 bgeu t0, t1, fail (reject list) (→ 76)
    .MV .x9 .x10,                            -- 17 mv s1, a0  (cursor := advanced)
    .SUB .x10 .x9 .x12,                      -- 18 sub a0, s1, a2  (contentPtr)
    .MV .x11 .x12,                           -- 19 mv a1, a2  (contentLen)
    .MV .x6 .x10,                            -- 20 mv t1, a0  (x6 = contentPtr)
    .JAL .x1 (872 : BitVec 21),              -- 21 jal ra, rlp_content_to_u64 (→ 239)
    .BNE .x11 .x0 (216 : BitVec 13),         -- 22 bnez a1, fail          (→ 76)
    .SD .x8 .x10 (0 : BitVec 12),            -- 23 sd a0, 0(s0)  (index)
    -- field 1: validator_index @ struct+8 (24..37)
    .MV .x10 .x9,                            -- 24
    .MV .x11 .x18,                           -- 25
    .JAL .x1 (440 : BitVec 21),              -- 26 walk_next (→ 136)
    .BNE .x11 .x0 (196 : BitVec 13),         -- 27 fail (→ 76)
    .LBU .x5 .x9 (0 : BitVec 12),            -- 28
    .LI .x6 (192 : Word),                    -- 29
    .BGEU .x5 .x6 (184 : BitVec 13),         -- 30 fail (→ 76)
    .MV .x9 .x10,                            -- 31
    .SUB .x10 .x9 .x12,                      -- 32
    .MV .x11 .x12,                           -- 33
    .MV .x6 .x10,                            -- 34
    .JAL .x1 (816 : BitVec 21),              -- 35 content_to_u64 (→ 239)
    .BNE .x11 .x0 (160 : BitVec 13),         -- 36 fail (→ 76)
    .SD .x8 .x10 (8 : BitVec 12),            -- 37 sd a0, 8(s0)
    -- field 2: address (20 bytes) @ struct+16 (38..54)
    .MV .x10 .x9,                            -- 38
    .MV .x11 .x18,                           -- 39
    .JAL .x1 (384 : BitVec 21),              -- 40 walk_next (→ 136)
    .BNE .x11 .x0 (140 : BitVec 13),         -- 41 fail (→ 76)
    .LBU .x5 .x9 (0 : BitVec 12),            -- 42
    .LI .x6 (192 : Word),                    -- 43
    .BGEU .x5 .x6 (128 : BitVec 13),         -- 44 reject list (→ 76)
    .LI .x6 (20 : Word),                     -- 45 li t1, 20
    .BNE .x12 .x6 (120 : BitVec 13),         -- 46 if contentLen != 20, fail (→ 76)
    .MV .x9 .x10,                            -- 47 mv s1, a0 (cursor := advanced)
    .SUB .x10 .x9 .x12,                      -- 48 sub a0, s1, a2 (contentPtr)
    .LD .x5 .x10 (0 : BitVec 12),            -- 49 ld t0, 0(contentPtr)
    .SD .x8 .x5 (16 : BitVec 12),            -- 50 sd t0, 16(s0)
    .LD .x5 .x10 (8 : BitVec 12),            -- 51 ld t0, 8(contentPtr)
    .SD .x8 .x5 (24 : BitVec 12),            -- 52 sd t0, 24(s0)
    .LWU .x5 .x10 (16 : BitVec 12),          -- 53 lwu t0, 16(contentPtr)
    .SW .x8 .x5 (32 : BitVec 12),            -- 54 sw t0, 32(s0)
    -- field 3: amount @ struct+40 (55..68)
    .MV .x10 .x9,                            -- 55
    .MV .x11 .x18,                           -- 56
    .JAL .x1 (316 : BitVec 21),              -- 57 walk_next (→ 136)
    .BNE .x11 .x0 (72 : BitVec 13),          -- 58 fail (→ 76)
    .LBU .x5 .x9 (0 : BitVec 12),            -- 59
    .LI .x6 (192 : Word),                    -- 60
    .BGEU .x5 .x6 (60 : BitVec 13),          -- 61 fail (→ 76)
    .MV .x9 .x10,                            -- 62
    .SUB .x10 .x9 .x12,                      -- 63
    .MV .x11 .x12,                           -- 64
    .MV .x6 .x10,                            -- 65
    .JAL .x1 (692 : BitVec 21),              -- 66 content_to_u64 (→ 239)
    .BNE .x11 .x0 (36 : BitVec 13),          -- 67 fail (→ 76)
    .SD .x8 .x10 (40 : BitVec 12),           -- 68 sd a0, 40(s0)
    -- exact-arity: a 5th walk_next must report end-of-list (status 2) (69..73)
    .MV .x10 .x9,                            -- 69
    .MV .x11 .x18,                           -- 70
    .JAL .x1 (260 : BitVec 21),              -- 71 walk_next (→ 136)
    .LI .x6 (2 : Word),                      -- 72 li t1, 2
    .BNE .x11 .x6 (12 : BitVec 13),          -- 73 if status != 2, fail (→ 76)
    -- success (74..75)
    .LI .x10 (0 : Word),                     -- 74 li a0, 0
    .JAL .x0 (8 : BitVec 21),                -- 75 j ret (→ 77)
    -- fail (76)
    .LI .x10 (1 : Word),                     -- 76 li a0, 1
    -- epilogue / ret (77..82)
    .LD .x1 .x2 (0 : BitVec 12),             -- 77 ld ra, 0(sp)
    .LD .x8 .x2 (8 : BitVec 12),             -- 78 ld s0, 8(sp)
    .LD .x9 .x2 (16 : BitVec 12),            -- 79 ld s1, 16(sp)
    .LD .x18 .x2 (24 : BitVec 12),           -- 80 ld s2, 24(sp)
    .ADDI .x2 .x2 (32 : BitVec 12),          -- 81 addi sp, sp, 32
    .JALR .x0 .x1 (0 : BitVec 12) ]          -- 82 ret

/-- The full self-contained drop-in: glue ⧺ the three verified leaf programs. The glue's
    `JAL`s target `rlp_walk_init` (idx 83), `rlp_walk_next` (idx 136), `rlp_content_to_u64`
    (idx 239) at the offsets above. -/
def withdrawal_decode_prog : List Instr :=
  withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog

theorem withdrawal_decode_glue_length : withdrawal_decode_glue.length = 83 := rfl

theorem withdrawal_decode_prog_length : withdrawal_decode_prog.length = 261 := by
  simp only [withdrawal_decode_prog, List.length_append, withdrawal_decode_glue_length,
    rlp_walk_init_prog_length, rlp_walk_next_prog_length, rlp_content_to_u64_prog_length]

end EvmAsm.Rv64.RLP
