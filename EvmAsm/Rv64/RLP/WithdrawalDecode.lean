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
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.CPSCall
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.WalkDecodeBridge
import EvmAsm.EL.Withdrawal

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.EL

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
            (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h))) := by
  have hcallee := rlp_content_to_u64_spec_within calleeEntry srcBase (callerPC + 4) t0Old t2Old
    t3Old srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  -- `cpsCallWithin` fixes the expected callee `Pre = (x1 ↦ callerPC+4) ** Prest` from the goal;
  -- reorder the callee's precondition (`x1` is mid-list) to that form via `xperm_hyp`.
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee)

/-- **Call block: `rlp_walk_next`.** A `jal ra` at `callerPC` into the verified `rlp_walk_next`
    (appended at `calleeEntry`) advances one RLP item and returns to `callerPC + 4` with the 6-way
    status result (`rlpWalkNextOk` on success, or status 2..6 on out-of-bounds/malformed).
    Mirrors `wd_call_content_to_u64`; used at the five `walk_next` call sites. -/
theorem wd_call_walk_next
    (callerPC calleeEntry srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_next_code calleeEntry))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_walk_next_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (callerPC + 4)) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h))) := by
  have hcallee := rlp_walk_next_spec_within calleeEntry srcBase endPtr (callerPC + 4) a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hover hvalid hss hls hll
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

/-- The drop-in body as a `CodeReq` rooted at `base`. -/
abbrev withdrawal_decode_code (base : Word) : CodeReq :=
  CodeReq.ofProg base withdrawal_decode_prog

/-! ## CPS characterization, anchored on the pure `decodeWithdrawal`

The contract below specifies `withdrawal_decode_prog` as a `cpsTripleWithin` whose
postcondition is stated entirely in terms of the pure strict decoder
`EvmAsm.EL.decodeWithdrawal`: on success the program returns `a0 = 0`, `decodeWithdrawal`
of the input bytes is `some w`, and the 48-byte output struct holds `w`; on failure it
returns `a0 = 1` and `decodeWithdrawal` of the input is `none`. Either way the input region
and the callee-saved registers (`s0`/`s1`/`s2`, `ra`, `sp`) are preserved. This is the
`withdrawal_decode_spec_within` target the block-by-block proof discharges. -/

open EvmAsm.EL in
/-- The writable 48-byte output struct, caller-owned with unconstrained content (six dwords). -/
def wd_outOwned (outPtr : Word) : Assertion :=
  memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) **
  memOwn (outPtr + 24) ** memOwn (outPtr + 32) ** memOwn (outPtr + 40)

open EvmAsm.EL in
/-- The 48-byte output struct holding decoded withdrawal `w` whose 20-byte address bytes are
    `d2`: `index` (u64, LE dword) @0, `validator_index` @8, the 20 address bytes @16..36
    (`bytesRegion`, dwords @16/@24/@32 — the high 4 bytes of @32 are the zero pad), `amount`
    @40. The scalar dwords are the little-endian u64 values written by `sd`. -/
def wd_outHolds (outPtr : Word) (w : Withdrawal) (d2 : List Byte) : Assertion :=
  (outPtr ↦ₘ BitVec.ofNat 64 w.index) **
  ((outPtr + 8) ↦ₘ BitVec.ofNat 64 w.validatorIndex) **
  bytesRegion (outPtr + 16) d2 **
  ((outPtr + 40) ↦ₘ BitVec.ofNat 64 w.amount)

open EvmAsm.EL in
/-- The clobbered scratch (`t0..t6`) register-ownership tokens. -/
def wd_scratchOwned : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

open EvmAsm.EL in
/-- The 32-byte stack frame `[sp0-32, sp0)` (four dwords), caller-owned. -/
def wd_frameOwned (sp0 : Word) : Assertion :=
  memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8)

open EvmAsm.EL in
/-- **CPS characterization of `withdrawal_decode_prog` against the pure `decodeWithdrawal`.**

    With the input RLP bytes `srcBytes` in `bytesRegion srcBase srcBytes` (the drop-in is called
    with `a0 = srcBase`, `a1 = |srcBytes|`, `a2 = outPtr`), a pre-zeroed 48-byte output struct,
    a 32-byte stack frame below `sp0`, and the callee-saved registers holding arbitrary old
    values, the routine runs to its return address `raVal &&& ~~~1` in some number of steps and:

    - **succeeds** (`a0 = 0`) exactly with a decoded `w` and address bytes `d2` such that
      `decodeWithdrawal srcBytes = some w`, leaving the output struct holding `w`; or
    - **fails** (`a0 = 1`) with `decodeWithdrawal srcBytes = none`, leaving the output owned.

    In both cases `sp`, `ra`, and `s0`/`s1`/`s2` are restored and the input region is intact;
    `t0..t6` are clobbered. The well-formedness hypotheses (alignment, in-range byte-access
    validity, `|srcBytes| < 2^64`) are the standard side-conditions the verified leaves require. -/
def withdrawal_decode_characterization
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte) : Prop :=
  srcBase.toNat % 8 = 0 →
  outPtr.toNat % 8 = 0 →
  srcBytes.length < 2 ^ 64 →
  srcBase.toNat + srcBytes.length ≤ 2 ^ 64 →
  (∀ k, k < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) →
  ∃ N, cpsTripleWithin N base (raVal &&& ~~~1) (withdrawal_decode_code base)
    -- precondition
    ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
      (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
      (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** wd_frameOwned sp0 **
      bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : Byte)))
    -- postcondition: shared frame + (success ∨ failure), anchored on `decodeWithdrawal`
    (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
      (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** wd_frameOwned sp0 **
      bytesRegion srcBase srcBytes) **
     (fun h =>
       (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
          ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
            ∧ d2.length = 20⌝) h)) ∨
       (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
          ⌜decodeWithdrawal srcBytes = none⌝) h)))

/-! ## M3 proof — block 1: prologue over the full program code

The composition proof of `withdrawal_decode_characterization` runs over
`withdrawal_decode_code base`. The first block is the prologue (idx 0..5), proved here
directly over the full program's `CodeReq` (so it composes with the remaining blocks via
`cpsTripleWithin_seq` without a code-lifting step). -/
theorem wd_decode_prologue (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 : Word) :
    cpsTripleWithin 6 base (base + 24) (withdrawal_decode_code base)
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

/-! ## M3 proof — block 8 (last): epilogue over the full program code

The epilogue (idx 77..82): restore `ra`/`s0`/`s1`/`s2` from the frame, pop the 32-byte frame,
and `ret` to the (restored) return address. Exits to `raSaved &&& ~~~1` — the routine's return
target. The success/fail paths both fall into this block (after `a0` is set). -/
theorem wd_decode_epilogue (base spF raSaved s0Saved s1Saved s2Saved raClob s0Clob s1Clob s2Clob :
    Word) :
    cpsTripleWithin 6 (base + 308) (raSaved &&& ~~~1) (withdrawal_decode_code base)
      ((.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) ** (.x9 ↦ᵣ s1Clob) **
        (.x18 ↦ᵣ s2Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) **
        ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved))
      ((.x2 ↦ᵣ (spF + signExtend12 (32 : BitVec 12))) ** (.x1 ↦ᵣ raSaved) **
        (.x8 ↦ᵣ s0Saved) ** (.x9 ↦ᵣ s1Saved) ** (.x18 ↦ᵣ s2Saved) **
        (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
        ((spF + 24) ↦ₘ s2Saved)) := by
  have hld0 := ld_spec_gen_within .x1 .x2 spF raClob raSaved (0 : BitVec 12) (base + 308) (by decide)
  have hld1 := ld_spec_gen_within .x8 .x2 spF s0Clob s0Saved (8 : BitVec 12) (base + 312) (by decide)
  have hld2 := ld_spec_gen_within .x9 .x2 spF s1Clob s1Saved (16 : BitVec 12) (base + 316) (by decide)
  have hld3 := ld_spec_gen_within .x18 .x2 spF s2Clob s2Saved (24 : BitVec 12) (base + 320) (by decide)
  have haddi := addi_spec_gen_same_within .x2 spF (32 : BitVec 12) (base + 324) (by decide)
  have hret := jalr_x0_spec_gen_within .x1 raSaved (0 : BitVec 12) (base + 328)
  simp only [signExtend12_0] at hld0 hret
  runBlock hld0 hld1 hld2 hld3 haddi hret

/-- **Success tail** (idx 74–75): `li a0, 0` then `j ret` — jump over the fail block to the
    epilogue entry (base+308) with `a0 = 0`. -/
theorem wd_decode_successTail (base a0Old : Word) :
    cpsTripleWithin 2 (base + 296) (base + 308) (withdrawal_decode_code base)
      (.x10 ↦ᵣ a0Old) (.x10 ↦ᵣ (0 : Word)) := by
  have hli := li_spec_gen_within .x10 a0Old (0 : Word) (base + 296) (by decide)
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (base + 300)
  rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide,
      show (base + 300) + (8 : Word) = base + 308 from by bv_omega] at hjal
  runBlock hli hjal

/-- **Fail tail** (idx 76): `li a0, 1` — set the failure status, then fall through to the
    epilogue entry (base+308). -/
theorem wd_decode_failTail (base a0Old : Word) :
    cpsTripleWithin 1 (base + 304) (base + 308) (withdrawal_decode_code base)
      (.x10 ↦ᵣ a0Old) (.x10 ↦ᵣ (1 : Word)) := by
  have hli := li_spec_gen_within .x10 a0Old (1 : Word) (base + 304) (by decide)
  runBlock hli

/-- **Success-return segment** (`successTail ⨾ epilogue`, idx 74–82): set `a0 = 0`, jump over the
    fail block, restore `ra`/`s0`/`s1`/`s2`, pop the frame, and `ret`. The first multi-block
    composition (via `cpsTripleWithin_seq_same_cr`), demonstrating the stitch: frame the tail with
    the epilogue's state (`frameR`) and the epilogue with `a0=0` (`frameL`), then sequence. -/
theorem wd_decode_successReturn (base spF raSaved s0Saved s1Saved s2Saved raClob s0Clob s1Clob
    s2Clob a0Old : Word) :
    cpsTripleWithin 8 (base + 296) (raSaved &&& ~~~1) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) ** ((.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
        (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) **
        ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved)))
      ((.x10 ↦ᵣ (0 : Word)) ** ((.x2 ↦ᵣ (spF + signExtend12 (32 : BitVec 12))) **
        (.x1 ↦ᵣ raSaved) ** (.x8 ↦ᵣ s0Saved) ** (.x9 ↦ᵣ s1Saved) ** (.x18 ↦ᵣ s2Saved) **
        (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
        ((spF + 24) ↦ₘ s2Saved))) := by
  have hst := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) ** (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) **
      (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
      ((spF + 24) ↦ₘ s2Saved)) (by pcFree) (wd_decode_successTail base a0Old)
  have hepi := cpsTripleWithin_frameL (.x10 ↦ᵣ (0 : Word)) (by pcFree)
    (wd_decode_epilogue base spF raSaved s0Saved s1Saved s2Saved raClob s0Clob s1Clob s2Clob)
  exact cpsTripleWithin_seq_same_cr hst hepi

/-- **Fail-return segment** (`failTail ⨾ epilogue`, idx 76–82): set `a0 = 1`, restore the frame,
    and `ret`. The exit target every reject branch funnels to. -/
theorem wd_decode_failReturn (base spF raSaved s0Saved s1Saved s2Saved raClob s0Clob s1Clob
    s2Clob a0Old : Word) :
    cpsTripleWithin 7 (base + 304) (raSaved &&& ~~~1) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) ** ((.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
        (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) **
        ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved)))
      ((.x10 ↦ᵣ (1 : Word)) ** ((.x2 ↦ᵣ (spF + signExtend12 (32 : BitVec 12))) **
        (.x1 ↦ᵣ raSaved) ** (.x8 ↦ᵣ s0Saved) ** (.x9 ↦ᵣ s1Saved) ** (.x18 ↦ᵣ s2Saved) **
        (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
        ((spF + 24) ↦ₘ s2Saved))) := by
  have hft := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) ** (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) **
      (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
      ((spF + 24) ↦ₘ s2Saved)) (by pcFree) (wd_decode_failTail base a0Old)
  have hepi := cpsTripleWithin_frameL (.x10 ↦ᵣ (1 : Word)) (by pcFree)
    (wd_decode_epilogue base spF raSaved s0Saved s1Saved s2Saved raClob s0Clob s1Clob s2Clob)
  exact cpsTripleWithin_seq_same_cr hft hepi

/-- **Cursor/end setup** (idx 8–9): after the `walk_init` call returns the cursor in `a0` and the
    list end in `a1`, save them into `s1`/`s2` (`base+32 → base+40`). The first body segment past
    the `walk_init` call + its `bnez` guard. -/
theorem wd_decode_setup (base cursor endv s1Old s2Old : Word) :
    cpsTripleWithin 2 (base + 32) (base + 40) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv))
      ((.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv)) := by
  have hmv0 := mv_spec_gen_within .x9 .x10 cursor s1Old (base + 32) (by decide)
  have hmv1 := mv_spec_gen_within .x18 .x11 endv s2Old (base + 36) (by decide)
  runBlock hmv0 hmv1

/-- **Field `walk_next` arg setup** (`mv a0,s1; mv a1,s2`): load the saved cursor/end into the
    `walk_next` argument registers before each field's call. Shown for field 0 (idx 10–11,
    `base+40 → base+48`); the same shape recurs at idx 24–25 / 38–39 / 55–56 / 69–70. -/
theorem wd_decode_fieldSetup (base cursor endv a0Old a1Old : Word) :
    cpsTripleWithin 2 (base + 40) (base + 48) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv)) := by
  have hmv0 := mv_spec_gen_within .x10 .x9 cursor a0Old (base + 40) (by decide)
  have hmv1 := mv_spec_gen_within .x11 .x18 endv a1Old (base + 44) (by decide)
  runBlock hmv0 hmv1

/-- **Scalar-field arithmetic** (field 0, idx 17–20, `base+68 → base+84`): set `s1 := advanced`
    (cursor), compute `a0 := contentPtr = advanced − contentLen`, and stage `content_to_u64`'s
    args `a1 := contentLen`, `t1 := contentPtr`. The same four-instruction shape recurs for
    fields 1 and 3 (idx 31–34, 62–65). -/
theorem wd_decode_scalarArith (base advanced contentLen s1Old t1Old a1Old : Word) :
    cpsTripleWithin 4 (base + 68) (base + 84) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ s1Old) ** (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old) **
        (.x6 ↦ᵣ t1Old))
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (advanced - contentLen)) ** (.x12 ↦ᵣ contentLen) **
        (.x11 ↦ᵣ contentLen) ** (.x6 ↦ᵣ (advanced - contentLen))) := by
  have hmv0 := mv_spec_gen_within .x9 .x10 advanced s1Old (base + 68) (by decide)
  have hsub := sub_spec_gen_within .x10 .x9 .x12 advanced contentLen advanced (base + 72) (by decide)
  have hmv1 := mv_spec_gen_within .x11 .x12 contentLen a1Old (base + 76) (by decide)
  have hmv2 := mv_spec_gen_within .x6 .x10 (advanced - contentLen) t1Old (base + 80) (by decide)
  runBlock hmv0 hsub hmv1 hmv2

/-! ## M3 proof — reusable in-situ call code-lifting toolkit

A call block from `wd_call_content_to_u64`'s pattern lives over
`singleton callerPC (jal) ∪ leaf_code calleeEntry`; to compose it into the program it is lifted
to `withdrawal_decode_code base` via `cpsTripleWithin_extend_code`. `wd_call_code_sub` factors
that lifting into (a) the `jal` is present at `callerPC` in the program and (b) the leaf body is
a contiguous segment of the program. The three body-subset lemmas supply (b) for the leaves
appended at idx 83 / 136 / 239 (bytes 332 / 544 / 956); they serve all nine call sites
(`walk_init` ×1, `walk_next` ×5, `content_to_u64` ×3). -/

/-- Uniform instruction lookup: the `k`-th instruction of the program sits at byte `4*k` from
    `base`. Used for every `jal` (call-site `hjal`) and branch lookup; identify the concrete
    instruction at the use site with `decide` on `withdrawal_decode_prog.get ⟨k, _⟩`. -/
theorem wd_prog_lookup (base : Word) (k : Nat) (hk : k < withdrawal_decode_prog.length) :
    withdrawal_decode_code base (base + BitVec.ofNat 64 (4 * k))
      = some (withdrawal_decode_prog.get ⟨k, hk⟩) :=
  CodeReq.ofProg_lookup_addr base withdrawal_decode_prog k _ hk
    (by rw [withdrawal_decode_prog_length]; norm_num) rfl

/-- Generic call code-lifting: a `jal` present in the program, unioned with a leaf body that is a
    program segment, is contained in the program. -/
theorem wd_call_code_sub {base callerPC : Word} {i_jal : Instr} {calleeCode : CodeReq}
    (hjal : withdrawal_decode_code base callerPC = some i_jal)
    (hbody : ∀ a i, calleeCode a = some i → withdrawal_decode_code base a = some i) :
    ∀ a i, ((CodeReq.singleton callerPC i_jal).union calleeCode) a = some i →
           withdrawal_decode_code base a = some i :=
  CodeReq.union_sub (CodeReq.singleton_mono hjal) hbody

/-- The appended `rlp_walk_init` body (idx 83, byte 332) is a segment of the program. -/
theorem wd_walkInitBody_sub (base : Word) :
    ∀ a i, (rlp_walk_init_code (base + 332)) a = some i →
           withdrawal_decode_code base a = some i := by
  intro a i hwi
  have hrest : withdrawal_decode_prog
      = withdrawal_decode_glue ++
          (rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog) := by
    simp only [withdrawal_decode_prog, List.append_assoc]
  have h1 := CodeReq.ofProg_mono_append_left (base + 332) rlp_walk_init_prog rlp_walk_next_prog
    a i hwi
  have h2 := CodeReq.ofProg_mono_append_left (base + 332)
    (rlp_walk_init_prog ++ rlp_walk_next_prog) rlp_content_to_u64_prog a i h1
  have hr := CodeReq.ofProg_mono_append_right base withdrawal_decode_glue
    (rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog)
    (by rw [← hrest, withdrawal_decode_prog_length]; norm_num) a i
  rw [withdrawal_decode_glue_length,
      show base + BitVec.ofNat 64 (4 * 83) = base + 332 from by bv_omega] at hr
  rw [withdrawal_decode_code, hrest]
  exact hr h2

/-- The appended `rlp_walk_next` body (idx 136, byte 544) is a segment of the program. -/
theorem wd_walkNextBody_sub (base : Word) :
    ∀ a i, (rlp_walk_next_code (base + 544)) a = some i →
           withdrawal_decode_code base a = some i := by
  intro a i hwn
  have hrest : withdrawal_decode_prog
      = (withdrawal_decode_glue ++ rlp_walk_init_prog) ++
          (rlp_walk_next_prog ++ rlp_content_to_u64_prog) := by
    simp only [withdrawal_decode_prog, List.append_assoc]
  have h1 := CodeReq.ofProg_mono_append_left (base + 544) rlp_walk_next_prog rlp_content_to_u64_prog
    a i hwn
  have hr := CodeReq.ofProg_mono_append_right base (withdrawal_decode_glue ++ rlp_walk_init_prog)
    (rlp_walk_next_prog ++ rlp_content_to_u64_prog)
    (by rw [← hrest, withdrawal_decode_prog_length]; norm_num) a i
  rw [show (withdrawal_decode_glue ++ rlp_walk_init_prog).length = 136 from by
        simp [List.length_append, withdrawal_decode_glue_length, rlp_walk_init_prog_length],
      show base + BitVec.ofNat 64 (4 * 136) = base + 544 from by bv_omega] at hr
  rw [withdrawal_decode_code, hrest]
  exact hr h1

/-- The appended `rlp_content_to_u64` body (idx 239, byte 956) is a segment of the program. -/
theorem wd_c2uBody_sub (base : Word) :
    ∀ a i, (rlp_content_to_u64_code (base + 956)) a = some i →
           withdrawal_decode_code base a = some i := by
  intro a i hc
  have hr := CodeReq.ofProg_mono_append_right base
    (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog) rlp_content_to_u64_prog
    (by simp [List.length_append, withdrawal_decode_glue_length, rlp_walk_init_prog_length,
              rlp_walk_next_prog_length, rlp_content_to_u64_prog_length]) a i
  rw [show (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog).length = 239 from by
        simp [List.length_append, withdrawal_decode_glue_length, rlp_walk_init_prog_length,
              rlp_walk_next_prog_length],
      show base + BitVec.ofNat 64 (4 * 239) = base + 956 from by bv_omega] at hr
  rw [withdrawal_decode_code]
  exact hr hc

/-- Code-lifting for the `walk_init` call (`jal` at idx 6 → body at idx 83), via the toolkit. -/
theorem wd_walkinit_code_sub (base : Word) :
    ∀ a i, ((CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).union
              (rlp_walk_init_code (base + 332))) a = some i →
           withdrawal_decode_code base a = some i := by
  refine wd_call_code_sub ?_ (wd_walkInitBody_sub base)
  have h := wd_prog_lookup base 6 (by rw [withdrawal_decode_prog_length]; norm_num)
  rwa [show base + BitVec.ofNat 64 (4 * 6) = base + 24 from by bv_omega,
       show withdrawal_decode_prog.get ⟨6, by rw [withdrawal_decode_prog_length]; norm_num⟩
         = (.JAL .x1 (308 : BitVec 21)) from by decide] at h

/-- Distribute `**` over a disjunction: a leaf's `Post` is `frame ** (d0 ∨ d1 ∨ …)`; this turns it
    into `(frame ** d0) ∨ (frame ** d1) ∨ …` so the disjuncts can be folded with
    `cpsBranchWithin_or_pre`. (Chain for >2-way.) -/
theorem sepConj_or_elim {P Q1 Q2 : Assertion} {h : PartialState} :
    (P ** (fun g => Q1 g ∨ Q2 g)) h → (P ** Q1) h ∨ (P ** Q2) h := by
  rintro ⟨h1, h2, hdisj, hunion, hP, hQ1 | hQ2⟩
  · exact Or.inl ⟨h1, h2, hdisj, hunion, hP, hQ1⟩
  · exact Or.inr ⟨h1, h2, hdisj, hunion, hP, hQ2⟩

/-- Distribute `**` over an existential on the right: pull a leaf's existentially-quantified arm
    (e.g. `rlpWalkNextOk = fun h => ∃ next len, …`) out past the frame, so the `∃` is at the top and
    can be threaded with `cpsTripleWithin_exists_pre` / `cpsBranchWithin_exists_pre`. -/
theorem sepConj_exists_right {α : Sort _} {P : Assertion} {Q : α → Assertion} {h : PartialState} :
    (P ** (fun s => ∃ a, Q a s)) h → ∃ a, (P ** Q a) h := by
  rintro ⟨h1, h2, hdisj, hunion, hP, a, hQ⟩
  exact ⟨a, h1, h2, hdisj, hunion, hP, hQ⟩

/-- Distribute `**` over an existential on the **left**: pull an existential frame (e.g. a `regOwn`
    scratch register, `regOwn r = fun h => ∃ v, (r ↦ᵣ v) h`) out to the top. The companion to
    `sepConj_exists_right`; used to turn a `regOwn`-carrying state from a leaf's post into the
    `∃ v, (r ↦ᵣ v) ** …` form the next segment's `regIs` precondition consumes (via the exists_pre
    combinators). -/
theorem sepConj_exists_left {α : Sort _} {P : α → Assertion} {Q : Assertion} {h : PartialState} :
    ((fun s => ∃ a, P a s) ** Q) h → ∃ a, (P a ** Q) h := by
  rintro ⟨h1, h2, hdisj, hunion, ⟨a, hP⟩, hQ⟩
  exact ⟨a, h1, h2, hdisj, hunion, hP, hQ⟩

/-- Extract the four scratch-register witnesses from a `regOwn` group. A leaf's post owns the
    temporaries as `regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28`; the next segment's
    precondition wants them as concrete `regIs` cells. This peels the four existentials so the
    composition can be done with `cpsTripleWithin_exists_pre` over the witnesses. -/
theorem regOwn4_exists {a b c d : Reg} {h : PartialState}
    (hp : (regOwn a ** regOwn b ** regOwn c ** regOwn d) h) :
    ∃ va vb vc vd, ((a ↦ᵣ va) ** (b ↦ᵣ vb) ** (c ↦ᵣ vc) ** (d ↦ᵣ vd)) h := by
  obtain ⟨h1, h2, hd, hu, ⟨va, ha⟩, h3, h4, hd2, hu2, ⟨vb, hb⟩, h5, h6, hd3, hu3, ⟨vc, hc⟩,
    vd, hdd⟩ := hp
  exact ⟨va, vb, vc, vd, h1, h2, hd, hu, ha, h3, h4, hd2, hu2, hb, h5, h6, hd3, hu3, hc, hdd⟩

/-- **Branch or-elimination.** If both `P1` and `P2` branch (same exits `lt`/`lf`), then their
    disjunction branches, with the per-exit posts disjoined. The tool for consuming a leaf call's
    disjunctive status `Post` as a branch `Pre`: fold the leaf's status disjuncts (each a branch
    via `wd_bnez_branch`) into one branch whose taken/not-taken posts collect the fail/success
    disjuncts. -/
theorem cpsBranchWithin_or_pre {n : Nat} {e : Word} {cr : CodeReq} {P1 P2 : Assertion}
    {lt lf : Word} {Qt1 Qt2 Qf1 Qf2 : Assertion}
    (h1 : cpsBranchWithin n e cr P1 lt Qt1 lf Qf1)
    (h2 : cpsBranchWithin n e cr P2 lt Qt2 lf Qf2) :
    cpsBranchWithin n e cr (fun h => P1 h ∨ P2 h) lt (fun h => Qt1 h ∨ Qt2 h)
      lf (fun h => Qf1 h ∨ Qf2 h) := by
  intro R hR s hcr hPR hpc
  obtain ⟨hh, hcompat, a, b, hab_disj, hab_union, hPor, hRb⟩ := hPR
  rcases hPor with hP1 | hP2
  · obtain ⟨k, hk, s', hstep, hbr⟩ :=
      h1 R hR s hcr ⟨hh, hcompat, a, b, hab_disj, hab_union, hP1, hRb⟩ hpc
    refine ⟨k, hk, s', hstep, ?_⟩
    rcases hbr with ⟨hpct, g, gc, ga, gb, gd, gu, gQ, gR⟩ | ⟨hpcf, g, gc, ga, gb, gd, gu, gQ, gR⟩
    · exact Or.inl ⟨hpct, g, gc, ga, gb, gd, gu, Or.inl gQ, gR⟩
    · exact Or.inr ⟨hpcf, g, gc, ga, gb, gd, gu, Or.inl gQ, gR⟩
  · obtain ⟨k, hk, s', hstep, hbr⟩ :=
      h2 R hR s hcr ⟨hh, hcompat, a, b, hab_disj, hab_union, hP2, hRb⟩ hpc
    refine ⟨k, hk, s', hstep, ?_⟩
    rcases hbr with ⟨hpct, g, gc, ga, gb, gd, gu, gQ, gR⟩ | ⟨hpcf, g, gc, ga, gb, gd, gu, gQ, gR⟩
    · exact Or.inl ⟨hpct, g, gc, ga, gb, gd, gu, Or.inr gQ, gR⟩
    · exact Or.inr ⟨hpcf, g, gc, ga, gb, gd, gu, Or.inr gQ, gR⟩

/-- **Branch existential-elimination.** If `P a` branches (same exits `lt`/`lf`) for every witness
    `a`, then the existential pre `∃ a, P a` branches, with each per-exit post existentially closed.
    The tool for consuming a leaf call's existentially-quantified success arm (e.g.
    `rlpWalkNextOk = fun h => ∃ next len, …`) as a branch `Pre`: peel the `∃`, run the per-witness
    branch, and re-close the `∃` on the taken/not-taken posts. -/
theorem cpsBranchWithin_exists_pre {α : Sort _} {n : Nat} {e : Word} {cr : CodeReq}
    {P : α → Assertion} {lt lf : Word} {Qt Qf : α → Assertion}
    (h : ∀ a, cpsBranchWithin n e cr (P a) lt (Qt a) lf (Qf a)) :
    cpsBranchWithin n e cr (fun s => ∃ a, P a s) lt (fun s => ∃ a, Qt a s)
      lf (fun s => ∃ a, Qf a s) := by
  intro R hR s hcr hPR hpc
  obtain ⟨hh, hcompat, x, y, hxy, hu, hPx, hRy⟩ := hPR
  obtain ⟨a, hPa⟩ := hPx
  obtain ⟨k, hk, s', hstep, hbr⟩ := h a R hR s hcr ⟨hh, hcompat, x, y, hxy, hu, hPa, hRy⟩ hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  rcases hbr with ⟨hpct, g, gc, ga, gb, gd, gu, gQ, gR⟩ | ⟨hpcf, g, gc, ga, gb, gd, gu, gQ, gR⟩
  · exact Or.inl ⟨hpct, g, gc, ga, gb, gd, gu, ⟨a, gQ⟩, gR⟩
  · exact Or.inr ⟨hpcf, g, gc, ga, gb, gd, gu, ⟨a, gQ⟩, gR⟩

/-- **Triple existential-elimination.** The straight-line analogue of `cpsBranchWithin_exists_pre`:
    if `P a` runs to `Q a` for every witness `a`, then the existential pre `∃ a, P a` runs to the
    existentially-closed post `∃ a, Q a`. Threads a leaf's existential success arm
    (`rlpWalkNextOk = fun h => ∃ next len, …`) through the straight-line continuation (guard, scalar
    arithmetic, store) so the runtime-determined `next`/`len` witnesses carry to the field post. -/
theorem cpsTripleWithin_exists_pre {α : Sort _} {n : Nat} {e1 e2 : Word} {cr : CodeReq}
    {P Q : α → Assertion}
    (h : ∀ a, cpsTripleWithin n e1 e2 cr (P a) (Q a)) :
    cpsTripleWithin n e1 e2 cr (fun s => ∃ a, P a s) (fun s => ∃ a, Q a s) := by
  intro R hR s hcr hPR hpc
  obtain ⟨hh, hcompat, x, y, hxy, hu, hPx, hRy⟩ := hPR
  obtain ⟨a, hPa⟩ := hPx
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h a R hR s hcr ⟨hh, hcompat, x, y, hxy, hu, hPa, hRy⟩ hpc
  refine ⟨k, hk, s', hstep, hpc', ?_⟩
  obtain ⟨g, gc, ga, gb, gd, gu, gQ, gR⟩ := hQR
  exact ⟨g, gc, ga, gb, gd, gu, ⟨a, gQ⟩, gR⟩

/-- **Pure-hypothesis extraction from the precondition.** If, *assuming* a pure fact `fact`, the body
    runs `P → Q`, then it runs `(P ** ⌜fact⌝) → Q`: the heap-level pure in the precondition is
    extracted into the proof context. The tool for turning a leaf's reported heap-pure (e.g. the
    `⌜rlpItemDecode …⌝` exposed by `rlp_walk_next`'s success arm) into a `Prop` hypothesis usable to
    discharge the next segment's side-conditions (`hcp`, the form classification, …). -/
theorem cpsTripleWithin_pure_pre {fact : Prop} {n : Nat} {e1 e2 : Word} {cr : CodeReq}
    {P Q : Assertion}
    (h : fact → cpsTripleWithin n e1 e2 cr P Q) :
    cpsTripleWithin n e1 e2 cr (P ** ⌜fact⌝) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hh, hcompat, x, y, hxy, hu, hPfact, hRy⟩ := hPR
  have hsplit := (sepConj_pure_right x).1 hPfact
  exact h hsplit.2 R hR s hcr ⟨hh, hcompat, x, y, hxy, hu, hsplit.1, hRy⟩ hpc

/-! ## M3 proof — reusable guard-branch machinery

Each leaf call is followed by `bnez status, fail` (`.BNE status .x0 failOff`). `wd_bnez_branch`
lifts that branch to the full program code at any site: from the program byte `4*idx`, on
`status ≠ 0` it jumps to the fail block (`+ sext failOff`), on `status = 0` it falls through
(`+4`). Generic over the status register, offset, and the (symbolic) status value `v` — so the
call's status disjunction is case-split at composition time (each disjunct fixes `v`). Serves all
nine guard branches (the `bgeu`/arity `bne` variants are analogous). -/
theorem wd_bnez_branch (base : Word) (idx : Nat) (statusReg : Reg) (failOff : BitVec 13) (v : Word)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE statusReg .x0 failOff) :
    cpsBranchWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (withdrawal_decode_code base)
      ((statusReg ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff)
        ((statusReg ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v ≠ (0 : Word)⌝)
      ((base + BitVec.ofNat 64 (4 * idx)) + 4)
        ((statusReg ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within statusReg .x0 failOff v (0 : Word)
    (base + BitVec.ofNat 64 (4 * idx))
  refine cpsBranchWithin_extend_code ?_ hbne
  apply CodeReq.singleton_mono
  have h := wd_prog_lookup base idx hidx
  rwa [hinstr] at h

/-- **Guard, status = 0 ⟹ fall through.** When the leaf returned success (`status = 0`), the
    `bnez status, fail` is not taken: a straight-line step to the next instruction. (The big proof
    instantiates this on the success path, where the input fixes the status to 0.) -/
theorem wd_bnez_notaken (base : Word) (idx : Nat) (statusReg : Reg) (failOff : BitVec 13)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE statusReg .x0 failOff) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (base + BitVec.ofNat 64 (4 * idx) + 4)
      (withdrawal_decode_code base)
      ((statusReg ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((statusReg ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝) :=
  cpsBranchWithin_ntakenPath (wd_bnez_branch base idx statusReg failOff (0 : Word) hidx hinstr)
    (fun _ hqt => by
      obtain ⟨_, b, _, _, _, hrest⟩ := hqt
      exact ((sepConj_pure_right b).1 hrest).2 rfl)

/-- **Guard, status ≠ 0 ⟹ jump to fail.** When the leaf returned an error status, the
    `bnez status, fail` is taken: a straight-line step to the fail block. (The big proof
    instantiates this on each fail path.) -/
theorem wd_bnez_taken (base : Word) (idx : Nat) (statusReg : Reg) (failOff : BitVec 13) (v : Word)
    (hv : v ≠ (0 : Word))
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE statusReg .x0 failOff) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx))
      ((base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff)
      (withdrawal_decode_code base)
      ((statusReg ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)))
      ((statusReg ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v ≠ (0 : Word)⌝) :=
  cpsBranchWithin_takenPath (wd_bnez_branch base idx statusReg failOff v hidx hinstr)
    (fun _ hqf => by
      obtain ⟨_, b, _, _, _, hrest⟩ := hqf
      exact hv ((sepConj_pure_right b).1 hrest).2)

/-- General two-register guard branch (`.BNE rs1 rs2`): for the equality checks
    `bne a2,20,fail` (address length, idx 46) and `bne a1,2,fail` (arity, idx 73). -/
theorem wd_bne_branch (base : Word) (idx : Nat) (rs1 rs2 : Reg) (failOff : BitVec 13) (v1 v2 : Word)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE rs1 rs2 failOff) :
    cpsBranchWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (withdrawal_decode_code base)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      ((base + BitVec.ofNat 64 (4 * idx)) + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) := by
  have hbne := bne_spec_gen_within rs1 rs2 failOff v1 v2 (base + BitVec.ofNat 64 (4 * idx))
  refine cpsBranchWithin_extend_code ?_ hbne
  apply CodeReq.singleton_mono
  have h := wd_prog_lookup base idx hidx
  rwa [hinstr] at h

/-- Equality-check passes (`v1 = v2` ⟹ not taken): the address-length/arity check succeeds. -/
theorem wd_bne_eq (base : Word) (idx : Nat) (rs1 rs2 : Reg) (failOff : BitVec 13) (v : Word)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE rs1 rs2 failOff) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (base + BitVec.ofNat 64 (4 * idx) + 4)
      (withdrawal_decode_code base)
      ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v))
      ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v) ** ⌜v = v⌝) :=
  cpsBranchWithin_ntakenPath (wd_bne_branch base idx rs1 rs2 failOff v v hidx hinstr)
    (fun _ hqt => by
      obtain ⟨_, b, _, _, _, hrest⟩ := hqt
      exact ((sepConj_pure_right b).1 hrest).2 rfl)

/-- Equality-check fails (`v1 ≠ v2` ⟹ taken ⟹ fail block): wrong address length / arity. -/
theorem wd_bne_ne (base : Word) (idx : Nat) (rs1 rs2 : Reg) (failOff : BitVec 13) (v1 v2 : Word)
    (hne : v1 ≠ v2)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE rs1 rs2 failOff) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx))
      ((base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff)
      (withdrawal_decode_code base)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  cpsBranchWithin_takenPath (wd_bne_branch base idx rs1 rs2 failOff v1 v2 hidx hinstr)
    (fun _ hqf => by
      obtain ⟨_, b, _, _, _, hrest⟩ := hqf
      exact hne ((sepConj_pure_right b).1 hrest).2)

/-- The reject-list guard branch (`.BGEU rs1 rs2`): `bgeu prefix, 0xc0, fail` — taken when
    `¬ult v1 v2` (prefix ≥ 0xc0, a list), not taken when `ult v1 v2` (prefix < 0xc0, a string). -/
theorem wd_bgeu_branch (base : Word) (idx : Nat) (rs1 rs2 : Reg) (failOff : BitVec 13) (v1 v2 : Word)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BGEU rs1 rs2 failOff) :
    cpsBranchWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (withdrawal_decode_code base)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬ BitVec.ult v1 v2⌝)
      ((base + BitVec.ofNat 64 (4 * idx)) + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝) := by
  have hb := bgeu_spec_gen_within rs1 rs2 failOff v1 v2 (base + BitVec.ofNat 64 (4 * idx))
  refine cpsBranchWithin_extend_code ?_ hb
  apply CodeReq.singleton_mono
  have h := wd_prog_lookup base idx hidx
  rwa [hinstr] at h

/-- Reject-check passes (`ult v1 v2` ⟹ not taken): `prefix < 0xc0`, a byte-string field. -/
theorem wd_bgeu_lt (base : Word) (idx : Nat) (rs1 rs2 : Reg) (failOff : BitVec 13) (v1 v2 : Word)
    (hlt : BitVec.ult v1 v2)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BGEU rs1 rs2 failOff) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (base + BitVec.ofNat 64 (4 * idx) + 4)
      (withdrawal_decode_code base)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝) :=
  cpsBranchWithin_ntakenPath (wd_bgeu_branch base idx rs1 rs2 failOff v1 v2 hidx hinstr)
    (fun _ hqt => by
      obtain ⟨_, b, _, _, _, hrest⟩ := hqt
      exact ((sepConj_pure_right b).1 hrest).2 hlt)

/-- Reject-check fails (`¬ult v1 v2` ⟹ taken ⟹ fail): `prefix ≥ 0xc0`, a list where bytes are
    required ⟹ `decodeWithdrawal = none`. -/
theorem wd_bgeu_ge (base : Word) (idx : Nat) (rs1 rs2 : Reg) (failOff : BitVec 13) (v1 v2 : Word)
    (hge : ¬ BitVec.ult v1 v2)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BGEU rs1 rs2 failOff) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx))
      ((base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff)
      (withdrawal_decode_code base)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬ BitVec.ult v1 v2⌝) :=
  cpsBranchWithin_takenPath (wd_bgeu_branch base idx rs1 rs2 failOff v1 v2 hidx hinstr)
    (fun _ hqf => by
      obtain ⟨_, b, _, _, _, hrest⟩ := hqf
      exact hge ((sepConj_pure_right b).1 hrest).2)

/-- **Arity-pass → success → return** (idx 73..82): the arity guard `bne a1, t1(=2), fail` is not
    taken (the 5th `walk_next` reported end-of-list, `a1 = 2`), so control falls into the success
    tail (`a0 := 0`) and the epilogue (`ret`). Composes `wd_bne_eq` (the arity guard, passing) with
    `wd_decode_successReturn` via `cpsTripleWithin_seq_same_cr` (frameR/frameL at the seam). A real
    tail segment of the monolithic assembly. -/
theorem wd_decode_aritySuccessReturn (base spF raSaved s0Saved s1Saved s2Saved raClob s0Clob s1Clob
    s2Clob a0Old : Word)
    (hinstr : withdrawal_decode_prog.get
        ⟨73, by rw [withdrawal_decode_prog_length]; norm_num⟩ = .BNE .x11 .x6 (12 : BitVec 13)) :
    cpsTripleWithin (1 + 8) (base + 292) (raSaved &&& ~~~1) (withdrawal_decode_code base)
      (((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word))) **
        ((.x10 ↦ᵣ a0Old) ** (.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
          (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) **
          ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved)))
      (((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** ⌜(2 : Word) = (2 : Word)⌝) **
        ((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (spF + signExtend12 (32 : BitVec 12))) **
          (.x1 ↦ᵣ raSaved) ** (.x8 ↦ᵣ s0Saved) ** (.x9 ↦ᵣ s1Saved) ** (.x18 ↦ᵣ s2Saved) **
          (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
          ((spF + 24) ↦ₘ s2Saved))) := by
  have hbne := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0Old) ** (.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) ** (.x9 ↦ᵣ s1Clob) **
      (.x18 ↦ᵣ s2Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
      ((spF + 24) ↦ₘ s2Saved)) (by pcFree)
    (wd_bne_eq base 73 .x11 .x6 (12 : BitVec 13) (2 : Word)
      (by rw [withdrawal_decode_prog_length]; norm_num) hinstr)
  rw [show base + BitVec.ofNat 64 292 = base + 292 from by bv_omega] at hbne
  rw [show base + 292 + 4 = base + 296 from by bv_omega] at hbne
  have hret := cpsTripleWithin_frameL
    ((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** ⌜(2 : Word) = (2 : Word)⌝) (by pcFree)
    (wd_decode_successReturn base spF raSaved s0Saved s1Saved s2Saved raClob s0Clob s1Clob s2Clob
      a0Old)
  exact cpsTripleWithin_seq_same_cr hbne hret

/-- **Prefix read** (`lbu t0, 0(s1)`): load the field's first byte (the RLP prefix at the cursor)
    from the input region into `t0`, for the reject-list check. Generic over the program index;
    serves the four reject-checks (idx 14/28/42/59). Reads byte `cursorOff` of `srcBytes` via
    `bytesRegion_lbu_within`. -/
theorem wd_decode_readPrefix (base srcBase t0Old : Word) (srcBytes : List (BitVec 8))
    (cursorOff idx : Nat) (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .LBU .x5 .x9 0)
    (halign : srcBase.toNat % 8 = 0) (hi : cursorOff < srcBytes.length)
    (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (base + BitVec.ofNat 64 (4 * idx) + 4)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
        (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes) := by
  refine cpsTripleWithin_extend_code ?_
    (bytesRegion_lbu_within .x5 .x9 srcBase t0Old (base + BitVec.ofNat 64 (4 * idx)) srcBytes
      cursorOff (by decide) halign hi hover hvalid)
  apply CodeReq.singleton_mono
  have h := wd_prog_lookup base idx hidx
  rwa [hinstr] at h

/-- **Generic scalar store** (`sd a0, structOff(s0)`): store the decoded u64 value (`a0`) into the
    output struct dword at `s0 + structOff`. Reusable for the three scalar stores (idx 23/37/68,
    offsets 0/8/40). Lifted to the program via `cpsTripleWithin_extend_code` + `wd_prog_lookup`. -/
theorem wd_decode_storeScalar (base struct value mOld : Word) (idx : Nat) (structOff : BitVec 12)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .SD .x8 .x10 structOff) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (base + BitVec.ofNat 64 (4 * idx) + 4)
      (withdrawal_decode_code base)
      ((.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) ** ((struct + signExtend12 structOff) ↦ₘ mOld))
      ((.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) ** ((struct + signExtend12 structOff) ↦ₘ value)) := by
  have hsd := sd_spec_gen_within .x8 .x10 struct value mOld structOff
    (base + BitVec.ofNat 64 (4 * idx))
  refine cpsTripleWithin_extend_code ?_ hsd
  apply CodeReq.singleton_mono
  have h := wd_prog_lookup base idx hidx
  rwa [hinstr] at h

/-- **Generic `li`** (`li rd, imm`): load an immediate. Reusable for the constants the program
    materializes — `0xc0` (reject-list, idx 15/29/43/60), `20` (address length, idx 45), `2`
    (arity, idx 72), `0`/`1` (success/fail status, idx 74/76). Lifted via
    `cpsTripleWithin_extend_code` + `wd_prog_lookup`. -/
theorem wd_decode_li (base : Word) (idx : Nat) (rd : Reg) (imm vOld : Word) (hrd : rd ≠ .x0)
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .LI rd imm) :
    cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * idx)) (base + BitVec.ofNat 64 (4 * idx) + 4)
      (withdrawal_decode_code base) (rd ↦ᵣ vOld) (rd ↦ᵣ imm) := by
  refine cpsTripleWithin_extend_code ?_
    (li_spec_gen_within rd vOld imm (base + BitVec.ofNat 64 (4 * idx)) hrd)
  apply CodeReq.singleton_mono
  have h := wd_prog_lookup base idx hidx
  rwa [hinstr] at h

/-- **Field-0 reject-check, pass path** (`lbu prefix; li 0xc0; bgeu prefix,0xc0,fail` — idx 14–16,
    base+56 → base+68): read field 0's RLP prefix byte from the input region, materialise the
    list-marker threshold `0xc0` into `t1`, and fall through the reject branch because the prefix
    is below it (`prefix < 0xc0`, i.e. a byte-string item — what `decodeWithdrawal` requires). A
    real straight-line segment of the monolith, composing the three proven blocks
    `wd_decode_readPrefix`, `wd_decode_li`, and `wd_bgeu_lt` via `cpsTripleWithin_seq_same_cr`
    (read⨾li, exact seam) and `cpsTripleWithin_seq_perm_same_cr` (⨾bgeu, permuted seam), reshaping
    the pre/post by `xperm`. Exposes `⌜prefix < 0xc0⌝` for the field body that follows. -/
theorem wd_decode_field0RejectCheck (base srcBase t0Old t1Old : Word) (srcBytes : List (BitVec 8))
    (cursorOff : Nat) (halign : srcBase.toNat % 8 = 0) (hi : cursorOff < srcBytes.length)
    (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 3 (base + 56) (base + 68) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
        (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** (.x6 ↦ᵣ (192 : Word)) **
        bytesRegion srcBase srcBytes **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) := by
  -- prefix-read (idx 14), framed with the old `t1`
  have h14 := cpsTripleWithin_frameR (.x6 ↦ᵣ t1Old) (by pcFree)
    (wd_decode_readPrefix base srcBase t0Old srcBytes cursorOff 14
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide) halign hi hover hvalid)
  rw [show base + BitVec.ofNat 64 56 = base + 56 from by bv_omega,
      show base + 56 + 4 = base + 60 from by bv_omega] at h14
  -- li 0xc0 (idx 15), framed with the read state (post of the prefix-read)
  have h15 := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
      (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_decode_li base 15 .x6 (192 : Word) t1Old (by decide)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 60 = base + 60 from by bv_omega,
      show base + 60 + 4 = base + 64 from by bv_omega] at h15
  -- bgeu pass (idx 16), framed with cursor + input region
  have h16 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_bgeu_lt base 16 .x5 .x6 (240 : BitVec 13)
      ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word) hlt
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 64 = base + 64 from by bv_omega,
      show base + 64 + 4 = base + 68 from by bv_omega] at h16
  -- compose: (read ⨾ li) ⨾ bgeu (permuted seam), then reshape pre/post
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr h14 h15) h16
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-0 scalar prep** (reject-check ⨾ scalar arithmetic — idx 14–20, base+56 → base+84):
    the reject-check (`prefix < 0xc0`) followed by the scalar-field arithmetic that advances the
    cursor (`s1 := advanced`), computes the content pointer (`a0 := advanced − contentLen`), and
    stages `content_to_u64`'s arguments (`a1 := contentLen`, `t1 := contentPtr`). Composes the
    proven `wd_decode_field0RejectCheck` and `wd_decode_scalarArith` over the full program code by
    framing each side's disjoint registers and reconciling the seam at base+68 with a permutation.
    Carries `⌜prefix < 0xc0⌝` forward for the field body's `decodeWithdrawal` threading. `advanced`
    and `contentLen` are the `walk_next` outputs (`a0`/`a2`) supplied by the preceding call. -/
theorem wd_decode_field0ScalarPrep (base srcBase t0Old t1Old advanced contentLen a1Old : Word)
    (srcBytes : List (BitVec 8)) (cursorOff : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 7 (base + 56) (base + 84) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) ** (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) **
        (.x6 ↦ᵣ (advanced - contentLen)) ** (.x10 ↦ᵣ (advanced - contentLen)) **
        (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ contentLen) ** bytesRegion srcBase srcBytes **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) := by
  -- reject-check (idx 14–16), framed with the walk_next outputs it does not touch
  have h_rc := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old)) (by pcFree)
    (wd_decode_field0RejectCheck base srcBase t0Old t1Old srcBytes cursorOff halign hi hover hvalid
      hlt)
  -- scalar arithmetic (idx 17–20), framed with the prefix/region/⌜<0xc0⌝ it does not touch
  have h_sa := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_scalarArith base advanced contentLen (srcBase + BitVec.ofNat 64 cursorOff)
      (192 : Word) a1Old)
  -- compose at base+68 (permuted seam), then reshape pre/post
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h_rc h_sa
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-0 `content_to_u64` call, over the full program code** (idx 21, base+84 → base+88):
    the `jal ra, rlp_content_to_u64` call lifted from its local call-`CodeReq`
    (`wd_call_content_to_u64`) to `withdrawal_decode_code base` via `cpsTripleWithin_extend_code`
    and the `wd_call_code_sub`/`wd_c2uBody_sub` toolkit (the `jal` is at byte 84, the verified
    `content_to_u64` body is the program segment at byte 956). Decodes the `len`-byte content at
    `srcBase + srcOff` and returns to base+88 with the 4-way status result. The call-over-full-code
    step the scalar field body composes after `wd_decode_field0ScalarPrep`. -/
theorem wd_call_c2u_field0 (base srcBase vOld t0Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (halign : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length) (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (1 + (7 * len + 11)) (base + 84) (base + 88) (withdrawal_decode_code base)
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
         (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 88)) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
            (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h))) := by
  have hoffset : (base + 84) + signExtend21 (872 : BitVec 21) = base + 956 := by
    rw [show signExtend21 (872 : BitVec 21) = (872 : Word) from by decide]; bv_omega
  have hjal : withdrawal_decode_code base (base + 84) = some (.JAL .x1 (872 : BitVec 21)) := by
    have h := wd_prog_lookup base 21 (by rw [withdrawal_decode_prog_length]; norm_num)
    rw [show base + BitVec.ofNat 64 (4 * 21) = base + 84 from by bv_omega] at h
    rw [h]; decide
  have hcall := wd_call_content_to_u64 (base + 84) (base + 956) srcBase vOld t0Old t2Old t3Old
    srcBytes srcOff len (872 : BitVec 21) hoffset
    (by rw [show (base + 84) + 4 = base + 88 from by bv_omega]; exact halign) hdisj
    hlen64 hsalign hslen hsover hsvalid
  rw [show (base + 84) + 4 = base + 88 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code (wd_call_code_sub hjal (wd_c2uBody_sub base)) hcall

/-- **Field-0 `rlp_walk_next` call, over the full program code** (idx 12, base+48 → base+52): the
    `jal ra, rlp_walk_next` call lifted from its local call-`CodeReq` (`wd_call_walk_next`) to
    `withdrawal_decode_code base` via `cpsTripleWithin_extend_code` + `wd_call_code_sub`/
    `wd_walkNextBody_sub` (the `jal` is at byte 48, the verified `walk_next` body is the program
    segment at byte 544). Advances one RLP item from the cursor `srcBase + srcOff` and returns to
    base+52 with the 6-way status result (`rlpWalkNextOk` on success, or status 2..6). The
    call-over-full-code step the field body composes after `wd_decode_fieldSetup`. -/
theorem wd_call_walknext_field0
    (base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : (base + 52) &&& ~~~1 = base + 52)
    (hdisj : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) (base + 48) (base + 52) (withdrawal_decode_code base)
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 52)) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h))) := by
  have hoffset : (base + 48) + signExtend21 (496 : BitVec 21) = base + 544 := by
    rw [show signExtend21 (496 : BitVec 21) = (496 : Word) from by decide]; bv_omega
  have hjal : withdrawal_decode_code base (base + 48) = some (.JAL .x1 (496 : BitVec 21)) := by
    have h := wd_prog_lookup base 12 (by rw [withdrawal_decode_prog_length]; norm_num)
    rw [show base + BitVec.ofNat 64 (4 * 12) = base + 48 from by bv_omega] at h
    rw [h]; decide
  have hcall := wd_call_walk_next (base + 48) (base + 544) srcBase endPtr vOld a2Old t0Old t1Old
    t2Old t3Old t4Old t5Old t6Old srcBytes srcOff (496 : BitVec 21) hoffset
    (by rw [show (base + 48) + 4 = base + 52 from by bv_omega]; exact halign) hdisj
    hsalign hoff hover hvalid hss hls hll
  rw [show (base + 48) + 4 = base + 52 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code (wd_call_code_sub hjal (wd_walkNextBody_sub base)) hcall

/-- **Field-0 scalar body, reject-check through the `content_to_u64` call** (idx 14–21,
    base+56 → base+88): composes `wd_decode_field0ScalarPrep` (reject-check ⨾ scalar arithmetic)
    with `wd_call_c2u_field0` (the decode call). The seam at base+84 threads the content-pointer
    identity `hcp : advanced − len = srcBase + srcOff` (the staged `t1`/`a0` content pointer equals
    the call's `srcBase + srcOff`, which the preceding `walk_next`'s `rlpItemDecode` fact supplies),
    and pins the content length to `len` (`x12 = ofNat len`). Frames each side's disjoint registers
    (`x1`/`x7`/`x28`/`x0` through the prep; `x9`/`x12`/`⌜<0xc0⌝` through the call) and reconciles by
    permutation. The result carries the 4-way `content_to_u64` status post — the input for the
    `bnez` status guard and scalar store that follow. -/
theorem wd_decode_field0ScalarBody (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 56) (base + 88) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 88)) ** bytesRegion srcBase srcBytes) **
         (fun h =>
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
              ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
           (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
              (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h))) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) := by
  -- scalar-prep (idx 14–20), framed with the call's other inputs (x1/x7/x28/x0)
  have hsp := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree)
    (wd_decode_field0ScalarPrep base srcBase t0Old t1Old advanced (BitVec.ofNat 64 len) a1Old
      srcBytes cursorOff halign hi hover hvalid hlt)
  -- the content_to_u64 call (idx 21); rewrite its content pointer to the prep's staged value
  have hc2u := wd_call_c2u_field0 base srcBase vOld ((srcBytes[cursorOff]'hi).zeroExtend 64) t2Old
    t3Old srcBytes srcOff len halign88 hdisj hlen64 halign hslen hsover hsvalid
  rw [← hcp] at hc2u
  have hc2u' := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree) hc2u
  -- compose at base+84 (permuted seam), then reshape the pre
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsp hc2u'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hcomp

/-- **Field-0 scalar store, success tail** (`bnez a1,fail` not taken ⨾ `sd a0,0(s0)` — idx 22–23,
    base+88 → base+96): on the `content_to_u64` success arm (status `a1 = 0`) the status guard
    falls through, and the decoded u64 value (`a0`) is stored into the output struct dword at
    `s0 + 0` (the `index` field). Straight-line composition of `wd_bnez_notaken` (idx 22) and
    `wd_decode_storeScalar` (idx 23) — the exact seam matches with no permutation. The same shape
    recurs for fields 1/3 at idx 36–37 (off 8) and 67–68 (off 40). -/
theorem wd_decode_field0ScalarStore (base struct value mOld : Word) :
    cpsTripleWithin 2 (base + 88) (base + 96) (withdrawal_decode_code base)
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝ **
        (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ value)) := by
  -- status guard (idx 22), not taken on success; framed with the store's footprint
  have hb := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld))
    (by pcFree)
    (wd_bnez_notaken base 22 .x11 (216 : BitVec 13)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 88 = base + 88 from by bv_omega,
      show base + 88 + 4 = base + 92 from by bv_omega] at hb
  -- scalar store (idx 23); framed with the guard's residual register state
  have hs := cpsTripleWithin_frameL
    ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝) (by pcFree)
    (wd_decode_storeScalar base struct value mOld 23 (0 : BitVec 12)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 92 = base + 92 from by bv_omega,
      show base + 92 + 4 = base + 96 from by bv_omega] at hs
  -- exact seam at base+92, then reshape pre/post
  have hcomp := cpsTripleWithin_seq_same_cr hb hs
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **walk_init-success setup segment** (`bnez a2,fail` not taken ⨾ `mv s1,a0; mv s2,a1` — idx 7–9,
    base+28 → base+40): on the `walk_init` success arm (status `a2 = 0`, a well-formed list) the
    guard falls through and the returned cursor (`a0`) and list end (`a1`) are saved into `s1`/`s2`.
    Composes `wd_bnez_notaken` (idx 7) ⨾ `wd_decode_setup` (idx 8–9) over the full program code with
    an exact seam at base+32 — the first body segment after the `walk_init` call. -/
theorem wd_decode_walkInitSetup (base cursor endv s1Old s2Old : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40) (withdrawal_decode_code base)
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv))
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝ **
        (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv)) := by
  -- status guard (idx 7), not taken on success; framed with the setup's footprint
  have hb := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv)) (by pcFree)
    (wd_bnez_notaken base 7 .x12 (276 : BitVec 13)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 28 = base + 28 from by bv_omega,
      show base + 28 + 4 = base + 32 from by bv_omega] at hb
  -- cursor/end save (idx 8–9); framed with the guard's residual register state
  have hs := cpsTripleWithin_frameL
    ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝) (by pcFree)
    (wd_decode_setup base cursor endv s1Old s2Old)
  -- exact seam at base+32, then reshape pre/post
  have hcomp := cpsTripleWithin_seq_same_cr hb hs
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-0 walk_next guard, success continuation** (`bnez a1,fail` not taken — idx 13, base+52 →
    base+56): on the `walk_next` success arm (`rlpWalkNextOk`, status `a1 = 0`) the guard falls
    through, threading the runtime-determined `next`/`len` witnesses (and the `rlpItemDecode` fact)
    to the post. Built by pulling `rlpWalkNextOk`'s `∃ next len` to the top (`sepConj_exists_right`),
    threading it through the per-witness `wd_bnez_notaken` triple (`cpsTripleWithin_exists_pre`).
    The per-witness state carries the saved-register frame the field body consumes. -/
theorem wd_walknext_guard_success (base srcBase cursor endPtr vx1 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 (base + 52) (base + 56) (withdrawal_decode_code base)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
        rlpWalkNextOk cursor endPtr srcBytes srcOff)
      (fun s => ∃ next len,
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) s) := by
  have per : ∀ next len : Word,
      cpsTripleWithin 1 (base + 52) (base + 56) (withdrawal_decode_code base)
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) := by
    intro next len
    have hb := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
        ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝ **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) (by pcFree)
      (wd_bnez_notaken base 13 .x11 (252 : BitVec 13)
        (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
    rw [show base + BitVec.ofNat 64 52 = base + 52 from by bv_omega,
        show base + 52 + 4 = base + 56 from by bv_omega] at hb
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hb
  have htriple := cpsTripleWithin_exists_pre (fun next : Word =>
    cpsTripleWithin_exists_pre (fun len : Word => per next len))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hp => hp) htriple
  unfold rlpWalkNextOk at hp
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, hp2⟩

/-! ## M3 proof — canonicity bridge

`content_to_u64`'s status uses `getByteAt` (the runtime byte read at the content pointer);
`decodeWithdrawal`'s canonicity uses `d.headD 1` (the first byte of the decoded content list).
For a nonempty content slice these are the same byte — bridging the two canonicity notions. -/

/-- The first byte of the content slice (`headD 1`) is the runtime `getByteAt` at that offset:
    both are `srcBytes[off]` when the slice is nonempty (`0 < len`, `off < length`). -/
theorem headD_take_drop_eq_getByteAt (srcBytes : List (BitVec 8)) (off len : Nat)
    (hlen : 0 < len) (hoff : off < srcBytes.length) :
    ((srcBytes.drop off).take len).headD 1 = getByteAt srcBytes off := by
  obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
  rw [getByteAt, dif_pos hoff,
      drop_eq_cons_of_getElem? (List.getElem?_eq_getElem hoff), List.take_succ_cons]
  rfl

/-! ## M3 proof — leaf status-derivations

Inside the assembly, the input's `decodeFully`/canonicity facts pin each leaf's returned status,
collapsing its disjunctive `Post` to a single arm. These lemmas do that collapse for
`content_to_u64` (used for the three scalar fields). -/

/-- `content_to_u64` returns **success** for a canonical scalar: given the content is nonempty
    (`0 < len`), fits a u64 (`len ≤ 8`), and has a nonzero leading byte
    (`getByteAt ≠ 0` — the canonicity), the 4-way status `Post` collapses to the status-0 arm
    (`a1 = 0`, `a0 = fromBytesBE content`). Rules out the `8<len` (D0), `len=0` (D1), and
    leading-zero (D2) fail arms via their pure facts. -/
theorem c2u_status_success {srcBytes : List Byte} {srcOff len : Nat} {h : PartialState}
    (hlen : len ≤ 8) (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0)
    (hpost :
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
         ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
      (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
         (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h)) :
    ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
      (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h := by
  rcases hpost with h0 | h1 | h2 | h3
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h0
    have : 8 < len := ((sepConj_pure_right b).1 hrest).2; omega
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h1
    have : len = 0 := ((sepConj_pure_right b).1 hrest).2; omega
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h2
    exact hbyte ((sepConj_pure_right b).1 hrest).2.2
  · exact h3

/-- `content_to_u64` returns **success with value 0** for an empty scalar (`len = 0`): the 4-way
    status `Post` collapses to the empty-content arm (`a1 = 0`, `a0 = 0`). This is the other success
    sub-case — a withdrawal scalar field that is `0` is canonically RLP-encoded as the empty string
    (prefix `0x80`, no content), which `content_to_u64` accepts with value `0`. Rules out the
    `8 < len` (D0) and the two `0 < len` arms (D2/D3) via their pure facts. -/
theorem c2u_status_empty {srcBytes : List Byte} {srcOff len : Nat} {h : PartialState}
    (hlen0 : len = 0)
    (hpost :
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
         ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
      (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
         (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h)) :
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h := by
  rcases hpost with h0 | h1 | h2 | h3
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h0
    have : 8 < len := ((sepConj_pure_right b).1 hrest).2; omega
  · exact h1
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h2
    have : 0 < len := ((sepConj_pure_right b).1 hrest).2.1; omega
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h3
    have : 0 < len := ((sepConj_pure_right b).1 hrest).2.1; omega

/-- **Field-0 scalar body, success arm** (idx 14–21, base+56 → base+88): `wd_decode_field0ScalarBody`
    with its 4-way `content_to_u64` status post **collapsed to the success arm** via
    `c2u_status_success`, given the scalar is canonical (nonempty `0 < len`, fits a u64 `len ≤ 8`,
    nonzero leading byte `getByteAt ≠ 0`). The post then carries the concrete decoded value
    `a0 = ofNat (fromBytesBE content)` and `a1 = 0`, ready for the status guard to fall through and
    the scalar store. Collapses the disjunction in place with `sepConj_mono_left/right`. -/
theorem wd_decode_field0ScalarBodySuccess (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 56) (base + 88) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 88)) ** bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝)) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => c2u_status_success hlen8 hpos hbyte hd)) _ hp)
    (wd_decode_field0ScalarBody base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign88 hdisj hlen64 hslen hsover
      hsvalid hcp)

/-- **Field-0 scalar decode, full success path** (idx 14–23, base+56 → base+96): the complete
    canonical-scalar decode of field 0 — reject-check, scalar arithmetic, `content_to_u64` call,
    status guard (fall-through), and store — composing `wd_decode_field0ScalarBodySuccess` with
    `wd_decode_field0ScalarStore`. Frames the struct pointer/cell through the body and the body's
    residual state through the store, reconciling the 15-atom seam at base+88 by permutation. On a
    canonical scalar (`0 < len`, `len ≤ 8`, leading byte ≠ 0) with the content-pointer identity
    `hcp`, it writes `index = fromBytesBE content` (little-endian u64) into the output dword `s0+0`
    and advances `s1` to the item end. -/
theorem wd_decode_field0Scalar (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct mOld :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 56) (base + 96)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hbody := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)) (by pcFree)
    (wd_decode_field0ScalarBodySuccess base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign88 hdisj hlen64 hslen hsover
      hsvalid hcp hpos hbyte hlen8)
  have hstore := cpsTripleWithin_frameL
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x1 ↦ᵣ (base + 88)) **
      bytesRegion srcBase srcBytes **
      ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ ** (.x9 ↦ᵣ advanced) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field0ScalarStore base struct
      (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) mOld)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody hstore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-0 scalar over `regOwn` scratch** (base+56 → base+96): `wd_decode_field0Scalar` with its
    four scratch temporaries (`x5`/`x6`/`x7`/`x28`) supplied as `regOwn` (their old values
    irrelevant — the reject-check and `content_to_u64` overwrite them) rather than concrete `regIs`.
    This is the form the preceding walk segment's post delivers (a leaf owns its temporaries as
    `regOwn`). Threads the four witnesses out with `regOwn4_exists` + nested `cpsTripleWithin_exists_pre`
    (the post is unchanged — it already returns the scratch as `regOwn`). The bridge that lets
    `wd_decode_field0Walk ⨾ (this)` compose into the full field-0 scalar body. -/
theorem wd_decode_field0Scalar_regOwn (base srcBase vOld advanced a1Old struct mOld : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 56) (base + 96)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28))
      ((.x9 ↦ᵣ advanced) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hgrouped : ∀ t0Old t1Old t2Old t3Old : Word,
      cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 56) (base + 96)
        (withdrawal_decode_code base)
        (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
          ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old)))
        ((.x9 ↦ᵣ advanced) **
          (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
          (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
          ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ
            BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
          ⌜(0 : Word) = (0 : Word)⌝) := by
    intro t0Old t1Old t2Old t3Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (wd_decode_field0Scalar base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct mOld
        srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign88 hdisj hlen64 hslen hsover
        hsvalid hcp hpos hbyte hlen8)
  have hbody := cpsTripleWithin_exists_pre (fun t0Old : Word =>
    cpsTripleWithin_exists_pre (fun t1Old : Word =>
      cpsTripleWithin_exists_pre (fun t2Old : Word =>
        cpsTripleWithin_exists_pre (fun t3Old : Word => hgrouped t0Old t1Old t2Old t3Old))))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hp => ?_) hbody
  · obtain ⟨hM, hG, hd, hu, hMain, hGrp⟩ := hp
    obtain ⟨va, vb, vc, vd, hReg⟩ := regOwn4_exists hGrp
    exact ⟨va, vb, vc, vd, hM, hG, hd, hu, hMain, hReg⟩
  · obtain ⟨_, _, _, _, h⟩ := hp; exact h

/-- `content_to_u64` **fails** on an over-long scalar (`8 < len`): the status `Post` collapses to a
    fail arm (D0 status 2 or D2 status 3) — both `a1 ≠ 0`, so the guard is taken ⟹ fail. Rules out
    `len = 0` (D1) and, crucially via the strengthened spec, the success arm D3 (which now carries
    `len ≤ 8`). This is the direction that motivated strengthening `content_to_u64`. -/
theorem c2u_status_fail_long {srcBytes : List Byte} {srcOff len : Nat} {h : PartialState}
    (hlong : 8 < len)
    (hpost :
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
         ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
      (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
         (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h)) :
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
       ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) := by
  rcases hpost with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h1
    have : len = 0 := ((sepConj_pure_right b).1 hrest).2; omega
  · exact Or.inr h2
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h3
    have : len ≤ 8 := ((sepConj_pure_right b).1 hrest).2.2.2; omega

/-- `content_to_u64` **fails** on a leading-zero scalar (`0 < len`, `getByteAt = 0`): the status
    `Post` collapses to a fail arm (D0 status 2 or D2 status 3) — both `a1 ≠ 0`. Rules out `len = 0`
    (D1) and the success arm D3 (which needs `getByteAt ≠ 0`). -/
theorem c2u_status_fail_leadzero {srcBytes : List Byte} {srcOff len : Nat} {h : PartialState}
    (hpos : 0 < len) (hlz : getByteAt srcBytes srcOff = 0)
    (hpost :
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
         ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
      (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
         (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h)) :
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
       ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) := by
  rcases hpost with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h1
    have : len = 0 := ((sepConj_pure_right b).1 hrest).2; omega
  · exact Or.inr h2
  · exfalso; obtain ⟨_, b, _, _, _, hrest⟩ := h3
    exact (((sepConj_pure_right b).1 hrest).2.2.1) hlz

/-- `rlp_walk_next` returns **success** for a decodable in-bounds item: given the cursor is before
    the list end (`ult cursor endPtr`) and the item decodes (`∃ next len, rlpItemDecode …`), the
    6-way status `Post` collapses to the `rlpWalkNextOk` arm. The premature-end arm (status 2)
    carries `⌜¬ ult cursor endPtr⌝` (ruled out by `hin`); the malformed arms (status 3/4/5/6) each
    carry `⌜¬ ∃ next len, rlpItemDecode …⌝` (ruled out by `hdec`). The `walk_next` analogue of
    `c2u_status_success`; the field body uses it to expose the `rlpItemDecode` fact that supplies
    the content-pointer/length/canonicity facts for the scalar (or address) decode. -/
theorem walknext_status_success {srcBytes : List Byte} {srcOff : Nat} {srcBase endPtr : Word}
    {h : PartialState}
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hdec : ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
      endPtr next len)
    (hpost :
      rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
         (.x12 ↦ᵣ (0 : Word)) **
         ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
         (.x12 ↦ᵣ (0 : Word)) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h) ∨
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
         (.x12 ↦ᵣ (0 : Word)) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h) ∨
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
         (.x12 ↦ᵣ (0 : Word)) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h) ∨
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
         (.x12 ↦ᵣ (0 : Word)) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h)) :
    rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  rcases hpost with h0 | h2 | h3 | h4 | h5 | h6
  · exact h0
  · exfalso; obtain ⟨_, _, _, _, _, hr1⟩ := h2
    obtain ⟨_, b, _, _, _, hr2⟩ := hr1
    exact (((sepConj_pure_right b).1 hr2).2) hin
  · exfalso; obtain ⟨_, _, _, _, _, hr1⟩ := h3
    obtain ⟨_, b, _, _, _, hr2⟩ := hr1
    exact (((sepConj_pure_right b).1 hr2).2) hdec
  · exfalso; obtain ⟨_, _, _, _, _, hr1⟩ := h4
    obtain ⟨_, b, _, _, _, hr2⟩ := hr1
    exact (((sepConj_pure_right b).1 hr2).2) hdec
  · exfalso; obtain ⟨_, _, _, _, _, hr1⟩ := h5
    obtain ⟨_, b, _, _, _, hr2⟩ := hr1
    exact (((sepConj_pure_right b).1 hr2).2) hdec
  · exfalso; obtain ⟨_, _, _, _, _, hr1⟩ := h6
    obtain ⟨_, b, _, _, _, hr2⟩ := hr1
    exact (((sepConj_pure_right b).1 hr2).2) hdec

/-- **Field-0 walk** (idx 10–13, base+40 → base+56): the full per-field item walk on the success
    path — load the cursor/end into the `walk_next` args (`wd_decode_fieldSetup`), call `walk_next`
    (`wd_call_walknext_field0`, framed with the saved `s1`/`s2`), collapse its 6-way status post to
    the `rlpWalkNextOk` arm (`walknext_status_success`, given the item is in bounds `hin` and decodes
    `hdec`), and fall through the status guard (`wd_walknext_guard_success`). The post exposes
    `∃ next len`, the advanced cursor `a0 = next`, the content length `a2 = len`, and the
    `rlpItemDecode` fact — everything the field body needs. `hdec`/`hin` are supplied by the monolith
    from the field's decodability (via the reverse bridges) and in-bounds. -/
theorem wd_decode_field0Walk (base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisj : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hdec : ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin (2 + (1 + 87) + 1) (base + 40) (base + 56) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      (fun s => ∃ next len,
        ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ next) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (base + 52)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** bytesRegion srcBase srcBytes ** ⌜(0 : Word) = (0 : Word)⌝ **
          ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) s) := by
  -- arg setup (idx 10-11), framed with the walk_next call inputs
  have hA := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree)
    (wd_decode_fieldSetup base (srcBase + BitVec.ofNat 64 srcOff) endPtr a0Old a1Old)
  -- walk_next call (idx 12), framed with the saved s1/s2 it does not touch
  have hB := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_call_walknext_field0 base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old
      t5Old t6Old srcBytes srcOff halign52 hdisj hsalign hoff hover hvalid hss hls hll)
  -- setup ⨾ call (permuted seam at base+48)
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA hB
  -- collapse the 6-way status post to the rlpWalkNextOk arm
  have hABc := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun s hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => walknext_status_success hin hdec hd)) s hp) hAB
  -- guard not-taken (idx 13), framed with the saved cursor/end; ⨾ at base+52 (permuted seam)
  have hC := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_walknext_guard_success base srcBase (srcBase + BitVec.ofNat 64 srcOff) endPtr (base + 52)
      srcBytes srcOff)
  have hABC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hABc hC
  -- reshape pre; distribute the ∃ out of the post and reshape
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun s hp => ?_) hABC
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, by xperm_hyp hp2⟩

/-- **Byte-string-form extraction.** A decoded item whose prefix is below `0xb8` is a single-byte
    or short-byte-string item: the three larger forms (long string ≥ 0xb8, short list ≥ 0xc0, long
    list ≥ 0xf8) are all ruled out by their prefix-range guards. The two surviving disjuncts are
    exactly `rlpItemDecode`'s single-byte / short-string cases (with their `next`/`len` equations).
    For the scalar/address withdrawal fields these are the only forms that can decode successfully
    (`content_to_u64` rejects `len > 8`, the address check rejects `len ≠ 20`, so the field is a
    short byte string); the surviving facts then feed the `decodeAux` byte-string bridges. -/
theorem rlpItemDecode_byteString_of_lt_0xb8 {bytes : List (BitVec 8)} {off : Nat}
    (hoff : off < bytes.length) {cursor endPtr next len : Word}
    (hpre : BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    ∃ b : BitVec 8, bytes[off]? = some b ∧
      ((BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
          BitVec.ult cursor endPtr = true ∧
          next = cursor + signExtend12 (1 : BitVec 12) ∧ len = (1 : Word)) ∨
       (¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
          BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
          (b.zeroExtend 64 - (0x80 : Word) = (1 : Word) →
            ∃ c : BitVec 8, bytes[off + 1]? = some c ∧
              ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
          BitVec.ult (b.zeroExtend 64 - (0x80 : Word)) (endPtr - cursor) = true ∧
          next = (cursor + signExtend12 (1 : BitVec 12)) + (b.zeroExtend 64 - (0x80 : Word)) ∧
          len = b.zeroExtend 64 - (0x80 : Word))) := by
  obtain ⟨b, hb, hdisj⟩ := h
  have hbe : b = bytes[off]'hoff := by
    rw [List.getElem?_eq_getElem hoff] at hb; exact (Option.some.inj hb).symm
  rw [← hbe] at hpre
  refine ⟨b, hb, ?_⟩
  rcases hdisj with sb | ss | ls | sl | ll
  · exact Or.inl sb
  · exact Or.inr ss
  · exact absurd hpre ls.1
  · exfalso; have h1 := sl.1
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 hpre; bv_omega
  · exfalso; have h1 := ll.1
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 hpre; bv_omega

/-- **Single-byte field decode step.** A single-byte item (prefix `< 0x80`) at offset `off`
    decodes (any positive fuel) to `.bytes [b]`, consuming `[off, off+1)`. The runtime
    `rlpItemDecode` prefix-range fact (`ult`) is converted to the `Nat` bound the pure
    `decodeAux_singleByte_bridge` needs. In the `∀ m` form `decodeFully_shortList_four` consumes. -/
theorem rlpItemDecode_singleByte_decodeAux {bytes : List Byte} {off : Nat} {b : Byte}
    (hget : bytes[off]? = some b)
    (hsingle : BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true) :
    ∀ m, decodeAux (m + 1) (bytes.drop off) = some (.bytes [b], bytes.drop (off + 1)) := by
  have hb : b.toNat < 0x80 := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle; bv_omega
  exact fun m => decodeAux_singleByte_bridge bytes off b hget hb m

/-- **Short-byte-string field decode step.** A short-string item (prefix `b ∈ [0x80, 0xB7]`) at
    offset `off`, with the declared `b - 0x80` content bytes available (`hlen`, a `Nat` fit the
    monolith derives from the cursor/end pointers) and the `len = 1` canonicity, decodes (any
    positive fuel) to `.bytes content` (`content = (drop (off+1)).take (b-0x80)`), consuming
    `[off, off+1+(b-0x80))`. The runtime `rlpItemDecode` `ult` prefix facts and the `Word` `len=1`
    canonicity guard are converted to the `Nat`/`Bool` forms `decodeAux_shortBytes_bridge` needs. -/
theorem rlpItemDecode_shortBytes_decodeAux {bytes : List Byte} {off : Nat} {b : Byte}
    (hget : bytes[off]? = some b)
    (hlo : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true)
    (hcanon : b.zeroExtend 64 - (0x80 : Word) = (1 : Word) →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length) :
    ∀ m, decodeAux (m + 1) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)),
        bytes.drop (off + 1 + (b.toNat - 0x80))) := by
  have hlo' : 0x80 ≤ b.toNat := by
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo; bv_omega
  have hhi' : b.toNat ≤ 0xB7 := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi; bv_omega
  have hcanon' : b.toNat - 0x80 = 1 →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80 := by
    intro hb1
    have hbw : b.zeroExtend 64 - (0x80 : Word) = (1 : Word) := by bv_omega
    obtain ⟨c, hc, hcge⟩ := hcanon hbw
    refine ⟨c, hc, ?_⟩
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hcge ⊢; bv_omega
  exact fun m => decodeAux_shortBytes_bridge bytes off b hget hlo' hhi' hlen hcanon' m

/-- **Short-string offset bookkeeping** (Word ↔ Nat). For a short-string item at byte offset `off`
    (cursor `srcBase + off`), the `rlpItemDecode` `next`/`len` Words convert to the `Nat` offsets the
    pure assembly needs: the item ends at `srcBase + (off + 1 + (b−0x80))` (the capstone's next
    offset), the reported length is `ofNat (b−0x80)`, and the **content pointer** `next − len`
    is `srcBase + (off + 1)` — i.e. content offset `off + 1` (after the 1-byte prefix), which is the
    scalar body's `hcp`. All three are pure `BitVec.ofNat` additive identities (the symbolic
    3-term sum is chained through the 2-term `ofNat_add` bridge). -/
theorem rlpItemDecode_shortBytes_offsets (srcBase cursor next len : Word) (b : BitVec 8) (off : Nat)
    (hcursor : cursor = srcBase + BitVec.ofNat 64 off)
    (hlo : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hnext : next = (cursor + signExtend12 (1 : BitVec 12)) + (b.zeroExtend 64 - (0x80 : Word)))
    (hlen : len = b.zeroExtend 64 - (0x80 : Word)) :
    next = srcBase + BitVec.ofNat 64 (off + 1 + (b.toNat - 0x80)) ∧
    len = BitVec.ofNat 64 (b.toNat - 0x80) ∧
    next - len = srcBase + BitVec.ofNat 64 (off + 1) := by
  have hb : 0x80 ≤ b.toNat := by
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo; bv_omega
  have hbw : b.zeroExtend 64 - (0x80 : Word) = BitVec.ofNat 64 (b.toNat - 0x80) := by bv_omega
  have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [hnext, hcursor, hse, hbw,
        show srcBase + BitVec.ofNat 64 off + BitVec.ofNat 64 1 = srcBase + BitVec.ofNat 64 (off + 1)
          from by bv_omega,
        show srcBase + BitVec.ofNat 64 (off + 1) + BitVec.ofNat 64 (b.toNat - 0x80)
          = srcBase + BitVec.ofNat 64 (off + 1 + (b.toNat - 0x80)) from by bv_omega]
  · rw [hlen, hbw]
  · rw [hnext, hlen, hcursor, hse, hbw,
        show srcBase + BitVec.ofNat 64 off + BitVec.ofNat 64 1 = srcBase + BitVec.ofNat 64 (off + 1)
          from by bv_omega]
    bv_omega

/-- **Single-byte offset bookkeeping** (Word ↔ Nat). For a single-byte item at byte offset `off`,
    the item ends at `srcBase + (off + 1)` (the capstone's next offset) and the content pointer
    `next − len` (with `len = 1`) is `srcBase + off` — i.e. the content is the byte itself, at
    offset `off` (the scalar body's `hcp`). -/
theorem rlpItemDecode_singleByte_offsets (srcBase cursor next len : Word) (off : Nat)
    (hcursor : cursor = srcBase + BitVec.ofNat 64 off)
    (hnext : next = cursor + signExtend12 (1 : BitVec 12)) (hlen : len = (1 : Word)) :
    next = srcBase + BitVec.ofNat 64 (off + 1) ∧
    next - len = srcBase + BitVec.ofNat 64 off := by
  have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
  refine ⟨?_, ?_⟩
  · rw [hnext, hcursor, hse,
        show srcBase + BitVec.ofNat 64 off + BitVec.ofNat 64 1 = srcBase + BitVec.ofNat 64 (off + 1)
          from by bv_omega]
  · rw [hnext, hlen, hcursor, hse]; bv_omega

/-! ## M3 proof — walk-succeeds (reverse) bridges

For the success path, the forward proof must show `rlp_walk_next` returns `rlpWalkNextOk` for each
decodable field — i.e. it must supply the `∃ next len, rlpItemDecode …` witness (`hdec`) that
`walknext_status_success` consumes to collapse the 6-way status `Post`. These lemmas construct that
witness directly from the byte-string item facts (the reverse of the `decodeAux` glue): given the
prefix byte and range (and, for short strings, the canonicity and the content-fit), the matching
`rlpItemDecode` disjunct holds with the concrete `next`/`len`. -/

/-- **Single-byte walk-succeeds.** A single-byte item (`b < 0x80`) at an in-bounds cursor decodes:
    `rlpItemDecode` holds with `next = cursor + 1`, `len = 1`. -/
theorem rlpItemDecode_of_singleByte {bytes : List Byte} {off : Nat} {b : Byte} {cursor endPtr : Word}
    (hget : bytes[off]? = some b) (hsingle : BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hin : BitVec.ult cursor endPtr = true) :
    rlpItemDecode bytes off cursor endPtr (cursor + signExtend12 (1 : BitVec 12)) (1 : Word) :=
  ⟨b, hget, Or.inl ⟨hsingle, hin, rfl, rfl⟩⟩

/-- **Short-byte-string walk-succeeds.** A short-string item (`b ∈ [0x80, 0xB7]`) with the `len = 1`
    canonicity and the content-fit (`b − 0x80 < endPtr − cursor`) decodes: `rlpItemDecode` holds
    with `next = (cursor + 1) + (b − 0x80)`, `len = b − 0x80`. -/
theorem rlpItemDecode_of_shortBytes {bytes : List Byte} {off : Nat} {b : Byte} {cursor endPtr : Word}
    (hget : bytes[off]? = some b)
    (hlo : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true)
    (hcanon : b.zeroExtend 64 - (0x80 : Word) = (1 : Word) →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true)
    (hfit : BitVec.ult (b.zeroExtend 64 - (0x80 : Word)) (endPtr - cursor) = true) :
    rlpItemDecode bytes off cursor endPtr
      ((cursor + signExtend12 (1 : BitVec 12)) + (b.zeroExtend 64 - (0x80 : Word)))
      (b.zeroExtend 64 - (0x80 : Word)) :=
  ⟨b, hget, Or.inr (Or.inl ⟨hlo, hhi, hcanon, hfit, rfl, rfl⟩)⟩

/-- **Single-byte `next`/`len` determination.** A decode whose prefix byte is `< 0x80` is forced
    into the single-byte form, so `next = cursor + 1` and `len = 1`: the four non-single-byte
    disjuncts require a prefix `≥ 0x80`/`0xb8`/`0xc0`/`0xf8`, all contradicting `< 0x80`. Used in the
    field body to pin the walk's existential `next`/`len` for a single-byte scalar field. -/
theorem rlpItemDecode_singleByte_eq {bytes : List (BitVec 8)} {off : Nat}
    (hoff : off < bytes.length) {cursor endPtr next len : Word}
    (hsingle : BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    next = cursor + signExtend12 (1 : BitVec 12) ∧ len = (1 : Word) := by
  obtain ⟨b, hb, hdisj⟩ := h
  have hbe : b = bytes[off]'hoff := by
    rw [List.getElem?_eq_getElem hoff] at hb; exact (Option.some.inj hb).symm
  rw [← hbe] at hsingle
  rcases hdisj with ⟨_, _, hn, hl⟩ | ss | ls | sl | ll
  · exact ⟨hn, hl⟩
  · exact absurd hsingle ss.1
  · exfalso; have h1 := ls.1
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 hsingle; bv_omega
  · exfalso; have h1 := sl.1
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 hsingle; bv_omega
  · exfalso; have h1 := ll.1
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 hsingle; bv_omega

/-- **Short-byte-string `next`/`len` determination.** A decode whose prefix byte is in
    `[0x80, 0xB8)` is forced into the short-byte-string form, so `next = (cursor + 1) + (b − 0x80)`
    and `len = b − 0x80`: single-byte needs `b < 0x80` (contradicts `¬ ult b 0x80`), and the three
    larger forms need `b ≥ 0xb8`/`0xc0`/`0xf8` (all contradict `ult b 0xb8`). The short-string
    analogue of `rlpItemDecode_singleByte_eq`; used in the field body to pin the walk's existential
    `next`/`len` for a multi-byte (short) scalar/address field. -/
theorem rlpItemDecode_shortBytes_eq {bytes : List (BitVec 8)} {off : Nat}
    (hoff : off < bytes.length) {cursor endPtr next len : Word}
    (hlo : ¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    next = (cursor + signExtend12 (1 : BitVec 12)) +
        ((bytes[off]'hoff).zeroExtend 64 - (0x80 : Word)) ∧
      len = (bytes[off]'hoff).zeroExtend 64 - (0x80 : Word) := by
  obtain ⟨b, hb, hdisj⟩ := h
  have hbe : b = bytes[off]'hoff := by
    rw [List.getElem?_eq_getElem hoff] at hb; exact (Option.some.inj hb).symm
  rw [← hbe] at hlo hhi
  rcases hdisj with sb | ⟨_, _, _, _, hn, hl⟩ | ls | sl | ll
  · exact absurd sb.1 hlo
  · rw [hbe] at hn hl; exact ⟨hn, hl⟩
  · exact absurd hhi ls.1
  · exfalso; have h1 := sl.1
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 hhi; bv_omega
  · exfalso; have h1 := ll.1
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 hhi; bv_omega

/-! ## M3 proof — fail-path bridge foundation

Every reject branch of `withdrawal_decode_prog` must conclude `decodeWithdrawal srcBytes = none`.
The lemma below is the foundation: `decodeWithdrawal bs = none` exactly when `bs` does **not**
fully decode to a canonical 4-element byte-list. Each assembly reject discharges its branch by
establishing that the structural/canonicity condition fails (`walk_init` not-a-list, `walk_next`
malformed/premature-end, prefix ≥ 0xc0 ⟹ element is a list, `content_to_u64` non-canonical
scalar, address length ≠ 20, wrong arity), then applying `.mpr`. Derived from
`decodeWithdrawal_eq_some_iff`. -/
theorem decodeWithdrawal_eq_none_iff (bs : List Byte) :
    decodeWithdrawal bs = none ↔
      ¬ ∃ d0 d1 d2 d3 : List Byte,
        decodeFully bs = some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3])
        ∧ d0.headD 1 ≠ 0 ∧ d0.length ≤ 8
        ∧ d1.headD 1 ≠ 0 ∧ d1.length ≤ 8
        ∧ d2.length = 20
        ∧ d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 := by
  constructor
  · -- none ⟹ no canonical 4-byte-list structure
    intro hnone ⟨d0, d1, d2, d3, hf, hc0, hl0, hc1, hl1, h20, hc3, hl3⟩
    have hsome : decodeWithdrawal bs =
        some { index := Nat.fromBytesBE d0, validatorIndex := Nat.fromBytesBE d1,
               address := BitVec.ofNat 160 (Nat.fromBytesBE d2), amount := Nat.fromBytesBE d3 } :=
      (decodeWithdrawal_eq_some_iff bs _).mpr
        ⟨d0, d1, d2, d3, hf, hc0, hl0, hc1, hl1, h20, hc3, hl3, rfl, rfl, rfl, rfl⟩
    rw [hsome] at hnone; simp at hnone
  · -- no structure ⟹ none
    intro hno
    cases hw : decodeWithdrawal bs with
    | none => rfl
    | some w =>
      exfalso
      obtain ⟨d0, d1, d2, d3, hf, hc0, hl0, hc1, hl1, h20, hc3, hl3, _, _, _, _⟩ :=
        (decodeWithdrawal_eq_some_iff bs w).mp hw
      exact hno ⟨d0, d1, d2, d3, hf, hc0, hl0, hc1, hl1, h20, hc3, hl3⟩

/-- Success-path bridge endpoint: once the assembly has established `decodeFully srcBytes` is the
    canonical 4-byte-list (the four element byte-lists `d0..d3` via the walk facts + M2
    `decodeFully_shortList_four`, with the canonicity/length conditions from `content_to_u64` and
    the address-length check), `decodeWithdrawal srcBytes = some w` with `w` the field values. -/
theorem decodeWithdrawal_eq_some_of_fields (bs : List Byte) (d0 d1 d2 d3 : List Byte)
    (hf : decodeFully bs = some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]))
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (h20 : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal bs =
      some { index := Nat.fromBytesBE d0, validatorIndex := Nat.fromBytesBE d1,
             address := BitVec.ofNat 160 (Nat.fromBytesBE d2), amount := Nat.fromBytesBE d3 } :=
  (decodeWithdrawal_eq_some_iff bs _).mpr
    ⟨d0, d1, d2, d3, hf, hc0, hl0, hc1, hl1, h20, hc3, hl3, rfl, rfl, rfl, rfl⟩

/-! ## M3 proof — field-0 body composition (single-byte case) -/

/-- **Single-byte resolution of the field-0 walk `Post`.** The field-0 walk
    (`wd_decode_field0Walk`) reports `∃ next len, … ⌜rlpItemDecode … next len⌝`. When the field's
    prefix byte is `< 0x80` (the single-byte form), `rlpItemDecode_singleByte_eq` pins
    `next = cursor + 1`, `len = 1`, so the existential `Post` collapses to its concrete single-byte
    instance. Peels the `⌜rlpItemDecode⌝` fact out of the (17-atom) walk post to feed the
    determination, then substitutes. Serves as the `Post`-weakening in the single-byte field body. -/
theorem wd_decode_field0Walk_singleByte_post
    (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat) (vx1 : Word)
    (hoff : srcOff < srcBytes.length)
    (hsingle : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    {s : PartialState}
    (hp : ∃ next len,
        ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ next) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ vx1) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** bytesRegion srcBase srcBytes ** ⌜(0 : Word) = (0 : Word)⌝ **
          ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) s) :
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) **
      (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
      (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x1 ↦ᵣ vx1) **
      (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
        ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word)⌝) s := by
  obtain ⟨next, len, hX⟩ := hp
  have hrlp : rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    exact ((sepConj_pure_right _).1 hX).2
  obtain ⟨hn, hl⟩ := rlpItemDecode_singleByte_eq hoff hsingle hrlp
  rw [hn, hl] at hX
  exact hX

/-- **Short-byte-string resolution of the field-0 walk `Post`.** When the field's prefix byte is in
    `[0x80, 0xB8)` (the short-byte-string form), `rlpItemDecode_shortBytes_eq` pins
    `next = (cursor + 1) + (b − 0x80)`, `len = b − 0x80`; the `len` word is then folded to its
    `ofNat`-of-`Nat` form (via `rlpItemDecode_shortBytes_offsets`) so it matches the scalar body's
    `x12 = ofNat lenNat`. The short-string analogue of `wd_decode_field0Walk_singleByte_post`. -/
theorem wd_decode_field0Walk_shortBytes_post
    (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat) (vx1 : Word)
    (hoff : srcOff < srcBytes.length)
    (hlo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    {s : PartialState}
    (hp : ∃ next len,
        ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ next) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ vx1) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** bytesRegion srcBase srcBytes ** ⌜(0 : Word) = (0 : Word)⌝ **
          ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) s) :
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) **
      (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff + signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 ((srcBytes[srcOff]'hoff).toNat - 0x80))) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[srcOff]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ vx1) **
      (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
        ((srcBase + BitVec.ofNat 64 srcOff + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[srcOff]'hoff).toNat - 0x80))
        (BitVec.ofNat 64 ((srcBytes[srcOff]'hoff).toNat - 0x80))⌝) s := by
  obtain ⟨next, len, hX⟩ := hp
  have hrlp : rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    obtain ⟨_, _, _, _, _, hX⟩ := hX
    exact ((sepConj_pure_right _).1 hX).2
  obtain ⟨hn, hl⟩ := rlpItemDecode_shortBytes_eq hoff hlo hhi hrlp
  have hlenEq := (rlpItemDecode_shortBytes_offsets srcBase (srcBase + BitVec.ofNat 64 srcOff)
    ((srcBase + BitVec.ofNat 64 srcOff + signExtend12 (1 : BitVec 12)) +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)))
    ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)) (srcBytes[srcOff]'hoff) srcOff
    rfl hlo rfl rfl).2.1
  rw [hn, hl, hlenEq] at hX
  exact hX

/-- **Field-0 single-byte body** (idx 10–23, base+40 → base+96): the complete per-field decode for a
    single-byte scalar field 0. Composes the field walk (`wd_decode_field0Walk`, base+40 → base+56)
    — whose existential `Post` is collapsed to the single-byte instance via
    `wd_decode_field0Walk_singleByte_post` — with the scalar body+store
    (`wd_decode_field0Scalar_regOwn`, base+56 → base+96), framing the output struct cell through the
    walk and the saved `s2`/upper temporaries through the scalar. The decoded byte
    `b = srcBytes[srcOff]` (`b < 0x80` single-byte, `b ≠ 0` for scalar canonicity) is stored as the
    u64 `index` field at `struct + 0`. The first end-to-end field assembly of the monolith. -/
theorem wd_decode_field0BodySingleByte
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hsingle : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hbyte : getByteAt srcBytes srcOff ≠ 0) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 1 + 11)) + 2))
      (base + 40) (base + 96) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        ⌜0 < 1 ∧ getByteAt srcBytes srcOff ≠ 0 ∧ 1 ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  -- range facts about the single prefix byte (b < 0x80 ⟹ b < 0xb8, 0xf8, 192)
  have h_b8 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have h_f8 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  -- the field walk, with the decodability witness from the single-byte form
  have hwalk := wd_decode_field0Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff halign52 hdisjW hsalign hoff hover
    hvalid (fun hns _ => absurd hsingle hns) (fun hns _ => absurd h_b8 hns)
    (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_singleByte (List.getElem?_eq_getElem hoff) hsingle hin⟩
  -- collapse the walk's existential `Post` to the single-byte instance (explicit post: no η-redex)
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 40) (base + 56)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x1 ↦ᵣ (base + 52)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
          ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word)⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_singleByte_post srcBase endPtr srcBytes srcOff
        (base + 52) hoff hsingle hp) hwalk
  -- frame the output struct cell (untouched by the walk)
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  -- the scalar body+store at advanced = cursor+1, len = 1, framed with s2/upper temps
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field0Scalar_regOwn base srcBase (base + 52)
      ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (0 : Word) struct mOld
      srcBytes srcOff srcOff 1 hsalign hoff hover hvalid hlt192 halign88 hdisjC
      (by norm_num) (by omega) (by omega)
      (fun k hk => by
        have hk0 : k = 0 := by omega
        subst hk0
        rw [Nat.add_zero]; exact hvalid)
      (rlpItemDecode_singleByte_offsets srcBase (srcBase + BitVec.ofNat 64 srcOff)
        ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word) srcOff
        rfl rfl rfl).2
      (by norm_num) hbyte (by norm_num))
  -- stitch walk (single-byte) ⨾ scalar; drop the walk's residual pures at the seam
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  -- reshape so the two residual pures sit at the front, then peel them with `sepConj_pure_left`
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
        ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word)⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 52)) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-- **Field-0 short-byte-string body** (idx 10–23, base+40 → base+96): the complete per-field decode
    for a short-byte-string scalar field 0 (prefix `b ∈ [0x80, 0xB8)`, content `lenNat = b − 0x80`
    bytes at `off + 1`). The short-string sibling of `wd_decode_field0BodySingleByte`: the walk's
    `∃` is collapsed via `wd_decode_field0Walk_shortBytes_post`, the decodability witness comes from
    `rlpItemDecode_of_shortBytes` (needing the `len = 1` canonicity `hcanon` and the content-fit
    `hfit`), and the scalar reads `lenNat` content bytes from `off + 1`. The non-trivial `walk_next`
    obligation `hss` (content offset in bounds) is discharged from the content-length hypotheses. -/
theorem wd_decode_field0BodyShortBytes
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (off : Nat)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : off < srcBytes.length)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hcanon : (srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
      ∃ c : BitVec 8, srcBytes[off + 1]? = some c ∧ ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true)
    (hfit : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 off)) = true)
    (hcontentlen : off + 1 + ((srcBytes[off]'hoff).toNat - 0x80) ≤ srcBytes.length)
    (hcontentover : srcBase.toNat + (off + 1 + ((srcBytes[off]'hoff).toNat - 0x80)) ≤ 2 ^ 64)
    (hcontentvalid : ∀ k, k < (srcBytes[off]'hoff).toNat - 0x80 →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1 + k)) = true)
    (hpos : 0 < (srcBytes[off]'hoff).toNat - 0x80)
    (hbyte : getByteAt srcBytes (off + 1) ≠ 0)
    (hlen8 : (srcBytes[off]'hoff).toNat - 0x80 ≤ 8) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 40) (base + 96) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        ⌜0 < (srcBytes[off]'hoff).toNat - 0x80 ∧ getByteAt srcBytes (off + 1) ≠ 0 ∧
          (srcBytes[off]'hoff).toNat - 0x80 ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  -- range facts about the (short) prefix byte (0x80 ≤ b < 0xb8 ⟹ b < 0xf8, 192)
  have h_f8 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  -- the field walk, with the decodability witness from the short-byte-string form
  have hwalk := wd_decode_field0Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes off halign52 hdisjW hsalign hoff hover
    hvalid
    (fun _ _ => ⟨by omega, by omega, by simpa using hcontentvalid 0 hpos⟩)
    (fun hns _ => absurd hhi hns) (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_shortBytes (List.getElem?_eq_getElem hoff) hlo hhi hcanon hfit⟩
  -- collapse the walk's existential `Post` to the short-byte-string instance (explicit post)
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 40) (base + 56)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ (base + 52)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
          ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
          (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_shortBytes_post srcBase endPtr srcBytes off
        (base + 52) hoff hlo hhi hp) hwalk
  -- frame the output struct cell (untouched by the walk)
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  -- the scalar body+store at advanced = next, content offset off+1, len = b-0x80
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field0Scalar_regOwn base srcBase (base + 52)
      ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80)) (0 : Word) struct mOld
      srcBytes off (off + 1) ((srcBytes[off]'hoff).toNat - 0x80)
      hsalign hoff hover hvalid hlt192 halign88 hdisjC
      (by have := (srcBytes[off]'hoff).isLt; omega) hcontentlen hcontentover hcontentvalid
      (by
        have h1 : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
        simp only [h1]; bv_omega)
      hpos hbyte hlen8)
  -- stitch walk (short-string) ⨾ scalar; drop the walk's residual pures at the seam
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
        ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
        (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 52)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-! ## M3 proof — field-0 body composition (empty case) -/

/-- **Field-0 scalar body, empty arm** (idx 14–21, base+56 → base+88): `wd_decode_field0ScalarBody`
    with its 4-way `content_to_u64` status post **collapsed to the empty arm** via `c2u_status_empty`
    (`len = 0`). The post carries the value `a0 = 0` and `a1 = 0` (success). The empty-string sibling
    of `wd_decode_field0ScalarBodySuccess`. -/
theorem wd_decode_field0ScalarBodyEmpty (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 56) (base + 88) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 88)) ** bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝)) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => c2u_status_empty hlen0 hd)) _ hp)
    (wd_decode_field0ScalarBody base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign88 hdisj hlen64 hslen hsover
      hsvalid hcp)

/-- **Field-0 scalar decode, empty path** (idx 14–23, base+56 → base+96): the complete empty-string
    decode of field 0 — reject-check, scalar arithmetic, `content_to_u64` call (value `0`), status
    guard (fall-through), and store of `0` into `s0+0`. Composes `wd_decode_field0ScalarBodyEmpty`
    with `wd_decode_field0ScalarStore` (value `0`). The empty-string sibling of
    `wd_decode_field0Scalar`. -/
theorem wd_decode_field0ScalarEmpty (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct
    mOld : Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat)
    (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 56) (base + 96)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜len = 0⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hbody := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)) (by pcFree)
    (wd_decode_field0ScalarBodyEmpty base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign88 hdisj hlen64 hslen hsover
      hsvalid hcp hlen0)
  have hstore := cpsTripleWithin_frameL
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x1 ↦ᵣ (base + 88)) **
      bytesRegion srcBase srcBytes ** ⌜len = 0⌝ ** (.x9 ↦ᵣ advanced) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field0ScalarStore base struct (0 : Word) mOld)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody hstore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-0 empty scalar over `regOwn` scratch** (base+56 → base+96): `wd_decode_field0ScalarEmpty`
    with its four scratch temporaries supplied as `regOwn` (the form the preceding walk delivers).
    The empty-string sibling of `wd_decode_field0Scalar_regOwn`. -/
theorem wd_decode_field0ScalarEmpty_regOwn (base srcBase vOld advanced a1Old struct mOld : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisj : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 56) (base + 96)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28))
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜len = 0⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hgrouped : ∀ t0Old t1Old t2Old t3Old : Word,
      cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 56) (base + 96)
        (withdrawal_decode_code base)
        (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
          ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old)))
        ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
          (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
          ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
          ⌜len = 0⌝ **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
          ⌜(0 : Word) = (0 : Word)⌝) := by
    intro t0Old t1Old t2Old t3Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (wd_decode_field0ScalarEmpty base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct
        mOld srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign88 hdisj hlen64 hslen
        hsover hsvalid hcp hlen0)
  have hbody := cpsTripleWithin_exists_pre (fun t0Old : Word =>
    cpsTripleWithin_exists_pre (fun t1Old : Word =>
      cpsTripleWithin_exists_pre (fun t2Old : Word =>
        cpsTripleWithin_exists_pre (fun t3Old : Word => hgrouped t0Old t1Old t2Old t3Old))))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hp => ?_) hbody
  · obtain ⟨hM, hG, hd, hu, hMain, hGrp⟩ := hp
    obtain ⟨va, vb, vc, vd, hReg⟩ := regOwn4_exists hGrp
    exact ⟨va, vb, vc, vd, hM, hG, hd, hu, hMain, hReg⟩
  · obtain ⟨_, _, _, _, h⟩ := hp; exact h

/-- **Field-0 empty-string body** (idx 10–23, base+40 → base+96): the complete per-field decode for
    an empty scalar field 0 (prefix `0x80`, 0 content bytes, value `0` — the canonical RLP encoding
    of the scalar 0). The empty sibling of `wd_decode_field0BodySingleByte` /
    `wd_decode_field0BodyShortBytes`: the walk resolves the short-byte-string form with
    `lenNat = b − 0x80 = 0` (`hempty`), and the scalar takes the `content_to_u64` value-0 arm. The
    decodability witness's `len = 1` canonicity (`hcanon`) is vacuous (`b − 0x80 = 0 ≠ 1`) and the
    content-fit (`hfit`) reduces to the cursor being before the list end (`hin`). -/
theorem wd_decode_field0BodyEmpty
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (off : Nat)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : off < srcBytes.length)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0)
    (hoff1 : off + 1 < srcBytes.length) (hover1 : srcBase.toNat + (off + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1)) = true) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 40) (base + 96) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜(srcBytes[off]'hoff).toNat - 0x80 = 0⌝ **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  have hb := (srcBytes[off]'hoff).isLt
  have h_f8 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  -- the field walk; the empty item's decodability witness from the short-byte-string form (b=0x80)
  have hwalk := wd_decode_field0Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes off halign52 hdisjW hsalign hoff hover
    hvalid
    (fun _ _ => ⟨hoff1, hover1, hvalid1⟩)
    (fun hns _ => absurd hhi hns) (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_shortBytes (List.getElem?_eq_getElem hoff) hlo hhi
      (fun hc => by
        exfalso
        simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo
        bv_omega)
      (by
        simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo hin ⊢
        bv_omega)⟩
  -- collapse the walk's existential `Post` to the short-byte-string instance (explicit post)
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 40) (base + 56)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ (base + 52)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
          ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
          (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_shortBytes_post srcBase endPtr srcBytes off
        (base + 52) hoff hlo hhi hp) hwalk
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  -- the empty scalar body+store at advanced = next, content offset off+1, len = 0
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field0ScalarEmpty_regOwn base srcBase (base + 52)
      ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80)) (0 : Word) struct mOld
      srcBytes off (off + 1) ((srcBytes[off]'hoff).toNat - 0x80)
      hsalign hoff hover hvalid hlt192 halign88 hdisjC
      (by have := (srcBytes[off]'hoff).isLt; omega) (by omega) (by omega)
      (fun k hk => by omega)
      (by
        have h1 : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
        simp only [h1]; bv_omega)
      hempty)
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
        ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
        (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 52)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-! ## M3 proof — field-1 building blocks (idx 24–37, struct+8)

Field 1 (`validatorIndex` @ struct+8) is the same 14-instruction scalar shape as field 0, shifted
to idx 24–37 (bytes 96–148). The reject-check and scalar-arithmetic runBlocks are re-derived at the
field-1 offsets (the per-index program lookups pin them to concrete indices); the `idx`-parametric
blocks (`readPrefix`/`li`/`bgeu`) just take the field-1 indices. -/

/-- **Field-1 reject-check** (idx 28–30, base+112 → base+124): `prefix < 0xc0` (reject list-form
    items), the field-1 analogue of `wd_decode_field0RejectCheck` (fail offset 184). -/
theorem wd_decode_field1RejectCheck (base srcBase t0Old t1Old : Word) (srcBytes : List (BitVec 8))
    (cursorOff : Nat) (halign : srcBase.toNat % 8 = 0) (hi : cursorOff < srcBytes.length)
    (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 3 (base + 112) (base + 124) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
        (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** (.x6 ↦ᵣ (192 : Word)) **
        bytesRegion srcBase srcBytes **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) := by
  have h28 := cpsTripleWithin_frameR (.x6 ↦ᵣ t1Old) (by pcFree)
    (wd_decode_readPrefix base srcBase t0Old srcBytes cursorOff 28
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide) halign hi hover hvalid)
  rw [show base + BitVec.ofNat 64 112 = base + 112 from by bv_omega,
      show base + 112 + 4 = base + 116 from by bv_omega] at h28
  have h29 := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
      (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_decode_li base 29 .x6 (192 : Word) t1Old (by decide)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 116 = base + 116 from by bv_omega,
      show base + 116 + 4 = base + 120 from by bv_omega] at h29
  have h30 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_bgeu_lt base 30 .x5 .x6 (184 : BitVec 13)
      ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word) hlt
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 120 = base + 120 from by bv_omega,
      show base + 120 + 4 = base + 124 from by bv_omega] at h30
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr h28 h29) h30
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-1 scalar arithmetic** (idx 31–34, base+124 → base+140): `s1 := advanced`,
    `a0 := advanced − contentLen` (content pointer), `a1 := contentLen`, `t1 := content pointer` —
    the field-1 analogue of `wd_decode_scalarArith`. -/
theorem wd_decode_field1ScalarArith (base advanced contentLen s1Old t1Old a1Old : Word) :
    cpsTripleWithin 4 (base + 124) (base + 140) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ s1Old) ** (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old) **
        (.x6 ↦ᵣ t1Old))
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (advanced - contentLen)) ** (.x12 ↦ᵣ contentLen) **
        (.x11 ↦ᵣ contentLen) ** (.x6 ↦ᵣ (advanced - contentLen))) := by
  have hmv0 := mv_spec_gen_within .x9 .x10 advanced s1Old (base + 124) (by decide)
  have hsub := sub_spec_gen_within .x10 .x9 .x12 advanced contentLen advanced (base + 128) (by decide)
  have hmv1 := mv_spec_gen_within .x11 .x12 contentLen a1Old (base + 132) (by decide)
  have hmv2 := mv_spec_gen_within .x6 .x10 (advanced - contentLen) t1Old (base + 136) (by decide)
  runBlock hmv0 hsub hmv1 hmv2

/-- **Field-1 scalar prep** (reject-check ⨾ scalar arithmetic — idx 28–34, base+112 → base+140):
    the field-1 analogue of `wd_decode_field0ScalarPrep`. -/
theorem wd_decode_field1ScalarPrep (base srcBase t0Old t1Old advanced contentLen a1Old : Word)
    (srcBytes : List (BitVec 8)) (cursorOff : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 7 (base + 112) (base + 140) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) ** (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) **
        (.x6 ↦ᵣ (advanced - contentLen)) ** (.x10 ↦ᵣ (advanced - contentLen)) **
        (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ contentLen) ** bytesRegion srcBase srcBytes **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) := by
  have h_rc := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old)) (by pcFree)
    (wd_decode_field1RejectCheck base srcBase t0Old t1Old srcBytes cursorOff halign hi hover hvalid
      hlt)
  have h_sa := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field1ScalarArith base advanced contentLen (srcBase + BitVec.ofNat 64 cursorOff)
      (192 : Word) a1Old)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h_rc h_sa
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-1 `content_to_u64` call, over the full program code** (idx 35, base+140 → base+144): the
    `jal ra, rlp_content_to_u64` (immediate 816 → byte 956) lifted to the program code; the field-1
    analogue of `wd_call_c2u_field0`. -/
theorem wd_call_c2u_field1 (base srcBase vOld t0Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (halign : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length) (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (1 + (7 * len + 11)) (base + 140) (base + 144) (withdrawal_decode_code base)
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
         (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 144)) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
            (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h))) := by
  have hoffset : (base + 140) + signExtend21 (816 : BitVec 21) = base + 956 := by
    rw [show signExtend21 (816 : BitVec 21) = (816 : Word) from by decide]; bv_omega
  have hjal : withdrawal_decode_code base (base + 140) = some (.JAL .x1 (816 : BitVec 21)) := by
    have h := wd_prog_lookup base 35 (by rw [withdrawal_decode_prog_length]; norm_num)
    rw [show base + BitVec.ofNat 64 (4 * 35) = base + 140 from by bv_omega] at h
    rw [h]; decide
  have hcall := wd_call_content_to_u64 (base + 140) (base + 956) srcBase vOld t0Old t2Old t3Old
    srcBytes srcOff len (816 : BitVec 21) hoffset
    (by rw [show (base + 140) + 4 = base + 144 from by bv_omega]; exact halign) hdisj
    hlen64 hsalign hslen hsover hsvalid
  rw [show (base + 140) + 4 = base + 144 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code (wd_call_code_sub hjal (wd_c2uBody_sub base)) hcall

/-- **Field-1 scalar body** (idx 28–35, base+112 → base+144): prep ⨾ `content_to_u64` call, the
    field-1 analogue of `wd_decode_field0ScalarBody` (4-way status post). -/
theorem wd_decode_field1ScalarBody (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 112) (base + 144) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 144)) ** bytesRegion srcBase srcBytes) **
         (fun h =>
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
              ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
           (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
              (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h))) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) := by
  have hsp := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree)
    (wd_decode_field1ScalarPrep base srcBase t0Old t1Old advanced (BitVec.ofNat 64 len) a1Old
      srcBytes cursorOff halign hi hover hvalid hlt)
  have hc2u := wd_call_c2u_field1 base srcBase vOld ((srcBytes[cursorOff]'hi).zeroExtend 64) t2Old
    t3Old srcBytes srcOff len halign144 hdisj hlen64 halign hslen hsover hsvalid
  rw [← hcp] at hc2u
  have hc2u' := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree) hc2u
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsp hc2u'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hcomp

/-- **Field-1 scalar body, success arm** (idx 28–35, base+112 → base+144): the field-1 analogue of
    `wd_decode_field0ScalarBodySuccess` (4-way collapsed to the canonical-scalar success arm). -/
theorem wd_decode_field1ScalarBodySuccess (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 112) (base + 144) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 144)) ** bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝)) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => c2u_status_success hlen8 hpos hbyte hd)) _ hp)
    (wd_decode_field1ScalarBody base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign144 hdisj hlen64 hslen hsover
      hsvalid hcp)

/-- **Field-1 scalar store, success tail** (idx 36–37, base+144 → base+152): `bnez a1` (not taken)
    ⨾ `sd a0, 8(s0)` — stores the decoded u64 into the `validatorIndex` dword. The field-1 analogue
    of `wd_decode_field0ScalarStore` (struct offset 8). -/
theorem wd_decode_field1ScalarStore (base struct value mOld : Word) :
    cpsTripleWithin 2 (base + 144) (base + 152) (withdrawal_decode_code base)
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝ **
        (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ value)) := by
  have hb := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld))
    (by pcFree)
    (wd_bnez_notaken base 36 .x11 (160 : BitVec 13)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 144 = base + 144 from by bv_omega,
      show base + 144 + 4 = base + 148 from by bv_omega] at hb
  have hs := cpsTripleWithin_frameL
    ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝) (by pcFree)
    (wd_decode_storeScalar base struct value mOld 37 (8 : BitVec 12)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 148 = base + 148 from by bv_omega,
      show base + 148 + 4 = base + 152 from by bv_omega] at hs
  have hcomp := cpsTripleWithin_seq_same_cr hb hs
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-1 scalar decode, full success path** (idx 28–37, base+112 → base+152): the complete
    canonical-scalar decode of field 1 — writes `validatorIndex = fromBytesBE content` into
    `s0+8`. The field-1 analogue of `wd_decode_field0Scalar`. -/
theorem wd_decode_field1Scalar (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct mOld :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 112) (base + 152)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hbody := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)) (by pcFree)
    (wd_decode_field1ScalarBodySuccess base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign144 hdisj hlen64 hslen hsover
      hsvalid hcp hpos hbyte hlen8)
  have hstore := cpsTripleWithin_frameL
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x1 ↦ᵣ (base + 144)) **
      bytesRegion srcBase srcBytes **
      ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ ** (.x9 ↦ᵣ advanced) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field1ScalarStore base struct
      (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) mOld)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody hstore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-1 scalar over `regOwn` scratch** (base+112 → base+152): the field-1 analogue of
    `wd_decode_field0Scalar_regOwn` — the form the preceding walk delivers. -/
theorem wd_decode_field1Scalar_regOwn (base srcBase vOld advanced a1Old struct mOld : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 112) (base + 152)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28))
      ((.x9 ↦ᵣ advanced) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hgrouped : ∀ t0Old t1Old t2Old t3Old : Word,
      cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 112) (base + 152)
        (withdrawal_decode_code base)
        (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
          ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old)))
        ((.x9 ↦ᵣ advanced) **
          (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
          (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
          ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ
            BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
          ⌜(0 : Word) = (0 : Word)⌝) := by
    intro t0Old t1Old t2Old t3Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (wd_decode_field1Scalar base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct mOld
        srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign144 hdisj hlen64 hslen hsover
        hsvalid hcp hpos hbyte hlen8)
  have hbody := cpsTripleWithin_exists_pre (fun t0Old : Word =>
    cpsTripleWithin_exists_pre (fun t1Old : Word =>
      cpsTripleWithin_exists_pre (fun t2Old : Word =>
        cpsTripleWithin_exists_pre (fun t3Old : Word => hgrouped t0Old t1Old t2Old t3Old))))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hp => ?_) hbody
  · obtain ⟨hM, hG, hd, hu, hMain, hGrp⟩ := hp
    obtain ⟨va, vb, vc, vd, hReg⟩ := regOwn4_exists hGrp
    exact ⟨va, vb, vc, vd, hM, hG, hd, hu, hMain, hReg⟩
  · obtain ⟨_, _, _, _, h⟩ := hp; exact h

/-! ## M3 proof — field-1 walk (idx 24–27, base+96 → base+112) -/

/-- **Field-1 arg setup** (idx 24–25, base+96 → base+104): `mv a0,s1; mv a1,s2`, the field-1
    analogue of `wd_decode_fieldSetup`. -/
theorem wd_decode_field1FieldSetup (base cursor endv a0Old a1Old : Word) :
    cpsTripleWithin 2 (base + 96) (base + 104) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv)) := by
  have hmv0 := mv_spec_gen_within .x10 .x9 cursor a0Old (base + 96) (by decide)
  have hmv1 := mv_spec_gen_within .x11 .x18 endv a1Old (base + 100) (by decide)
  runBlock hmv0 hmv1

/-- **Field-1 `rlp_walk_next` call, over the full program code** (idx 26, base+104 → base+108):
    the `jal ra, rlp_walk_next` (immediate 440 → byte 544) lifted to the program code; the field-1
    analogue of `wd_call_walknext_field0`. -/
theorem wd_call_walknext_field1
    (base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : (base + 108) &&& ~~~1 = base + 108)
    (hdisj : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) (base + 104) (base + 108) (withdrawal_decode_code base)
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 108)) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h))) := by
  have hoffset : (base + 104) + signExtend21 (440 : BitVec 21) = base + 544 := by
    rw [show signExtend21 (440 : BitVec 21) = (440 : Word) from by decide]; bv_omega
  have hjal : withdrawal_decode_code base (base + 104) = some (.JAL .x1 (440 : BitVec 21)) := by
    have h := wd_prog_lookup base 26 (by rw [withdrawal_decode_prog_length]; norm_num)
    rw [show base + BitVec.ofNat 64 (4 * 26) = base + 104 from by bv_omega] at h
    rw [h]; decide
  have hcall := wd_call_walk_next (base + 104) (base + 544) srcBase endPtr vOld a2Old t0Old t1Old
    t2Old t3Old t4Old t5Old t6Old srcBytes srcOff (440 : BitVec 21) hoffset
    (by rw [show (base + 104) + 4 = base + 108 from by bv_omega]; exact halign) hdisj
    hsalign hoff hover hvalid hss hls hll
  rw [show (base + 104) + 4 = base + 108 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code (wd_call_code_sub hjal (wd_walkNextBody_sub base)) hcall

/-- **Field-1 walk_next status guard** (idx 27, base+108 → base+112): `bnez a1, fail` (not taken on
    success), the field-1 analogue of `wd_walknext_guard_success` (fail offset 196). -/
theorem wd_walknext_guard_success_field1 (base srcBase cursor endPtr vx1 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 (base + 108) (base + 112) (withdrawal_decode_code base)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
        rlpWalkNextOk cursor endPtr srcBytes srcOff)
      (fun s => ∃ next len,
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) s) := by
  have per : ∀ next len : Word,
      cpsTripleWithin 1 (base + 108) (base + 112) (withdrawal_decode_code base)
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) := by
    intro next len
    have hb := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
        ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝ **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) (by pcFree)
      (wd_bnez_notaken base 27 .x11 (196 : BitVec 13)
        (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
    rw [show base + BitVec.ofNat 64 108 = base + 108 from by bv_omega,
        show base + 108 + 4 = base + 112 from by bv_omega] at hb
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hb
  have htriple := cpsTripleWithin_exists_pre (fun next : Word =>
    cpsTripleWithin_exists_pre (fun len : Word => per next len))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hp => hp) htriple
  unfold rlpWalkNextOk at hp
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, hp2⟩

/-- **Field-1 walk** (idx 24–27, base+96 → base+112): arg setup ⨾ `walk_next` call ⨾ status guard,
    exposing `∃ next len, … ⌜rlpItemDecode …⌝`. The field-1 analogue of `wd_decode_field0Walk`. -/
theorem wd_decode_field1Walk (base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisj : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hdec : ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin (2 + (1 + 87) + 1) (base + 96) (base + 112) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      (fun s => ∃ next len,
        ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ next) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (base + 108)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** bytesRegion srcBase srcBytes ** ⌜(0 : Word) = (0 : Word)⌝ **
          ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) s) := by
  have hA := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree)
    (wd_decode_field1FieldSetup base (srcBase + BitVec.ofNat 64 srcOff) endPtr a0Old a1Old)
  have hB := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_call_walknext_field1 base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old
      t5Old t6Old srcBytes srcOff halign108 hdisj hsalign hoff hover hvalid hss hls hll)
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA hB
  have hABc := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun s hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => walknext_status_success hin hdec hd)) s hp) hAB
  have hC := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_walknext_guard_success_field1 base srcBase (srcBase + BitVec.ofNat 64 srcOff) endPtr
      (base + 108) srcBytes srcOff)
  have hABC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hABc hC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun s hp => ?_) hABC
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, by xperm_hyp hp2⟩

/-! ## M3 proof — field-1 bodies (idx 24–37, base+96 → base+152, struct+8) -/

/-- **Field-1 single-byte body** (base+96 → base+152): the complete single-byte decode of field 1,
    writing the decoded u64 (`validatorIndex`) into `s0+8`. The field-1 analogue of
    `wd_decode_field0BodySingleByte` (walk ⨾ scalar at the shifted offsets; `vx1 = base+108`). -/
theorem wd_decode_field1BodySingleByte
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisjW : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisjC : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hsingle : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hbyte : getByteAt srcBytes srcOff ≠ 0) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 1 + 11)) + 2))
      (base + 96) (base + 152) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        ⌜0 < 1 ∧ getByteAt srcBytes srcOff ≠ 0 ∧ 1 ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  have h_b8 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have h_f8 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have hwalk := wd_decode_field1Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff halign108 hdisjW hsalign hoff hover
    hvalid (fun hns _ => absurd hsingle hns) (fun hns _ => absurd h_b8 hns)
    (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_singleByte (List.getElem?_eq_getElem hoff) hsingle hin⟩
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 96) (base + 112)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x1 ↦ᵣ (base + 108)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
          ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word)⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_singleByte_post srcBase endPtr srcBytes srcOff
        (base + 108) hoff hsingle hp) hwalk
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field1Scalar_regOwn base srcBase (base + 108)
      ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (0 : Word) struct mOld
      srcBytes srcOff srcOff 1 hsalign hoff hover hvalid hlt192 halign144 hdisjC
      (by norm_num) (by omega) (by omega)
      (fun k hk => by
        have hk0 : k = 0 := by omega
        subst hk0
        rw [Nat.add_zero]; exact hvalid)
      (rlpItemDecode_singleByte_offsets srcBase (srcBase + BitVec.ofNat 64 srcOff)
        ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word) srcOff
        rfl rfl rfl).2
      (by norm_num) hbyte (by norm_num))
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
        ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word)⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 108)) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-- **Field-1 short-byte-string body** (base+96 → base+152): the complete short-string decode of
    field 1, writing the decoded u64 into `s0+8`. The field-1 analogue of
    `wd_decode_field0BodyShortBytes`. -/
theorem wd_decode_field1BodyShortBytes
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (off : Nat)
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisjW : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisjC : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : off < srcBytes.length)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hcanon : (srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
      ∃ c : BitVec 8, srcBytes[off + 1]? = some c ∧ ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true)
    (hfit : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 off)) = true)
    (hcontentlen : off + 1 + ((srcBytes[off]'hoff).toNat - 0x80) ≤ srcBytes.length)
    (hcontentover : srcBase.toNat + (off + 1 + ((srcBytes[off]'hoff).toNat - 0x80)) ≤ 2 ^ 64)
    (hcontentvalid : ∀ k, k < (srcBytes[off]'hoff).toNat - 0x80 →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1 + k)) = true)
    (hpos : 0 < (srcBytes[off]'hoff).toNat - 0x80)
    (hbyte : getByteAt srcBytes (off + 1) ≠ 0)
    (hlen8 : (srcBytes[off]'hoff).toNat - 0x80 ≤ 8) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 96) (base + 152) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        ⌜0 < (srcBytes[off]'hoff).toNat - 0x80 ∧ getByteAt srcBytes (off + 1) ≠ 0 ∧
          (srcBytes[off]'hoff).toNat - 0x80 ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  have h_f8 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hwalk := wd_decode_field1Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes off halign108 hdisjW hsalign hoff hover
    hvalid
    (fun _ _ => ⟨by omega, by omega, by simpa using hcontentvalid 0 hpos⟩)
    (fun hns _ => absurd hhi hns) (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_shortBytes (List.getElem?_eq_getElem hoff) hlo hhi hcanon hfit⟩
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 96) (base + 112)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ (base + 108)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
          ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
          (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_shortBytes_post srcBase endPtr srcBytes off
        (base + 108) hoff hlo hhi hp) hwalk
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field1Scalar_regOwn base srcBase (base + 108)
      ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80)) (0 : Word) struct mOld
      srcBytes off (off + 1) ((srcBytes[off]'hoff).toNat - 0x80)
      hsalign hoff hover hvalid hlt192 halign144 hdisjC
      (by have := (srcBytes[off]'hoff).isLt; omega) hcontentlen hcontentover hcontentvalid
      (by
        have h1 : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
        simp only [h1]; bv_omega)
      hpos hbyte hlen8)
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
        ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
        (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 108)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-! ## M3 proof — field-1 empty body (base+96 → base+152, struct+8) -/

/-- **Field-1 scalar body, empty arm** (base+112 → base+144): the field-1 analogue of
    `wd_decode_field0ScalarBodyEmpty`. -/
theorem wd_decode_field1ScalarBodyEmpty (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 112) (base + 144) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 144)) ** bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝)) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => c2u_status_empty hlen0 hd)) _ hp)
    (wd_decode_field1ScalarBody base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign144 hdisj hlen64 hslen hsover
      hsvalid hcp)

/-- **Field-1 scalar decode, empty path** (base+112 → base+152): writes `0` into `s0+8`. The
    field-1 analogue of `wd_decode_field0ScalarEmpty`. -/
theorem wd_decode_field1ScalarEmpty (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct
    mOld : Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat)
    (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 112) (base + 152)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜len = 0⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hbody := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)) (by pcFree)
    (wd_decode_field1ScalarBodyEmpty base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign144 hdisj hlen64 hslen hsover
      hsvalid hcp hlen0)
  have hstore := cpsTripleWithin_frameL
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x1 ↦ᵣ (base + 144)) **
      bytesRegion srcBase srcBytes ** ⌜len = 0⌝ ** (.x9 ↦ᵣ advanced) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field1ScalarStore base struct (0 : Word) mOld)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody hstore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-1 empty scalar over `regOwn` scratch** (base+112 → base+152): the field-1 analogue of
    `wd_decode_field0ScalarEmpty_regOwn`. -/
theorem wd_decode_field1ScalarEmpty_regOwn (base srcBase vOld advanced a1Old struct mOld : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisj : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 112) (base + 152)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28))
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜len = 0⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hgrouped : ∀ t0Old t1Old t2Old t3Old : Word,
      cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 112) (base + 152)
        (withdrawal_decode_code base)
        (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
          ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old)))
        ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
          (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
          ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
          ⌜len = 0⌝ **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
          ⌜(0 : Word) = (0 : Word)⌝) := by
    intro t0Old t1Old t2Old t3Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (wd_decode_field1ScalarEmpty base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct
        mOld srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign144 hdisj hlen64 hslen
        hsover hsvalid hcp hlen0)
  have hbody := cpsTripleWithin_exists_pre (fun t0Old : Word =>
    cpsTripleWithin_exists_pre (fun t1Old : Word =>
      cpsTripleWithin_exists_pre (fun t2Old : Word =>
        cpsTripleWithin_exists_pre (fun t3Old : Word => hgrouped t0Old t1Old t2Old t3Old))))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hp => ?_) hbody
  · obtain ⟨hM, hG, hd, hu, hMain, hGrp⟩ := hp
    obtain ⟨va, vb, vc, vd, hReg⟩ := regOwn4_exists hGrp
    exact ⟨va, vb, vc, vd, hM, hG, hd, hu, hMain, hReg⟩
  · obtain ⟨_, _, _, _, h⟩ := hp; exact h

/-- **Field-1 empty-string body** (base+96 → base+152): empty `validatorIndex` (prefix 0x80, value
    0 written to s0+8). The field-1 analogue of `wd_decode_field0BodyEmpty`. -/
theorem wd_decode_field1BodyEmpty
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (off : Nat)
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisjW : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisjC : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : off < srcBytes.length)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0)
    (hoff1 : off + 1 < srcBytes.length) (hover1 : srcBase.toNat + (off + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1)) = true) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 96) (base + 152) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜(srcBytes[off]'hoff).toNat - 0x80 = 0⌝ **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  have hb := (srcBytes[off]'hoff).isLt
  have h_f8 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hwalk := wd_decode_field1Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes off halign108 hdisjW hsalign hoff hover
    hvalid
    (fun _ _ => ⟨hoff1, hover1, hvalid1⟩)
    (fun hns _ => absurd hhi hns) (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_shortBytes (List.getElem?_eq_getElem hoff) hlo hhi
      (fun hc => by
        exfalso
        simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo
        bv_omega)
      (by
        simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo hin ⊢
        bv_omega)⟩
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 96) (base + 112)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ (base + 108)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
          ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
          (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_shortBytes_post srcBase endPtr srcBytes off
        (base + 108) hoff hlo hhi hp) hwalk
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field1ScalarEmpty_regOwn base srcBase (base + 108)
      ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80)) (0 : Word) struct mOld
      srcBytes off (off + 1) ((srcBytes[off]'hoff).toNat - 0x80)
      hsalign hoff hover hvalid hlt192 halign144 hdisjC
      (by have := (srcBytes[off]'hoff).isLt; omega) (by omega) (by omega)
      (fun k hk => by omega)
      (by
        have h1 : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
        simp only [h1]; bv_omega)
      hempty)
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
        ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
        (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 108)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-! ## M3 proof — field-3 building blocks (idx 55–68, struct+40)

Field 3 (`amount` @ struct+40, idx 55–68 = bytes 220–272) is the same 14-instruction scalar shape as
fields 0/1, shifted +124 bytes from field 1. Re-derived at the field-3 offsets (jal immediates
316/692, struct off 40, fail offsets 72/60/36). -/

/-- **Field-3 reject-check** (idx 59–61, base+236 → base+248): `prefix < 0xc0`, fail offset 60. -/
theorem wd_decode_field3RejectCheck (base srcBase t0Old t1Old : Word) (srcBytes : List (BitVec 8))
    (cursorOff : Nat) (halign : srcBase.toNat % 8 = 0) (hi : cursorOff < srcBytes.length)
    (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 3 (base + 236) (base + 248) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
        (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** (.x6 ↦ᵣ (192 : Word)) **
        bytesRegion srcBase srcBytes **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) := by
  have h59 := cpsTripleWithin_frameR (.x6 ↦ᵣ t1Old) (by pcFree)
    (wd_decode_readPrefix base srcBase t0Old srcBytes cursorOff 59
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide) halign hi hover hvalid)
  rw [show base + BitVec.ofNat 64 236 = base + 236 from by bv_omega,
      show base + 236 + 4 = base + 240 from by bv_omega] at h59
  have h60 := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
      (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_decode_li base 60 .x6 (192 : Word) t1Old (by decide)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 240 = base + 240 from by bv_omega,
      show base + 240 + 4 = base + 244 from by bv_omega] at h60
  have h61 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_bgeu_lt base 61 .x5 .x6 (60 : BitVec 13)
      ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word) hlt
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 244 = base + 244 from by bv_omega,
      show base + 244 + 4 = base + 248 from by bv_omega] at h61
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr h59 h60) h61
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-3 scalar arithmetic** (idx 62–65, base+248 → base+264). -/
theorem wd_decode_field3ScalarArith (base advanced contentLen s1Old t1Old a1Old : Word) :
    cpsTripleWithin 4 (base + 248) (base + 264) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ s1Old) ** (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old) **
        (.x6 ↦ᵣ t1Old))
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (advanced - contentLen)) ** (.x12 ↦ᵣ contentLen) **
        (.x11 ↦ᵣ contentLen) ** (.x6 ↦ᵣ (advanced - contentLen))) := by
  have hmv0 := mv_spec_gen_within .x9 .x10 advanced s1Old (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x10 .x9 .x12 advanced contentLen advanced (base + 252) (by decide)
  have hmv1 := mv_spec_gen_within .x11 .x12 contentLen a1Old (base + 256) (by decide)
  have hmv2 := mv_spec_gen_within .x6 .x10 (advanced - contentLen) t1Old (base + 260) (by decide)
  runBlock hmv0 hsub hmv1 hmv2

/-- **Field-3 scalar prep** (idx 59–65, base+236 → base+264). -/
theorem wd_decode_field3ScalarPrep (base srcBase t0Old t1Old advanced contentLen a1Old : Word)
    (srcBytes : List (BitVec 8)) (cursorOff : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 7 (base + 236) (base + 264) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) ** (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) **
        (.x6 ↦ᵣ (advanced - contentLen)) ** (.x10 ↦ᵣ (advanced - contentLen)) **
        (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ contentLen) ** bytesRegion srcBase srcBytes **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) := by
  have h_rc := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ contentLen) ** (.x11 ↦ᵣ a1Old)) (by pcFree)
    (wd_decode_field3RejectCheck base srcBase t0Old t1Old srcBytes cursorOff halign hi hover hvalid
      hlt)
  have h_sa := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field3ScalarArith base advanced contentLen (srcBase + BitVec.ofNat 64 cursorOff)
      (192 : Word) a1Old)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h_rc h_sa
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-3 `content_to_u64` call** (idx 66, base+264 → base+268, immediate 692 → byte 956). -/
theorem wd_call_c2u_field3 (base srcBase vOld t0Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (halign : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length) (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (1 + (7 * len + 11)) (base + 264) (base + 268) (withdrawal_decode_code base)
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
         (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 268)) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
            (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h))) := by
  have hoffset : (base + 264) + signExtend21 (692 : BitVec 21) = base + 956 := by
    rw [show signExtend21 (692 : BitVec 21) = (692 : Word) from by decide]; bv_omega
  have hjal : withdrawal_decode_code base (base + 264) = some (.JAL .x1 (692 : BitVec 21)) := by
    have h := wd_prog_lookup base 66 (by rw [withdrawal_decode_prog_length]; norm_num)
    rw [show base + BitVec.ofNat 64 (4 * 66) = base + 264 from by bv_omega] at h
    rw [h]; decide
  have hcall := wd_call_content_to_u64 (base + 264) (base + 956) srcBase vOld t0Old t2Old t3Old
    srcBytes srcOff len (692 : BitVec 21) hoffset
    (by rw [show (base + 264) + 4 = base + 268 from by bv_omega]; exact halign) hdisj
    hlen64 hsalign hslen hsover hsvalid
  rw [show (base + 264) + 4 = base + 268 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code (wd_call_code_sub hjal (wd_c2uBody_sub base)) hcall

/-- **Field-3 scalar body** (idx 59–66, base+236 → base+268). -/
theorem wd_decode_field3ScalarBody (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 236) (base + 268) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 268)) ** bytesRegion srcBase srcBytes) **
         (fun h =>
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
           (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
              ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
           (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
              (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝) h))) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) := by
  have hsp := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree)
    (wd_decode_field3ScalarPrep base srcBase t0Old t1Old advanced (BitVec.ofNat 64 len) a1Old
      srcBytes cursorOff halign hi hover hvalid hlt)
  have hc2u := wd_call_c2u_field3 base srcBase vOld ((srcBytes[cursorOff]'hi).zeroExtend 64) t2Old
    t3Old srcBytes srcOff len halign268 hdisj hlen64 halign hslen hsover hsvalid
  rw [← hcp] at hc2u
  have hc2u' := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree) hc2u
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsp hc2u'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hcomp

/-- **Field-3 scalar body, success arm** (idx 59–66, base+236 → base+268). -/
theorem wd_decode_field3ScalarBodySuccess (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 236) (base + 268) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 268)) ** bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝)) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => c2u_status_success hlen8 hpos hbyte hd)) _ hp)
    (wd_decode_field3ScalarBody base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign268 hdisj hlen64 hslen hsover
      hsvalid hcp)

/-- **Field-3 scalar store, success tail** (idx 67–68, base+268 → base+276): `bnez a1` ⨾
    `sd a0, 40(s0)` — stores the decoded `amount` u64 into `s0+40`. -/
theorem wd_decode_field3ScalarStore (base struct value mOld : Word) :
    cpsTripleWithin 2 (base + 268) (base + 276) (withdrawal_decode_code base)
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝ **
        (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ value)) := by
  have hb := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ value) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld))
    (by pcFree)
    (wd_bnez_notaken base 67 .x11 (36 : BitVec 13)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 268 = base + 268 from by bv_omega,
      show base + 268 + 4 = base + 272 from by bv_omega] at hb
  have hs := cpsTripleWithin_frameL
    ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝) (by pcFree)
    (wd_decode_storeScalar base struct value mOld 68 (40 : BitVec 12)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 272 = base + 272 from by bv_omega,
      show base + 272 + 4 = base + 276 from by bv_omega] at hs
  have hcomp := cpsTripleWithin_seq_same_cr hb hs
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-3 scalar decode, full success path** (idx 59–68, base+236 → base+276): writes
    `amount = fromBytesBE content` into `s0+40`. -/
theorem wd_decode_field3Scalar (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct mOld :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 236) (base + 276)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hbody := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)) (by pcFree)
    (wd_decode_field3ScalarBodySuccess base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign268 hdisj hlen64 hslen hsover
      hsvalid hcp hpos hbyte hlen8)
  have hstore := cpsTripleWithin_frameL
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x1 ↦ᵣ (base + 268)) **
      bytesRegion srcBase srcBytes **
      ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ ** (.x9 ↦ᵣ advanced) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field3ScalarStore base struct
      (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) mOld)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody hstore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-3 scalar over `regOwn` scratch** (base+236 → base+276). -/
theorem wd_decode_field3Scalar_regOwn (base srcBase vOld advanced a1Old struct mOld : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hpos : 0 < len) (hbyte : getByteAt srcBytes srcOff ≠ 0) (hlen8 : len ≤ 8) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 236) (base + 276)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28))
      ((.x9 ↦ᵣ advanced) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hgrouped : ∀ t0Old t1Old t2Old t3Old : Word,
      cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 236) (base + 276)
        (withdrawal_decode_code base)
        (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
          ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old)))
        ((.x9 ↦ᵣ advanced) **
          (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
          (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
          ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ
            BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
          ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0 ∧ len ≤ 8⌝ **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
          ⌜(0 : Word) = (0 : Word)⌝) := by
    intro t0Old t1Old t2Old t3Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (wd_decode_field3Scalar base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct mOld
        srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign268 hdisj hlen64 hslen hsover
        hsvalid hcp hpos hbyte hlen8)
  have hbody := cpsTripleWithin_exists_pre (fun t0Old : Word =>
    cpsTripleWithin_exists_pre (fun t1Old : Word =>
      cpsTripleWithin_exists_pre (fun t2Old : Word =>
        cpsTripleWithin_exists_pre (fun t3Old : Word => hgrouped t0Old t1Old t2Old t3Old))))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hp => ?_) hbody
  · obtain ⟨hM, hG, hd, hu, hMain, hGrp⟩ := hp
    obtain ⟨va, vb, vc, vd, hReg⟩ := regOwn4_exists hGrp
    exact ⟨va, vb, vc, vd, hM, hG, hd, hu, hMain, hReg⟩
  · obtain ⟨_, _, _, _, h⟩ := hp; exact h

/-! ## M3 proof — field-3 walk (idx 55–58, base+220 → base+236) -/

/-- **Field-3 arg setup** (idx 55–56, base+220 → base+228). -/
theorem wd_decode_field3FieldSetup (base cursor endv a0Old a1Old : Word) :
    cpsTripleWithin 2 (base + 220) (base + 228) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv)) := by
  have hmv0 := mv_spec_gen_within .x10 .x9 cursor a0Old (base + 220) (by decide)
  have hmv1 := mv_spec_gen_within .x11 .x18 endv a1Old (base + 224) (by decide)
  runBlock hmv0 hmv1

/-- **Field-3 `rlp_walk_next` call** (idx 57, base+228 → base+232, immediate 316 → byte 544). -/
theorem wd_call_walknext_field3
    (base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : (base + 232) &&& ~~~1 = base + 232)
    (hdisj : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) (base + 228) (base + 232) (withdrawal_decode_code base)
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 232)) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h))) := by
  have hoffset : (base + 228) + signExtend21 (316 : BitVec 21) = base + 544 := by
    rw [show signExtend21 (316 : BitVec 21) = (316 : Word) from by decide]; bv_omega
  have hjal : withdrawal_decode_code base (base + 228) = some (.JAL .x1 (316 : BitVec 21)) := by
    have h := wd_prog_lookup base 57 (by rw [withdrawal_decode_prog_length]; norm_num)
    rw [show base + BitVec.ofNat 64 (4 * 57) = base + 228 from by bv_omega] at h
    rw [h]; decide
  have hcall := wd_call_walk_next (base + 228) (base + 544) srcBase endPtr vOld a2Old t0Old t1Old
    t2Old t3Old t4Old t5Old t6Old srcBytes srcOff (316 : BitVec 21) hoffset
    (by rw [show (base + 228) + 4 = base + 232 from by bv_omega]; exact halign) hdisj
    hsalign hoff hover hvalid hss hls hll
  rw [show (base + 228) + 4 = base + 232 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code (wd_call_code_sub hjal (wd_walkNextBody_sub base)) hcall

/-- **Field-3 walk_next status guard** (idx 58, base+232 → base+236, fail offset 72). -/
theorem wd_walknext_guard_success_field3 (base srcBase cursor endPtr vx1 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 (base + 232) (base + 236) (withdrawal_decode_code base)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
        rlpWalkNextOk cursor endPtr srcBytes srcOff)
      (fun s => ∃ next len,
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) s) := by
  have per : ∀ next len : Word,
      cpsTripleWithin 1 (base + 232) (base + 236) (withdrawal_decode_code base)
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) := by
    intro next len
    have hb := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
        ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝ **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) (by pcFree)
      (wd_bnez_notaken base 58 .x11 (72 : BitVec 13)
        (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
    rw [show base + BitVec.ofNat 64 232 = base + 232 from by bv_omega,
        show base + 232 + 4 = base + 236 from by bv_omega] at hb
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hb
  have htriple := cpsTripleWithin_exists_pre (fun next : Word =>
    cpsTripleWithin_exists_pre (fun len : Word => per next len))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hp => hp) htriple
  unfold rlpWalkNextOk at hp
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, hp2⟩

/-- **Field-3 walk** (idx 55–58, base+220 → base+236). -/
theorem wd_decode_field3Walk (base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign232 : (base + 232) &&& ~~~1 = base + 232)
    (hdisj : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hdec : ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin (2 + (1 + 87) + 1) (base + 220) (base + 236) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      (fun s => ∃ next len,
        ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ next) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (base + 232)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** bytesRegion srcBase srcBytes ** ⌜(0 : Word) = (0 : Word)⌝ **
          ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) s) := by
  have hA := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree)
    (wd_decode_field3FieldSetup base (srcBase + BitVec.ofNat 64 srcOff) endPtr a0Old a1Old)
  have hB := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_call_walknext_field3 base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old
      t5Old t6Old srcBytes srcOff halign232 hdisj hsalign hoff hover hvalid hss hls hll)
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA hB
  have hABc := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun s hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => walknext_status_success hin hdec hd)) s hp) hAB
  have hC := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_walknext_guard_success_field3 base srcBase (srcBase + BitVec.ofNat 64 srcOff) endPtr
      (base + 232) srcBytes srcOff)
  have hABC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hABc hC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun s hp => ?_) hABC
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, by xperm_hyp hp2⟩

/-! ## M3 proof — field-3 bodies (idx 55–68, base+220 → base+276, struct+40) -/

/-- **Field-3 single-byte body** (base+220 → base+276): single-byte `amount` into `s0+40`. -/
theorem wd_decode_field3BodySingleByte
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign232 : (base + 232) &&& ~~~1 = base + 232)
    (hdisjW : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisjC : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hsingle : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hbyte : getByteAt srcBytes srcOff ≠ 0) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 1 + 11)) + 2))
      (base + 220) (base + 276) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        ⌜0 < 1 ∧ getByteAt srcBytes srcOff ≠ 0 ∧ 1 ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  have h_b8 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have h_f8 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hsingle ⊢; bv_omega
  have hwalk := wd_decode_field3Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff halign232 hdisjW hsalign hoff hover
    hvalid (fun hns _ => absurd hsingle hns) (fun hns _ => absurd h_b8 hns)
    (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_singleByte (List.getElem?_eq_getElem hoff) hsingle hin⟩
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 220) (base + 236)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x1 ↦ᵣ (base + 232)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
          ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word)⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_singleByte_post srcBase endPtr srcBytes srcOff
        (base + 232) hoff hsingle hp) hwalk
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field3Scalar_regOwn base srcBase (base + 232)
      ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (0 : Word) struct mOld
      srcBytes srcOff srcOff 1 hsalign hoff hover hvalid hlt192 halign268 hdisjC
      (by norm_num) (by omega) (by omega)
      (fun k hk => by
        have hk0 : k = 0 := by omega
        subst hk0
        rw [Nat.add_zero]; exact hvalid)
      (rlpItemDecode_singleByte_offsets srcBase (srcBase + BitVec.ofNat 64 srcOff)
        ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word) srcOff
        rfl rfl rfl).2
      (by norm_num) hbyte (by norm_num))
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
        ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word)⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 232)) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-- **Field-3 short-byte-string body** (base+220 → base+276): short-string `amount` into `s0+40`. -/
theorem wd_decode_field3BodyShortBytes
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (off : Nat)
    (halign232 : (base + 232) &&& ~~~1 = base + 232)
    (hdisjW : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisjC : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : off < srcBytes.length)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hcanon : (srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
      ∃ c : BitVec 8, srcBytes[off + 1]? = some c ∧ ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true)
    (hfit : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 off)) = true)
    (hcontentlen : off + 1 + ((srcBytes[off]'hoff).toNat - 0x80) ≤ srcBytes.length)
    (hcontentover : srcBase.toNat + (off + 1 + ((srcBytes[off]'hoff).toNat - 0x80)) ≤ 2 ^ 64)
    (hcontentvalid : ∀ k, k < (srcBytes[off]'hoff).toNat - 0x80 →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1 + k)) = true)
    (hpos : 0 < (srcBytes[off]'hoff).toNat - 0x80)
    (hbyte : getByteAt srcBytes (off + 1) ≠ 0)
    (hlen8 : (srcBytes[off]'hoff).toNat - 0x80 ≤ 8) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 220) (base + 276) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        ⌜0 < (srcBytes[off]'hoff).toNat - 0x80 ∧ getByteAt srcBytes (off + 1) ≠ 0 ∧
          (srcBytes[off]'hoff).toNat - 0x80 ≤ 8⌝ **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  have h_f8 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hwalk := wd_decode_field3Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes off halign232 hdisjW hsalign hoff hover
    hvalid
    (fun _ _ => ⟨by omega, by omega, by simpa using hcontentvalid 0 hpos⟩)
    (fun hns _ => absurd hhi hns) (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_shortBytes (List.getElem?_eq_getElem hoff) hlo hhi hcanon hfit⟩
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 220) (base + 236)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ (base + 232)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
          ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
          (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_shortBytes_post srcBase endPtr srcBytes off
        (base + 232) hoff hlo hhi hp) hwalk
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field3Scalar_regOwn base srcBase (base + 232)
      ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80)) (0 : Word) struct mOld
      srcBytes off (off + 1) ((srcBytes[off]'hoff).toNat - 0x80)
      hsalign hoff hover hvalid hlt192 halign268 hdisjC
      (by have := (srcBytes[off]'hoff).isLt; omega) hcontentlen hcontentover hcontentvalid
      (by
        have h1 : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
        simp only [h1]; bv_omega)
      hpos hbyte hlen8)
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
        ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
        (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 232)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-! ## M3 proof — field-3 empty body (base+220 → base+276, struct+40) -/

/-- **Field-3 scalar body, empty arm** (base+236 → base+268). -/
theorem wd_decode_field3ScalarBodyEmpty (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old :
    Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11))) (base + 236) (base + 268) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 268)) ** bytesRegion srcBase srcBytes) **
         ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝)) **
        ((.x9 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝)) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => c2u_status_empty hlen0 hd)) _ hp)
    (wd_decode_field3ScalarBody base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign268 hdisj hlen64 hslen hsover
      hsvalid hcp)

/-- **Field-3 scalar decode, empty path** (base+236 → base+276): writes `0` into `s0+40`. -/
theorem wd_decode_field3ScalarEmpty (base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct
    mOld : Word) (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat)
    (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 236) (base + 276)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜len = 0⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hbody := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)) (by pcFree)
    (wd_decode_field3ScalarBodyEmpty base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old
      srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign268 hdisj hlen64 hslen hsover
      hsvalid hcp hlen0)
  have hstore := cpsTripleWithin_frameL
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x1 ↦ᵣ (base + 268)) **
      bytesRegion srcBase srcBytes ** ⌜len = 0⌝ ** (.x9 ↦ᵣ advanced) **
      (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
      ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) (by pcFree)
    (wd_decode_field3ScalarStore base struct (0 : Word) mOld)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbody hstore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

/-- **Field-3 empty scalar over `regOwn` scratch** (base+236 → base+276). -/
theorem wd_decode_field3ScalarEmpty_regOwn (base srcBase vOld advanced a1Old struct mOld : Word)
    (srcBytes : List (BitVec 8)) (cursorOff srcOff len : Nat) (halign : srcBase.toNat % 8 = 0)
    (hi : cursorOff < srcBytes.length) (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisj : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hlen64 : len < 2 ^ 64) (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hcp : advanced - BitVec.ofNat 64 len = srcBase + BitVec.ofNat 64 srcOff)
    (hlen0 : len = 0) :
    cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 236) (base + 276)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) **
        bytesRegion srcBase srcBytes) **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28))
      ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜len = 0⌝ **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) := by
  have hgrouped : ∀ t0Old t1Old t2Old t3Old : Word,
      cpsTripleWithin (7 + (1 + (7 * len + 11)) + 2) (base + 236) (base + 276)
        (withdrawal_decode_code base)
        (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x10 ↦ᵣ advanced) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
          ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old)))
        ((.x9 ↦ᵣ advanced) ** (.x10 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x8 ↦ᵣ struct) **
          (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
          ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
          ⌜len = 0⌝ **
          ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝ **
          ⌜(0 : Word) = (0 : Word)⌝) := by
    intro t0Old t1Old t2Old t3Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (wd_decode_field3ScalarEmpty base srcBase vOld t0Old t1Old advanced a1Old t2Old t3Old struct
        mOld srcBytes cursorOff srcOff len halign hi hover hvalid hlt halign268 hdisj hlen64 hslen
        hsover hsvalid hcp hlen0)
  have hbody := cpsTripleWithin_exists_pre (fun t0Old : Word =>
    cpsTripleWithin_exists_pre (fun t1Old : Word =>
      cpsTripleWithin_exists_pre (fun t2Old : Word =>
        cpsTripleWithin_exists_pre (fun t3Old : Word => hgrouped t0Old t1Old t2Old t3Old))))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hp => ?_) hbody
  · obtain ⟨hM, hG, hd, hu, hMain, hGrp⟩ := hp
    obtain ⟨va, vb, vc, vd, hReg⟩ := regOwn4_exists hGrp
    exact ⟨va, vb, vc, vd, hM, hG, hd, hu, hMain, hReg⟩
  · obtain ⟨_, _, _, _, h⟩ := hp; exact h

/-- **Field-3 empty-string body** (base+220 → base+276): empty `amount` (value 0 into s0+40). -/
theorem wd_decode_field3BodyEmpty
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct mOld : Word)
    (srcBytes : List (BitVec 8)) (off : Nat)
    (halign232 : (base + 232) &&& ~~~1 = base + 232)
    (hdisjW : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisjC : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : off < srcBytes.length)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0)
    (hoff1 : off + 1 < srcBytes.length) (hover1 : srcBase.toNat + (off + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1)) = true) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 220) (base + 276) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        ⌜(srcBytes[off]'hoff).toNat - 0x80 = 0⌝ **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
        ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) := by
  have hb := (srcBytes[off]'hoff).isLt
  have h_f8 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hwalk := wd_decode_field3Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes off halign232 hdisjW hsalign hoff hover
    hvalid
    (fun _ _ => ⟨hoff1, hover1, hvalid1⟩)
    (fun hns _ => absurd hhi hns) (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_shortBytes (List.getElem?_eq_getElem hoff) hlo hhi
      (fun hc => by
        exfalso
        simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo
        bv_omega)
      (by
        simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo hin ⊢
        bv_omega)⟩
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 220) (base + 236)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ (base + 232)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
          ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
          (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_shortBytes_post srcBase endPtr srcBytes off
        (base + 232) hoff hlo hhi hp) hwalk
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)) (by pcFree) hwalkSB
  have hscalar := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field3ScalarEmpty_regOwn base srcBase (base + 232)
      ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80)) (0 : Word) struct mOld
      srcBytes off (off + 1) ((srcBytes[off]'hoff).toNat - 0x80)
      hsalign hoff hover hvalid hlt192 halign268 hdisjC
      (by have := (srcBytes[off]'hoff).isLt; omega) (by omega) (by omega)
      (fun k hk => by omega)
      (by
        have h1 : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide
        simp only [h1]; bv_omega)
      hempty)
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hscalar
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
        ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
        (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) **
          (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (base + 232)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
          ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** bytesRegion srcBase srcBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-! ## M3 proof — field-2 walk (idx 38–41, base+152 → base+168)

Field 2 (`address`, 20-byte fixed string @ struct+16) walk segment — the same shape as the scalar
fields' walk (jal@40 immediate 384, fail offset 140), feeding the 20-byte copy block. -/

/-- **Field-2 arg setup** (idx 38–39, base+152 → base+160). -/
theorem wd_decode_field2FieldSetup (base cursor endv a0Old a1Old : Word) :
    cpsTripleWithin 2 (base + 152) (base + 160) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endv) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endv)) := by
  have hmv0 := mv_spec_gen_within .x10 .x9 cursor a0Old (base + 152) (by decide)
  have hmv1 := mv_spec_gen_within .x11 .x18 endv a1Old (base + 156) (by decide)
  runBlock hmv0 hmv1

/-- **Field-2 `rlp_walk_next` call** (idx 40, base+160 → base+164, immediate 384 → byte 544). -/
theorem wd_call_walknext_field2
    (base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : (base + 164) &&& ~~~1 = base + 164)
    (hdisj : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) (base + 160) (base + 164) (withdrawal_decode_code base)
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 164)) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
              endPtr next len⌝) h))) := by
  have hoffset : (base + 160) + signExtend21 (384 : BitVec 21) = base + 544 := by
    rw [show signExtend21 (384 : BitVec 21) = (384 : Word) from by decide]; bv_omega
  have hjal : withdrawal_decode_code base (base + 160) = some (.JAL .x1 (384 : BitVec 21)) := by
    have h := wd_prog_lookup base 40 (by rw [withdrawal_decode_prog_length]; norm_num)
    rw [show base + BitVec.ofNat 64 (4 * 40) = base + 160 from by bv_omega] at h
    rw [h]; decide
  have hcall := wd_call_walk_next (base + 160) (base + 544) srcBase endPtr vOld a2Old t0Old t1Old
    t2Old t3Old t4Old t5Old t6Old srcBytes srcOff (384 : BitVec 21) hoffset
    (by rw [show (base + 160) + 4 = base + 164 from by bv_omega]; exact halign) hdisj
    hsalign hoff hover hvalid hss hls hll
  rw [show (base + 160) + 4 = base + 164 from by bv_omega] at hcall
  exact cpsTripleWithin_extend_code (wd_call_code_sub hjal (wd_walkNextBody_sub base)) hcall

/-- **Field-2 walk_next status guard** (idx 41, base+164 → base+168, fail offset 140). -/
theorem wd_walknext_guard_success_field2 (base srcBase cursor endPtr vx1 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 (base + 164) (base + 168) (withdrawal_decode_code base)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
        rlpWalkNextOk cursor endPtr srcBytes srcOff)
      (fun s => ∃ next len,
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) s) := by
  have per : ∀ next len : Word,
      cpsTripleWithin 1 (base + 164) (base + 168) (withdrawal_decode_code base)
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝))
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** ⌜(0 : Word) = (0 : Word)⌝ **
            ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝)) := by
    intro next len
    have hb := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
        ⌜rlpItemDecode srcBytes srcOff cursor endPtr next len⌝ **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x1 ↦ᵣ vx1) ** bytesRegion srcBase srcBytes) (by pcFree)
      (wd_bnez_notaken base 41 .x11 (140 : BitVec 13)
        (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
    rw [show base + BitVec.ofNat 64 164 = base + 164 from by bv_omega,
        show base + 164 + 4 = base + 168 from by bv_omega] at hb
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hb
  have htriple := cpsTripleWithin_exists_pre (fun next : Word =>
    cpsTripleWithin_exists_pre (fun len : Word => per next len))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hp => hp) htriple
  unfold rlpWalkNextOk at hp
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, hp2⟩

/-- **Field-2 walk** (idx 38–41, base+152 → base+168). -/
theorem wd_decode_field2Walk (base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign164 : (base + 164) &&& ~~~1 = base + 164)
    (hdisj : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hdec : ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin (2 + (1 + 87) + 1) (base + 152) (base + 168) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      (fun s => ∃ next len,
        ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ next) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (base + 164)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** bytesRegion srcBase srcBytes ** ⌜(0 : Word) = (0 : Word)⌝ **
          ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) s) := by
  have hA := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree)
    (wd_decode_field2FieldSetup base (srcBase + BitVec.ofNat 64 srcOff) endPtr a0Old a1Old)
  have hB := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_call_walknext_field2 base srcBase endPtr vOld a2Old t0Old t1Old t2Old t3Old t4Old
      t5Old t6Old srcBytes srcOff halign164 hdisj hsalign hoff hover hvalid hss hls hll)
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA hB
  have hABc := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun s hp => sepConj_mono_left
      (sepConj_mono_right (fun _ hd => walknext_status_success hin hdec hd)) s hp) hAB
  have hC := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr)) (by pcFree)
    (wd_walknext_guard_success_field2 base srcBase (srcBase + BitVec.ofNat 64 srcOff) endPtr
      (base + 164) srcBytes srcOff)
  have hABC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hABc hC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun s hp => ?_) hABC
  obtain ⟨next, hp1⟩ := sepConj_exists_right hp
  obtain ⟨len, hp2⟩ := sepConj_exists_right hp1
  exact ⟨next, len, by xperm_hyp hp2⟩

/-- **Field-2 reject-check** (idx 42–44, base+168 → base+180): `prefix < 0xc0` (reject list-form
    items), fail offset 128. The address is a short string so its prefix (0x94 for 20 bytes) is
    below 0xc0. -/
theorem wd_decode_field2RejectCheck (base srcBase t0Old t1Old : Word) (srcBytes : List (BitVec 8))
    (cursorOff : Nat) (halign : srcBase.toNat % 8 = 0) (hi : cursorOff < srcBytes.length)
    (hover : srcBase.toNat + cursorOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 cursorOff) = true)
    (hlt : BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 3 (base + 168) (base + 180) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
        (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** (.x6 ↦ᵣ (192 : Word)) **
        bytesRegion srcBase srcBytes **
        ⌜BitVec.ult ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word)⌝) := by
  have h42 := cpsTripleWithin_frameR (.x6 ↦ᵣ t1Old) (by pcFree)
    (wd_decode_readPrefix base srcBase t0Old srcBytes cursorOff 42
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide) halign hi hover hvalid)
  rw [show base + BitVec.ofNat 64 168 = base + 168 from by bv_omega,
      show base + 168 + 4 = base + 172 from by bv_omega] at h42
  have h43 := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) **
      (.x5 ↦ᵣ ((srcBytes[cursorOff]'hi).zeroExtend 64)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_decode_li base 43 .x6 (192 : Word) t1Old (by decide)
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 172 = base + 172 from by bv_omega,
      show base + 172 + 4 = base + 176 from by bv_omega] at h43
  have h44 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 cursorOff)) ** bytesRegion srcBase srcBytes)
    (by pcFree)
    (wd_bgeu_lt base 44 .x5 .x6 (128 : BitVec 13)
      ((srcBytes[cursorOff]'hi).zeroExtend 64) (192 : Word) hlt
      (by rw [withdrawal_decode_prog_length]; norm_num) (by decide))
  rw [show base + BitVec.ofNat 64 176 = base + 176 from by bv_omega,
      show base + 176 + 4 = base + 180 from by bv_omega] at h44
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr h42 h43) h44
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

end EvmAsm.Rv64.RLP
