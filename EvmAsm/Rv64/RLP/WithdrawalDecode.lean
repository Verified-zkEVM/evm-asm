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

end EvmAsm.Rv64.RLP
