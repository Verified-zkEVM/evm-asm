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
import EvmAsm.Rv64.BitAux
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
import EvmAsm.Rv64.RLP.ByteCopyChainGen
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
`rlp_walk_next_prog`, `rlp_content_to_u64_prog`, and the 20-byte-address `withdrawal_copy_routine`
are appended after the 83-instruction glue, and the glue's `JAL`s target them at concrete
PC-relative offsets (since `emitProgram` renders `JAL` as `.+N`). Layout (instruction indices):

  glue            0   .. 82   (83 instrs)
  rlp_walk_init   83  .. 135  (53)
  rlp_walk_next   136 .. 238  (103)
  rlp_content_to_u64  239 .. 260  (22)
  copy_routine    261 .. 361  (101 = 100-instr byte-copy chain + `ret`)

Calling convention (drop-in identical to the old `withdrawal_decode`): `a0 = rlp ptr`,
`a1 = rlp len`, `a2 = struct out ptr`; on return `a0 = 0` success / `a0 = 1` failure;
`ra`/`s0`/`s1`/`s2` preserved via a 32-byte frame. Registers: `s0 = struct`, `s1 = cursor`,
`s2 = end`, `t0 = x5`, `t1 = x6` (also the `rlp_content_to_u64` content pointer). -/

/-- The 83-instruction glue: prologue, `walk_init`, four field decodes (`walk_next` →
    reject-list → `content_to_u64` / `jal` to the 20-byte copy routine → store → advance), an
    exact-arity check (a 5th `walk_next` must report end-of-list, status 2), then success/fail
    epilogue. (Field 2's address copy is a `jal` to `withdrawal_copy_routine`; idx 51..54 are
    `nop`s the routine returns into.) -/
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
    .SUB .x13 .x9 .x12,                      -- 48 sub a3, s1, a2 (a3 = contentPtr)
    .ADDI .x14 .x8 (16 : BitVec 12),         -- 49 addi a4, s0, 16 (a4 = struct+16 dst)
    .JAL .x1 (844 : BitVec 21),              -- 50 jal ra, copy_routine (→ 261)
    .NOP,                                    -- 51 nop (copy_routine returns here)
    .NOP,                                    -- 52 nop
    .NOP,                                    -- 53 nop
    .NOP,                                    -- 54 nop
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

/-- The unrolled `N`-byte copy chain as a concrete instruction list (block `j` at offset `20*j`),
    matching `byteCopyChainCR`: each block is `lbu x12,0(x13); sb x12,0(x14); x13++; x14++; x15--`. -/
def byteCopyChainInstrs : Nat → List Instr
  | 0 => []
  | n + 1 =>
    [.LBU .x12 .x13 0, .SB .x14 .x12 0, .ADDI .x13 .x13 1, .ADDI .x14 .x14 1,
     .ADDI .x15 .x15 (-1)] ++ byteCopyChainInstrs n

theorem byteCopyChainInstrs_length (N : Nat) : (byteCopyChainInstrs N).length = 5 * N := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [byteCopyChainInstrs, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

/-- The appended 20-byte address copy routine: the unrolled 100-instruction copy chain followed
    by `ret` (`jalr x0, ra, 0`). Entered by `jal ra` from field 2; returns to the link register. -/
def withdrawal_copy_routine : List Instr :=
  byteCopyChainInstrs 20 ++ [.JALR .x0 .x1 (0 : BitVec 12)]

theorem withdrawal_copy_routine_length : withdrawal_copy_routine.length = 101 := by
  simp only [withdrawal_copy_routine, List.length_append, byteCopyChainInstrs_length,
    List.length_cons, List.length_nil]

/-- The full self-contained drop-in: glue ⧺ the three verified leaf programs ⧺ the copy routine.
    The glue's `JAL`s target `rlp_walk_init` (idx 83), `rlp_walk_next` (idx 136),
    `rlp_content_to_u64` (idx 239), and `withdrawal_copy_routine` (idx 261). -/
def withdrawal_decode_prog : List Instr :=
  withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog
    ++ withdrawal_copy_routine

theorem withdrawal_decode_glue_length : withdrawal_decode_glue.length = 83 := rfl

theorem withdrawal_decode_prog_length : withdrawal_decode_prog.length = 362 := by
  simp only [withdrawal_decode_prog, List.length_append, withdrawal_decode_glue_length,
    rlp_walk_init_prog_length, rlp_walk_next_prog_length, rlp_content_to_u64_prog_length,
    withdrawal_copy_routine_length]

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
    `t0..t6` and `a3..a5` (`x13`/`x14`/`x15`, used by the address copy) are clobbered. The
    well-formedness hypotheses (alignment, in-range byte-access
    validity, `|srcBytes| < 2^64`) are the standard side-conditions the verified leaves require. -/
def withdrawal_decode_characterization
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte) : Prop :=
  base &&& 1 = 0 →
  base.toNat + 1444 < 2 ^ 64 →
  srcBase.toNat % 8 = 0 →
  outPtr.toNat % 8 = 0 →
  srcBytes.length < 2 ^ 64 →
  srcBase.toNat + srcBytes.length < 2 ^ 64 →
  outPtr.toNat + 48 < 2 ^ 64 →
  (∀ k, k < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) →
  (∀ k, k < 48 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) →
  cpsTripleWithin 2048 base (raVal &&& ~~~1) (withdrawal_decode_code base)
    -- precondition
    ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
      (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
      (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
      wd_frameOwned sp0 **
      bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : Byte)))
    -- postcondition: shared frame + (success ∨ failure), anchored on `decodeWithdrawal`
    (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
      (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
      wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
      wd_frameOwned sp0 **
      bytesRegion srcBase srcBytes) **
     (fun h =>
       (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
          ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
            ∧ d2.length = 20⌝) h)) ∨
       (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
          ⌜decodeWithdrawal srcBytes = none⌝) h)))

/-- **Return-point alignment facts.** Every jal-return PC `base + k` (k a multiple of 4) survives
    the JALR low-bit mask when `base` is even. The 10 `halign…` hypotheses the success leaf (and the
    fail tree) thread are exactly these, discharged from one base-evenness fact via
    `BitAux.word_add_even_andn_one`. -/
theorem wd_decode_align_facts (base : Word) (hbe : base &&& 1 = 0) :
    ((base + 28) &&& ~~~1 = base + 28) ∧ ((base + 52) &&& ~~~1 = base + 52) ∧
    ((base + 88) &&& ~~~1 = base + 88) ∧ ((base + 108) &&& ~~~1 = base + 108) ∧
    ((base + 144) &&& ~~~1 = base + 144) ∧ ((base + 164) &&& ~~~1 = base + 164) ∧
    ((base + 204) &&& ~~~1 = base + 204) ∧ ((base + 232) &&& ~~~1 = base + 232) ∧
    ((base + 268) &&& ~~~1 = base + 268) ∧ ((base + 288) &&& ~~~1 = base + 288) :=
  ⟨BitAux.word_add_even_andn_one hbe (by decide), BitAux.word_add_even_andn_one hbe (by decide),
   BitAux.word_add_even_andn_one hbe (by decide), BitAux.word_add_even_andn_one hbe (by decide),
   BitAux.word_add_even_andn_one hbe (by decide), BitAux.word_add_even_andn_one hbe (by decide),
   BitAux.word_add_even_andn_one hbe (by decide), BitAux.word_add_even_andn_one hbe (by decide),
   BitAux.word_add_even_andn_one hbe (by decide), BitAux.word_add_even_andn_one hbe (by decide)⟩

/-- **Call-site / callee-code disjointness facts.** Each `jal` instruction (a one-instruction
    `CodeReq.singleton` at `base + j`) sits strictly before the appended callee block it targets
    (`rlp_walk_init` at `base+332`, `rlp_walk_next` at `base+544`, `rlp_content_to_u64` at
    `base+956`), so their `CodeReq`s are disjoint. The 9 `hdisj…` hypotheses the success leaf (and
    the fail tree) thread, discharged from one base-range fact via `singleton_ofProg` +
    `ofProg_none_range_len` (the singleton's address is below every callee instruction). -/
theorem wd_decode_disjoint_facts (base : Word) (hbase : base.toNat + 1444 < 2 ^ 64) :
    ((CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332))) ∧
    ((CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544))) ∧
    ((CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956))) ∧
    ((CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544))) ∧
    ((CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956))) ∧
    ((CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544))) ∧
    ((CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544))) ∧
    ((CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956))) ∧
    ((CodeReq.singleton (base + 284) (.JAL .x1 (260 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544))) :=
  ⟨CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 332)
      rlp_walk_init_prog 53 (base + 24) rlp_walk_init_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 544)
      rlp_walk_next_prog 103 (base + 48) rlp_walk_next_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 956)
      rlp_content_to_u64_prog 22 (base + 84) rlp_content_to_u64_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 544)
      rlp_walk_next_prog 103 (base + 104) rlp_walk_next_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 956)
      rlp_content_to_u64_prog 22 (base + 140) rlp_content_to_u64_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 544)
      rlp_walk_next_prog 103 (base + 160) rlp_walk_next_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 544)
      rlp_walk_next_prog 103 (base + 228) rlp_walk_next_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 956)
      rlp_content_to_u64_prog 22 (base + 264) rlp_content_to_u64_prog_length (fun k hk => by bv_omega)),
   CodeReq.Disjoint.singleton_ofProg (CodeReq.ofProg_none_range_len (base + 544)
      rlp_walk_next_prog 103 (base + 284) rlp_walk_next_prog_length (fun k hk => by bv_omega))⟩

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
          (rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog
            ++ withdrawal_copy_routine) := by
    simp only [withdrawal_decode_prog, List.append_assoc]
  have h1 := CodeReq.ofProg_mono_append_left (base + 332) rlp_walk_init_prog rlp_walk_next_prog
    a i hwi
  have h2 := CodeReq.ofProg_mono_append_left (base + 332)
    (rlp_walk_init_prog ++ rlp_walk_next_prog) rlp_content_to_u64_prog a i h1
  have h3 := CodeReq.ofProg_mono_append_left (base + 332)
    (rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog) withdrawal_copy_routine
    a i h2
  have hr := CodeReq.ofProg_mono_append_right base withdrawal_decode_glue
    (rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog ++ withdrawal_copy_routine)
    (by rw [← hrest, withdrawal_decode_prog_length]; norm_num) a i
  rw [withdrawal_decode_glue_length,
      show base + BitVec.ofNat 64 (4 * 83) = base + 332 from by bv_omega] at hr
  rw [withdrawal_decode_code, hrest]
  exact hr h3

/-- The appended `rlp_walk_next` body (idx 136, byte 544) is a segment of the program. -/
theorem wd_walkNextBody_sub (base : Word) :
    ∀ a i, (rlp_walk_next_code (base + 544)) a = some i →
           withdrawal_decode_code base a = some i := by
  intro a i hwn
  have hrest : withdrawal_decode_prog
      = (withdrawal_decode_glue ++ rlp_walk_init_prog) ++
          (rlp_walk_next_prog ++ rlp_content_to_u64_prog ++ withdrawal_copy_routine) := by
    simp only [withdrawal_decode_prog, List.append_assoc]
  have h1 := CodeReq.ofProg_mono_append_left (base + 544) rlp_walk_next_prog rlp_content_to_u64_prog
    a i hwn
  have h2 := CodeReq.ofProg_mono_append_left (base + 544)
    (rlp_walk_next_prog ++ rlp_content_to_u64_prog) withdrawal_copy_routine a i h1
  have hr := CodeReq.ofProg_mono_append_right base (withdrawal_decode_glue ++ rlp_walk_init_prog)
    (rlp_walk_next_prog ++ rlp_content_to_u64_prog ++ withdrawal_copy_routine)
    (by rw [← hrest, withdrawal_decode_prog_length]; norm_num) a i
  rw [show (withdrawal_decode_glue ++ rlp_walk_init_prog).length = 136 from by
        simp [List.length_append, withdrawal_decode_glue_length, rlp_walk_init_prog_length],
      show base + BitVec.ofNat 64 (4 * 136) = base + 544 from by bv_omega] at hr
  rw [withdrawal_decode_code, hrest]
  exact hr h2

/-- The appended `rlp_content_to_u64` body (idx 239, byte 956) is a segment of the program. -/
theorem wd_c2uBody_sub (base : Word) :
    ∀ a i, (rlp_content_to_u64_code (base + 956)) a = some i →
           withdrawal_decode_code base a = some i := by
  intro a i hc
  have hrest : withdrawal_decode_prog
      = (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog) ++
          (rlp_content_to_u64_prog ++ withdrawal_copy_routine) := by
    simp only [withdrawal_decode_prog, List.append_assoc]
  have h1 := CodeReq.ofProg_mono_append_left (base + 956) rlp_content_to_u64_prog
    withdrawal_copy_routine a i hc
  have hr := CodeReq.ofProg_mono_append_right base
    (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog)
    (rlp_content_to_u64_prog ++ withdrawal_copy_routine)
    (by rw [← hrest, withdrawal_decode_prog_length]; norm_num) a i
  rw [show (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog).length = 239 from by
        simp [List.length_append, withdrawal_decode_glue_length, rlp_walk_init_prog_length,
              rlp_walk_next_prog_length],
      show base + BitVec.ofNat 64 (4 * 239) = base + 956 from by bv_omega] at hr
  rw [withdrawal_decode_code, hrest]
  exact hr h1

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

/-! ### Field-2 address copy: lifting the verified byte-copy chain into the program

The 20-byte address copy is the appended `withdrawal_copy_routine` (`byteCopyChainInstrs 20 ++
[ret]`, idx 261..361). Its CodeReq comes from `rlp_copy_chain_gen_spec`, which is stated over
`byteCopyChainCR` (a `copyIterCR`-union, not an `ofProg`). The bridge below shows
`byteCopyChainCR b N ⊆ ofProg b (byteCopyChainInstrs N)`, then `wd_copyChainBody_sub` lifts the
chain at `base + 1044` (= byte `4*261`) into the full program. -/

/-- One copy block's `copyIterCR` is contained in the `ofProg` of its 5 instructions. -/
private theorem copyIterCR_sub_ofProg_block (b : Word) :
    ∀ a i, copyIterCR b a = some i →
      CodeReq.ofProg b [(.LBU .x12 .x13 0 : Instr), .SB .x14 .x12 0, .ADDI .x13 .x13 1,
        .ADDI .x14 .x14 1, .ADDI .x15 .x15 (-1)] a = some i := by
  have e : ∀ (k : Nat) (hk : k < 5) (addr : Word), addr = b + BitVec.ofNat 64 (4 * k) →
      CodeReq.ofProg b [(.LBU .x12 .x13 0 : Instr), .SB .x14 .x12 0, .ADDI .x13 .x13 1,
        .ADDI .x14 .x14 1, .ADDI .x15 .x15 (-1)] addr
        = some (([(.LBU .x12 .x13 0 : Instr), .SB .x14 .x12 0, .ADDI .x13 .x13 1,
            .ADDI .x14 .x14 1, .ADDI .x15 .x15 (-1)]).get ⟨k, hk⟩) :=
    fun k hk addr ha => CodeReq.ofProg_lookup_addr b
      [(.LBU .x12 .x13 0 : Instr), .SB .x14 .x12 0, .ADDI .x13 .x13 1, .ADDI .x14 .x14 1,
        .ADDI .x15 .x15 (-1)] k addr hk (by decide) ha
  refine CodeReq.union_sub (CodeReq.union_sub (CodeReq.union_sub
    (CodeReq.union_sub ?_ ?_) ?_) ?_) ?_
  · exact CodeReq.singleton_mono (e 0 (by decide) b (by bv_omega))
  · exact CodeReq.singleton_mono (e 1 (by decide) (b + 4) (by bv_omega))
  · exact CodeReq.singleton_mono (e 2 (by decide) (b + 8) (by bv_omega))
  · exact CodeReq.singleton_mono (e 3 (by decide) (b + 12) (by bv_omega))
  · exact CodeReq.singleton_mono (e 4 (by decide) (b + 16) (by bv_omega))

/-- **Bridge: the unrolled copy chain's CodeReq is contained in the `ofProg` of its instructions.**
    By induction on `N`, reusing `copyIterCR_sub_ofProg_block` and the `ofProg` append lemmas. -/
theorem byteCopyChainCR_sub_ofProg : ∀ (N : Nat) (b : Word), 4 * (5 * N) < 2 ^ 64 →
    ∀ a i, byteCopyChainCR b N a = some i →
      CodeReq.ofProg b (byteCopyChainInstrs N) a = some i := by
  intro N
  induction N with
  | zero => intro b _ a i h; simp [byteCopyChainCR, CodeReq.empty] at h
  | succ n ih =>
    intro b hbound a i h
    rw [byteCopyChainInstrs]
    rw [byteCopyChainCR] at h
    refine CodeReq.union_sub ?_ ?_ a i h
    · intro a' i' hc
      exact CodeReq.ofProg_mono_append_left b _ _ a' i' (copyIterCR_sub_ofProg_block b a' i' hc)
    · intro a' i' hc
      have htail := ih (b + 20) (by omega) a' i' hc
      have happ := CodeReq.ofProg_mono_append_right b
        [(.LBU .x12 .x13 0 : Instr), .SB .x14 .x12 0, .ADDI .x13 .x13 1, .ADDI .x14 .x14 1,
          .ADDI .x15 .x15 (-1)] (byteCopyChainInstrs n)
        (by rw [List.length_append, byteCopyChainInstrs_length]
            simp only [List.length_cons, List.length_nil]; omega) a' i'
      simp only [List.length_cons, List.length_nil] at happ
      rw [show b + BitVec.ofNat 64 (4 * 5) = b + 20 from by bv_omega] at happ
      exact happ htail

/-- The appended `withdrawal_copy_routine` (idx 261, byte 1044) is a program segment. -/
theorem wd_routineBody_sub (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1044) withdrawal_copy_routine) a = some i →
           withdrawal_decode_code base a = some i := by
  intro a i h
  have hrest : withdrawal_decode_prog
      = (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog
          ++ rlp_content_to_u64_prog) ++ withdrawal_copy_routine := by
    simp only [withdrawal_decode_prog, List.append_assoc]
  have hr := CodeReq.ofProg_mono_append_right base
    (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog ++ rlp_content_to_u64_prog)
    withdrawal_copy_routine
    (by rw [← hrest, withdrawal_decode_prog_length]; norm_num) a i
  rw [show (withdrawal_decode_glue ++ rlp_walk_init_prog ++ rlp_walk_next_prog
        ++ rlp_content_to_u64_prog).length = 261 from by
        simp [List.length_append, withdrawal_decode_glue_length, rlp_walk_init_prog_length,
              rlp_walk_next_prog_length, rlp_content_to_u64_prog_length],
      show base + BitVec.ofNat 64 (4 * 261) = base + 1044 from by bv_omega] at hr
  rw [withdrawal_decode_code, hrest]
  exact hr h

/-- The copy routine's 100-instruction chain (idx 261, byte 1044) is a program segment:
    `byteCopyChainCR (base + 1044) 20 ⊆ withdrawal_decode_code base`. -/
theorem wd_copyChainBody_sub (base : Word) :
    ∀ a i, byteCopyChainCR (base + 1044) 20 a = some i →
           withdrawal_decode_code base a = some i := by
  intro a i h
  have h1 := byteCopyChainCR_sub_ofProg 20 (base + 1044) (by norm_num) a i h
  have h2 := CodeReq.ofProg_mono_append_left (base + 1044) (byteCopyChainInstrs 20)
    [(.JALR .x0 .x1 (0 : BitVec 12) : Instr)] a i h1
  exact wd_routineBody_sub base a i h2

/-- The copy routine's terminal `ret` (`jalr x0, ra, 0`) at idx 361 (byte 1444). -/
theorem wd_copyRoutineRet_lookup (base : Word) :
    withdrawal_decode_code base (base + 1444) = some (.JALR .x0 .x1 (0 : BitVec 12)) := by
  apply wd_routineBody_sub
  have h := CodeReq.ofProg_lookup_addr (base + 1044) withdrawal_copy_routine 100 (base + 1444)
    (by rw [withdrawal_copy_routine_length]; norm_num) (by rw [withdrawal_copy_routine_length]; norm_num)
    (by bv_omega)
  rwa [show withdrawal_copy_routine.get ⟨100, by rw [withdrawal_copy_routine_length]; norm_num⟩
        = (.JALR .x0 .x1 (0 : BitVec 12)) from by decide] at h

set_option maxRecDepth 8000 in
/-- **Copy routine leaf spec.** From `x13 = srcBase + off`, `x14 = dstBase + di0`, `x1 = raVal`,
    `withdrawal_copy_routine` copies 20 bytes `srcBytes[off..off+20)` into the dest region at
    `[di0, di0+20)` and returns to `raVal &&& ~~~1` (the verified `rlp_copy_chain_gen_spec` chain
    followed by `ret`, lifted to the full program code). -/
theorem wd_copy_routine_leaf (base srcBase dstBase raVal v12Old cnt : Word)
    (srcBytes dstBytes : List (BitVec 8)) (off di0 : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hsrc : off + 20 ≤ srcBytes.length) (hdst : di0 + 20 ≤ dstBytes.length)
    (hdov : dstBase.toNat + dstBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length → isValidByteAccess (dstBase + BitVec.ofNat 64 i) = true)
    (hbase : base.toNat + 1444 < 2 ^ 64) :
    cpsTripleWithin (5 * 20 + 1) (base + 1044) (raVal &&& ~~~1) (withdrawal_decode_code base)
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) **
        (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di0)) ** (.x15 ↦ᵣ cnt) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((regOwn .x12) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + 20))) **
        (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di0 + 20))) ** (regOwn .x15) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes **
        bytesRegion dstBase (copyRangeGen dstBytes srcBytes off di0 20)) := by
  have chain := rlp_copy_chain_gen_spec srcBase dstBase srcBytes hsalign hdalign hsover hsvalid
    20 off di0 cnt v12Old dstBytes (base + 1044) hsrc hdst hdov hdval (by bv_omega)
  have chain1 := cpsTripleWithin_extend_code (wd_copyChainBody_sub base) chain
  rw [show (base + 1044) + BitVec.ofNat 64 (20 * 20) = base + 1444 from by bv_omega] at chain1
  have chain2 := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) chain1
  have hret := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 1444)
  rw [show ((raVal + signExtend12 (0 : BitVec 12)) &&& ~~~1) = raVal &&& ~~~1 from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
            show raVal + (0 : Word) = raVal from by bv_omega]] at hret
  have hret1 := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (wd_copyRoutineRet_lookup base)) hret
  have hret2 := cpsTripleWithin_frameR
    ((regOwn .x12) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + 20))) **
      (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di0 + 20))) ** (regOwn .x15) **
      bytesRegion srcBase srcBytes **
      bytesRegion dstBase (copyRangeGen dstBytes srcBytes off di0 20)) (by pcFree) hret1
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) chain2 hret2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
    (fun _ _ _ => ⟨by omega, by omega, by simpa using hcontentvalid 0 hpos⟩)
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
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0) :
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
    (fun _ _ hpos => absurd hempty (by omega))
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
    (fun _ _ _ => ⟨by omega, by omega, by simpa using hcontentvalid 0 hpos⟩)
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
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0) :
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
    (fun _ _ hpos => absurd hempty (by omega))
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
    (fun _ _ _ => ⟨by omega, by omega, by simpa using hcontentvalid 0 hpos⟩)
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
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0) :
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
    (fun _ _ hpos => absurd hempty (by omega))
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 →
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

set_option maxRecDepth 8000 in
/-- **Field-2 copy setup** (idx 45–49, base+180 → base+200): `li t1,20`; `bne a2,t1,fail` (not
    taken since `contentLen = 20`); `mv s1,a0` (cursor := advanced); `sub a3,s1,a2`
    (`a3 = advanced − 20 = contentPtr`); `addi a4,s0,16` (`a4 = struct+16`, the copy dest). -/
theorem wd_decode_field2CopyPre (base srcBase struct x6Old cursorOld x13Old x14Old : Word)
    (srcOff : Nat) :
    cpsTripleWithin 5 (base + 180) (base + 200) (withdrawal_decode_code base)
      ((.x6 ↦ᵣ x6Old) ** (.x12 ↦ᵣ (20 : Word)) ** (.x9 ↦ᵣ cursorOld) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x13 ↦ᵣ x13Old) **
        (.x8 ↦ᵣ struct) ** (.x14 ↦ᵣ x14Old))
      ((.x6 ↦ᵣ (20 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
        (.x13 ↦ᵣ ((srcBase + BitVec.ofNat 64 (srcOff + 21)) - (20 : Word))) **
        (.x8 ↦ᵣ struct) ** (.x14 ↦ᵣ (struct + signExtend12 (16 : BitVec 12)))) := by
  -- A: li t1, 20  (idx 45)
  have hA := wd_decode_li base 45 .x6 (20 : Word) x6Old (by decide)
    (by rw [withdrawal_decode_prog_length]; norm_num) (by decide)
  rw [show base + BitVec.ofNat 64 (4 * 45) = base + 180 from by bv_omega,
      show base + 180 + 4 = base + 184 from by bv_omega] at hA
  -- B: bne a2, t1, fail  (idx 46), not taken (a2 = t1 = 20); drop the ⌜20=20⌝ pure
  have hB0 := wd_bne_eq base 46 .x12 .x6 (120 : BitVec 13) (20 : Word)
    (by rw [withdrawal_decode_prog_length]; norm_num) (by decide)
  rw [show base + BitVec.ofNat 64 (4 * 46) = base + 184 from by bv_omega,
      show base + 184 + 4 = base + 188 from by bv_omega] at hB0
  have hB := cpsTripleWithin_weaken (fun _ h => h)
    (fun s hp => sepConj_mono_right (fun s' h => ((sepConj_pure_right s').1 h).1) s hp) hB0
  -- C: mv s1,a0 ; sub a3,s1,a2 ; addi a4,s0,16  (idx 47–49)
  have hC : cpsTripleWithin 3 (base + 188) (base + 200) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ cursorOld) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x13 ↦ᵣ x13Old) ** (.x8 ↦ᵣ struct) ** (.x14 ↦ᵣ x14Old))
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x13 ↦ᵣ ((srcBase + BitVec.ofNat 64 (srcOff + 21)) - (20 : Word))) **
        (.x8 ↦ᵣ struct) ** (.x14 ↦ᵣ (struct + signExtend12 (16 : BitVec 12)))) := by
    have hmv := mv_spec_gen_within .x9 .x10 (srcBase + BitVec.ofNat 64 (srcOff + 21)) cursorOld
      (base + 188) (by decide)
    have hsub := sub_spec_gen_within .x13 .x9 .x12 (srcBase + BitVec.ofNat 64 (srcOff + 21))
      (20 : Word) x13Old (base + 192) (by decide)
    have haddi := addi_spec_gen_within .x14 .x8 x14Old struct (16 : BitVec 12) (base + 196)
      (by decide)
    runBlock hmv hsub haddi
  -- compose A ⨾ B ⨾ C
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR ((.x12 ↦ᵣ (20 : Word)) ** (.x9 ↦ᵣ cursorOld) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x13 ↦ᵣ x13Old) **
        (.x8 ↦ᵣ struct) ** (.x14 ↦ᵣ x14Old)) (by pcFree) hA)
    (cpsTripleWithin_frameR ((.x9 ↦ᵣ cursorOld) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x13 ↦ᵣ x13Old) **
        (.x8 ↦ᵣ struct) ** (.x14 ↦ᵣ x14Old)) (by pcFree) hB)
  have hABC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hAB
    (cpsTripleWithin_frameL (.x6 ↦ᵣ (20 : Word)) (by pcFree) hC)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hABC

set_option maxRecDepth 8000 in
/-- **Field-2 address copy body** (idx 45–54, base+180 → base+220): the copy setup
    (`wd_decode_field2CopyPre`), then `jal` to `withdrawal_copy_routine` (copies the 20 address
    bytes `srcBytes[srcOff+1 .. srcOff+21)` into `bytesRegion (struct+16)`), then the 4 `nop`s the
    routine returns into. The address bytes land in `bytesRegion (struct+16) (copyRangeGen …)`. -/
theorem wd_decode_field2Copy (base srcBase struct x6Old x1Old cursorOld x13Old x14Old cnt : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hstalign : struct.toNat % 8 = 0)
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hsrc : srcOff + 21 ≤ srcBytes.length) (hdlen : dstBytes.length = 20)
    (hdov : (struct + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length → isValidByteAccess ((struct + 16) + BitVec.ofNat 64 i) = true)
    (hbase : base.toNat + 1444 < 2 ^ 64) (halign204 : (base + 204) &&& ~~~1 = base + 204) :
    cpsTripleWithin 111 (base + 180) (base + 220) (withdrawal_decode_code base)
      ((.x6 ↦ᵣ x6Old) ** (.x1 ↦ᵣ x1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
        (.x9 ↦ᵣ cursorOld) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
        bytesRegion srcBase srcBytes ** bytesRegion (struct + 16) dstBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x8 ↦ᵣ struct) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** regOwn .x12 **
        (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((srcOff + 1) + 20))) **
        (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
        bytesRegion srcBase srcBytes **
        bytesRegion (struct + 16) (copyRangeGen dstBytes srcBytes (srcOff + 1) 0 20)) := by
  -- P0: the setup (idx 45–49), with x13/x14 normalized to chain-ready forms
  have hP0 := wd_decode_field2CopyPre base srcBase struct x6Old cursorOld x13Old x14Old srcOff
  rw [show (srcBase + BitVec.ofNat 64 (srcOff + 21)) - (20 : Word)
        = srcBase + BitVec.ofNat 64 (srcOff + 1) from by bv_omega,
      show struct + signExtend12 (16 : BitVec 12) = (struct + 16) + BitVec.ofNat 64 0 from by
        rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at hP0
  have hP0' := cpsTripleWithin_frameR ((.x1 ↦ᵣ x1Old) ** (.x15 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion srcBase srcBytes ** bytesRegion (struct + 16) dstBytes) (by pcFree) hP0
  -- D: jal ra, copy_routine  (idx 50)
  have hjal : withdrawal_decode_code base (base + 200) = some (.JAL .x1 (844 : BitVec 21)) := by
    have h := wd_prog_lookup base 50 (by rw [withdrawal_decode_prog_length]; norm_num)
    rwa [show base + BitVec.ofNat 64 (4 * 50) = base + 200 from by bv_omega,
         show withdrawal_decode_prog.get ⟨50, by rw [withdrawal_decode_prog_length]; norm_num⟩
           = (.JAL .x1 (844 : BitVec 21)) from by decide] at h
  have hD0 := jal_spec_within .x1 x1Old (844 : BitVec 21) (base + 200) (by decide)
  rw [show (base + 200) + signExtend21 (844 : BitVec 21) = base + 1044 from by
        rw [show signExtend21 (844 : BitVec 21) = (844 : Word) from by decide]; bv_omega,
      show (base + 200) + 4 = base + 204 from by bv_omega] at hD0
  have hD := cpsTripleWithin_extend_code (CodeReq.singleton_mono hjal) hD0
  have hD' := cpsTripleWithin_frameR ((.x6 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ struct) ** (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
    (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x12 ↦ᵣ (20 : Word)) **
    (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) ** (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 0)) **
    (.x15 ↦ᵣ cnt) ** bytesRegion srcBase srcBytes ** bytesRegion (struct + 16) dstBytes)
    (by pcFree) hD
  -- E: the copy routine (returns to base+204 via halign204)
  have hE0 := wd_copy_routine_leaf base srcBase (struct + 16) (base + 204) (20 : Word) cnt
    srcBytes dstBytes (srcOff + 1) 0 hsalign (by bv_omega) hsover hsvalid (by omega)
    (by omega) (by rw [hdlen]; exact hdov) hdval hbase
  rw [halign204] at hE0
  have hE' := cpsTripleWithin_frameL ((.x6 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ struct) ** (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
    (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21)))) (by pcFree) hE0
  -- F: 4 nops (idx 51–54) — emp → emp, lifted to the program code
  have hnop : ∀ (k : Nat) (hk : k < withdrawal_decode_prog.length),
      withdrawal_decode_prog.get ⟨k, hk⟩ = .NOP →
      cpsTripleWithin 1 (base + BitVec.ofNat 64 (4 * k)) (base + BitVec.ofNat 64 (4 * k) + 4)
        (withdrawal_decode_code base) empAssertion empAssertion := by
    intro k hk hinstr
    refine cpsTripleWithin_extend_code ?_ (nop_spec_within (base + BitVec.ofNat 64 (4 * k)))
    apply CodeReq.singleton_mono
    have h := wd_prog_lookup base k hk
    rwa [hinstr] at h
  have hn51 := hnop 51 (by rw [withdrawal_decode_prog_length]; norm_num) (by decide)
  have hn52 := hnop 52 (by rw [withdrawal_decode_prog_length]; norm_num) (by decide)
  have hn53 := hnop 53 (by rw [withdrawal_decode_prog_length]; norm_num) (by decide)
  have hn54 := hnop 54 (by rw [withdrawal_decode_prog_length]; norm_num) (by decide)
  rw [show base + BitVec.ofNat 64 (4 * 51) = base + 204 from by bv_omega,
      show base + 204 + 4 = base + 208 from by bv_omega] at hn51
  rw [show base + BitVec.ofNat 64 (4 * 52) = base + 208 from by bv_omega,
      show base + 208 + 4 = base + 212 from by bv_omega] at hn52
  rw [show base + BitVec.ofNat 64 (4 * 53) = base + 212 from by bv_omega,
      show base + 212 + 4 = base + 216 from by bv_omega] at hn53
  rw [show base + BitVec.ofNat 64 (4 * 54) = base + 216 from by bv_omega,
      show base + 216 + 4 = base + 220 from by bv_omega] at hn54
  have hF : cpsTripleWithin 4 (base + 204) (base + 220) (withdrawal_decode_code base)
      empAssertion empAssertion :=
    cpsTripleWithin_seq_same_cr (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr hn51 hn52) hn53) hn54
  -- compose P0' ⨾ D' ⨾ E', then thread the post through the nops (emp frame)
  have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hP0' hD'
  have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1 hE'
  have hF' := cpsTripleWithin_frameL
    ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x8 ↦ᵣ struct) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
      regOwn .x12 ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((srcOff + 1) + 20))) **
      (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
      bytesRegion srcBase srcBytes **
      bytesRegion (struct + 16) (copyRangeGen dstBytes srcBytes (srcOff + 1) 0 20))
    (by pcFree) hF
  rw [sepConj_emp_right'] at hF'
  have h3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h2 hF'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h3

set_option maxRecDepth 8000 in
/-- **Field-2 reject-check ⨾ copy** (idx 42–54, base+168 → base+220): the list-form reject
    (`prefix < 0xc0`) then the 20-byte address copy. Composes `wd_decode_field2RejectCheck` and
    `wd_decode_field2Copy`; the reject's `x6 = 0xc0` becomes the copy's clobbered `t1`, its `x5`
    (prefix) and `⌜prefix<192⌝` ride through the copy as a frame. -/
theorem wd_decode_field2RejectCopy (base srcBase struct t0Old t1Old x1Old x13Old x14Old cnt : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hstalign : struct.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hlt : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word))
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hsrc : srcOff + 21 ≤ srcBytes.length) (hdlen : dstBytes.length = 20)
    (hdov : (struct + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length → isValidByteAccess ((struct + 16) + BitVec.ofNat 64 i) = true)
    (hbase : base.toNat + 1444 < 2 ^ 64) (halign204 : (base + 204) &&& ~~~1 = base + 204) :
    cpsTripleWithin (3 + 111) (base + 168) (base + 220) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x1 ↦ᵣ x1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
        bytesRegion srcBase srcBytes ** bytesRegion (struct + 16) dstBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x8 ↦ᵣ struct) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** regOwn .x12 **
        (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((srcOff + 1) + 20))) **
        (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
        (.x5 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) **
        bytesRegion srcBase srcBytes **
        bytesRegion (struct + 16) (copyRangeGen dstBytes srcBytes (srcOff + 1) 0 20) **
        ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝) := by
  -- reject-check (idx 42–44), framed with the copy's registers + dest region
  have hRej := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ x1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ struct) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x12 ↦ᵣ (20 : Word)) **
      (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes)
    (by pcFree)
    (wd_decode_field2RejectCheck base srcBase t0Old t1Old srcBytes srcOff hsalign hoff hover
      hvalid hlt)
  -- copy (idx 45–54), framed with x5 (prefix) and the ⌜prefix<192⌝ pure
  have hCopy := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) **
      ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝)
    (by pcFree)
    (wd_decode_field2Copy base srcBase struct (192 : Word) x1Old
      (srcBase + BitVec.ofNat 64 srcOff) x13Old x14Old cnt srcBytes dstBytes srcOff
      hsalign hstalign hsover hsvalid hsrc hdlen hdov hdval hbase halign204)
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hRej hCopy
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hcomp

set_option maxRecDepth 8000 in
/-- `wd_decode_field2RejectCopy` with `t0`/`t1` (`x5`/`x6`) exposed only as ownership — matches the
    field-2 walk's `regOwn .x5 ** regOwn .x6` post, so the walk and reject-copy compose directly. -/
theorem wd_decode_field2RejectCopy_regOwn (base srcBase struct x1Old x13Old x14Old cnt : Word)
    (srcBytes dstBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hstalign : struct.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hlt : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word))
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hsrc : srcOff + 21 ≤ srcBytes.length) (hdlen : dstBytes.length = 20)
    (hdov : (struct + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length → isValidByteAccess ((struct + 16) + BitVec.ofNat 64 i) = true)
    (hbase : base.toNat + 1444 < 2 ^ 64) (halign204 : (base + 204) &&& ~~~1 = base + 204) :
    cpsTripleWithin (3 + 111) (base + 168) (base + 220) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x1 ↦ᵣ x1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
        bytesRegion srcBase srcBytes ** bytesRegion (struct + 16) dstBytes) **
        (regOwn .x5 ** regOwn .x6))
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x8 ↦ᵣ struct) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** regOwn .x12 **
        (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((srcOff + 1) + 20))) **
        (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
        (.x5 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) **
        bytesRegion srcBase srcBytes **
        bytesRegion (struct + 16) (copyRangeGen dstBytes srcBytes (srcOff + 1) 0 20) **
        ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝) := by
  have hgrouped : ∀ t0Old t1Old : Word,
      cpsTripleWithin (3 + 111) (base + 168) (base + 220) (withdrawal_decode_code base)
        (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x1 ↦ᵣ x1Old) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) **
          (.x12 ↦ᵣ (20 : Word)) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion srcBase srcBytes ** bytesRegion (struct + 16) dstBytes) **
          ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old)))
        ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** (.x8 ↦ᵣ struct) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
          (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 21))) ** regOwn .x12 **
          (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((srcOff + 1) + 20))) **
          (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
          (.x5 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) **
          bytesRegion srcBase srcBytes **
          bytesRegion (struct + 16) (copyRangeGen dstBytes srcBytes (srcOff + 1) 0 20) **
          ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝) := by
    intro t0Old t1Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
      (wd_decode_field2RejectCopy base srcBase struct t0Old t1Old x1Old x13Old x14Old cnt
        srcBytes dstBytes srcOff hsalign hstalign hoff hover hvalid hlt hsover hsvalid hsrc hdlen
        hdov hdval hbase halign204)
  have hbody := cpsTripleWithin_exists_pre (fun t0Old : Word =>
    cpsTripleWithin_exists_pre (fun t1Old : Word => hgrouped t0Old t1Old))
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hp => ?_) hbody
  · obtain ⟨hM, hG, hd, hu, hMain, hGrp⟩ := hp
    obtain ⟨h1, h2, hd2, hu2, ⟨va, ha⟩, vb, hb⟩ := hGrp
    exact ⟨va, vb, hM, hG, hd, hu, hMain, h1, h2, hd2, hu2, ha, hb⟩
  · obtain ⟨_, _, h⟩ := hp; exact h

set_option maxRecDepth 8000 in
/-- **Field-2 (address) body** (idx 38–54, base+152 → base+220): the complete per-field decode of
    the 20-byte address. Composes the field walk (`wd_decode_field2Walk`, base+152 → base+168) —
    whose existential `Post` is collapsed to the 20-byte short-string instance (prefix `0x94`) and
    specialised to `len = 20` — with `wd_decode_field2RejectCopy_regOwn` (base+168 → base+220), which
    reject-checks the list-form and copies the 20 content bytes into `bytesRegion (struct+16)`. The
    walk's `⌜rlpItemDecode⌝`/`⌜0=0⌝` residuals are dropped at the seam (the monolith re-derives the
    decode). `hlen20` (`prefix − 0x80 = 20`, i.e. prefix `0x94`) is the 20-byte-address requirement. -/
theorem wd_decode_field2Body
    (base srcBase endPtr vOld a0Old a1Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      struct x13Old x14Old cnt : Word)
    (srcBytes dstBytes : List (BitVec 8)) (off : Nat)
    (halign164 : (base + 164) &&& ~~~1 = base + 164)
    (hdisjW : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign204 : (base + 204) &&& ~~~1 = base + 204)
    (hsalign : srcBase.toNat % 8 = 0) (hstalign : struct.toNat % 8 = 0)
    (hoff : off < srcBytes.length) (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hlen20 : (srcBytes[off]'hoff).toNat - 0x80 = 20)
    (hfit : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 off)) = true)
    (hcontentlen : off + 21 ≤ srcBytes.length)
    (hcontentover : srcBase.toNat + (off + 21) ≤ 2 ^ 64)
    (hcontentvalid : ∀ k, k < 20 → isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1 + k)) = true)
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hdlen : dstBytes.length = 20) (hdov : (struct + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length → isValidByteAccess ((struct + 16) + BitVec.ofNat 64 i) = true)
    (hbase : base.toNat + 1444 < 2 ^ 64) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (3 + 111)) (base + 152) (base + 220)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion (struct + 16) dstBytes))
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + 21))) ** (.x8 ↦ᵣ struct) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + 21))) ** regOwn .x12 **
        (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((off + 1) + 20))) **
        (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
        (.x5 ↦ᵣ ((srcBytes[off]'hoff).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
        bytesRegion (struct + 16) (copyRangeGen dstBytes srcBytes (off + 1) 0 20) **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** (.x11 ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31)) := by
  have h_f8 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  have hlt192 : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq] at hhi ⊢; bv_omega
  -- the field walk, with the short-byte-string decodability witness
  have hwalk := wd_decode_field2Walk base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes off halign164 hdisjW hsalign hoff hover
    hvalid
    (fun _ _ _ => ⟨by omega, by omega, by simpa using hcontentvalid 0 (by omega)⟩)
    (fun hns _ => absurd hhi hns) (fun hns => absurd h_f8 hns) hin
    ⟨_, _, rlpItemDecode_of_shortBytes (List.getElem?_eq_getElem hoff) hlo hhi
      (fun hc => by exfalso
                    have : (srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word) = (20 : Word) := by
                      have hb := (srcBytes[off]'hoff).isLt
                      have := hlen20; bv_omega
                    rw [this] at hc; exact absurd hc (by decide)) hfit⟩
  -- collapse the walk's existential Post to the short-byte-string instance
  have hwalkSB : cpsTripleWithin (2 + (1 + 87) + 1) (base + 152) (base + 168)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x1 ↦ᵣ (base + 164)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion srcBase srcBytes **
        ⌜(0 : Word) = (0 : Word)⌝ **
        ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
          ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
            BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))
          (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))⌝) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => wd_decode_field0Walk_shortBytes_post srcBase endPtr srcBytes off
        (base + 164) hoff hlo hhi hp) hwalk
  -- specialise the resolved walk to the 20-byte address (prefix 0x94 ⟹ len = 20)
  rw [hlen20,
      show (srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 20
        = srcBase + BitVec.ofNat 64 (off + 21) from by
          rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at hwalkSB
  -- frame struct / a3 / a4 / a5 / the address dest region through the walk (untouched)
  have hwalkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
      bytesRegion (struct + 16) dstBytes) (by pcFree) hwalkSB
  -- the reject-copy at the resolved cursor, framing the walk's leftover registers through it
  have hRC := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) ** (.x11 ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31) (by pcFree)
    (wd_decode_field2RejectCopy_regOwn base srcBase struct (base + 164) x13Old x14Old cnt
      srcBytes dstBytes off hsalign hstalign hoff hover hvalid hlt192 hsover hsvalid hcontentlen
      hdlen hdov hdval hbase halign204)
  -- stitch walk ⨾ reject-copy; drop the walk's residual pures at the seam
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hwalkF hRC
  have hp' : (⌜(0 : Word) = (0 : Word)⌝ **
      ⌜rlpItemDecode srcBytes off (srcBase + BitVec.ofNat 64 off) endPtr
        (srcBase + BitVec.ofNat 64 (off + 21)) (BitVec.ofNat 64 20)⌝ **
      ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x1 ↦ᵣ (base + 164)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ struct) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + 21))) **
          (.x12 ↦ᵣ (BitVec.ofNat 64 20)) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion srcBase srcBytes ** bytesRegion (struct + 16) dstBytes) **
          (regOwn .x5 ** regOwn .x6)) **
        ((.x18 ↦ᵣ endPtr) ** (.x11 ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31))) s := by
    xperm_hyp hp
  exact ((sepConj_pure_left _).1 ((sepConj_pure_left _).1 hp').2).2

/-- **Field-2 body dispatcher, regOwn-input.** The seven clobbered scratch registers
    (`x5/x6/x7/x28/x29/x30/x31`) are exposed as `regOwn` instead of `regIs`, so this field's PRE
    matches the previous (scalar) field's `regOwn` POST at the field1 ⨾ field2 seam. Field 2's body
    has a fixed step count (the address is always 20 bytes), so the peel is taken directly off
    `wd_decode_field2Body` — no `fixedN` intermediate needed. The address-copy bookkeeping registers
    `x13/x14/x15` stay `regIs` (the capstone owns them and supplies witnesses at the seam). -/
theorem wd_decode_field2Body_regOwn
    (base srcBase endPtr vOld a0Old a1Old a2Old struct x13Old x14Old cnt : Word)
    (srcBytes dstBytes : List (BitVec 8)) (off : Nat)
    (halign164 : (base + 164) &&& ~~~1 = base + 164)
    (hdisjW : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign204 : (base + 204) &&& ~~~1 = base + 204)
    (hsalign : srcBase.toNat % 8 = 0) (hstalign : struct.toNat % 8 = 0)
    (hoff : off < srcBytes.length) (hover : srcBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true)
    (hin : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hlen20 : (srcBytes[off]'hoff).toNat - 0x80 = 20)
    (hfit : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 off)) = true)
    (hcontentlen : off + 21 ≤ srcBytes.length)
    (hcontentover : srcBase.toNat + (off + 21) ≤ 2 ^ 64)
    (hcontentvalid : ∀ k, k < 20 → isValidByteAccess (srcBase + BitVec.ofNat 64 (off + 1 + k)) = true)
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hdlen : dstBytes.length = 20) (hdov : (struct + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length → isValidByteAccess ((struct + 16) + BitVec.ofNat 64 i) = true)
    (hbase : base.toNat + 1444 < 2 ^ 64) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (3 + 111)) (base + 152) (base + 220)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) **
        (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + 21))) ** (.x8 ↦ᵣ struct) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + 21))) ** regOwn .x12 **
        (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((off + 1) + 20))) **
        (.x14 ↦ᵣ ((struct + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
        (.x5 ↦ᵣ ((srcBytes[off]'hoff).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
        bytesRegion (struct + 16) (copyRangeGen dstBytes srcBytes (off + 1) 0 20) **
        ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝) **
        ((.x18 ↦ᵣ endPtr) ** (.x11 ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31)) := by
  have hfull := fun (t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word) =>
    wd_decode_field2Body base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct x13Old x14Old cnt srcBytes dstBytes off
      halign164 hdisjW halign204 hsalign hstalign hoff hover hvalid hin hlo hhi hlen20 hfit
      hcontentlen hcontentover hcontentvalid hsover hsvalid hdlen hdov hdval hbase
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x5) (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes ** (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x6) (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x28) (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** regOwn .x30 ** regOwn .x31)
      (r := .x29) (fun v29 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** regOwn .x31)
      (r := .x30) (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (struct + 16) dstBytes ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30))
      (r := .x31) (fun v31 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hfull v5 v6 v7 v28 v29 v30 v31)

set_option maxRecDepth 8000 in
/-- **Arity block** (idx 69–72, base+276 → base+292): the exact-arity check's straight-line part —
    `mv a0,s1; mv a1,s2; jal walk_next; li t1,2`. On the success path the cursor `s1` after field 3
    equals the list end, so the 5th `walk_next` reports **end-of-list** (status `a1 = 2`, via
    `rlp_walk_next_end_spec_within` given `h_end : ¬ ult cursor endPtr`). Produces `a1 = 2`, `t1 = 2`
    for the `bne` guard in `wd_decode_aritySuccessReturn`. -/
theorem wd_decode_arity (base cursor endPtr a0Old a1Old vOld a2Old t1Old : Word)
    (h_end : ¬ BitVec.ult cursor endPtr)
    (halign288 : (base + 288) &&& ~~~1 = base + 288)
    (hdisj : (CodeReq.singleton (base + 284) (.JAL .x1 (260 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544))) :
    cpsTripleWithin (2 + ((1 + 4) + 1)) (base + 276) (base + 292) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ t1Old))
      ((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ cursor) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 288)) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr)) := by
  -- A: mv a0,s1 ; mv a1,s2  (idx 69–70)
  have hA : cpsTripleWithin 2 (base + 276) (base + 284) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr)) := by
    have hmv0 := mv_spec_gen_within .x10 .x9 cursor a0Old (base + 276) (by decide)
    have hmv1 := mv_spec_gen_within .x11 .x18 endPtr a1Old (base + 280) (by decide)
    runBlock hmv0 hmv1
  -- B: jal walk_next  (idx 71), end-of-list arm
  have hoffset : (base + 284) + signExtend21 (260 : BitVec 21) = base + 544 := by
    rw [show signExtend21 (260 : BitVec 21) = (260 : Word) from by decide]; bv_omega
  have hleaf : cpsTripleWithin 4 (base + 544) ((base + 284 + 4) &&& ~~~1)
      (rlp_walk_next_code (base + 544))
      ((.x1 ↦ᵣ (base + 284 + 4)) **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word))))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 284 + 4))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (rlp_walk_next_end_spec_within (base + 544) cursor endPtr (base + 284 + 4) a2Old h_end)
  have hcall := cpsCallWithin (vOld := vOld) (260 : BitVec 21) hoffset
    (by rw [show base + 284 + 4 = base + 288 from by bv_omega]; exact halign288) (by pcFree)
    hdisj hleaf
  have hB := cpsTripleWithin_extend_code (wd_call_code_sub
    (show withdrawal_decode_code base (base + 284) = some (.JAL .x1 (260 : BitVec 21)) from by
      have h := wd_prog_lookup base 71 (by rw [withdrawal_decode_prog_length]; norm_num)
      rw [show base + BitVec.ofNat 64 (4 * 71) = base + 284 from by bv_omega] at h
      rw [h]; decide)
    (wd_walkNextBody_sub base)) hcall
  rw [show base + 284 + 4 = base + 288 from by bv_omega] at hB
  -- C: li t1,2  (idx 72)
  have hC := wd_decode_li base 72 .x6 (2 : Word) t1Old (by decide)
    (by rw [withdrawal_decode_prog_length]; norm_num) (by decide)
  rw [show base + BitVec.ofNat 64 (4 * 72) = base + 288 from by bv_omega,
      show base + 288 + 4 = base + 292 from by bv_omega] at hC
  -- compose A ⨾ B ⨾ C, framing each step's idle registers
  have hAf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ vOld) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ t1Old)) (by pcFree) hA
  have hBf := cpsTripleWithin_frameR ((.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr) ** (.x6 ↦ᵣ t1Old))
    (by pcFree) hB
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hAf hBf
  have hCf := cpsTripleWithin_frameL
    ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ (base + 288)) ** (.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr)) (by pcFree) hC
  have hABC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hAB hCf
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hABC

/-! ## M3 proof — unified field-0 body (form-independent postcondition)

The three scalar forms of field 0 (`single-byte`, `short-byte-string`, `empty`) have distinct
concrete postconditions. To keep the success-chain composition from branching `3³`-ways across
the three scalar fields, each form is re-expressed against one *unified* postcondition
parameterised by the decoded content list `d0` and the next byte offset `nextOff`. The unified
post carries exactly what the chain needs downstream: the advanced cursor (`x9 = srcBase +
nextOff`), the live struct cell, and a trailing pure bundling the scalar canonicity
(`headD ≠ 0`, `length ≤ 8`) with the `decodeAux` consumption fact that
`decodeFully_shortList_four` consumes. -/

/-- **Unified scalar-field-body postcondition** (form-independent), shared by the three scalar
    fields (0/1/3), parameterised by the clobbered `x1` value `x1Val`, the output struct base
    `struct` and its dword offset `structOff` (0/8/40), and — per form — the decoded content `d0`
    and next byte offset `nextOff`. Spatial atoms in the same order as the per-form variant posts;
    the single trailing pure bundles the scalar canonicity (`headD ≠ 0`, `length ≤ 8`) with the
    `decodeAux` consumption fact `decodeFully_shortList_four` consumes. -/
def wd_scalarFieldUnifiedPost (x1Val struct : Word) (structOff : BitVec 12)
    (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) (off : Nat)
    (d0 : List Byte) (nextOff : Nat) : Assertion :=
  ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 nextOff)) **
    (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE d0)) ** (.x11 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ BitVec.ofNat 64 d0.length) ** (.x8 ↦ᵣ struct) ** (.x1 ↦ᵣ x1Val) **
    (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    bytesRegion srcBase srcBytes **
    ((struct + signExtend12 structOff) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
    (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
  ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
    (∀ m, decodeAux (m + 1) (srcBytes.drop off) = some (.bytes d0, srcBytes.drop nextOff)) ∧
    nextOff ≤ srcBytes.length⌝

/-- **Field-0 single-byte body → unified post.** Re-expresses `wd_decode_field0BodySingleByte`
    against `wd_scalarFieldUnifiedPost` with `d0 = (drop srcOff).take 1` (`= [b]`), `nextOff = srcOff + 1`. -/
theorem wd_decode_field0BodySingleByte_unified
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
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 88) struct (0 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hv := wd_decode_field0BodySingleByte base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
    halign52 hdisjW halign88 hdisjC hsalign hoff hover hvalid hin hsingle hbyte
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  refine ⟨(srcBytes.drop srcOff).take 1, srcOff + 1, ?_⟩
  have hd0 : (srcBytes.drop srcOff).take 1 = [srcBytes[srcOff]'hoff] := by
    rw [drop_eq_cons_of_getElem? (List.getElem?_eq_getElem hoff)]; rfl
  have hlen1 : ((srcBytes.drop srcOff).take 1).length = 1 := by rw [hd0]; rfl
  have hlen8 : ((srcBytes.drop srcOff).take 1).length ≤ 8 := by rw [hlen1]; norm_num
  have hhead : ((srcBytes.drop srcOff).take 1).headD 1 ≠ 0 := by
    rw [headD_take_drop_eq_getByteAt srcBytes srcOff 1 (by norm_num) hoff]; exact hbyte
  have hdecU : ∀ m, decodeAux (m + 1) (srcBytes.drop srcOff) =
      some (.bytes ((srcBytes.drop srcOff).take 1), srcBytes.drop (srcOff + 1)) := by
    intro m; rw [hd0]
    exact rlpItemDecode_singleByte_decodeAux (List.getElem?_eq_getElem hoff) hsingle m
  have hx9 : (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) =
      srcBase + BitVec.ofNat 64 (srcOff + 1) :=
    (rlpItemDecode_singleByte_offsets srcBase (srcBase + BitVec.ofNat 64 srcOff)
      ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word) srcOff
      rfl rfl rfl).1
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8, hdecU, by omega⟩
  rw [hlen1, ← hx9]
  have hpf : (⌜0 < 1 ∧ getByteAt srcBytes srcOff ≠ 0 ∧ 1 ≤ 8⌝ **
      ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-0 short-byte-string body → unified post.** Re-expresses `wd_decode_field0BodyShortBytes`
    against `wd_scalarFieldUnifiedPost` with `d0 = (drop (off+1)).take L`, `nextOff = off + 1 + L`
    (`L = b - 0x80`); the `decodeAux` step is exactly `rlpItemDecode_shortBytes_decodeAux`. -/
theorem wd_decode_field0BodyShortBytes_unified
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
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 88) struct (0 : BitVec 12) srcBase endPtr
          srcBytes off d0 nextOff h) := by
  have hv := wd_decode_field0BodyShortBytes base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes off
    halign52 hdisjW halign88 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit
    hcontentlen hcontentover hcontentvalid hpos hbyte hlen8
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  refine ⟨(srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80),
          off + 1 + ((srcBytes[off]'hoff).toNat - 0x80), ?_⟩
  have hoff1 : off + 1 < srcBytes.length := by omega
  have hlenL : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).length =
      (srcBytes[off]'hoff).toNat - 0x80 := by
    rw [List.length_take, List.length_drop]; omega
  have hlen8' : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).length ≤ 8 := by
    rw [hlenL]; exact hlen8
  have hhead : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).headD 1 ≠ 0 := by
    rw [headD_take_drop_eq_getByteAt srcBytes (off + 1) ((srcBytes[off]'hoff).toNat - 0x80) hpos hoff1]
    exact hbyte
  have hdecU := rlpItemDecode_shortBytes_decodeAux (List.getElem?_eq_getElem hoff) hlo hhi
    hcanon hcontentlen
  have hx9 : (srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
      BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80) =
      srcBase + BitVec.ofNat 64 (off + 1 + ((srcBytes[off]'hoff).toNat - 0x80)) := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]; bv_omega
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8', hdecU, by omega⟩
  rw [hlenL, ← hx9]
  have hpf : (⌜0 < (srcBytes[off]'hoff).toNat - 0x80 ∧ getByteAt srcBytes (off + 1) ≠ 0 ∧
        (srcBytes[off]'hoff).toNat - 0x80 ≤ 8⌝ **
      ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-0 empty body → unified post.** Re-expresses `wd_decode_field0BodyEmpty` against
    `wd_scalarFieldUnifiedPost` with `d0 = []`, `nextOff = off + 1`: the empty string is the canonical
    encoding of the scalar `0`, so `headD 1 = 1 ≠ 0` vacuously and the stored value is `0`. -/
theorem wd_decode_field0BodyEmpty_unified
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
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 40) (base + 96) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 88) struct (0 : BitVec 12) srcBase endPtr
          srcBytes off d0 nextOff h) := by
  have hv := wd_decode_field0BodyEmpty base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes off
    halign52 hdisjW halign88 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  rw [hempty] at hp
  refine ⟨([] : List (BitVec 8)), off + 1, ?_⟩
  have hhead : ([] : List (BitVec 8)).headD 1 ≠ 0 := by decide
  have hlen8 : ([] : List (BitVec 8)).length ≤ 8 := by norm_num
  have hval0 : BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) := by rfl
  have hdecU : ∀ m, decodeAux (m + 1) (srcBytes.drop off) =
      some (.bytes ([] : List (BitVec 8)), srcBytes.drop (off + 1)) := by
    intro m
    have h := rlpItemDecode_shortBytes_decodeAux (List.getElem?_eq_getElem hoff) hlo hhi
      (fun _ => by exfalso; simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo; bv_omega)
      (by rw [hempty]; omega) m
    rw [hempty] at h
    simpa using h
  have hx9 : (srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 0 =
      srcBase + BitVec.ofNat 64 (off + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]; bv_omega
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8, hdecU, by omega⟩
  rw [hval0, ← hx9, List.length_nil]
  have hpf : (⌜(0 : Nat) = 0⌝ **
      ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 0)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 0)) **
        (.x8 ↦ᵣ struct) ** (.x1 ↦ᵣ (base + 88)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-1 single-byte body → unified post.** Re-expresses `wd_decode_field1BodySingleByte`
    against `wd_scalarFieldUnifiedPost` with `d0 = (drop srcOff).take 1` (`= [b]`), `nextOff = srcOff + 1`. -/
theorem wd_decode_field1BodySingleByte_unified
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
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 144) struct (8 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hv := wd_decode_field1BodySingleByte base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
    halign108 hdisjW halign144 hdisjC hsalign hoff hover hvalid hin hsingle hbyte
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  refine ⟨(srcBytes.drop srcOff).take 1, srcOff + 1, ?_⟩
  have hd0 : (srcBytes.drop srcOff).take 1 = [srcBytes[srcOff]'hoff] := by
    rw [drop_eq_cons_of_getElem? (List.getElem?_eq_getElem hoff)]; rfl
  have hlen1 : ((srcBytes.drop srcOff).take 1).length = 1 := by rw [hd0]; rfl
  have hlen8 : ((srcBytes.drop srcOff).take 1).length ≤ 8 := by rw [hlen1]; norm_num
  have hhead : ((srcBytes.drop srcOff).take 1).headD 1 ≠ 0 := by
    rw [headD_take_drop_eq_getByteAt srcBytes srcOff 1 (by norm_num) hoff]; exact hbyte
  have hdecU : ∀ m, decodeAux (m + 1) (srcBytes.drop srcOff) =
      some (.bytes ((srcBytes.drop srcOff).take 1), srcBytes.drop (srcOff + 1)) := by
    intro m; rw [hd0]
    exact rlpItemDecode_singleByte_decodeAux (List.getElem?_eq_getElem hoff) hsingle m
  have hx9 : (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) =
      srcBase + BitVec.ofNat 64 (srcOff + 1) :=
    (rlpItemDecode_singleByte_offsets srcBase (srcBase + BitVec.ofNat 64 srcOff)
      ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word) srcOff
      rfl rfl rfl).1
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8, hdecU, by omega⟩
  rw [hlen1, ← hx9]
  have hpf : (⌜0 < 1 ∧ getByteAt srcBytes srcOff ≠ 0 ∧ 1 ≤ 8⌝ **
      ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-1 short-byte-string body → unified post.** Re-expresses `wd_decode_field1BodyShortBytes`
    against `wd_scalarFieldUnifiedPost` with `d0 = (drop (off+1)).take L`, `nextOff = off + 1 + L`
    (`L = b - 0x80`); the `decodeAux` step is exactly `rlpItemDecode_shortBytes_decodeAux`. -/
theorem wd_decode_field1BodyShortBytes_unified
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
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 144) struct (8 : BitVec 12) srcBase endPtr
          srcBytes off d0 nextOff h) := by
  have hv := wd_decode_field1BodyShortBytes base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes off
    halign108 hdisjW halign144 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit
    hcontentlen hcontentover hcontentvalid hpos hbyte hlen8
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  refine ⟨(srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80),
          off + 1 + ((srcBytes[off]'hoff).toNat - 0x80), ?_⟩
  have hoff1 : off + 1 < srcBytes.length := by omega
  have hlenL : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).length =
      (srcBytes[off]'hoff).toNat - 0x80 := by
    rw [List.length_take, List.length_drop]; omega
  have hlen8' : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).length ≤ 8 := by
    rw [hlenL]; exact hlen8
  have hhead : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).headD 1 ≠ 0 := by
    rw [headD_take_drop_eq_getByteAt srcBytes (off + 1) ((srcBytes[off]'hoff).toNat - 0x80) hpos hoff1]
    exact hbyte
  have hdecU := rlpItemDecode_shortBytes_decodeAux (List.getElem?_eq_getElem hoff) hlo hhi
    hcanon hcontentlen
  have hx9 : (srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
      BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80) =
      srcBase + BitVec.ofNat 64 (off + 1 + ((srcBytes[off]'hoff).toNat - 0x80)) := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]; bv_omega
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8', hdecU, by omega⟩
  rw [hlenL, ← hx9]
  have hpf : (⌜0 < (srcBytes[off]'hoff).toNat - 0x80 ∧ getByteAt srcBytes (off + 1) ≠ 0 ∧
        (srcBytes[off]'hoff).toNat - 0x80 ≤ 8⌝ **
      ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-1 empty body → unified post.** Re-expresses `wd_decode_field1BodyEmpty` against
    `wd_scalarFieldUnifiedPost` with `d0 = []`, `nextOff = off + 1`: the empty string is the canonical
    encoding of the scalar `0`, so `headD 1 = 1 ≠ 0` vacuously and the stored value is `0`. -/
theorem wd_decode_field1BodyEmpty_unified
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
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 96) (base + 152) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 144) struct (8 : BitVec 12) srcBase endPtr
          srcBytes off d0 nextOff h) := by
  have hv := wd_decode_field1BodyEmpty base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes off
    halign108 hdisjW halign144 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  rw [hempty] at hp
  refine ⟨([] : List (BitVec 8)), off + 1, ?_⟩
  have hhead : ([] : List (BitVec 8)).headD 1 ≠ 0 := by decide
  have hlen8 : ([] : List (BitVec 8)).length ≤ 8 := by norm_num
  have hval0 : BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) := by rfl
  have hdecU : ∀ m, decodeAux (m + 1) (srcBytes.drop off) =
      some (.bytes ([] : List (BitVec 8)), srcBytes.drop (off + 1)) := by
    intro m
    have h := rlpItemDecode_shortBytes_decodeAux (List.getElem?_eq_getElem hoff) hlo hhi
      (fun _ => by exfalso; simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo; bv_omega)
      (by rw [hempty]; omega) m
    rw [hempty] at h
    simpa using h
  have hx9 : (srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 0 =
      srcBase + BitVec.ofNat 64 (off + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]; bv_omega
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8, hdecU, by omega⟩
  rw [hval0, ← hx9, List.length_nil]
  have hpf : (⌜(0 : Nat) = 0⌝ **
      ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 0)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 0)) **
        (.x8 ↦ᵣ struct) ** (.x1 ↦ᵣ (base + 144)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-3 single-byte body → unified post.** Re-expresses `wd_decode_field3BodySingleByte`
    against `wd_scalarFieldUnifiedPost` with `d0 = (drop srcOff).take 1` (`= [b]`), `nextOff = srcOff + 1`. -/
theorem wd_decode_field3BodySingleByte_unified
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
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 268) struct (40 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hv := wd_decode_field3BodySingleByte base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
    halign232 hdisjW halign268 hdisjC hsalign hoff hover hvalid hin hsingle hbyte
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  refine ⟨(srcBytes.drop srcOff).take 1, srcOff + 1, ?_⟩
  have hd0 : (srcBytes.drop srcOff).take 1 = [srcBytes[srcOff]'hoff] := by
    rw [drop_eq_cons_of_getElem? (List.getElem?_eq_getElem hoff)]; rfl
  have hlen1 : ((srcBytes.drop srcOff).take 1).length = 1 := by rw [hd0]; rfl
  have hlen8 : ((srcBytes.drop srcOff).take 1).length ≤ 8 := by rw [hlen1]; norm_num
  have hhead : ((srcBytes.drop srcOff).take 1).headD 1 ≠ 0 := by
    rw [headD_take_drop_eq_getByteAt srcBytes srcOff 1 (by norm_num) hoff]; exact hbyte
  have hdecU : ∀ m, decodeAux (m + 1) (srcBytes.drop srcOff) =
      some (.bytes ((srcBytes.drop srcOff).take 1), srcBytes.drop (srcOff + 1)) := by
    intro m; rw [hd0]
    exact rlpItemDecode_singleByte_decodeAux (List.getElem?_eq_getElem hoff) hsingle m
  have hx9 : (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) =
      srcBase + BitVec.ofNat 64 (srcOff + 1) :=
    (rlpItemDecode_singleByte_offsets srcBase (srcBase + BitVec.ofNat 64 srcOff)
      ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) (1 : Word) srcOff
      rfl rfl rfl).1
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8, hdecU, by omega⟩
  rw [hlen1, ← hx9]
  have hpf : (⌜0 < 1 ∧ getByteAt srcBytes srcOff ≠ 0 ∧ 1 ≤ 8⌝ **
      ⌜BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 1)) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take 1))) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-3 short-byte-string body → unified post.** Re-expresses `wd_decode_field3BodyShortBytes`
    against `wd_scalarFieldUnifiedPost` with `d0 = (drop (off+1)).take L`, `nextOff = off + 1 + L`
    (`L = b - 0x80`); the `decodeAux` step is exactly `rlpItemDecode_shortBytes_decodeAux`. -/
theorem wd_decode_field3BodyShortBytes_unified
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
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 268) struct (40 : BitVec 12) srcBase endPtr
          srcBytes off d0 nextOff h) := by
  have hv := wd_decode_field3BodyShortBytes base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes off
    halign232 hdisjW halign268 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit
    hcontentlen hcontentover hcontentvalid hpos hbyte hlen8
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  refine ⟨(srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80),
          off + 1 + ((srcBytes[off]'hoff).toNat - 0x80), ?_⟩
  have hoff1 : off + 1 < srcBytes.length := by omega
  have hlenL : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).length =
      (srcBytes[off]'hoff).toNat - 0x80 := by
    rw [List.length_take, List.length_drop]; omega
  have hlen8' : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).length ≤ 8 := by
    rw [hlenL]; exact hlen8
  have hhead : ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)).headD 1 ≠ 0 := by
    rw [headD_take_drop_eq_getByteAt srcBytes (off + 1) ((srcBytes[off]'hoff).toNat - 0x80) hpos hoff1]
    exact hbyte
  have hdecU := rlpItemDecode_shortBytes_decodeAux (List.getElem?_eq_getElem hoff) hlo hhi
    hcanon hcontentlen
  have hx9 : (srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
      BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80) =
      srcBase + BitVec.ofNat 64 (off + 1 + ((srcBytes[off]'hoff).toNat - 0x80)) := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]; bv_omega
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8', hdecU, by omega⟩
  rw [hlenL, ← hx9]
  have hpf : (⌜0 < (srcBytes[off]'hoff).toNat - 0x80 ∧ getByteAt srcBytes (off + 1) ≠ 0 ∧
        (srcBytes[off]'hoff).toNat - 0x80 ≤ 8⌝ **
      ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) **
        (.x10 ↦ᵣ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 ((srcBytes[off]'hoff).toNat - 0x80))) ** (.x8 ↦ᵣ struct) **
        (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ BitVec.ofNat 64
          (Nat.fromBytesBE ((srcBytes.drop (off + 1)).take ((srcBytes[off]'hoff).toNat - 0x80)))) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-- **Field-3 empty body → unified post.** Re-expresses `wd_decode_field3BodyEmpty` against
    `wd_scalarFieldUnifiedPost` with `d0 = []`, `nextOff = off + 1`: the empty string is the canonical
    encoding of the scalar `0`, so `headD 1 = 1 ≠ 0` vacuously and the stored value is `0`. -/
theorem wd_decode_field3BodyEmpty_unified
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
    (hempty : (srcBytes[off]'hoff).toNat - 0x80 = 0) :
    cpsTripleWithin ((2 + (1 + 87) + 1) +
        (7 + (1 + (7 * ((srcBytes[off]'hoff).toNat - 0x80) + 11)) + 2))
      (base + 220) (base + 276) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 off)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 268) struct (40 : BitVec 12) srcBase endPtr
          srcBytes off d0 nextOff h) := by
  have hv := wd_decode_field3BodyEmpty base srcBase endPtr vOld a0Old a1Old a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes off
    halign232 hdisjW halign268 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hv
  rw [hempty] at hp
  refine ⟨([] : List (BitVec 8)), off + 1, ?_⟩
  have hhead : ([] : List (BitVec 8)).headD 1 ≠ 0 := by decide
  have hlen8 : ([] : List (BitVec 8)).length ≤ 8 := by norm_num
  have hval0 : BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) := by rfl
  have hdecU : ∀ m, decodeAux (m + 1) (srcBytes.drop off) =
      some (.bytes ([] : List (BitVec 8)), srcBytes.drop (off + 1)) := by
    intro m
    have h := rlpItemDecode_shortBytes_decodeAux (List.getElem?_eq_getElem hoff) hlo hhi
      (fun _ => by exfalso; simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hlo; bv_omega)
      (by rw [hempty]; omega) m
    rw [hempty] at h
    simpa using h
  have hx9 : (srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 0 =
      srcBase + BitVec.ofNat 64 (off + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]; bv_omega
  unfold wd_scalarFieldUnifiedPost
  refine (sepConj_pure_right h).mpr ⟨?_, hhead, hlen8, hdecU, by omega⟩
  rw [hval0, ← hx9, List.length_nil]
  have hpf : (⌜(0 : Nat) = 0⌝ **
      ⌜BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (192 : Word)⌝ **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12)) +
          BitVec.ofNat 64 0)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 0)) **
        (.x8 ↦ᵣ struct) ** (.x1 ↦ᵣ (base + 268)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion srcBase srcBytes **
        ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
        (.x18 ↦ᵣ endPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h := by
    xperm_hyp hp
  have hsp := ((sepConj_pure_left _).1 ((sepConj_pure_left _).1
    ((sepConj_pure_left _).1 hpf).2).2).2
  xperm_hyp hsp

/-! ## M3 proof — success-path semantic endpoint

The forward success chain, having run the four field bodies, collects the four `decodeAux`
consumption facts (the unified posts' trailing pures + a derived one for the address) plus the
per-field canonicity. These two lemmas turn that bundle into `decodeWithdrawal srcBytes = some
w`: `…_payloadFacts` over the inner payload offsets (the form `decodeFully_shortList_four`
consumes), and `…_srcFacts` over the raw `srcBytes` offsets the walk actually produces (the
`srcBytes = pfx :: payload` ⇒ `srcBytes.drop (k+1) = payload.drop k` shift is discharged here, so
the chain never has to do offset bookkeeping). -/

/-- **Success endpoint over payload offsets.** A short-list prefix `pfx` whose payload is a run of
    four canonical byte-string items (the `decodeAux` steps `h0..h3`, ending exactly at `off4`)
    decodes as a withdrawal. Thin composition of `decodeFully_shortList_four` (payload structure)
    and `decodeWithdrawal_eq_some_of_fields` (canonicity ⇒ `some w`). -/
theorem wd_decodeWithdrawal_some_of_payloadFacts
    (pfx : Byte) (payload : List Byte) (d0 d1 d2 d3 : List Byte) (off1 off2 off3 off4 : Nat)
    (hclass : classifyPrefix pfx = .shortList)
    (hplen : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hmin : 2 ≤ payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, payload.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (payload.drop off1) = some (.bytes d1, payload.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (payload.drop off2) = some (.bytes d2, payload.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (payload.drop off3) = some (.bytes d3, payload.drop off4))
    (hend : payload.drop off4 = [])
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (h20 : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal (pfx :: payload) =
      some { index := Nat.fromBytesBE d0, validatorIndex := Nat.fromBytesBE d1,
             address := BitVec.ofNat 160 (Nat.fromBytesBE d2), amount := Nat.fromBytesBE d3 } := by
  refine decodeWithdrawal_eq_some_of_fields (pfx :: payload) d0 d1 d2 d3 ?_ hc0 hl0 hc1 hl1 h20 hc3 hl3
  exact decodeFully_shortList_four pfx payload off1 off2 off3 off4
    (.bytes d0) (.bytes d1) (.bytes d2) (.bytes d3) hclass hplen h0 h1 h2 h3 hend hmin

/-- **Success endpoint over `srcBytes` offsets.** The walk produces its `decodeAux` steps over
    `srcBytes.drop off` with byte offsets into the full input; with `srcBytes = pfx :: payload` the
    first content byte sits at offset `1`, and consuming exactly `srcBytes.length` bytes (`h3`'s
    tail) closes the list. Discharges the `srcBytes ↔ payload` offset shift, then delegates to
    `wd_decodeWithdrawal_some_of_payloadFacts`. The form the forward chain plugs into directly. -/
theorem wd_decodeWithdrawal_some_of_srcFacts
    (srcBytes : List Byte) (pfx : Byte) (payload : List Byte)
    (d0 d1 d2 d3 : List Byte) (off1 off2 off3 : Nat)
    (hsrc : srcBytes = pfx :: payload)
    (h1le : 1 ≤ off1) (h2le : 1 ≤ off2) (h3le : 1 ≤ off3)
    (hclass : classifyPrefix pfx = .shortList)
    (hplen : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hmin : 2 ≤ payload.length)
    (h0 : ∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (srcBytes.drop off1) = some (.bytes d1, srcBytes.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (srcBytes.drop off2) = some (.bytes d2, srcBytes.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (srcBytes.drop off3) =
      some (.bytes d3, srcBytes.drop srcBytes.length))
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (h20 : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal srcBytes =
      some { index := Nat.fromBytesBE d0, validatorIndex := Nat.fromBytesBE d1,
             address := BitVec.ofNat 160 (Nat.fromBytesBE d2), amount := Nat.fromBytesBE d3 } := by
  subst hsrc
  -- `(pfx :: payload).drop k = payload.drop (k-1)` for `k ≥ 1`
  have hd : ∀ k, 1 ≤ k → (pfx :: payload).drop k = payload.drop (k - 1) := fun k hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [List.drop_succ_cons, Nat.add_sub_cancel]
  have hlen1 : (pfx :: payload).length = payload.length + 1 := by simp
  -- rewrite the four steps + the closing tail into payload form
  rw [show (pfx :: payload).drop 1 = payload from by rw [hd 1 (le_refl 1)]; simp] at h0
  rw [hd off1 h1le] at h0 h1
  rw [hd off2 h2le] at h1 h2
  rw [hd off3 h3le] at h2 h3
  rw [hlen1, hd (payload.length + 1) (by omega)] at h3
  simp only [Nat.add_sub_cancel] at h3
  exact wd_decodeWithdrawal_some_of_payloadFacts pfx payload d0 d1 d2 d3
    (off1 - 1) (off2 - 1) (off3 - 1) payload.length hclass hplen hmin h0 h1 h2 h3
    List.drop_length hc0 hl0 hc1 hl1 h20 hc3 hl3

/-- **Reverse-decode entry (encode round-trip).** From `decodeWithdrawal srcBytes = some w` the
    input is exactly the RLP encoding of the four decoded byte-lists, carrying the canonicity the
    strict decoder enforced and `w`'s fields read off them. The clean entry point for discharging
    `wd_decode_successLeaf`'s hypotheses in the capstone success case: `decode_eq_some_imp_encode`
    (no length bound needed) pins `srcBytes = encode (.list […])`, whence the per-field offsets,
    `decodeAux` steps, byte forms, and bounds follow from the encode structure (`encode_list_short`
    + `decode_encode_append`). -/
theorem wd_srcBytes_eq_encode (srcBytes : List Byte) (w : Withdrawal)
    (h : decodeWithdrawal srcBytes = some w) :
    ∃ d0 d1 d2 d3 : List Byte,
      srcBytes = encode (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]) ∧
      d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧ d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
      d2.length = 20 ∧ d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
      w.index = Nat.fromBytesBE d0 ∧ w.validatorIndex = Nat.fromBytesBE d1 ∧
      w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2) ∧ w.amount = Nat.fromBytesBE d3 := by
  obtain ⟨d0, d1, d2, d3, hdf, hc0, hl0, hc1, hl1, h20, hc3, hl3, hi, hv, ha, hamt⟩ :=
    (decodeWithdrawal_eq_some_iff srcBytes w).mp h
  refine ⟨d0, d1, d2, d3, ?_, hc0, hl0, hc1, hl1, h20, hc3, hl3, hi, hv, ha, hamt⟩
  have hdec := (decodeFully_eq_some_iff srcBytes _).mp hdf
  have henc := decode_eq_some_imp_encode srcBytes _ [] hdec
  simpa using henc

/-- **Field-2 (address) `decodeAux` step.** The address field is a fixed 20-byte short string
    (prefix `0x94`); its body (`wd_decode_field2Body`) exposes the byte-copy and `rlpItemDecode`
    but not a `decodeAux` step. This derives the missing step from the same prefix/length facts, so
    the success chain treats field 2 uniformly with the three scalar fields: content
    `d2 = (drop (off+1)).take 20` (`d2.length = 20`), consuming `[off, off+21)`. -/
theorem wd_field2_decodeAux (srcBytes : List Byte) (off : Nat) (hoff : off < srcBytes.length)
    (hlo : ¬ BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult ((srcBytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hlen20 : (srcBytes[off]'hoff).toNat - 0x80 = 20)
    (hcontentlen : off + 21 ≤ srcBytes.length) :
    ∀ m, decodeAux (m + 1) (srcBytes.drop off) =
      some (.bytes ((srcBytes.drop (off + 1)).take 20), srcBytes.drop (off + 21)) := by
  intro m
  have h := rlpItemDecode_shortBytes_decodeAux (List.getElem?_eq_getElem hoff) hlo hhi
    (fun hc => by
      exfalso
      have h20 : (srcBytes[off]'hoff).zeroExtend 64 - (0x80 : Word) = (20 : Word) := by
        have hb := (srcBytes[off]'hoff).isLt; have := hlen20; bv_omega
      rw [h20] at hc; exact absurd hc (by decide))
    (by rw [hlen20]; omega) m
  rw [hlen20] at h
  rw [show off + 21 = off + 1 + 20 from by omega]
  exact h

/-- **Per-field `decodeAux` from an `encodeBytes` prefix (reverse-decode core).** If the suffix
    `srcBytes.drop off` is exactly `encodeBytes data ++ rest`, then `decodeAux` consumes that one
    byte-string item, advancing the cursor by `(encodeBytes data).length`; the next suffix is
    `rest`. The fuel-parametric `∀ m` form holds because a byte string needs only one fuel level
    (`decodeAux_succ_encodeBytes_append`). This is the workhorse for discharging the success leaf's
    `decodeAux` hypotheses from `srcBytes = encode (.list […])` (`wd_srcBytes_eq_encode`): peel the
    payload one field at a time, feeding `rest` (the tail encoding) as the next field's prefix. -/
theorem wd_decodeAux_of_encodeBytes_drop (srcBytes : List Byte) (off : Nat) (data rest : List Byte)
    (hdrop : srcBytes.drop off = encodeBytes data ++ rest)
    (hlen : data.length < 256 ^ 8) :
    (∀ m, decodeAux (m + 1) (srcBytes.drop off) =
      some (.bytes data, srcBytes.drop (off + (encodeBytes data).length))) ∧
    srcBytes.drop (off + (encodeBytes data).length) = rest := by
  have hnext : srcBytes.drop (off + (encodeBytes data).length) = rest := by
    rw [← List.drop_drop, hdrop, List.drop_left]
  refine ⟨fun m => ?_, hnext⟩
  rw [hdrop, hnext]
  exact decodeAux_succ_encodeBytes_append m data rest hlen

/-! ## M3 proof — success spine: field1 ⨾ field2 seam consumer -/

/-- **Address-field precondition bundle.** The offset-dependent side-conditions field 2's body
    (`wd_decode_field2Body_regOwn`) requires at its entry offset `srcOff`: range, non-overflow,
    valid access, cursor before end, and the prefix classifies as a **20-byte short string**
    (`0x94`: `¬ult b 0x80 ∧ ult b 0xb8 ∧ b-0x80 = 20`) that fits, with the full 21-byte span in
    range and accessible. The global/output-region conditions (`hsalign`, `hstalign`, `hsover`,
    `hsvalid`, `hdlen`, `hdov`, `hdval`, `hbase`) are *not* offset-dependent and are supplied
    directly. The companion to `wd_scalarFieldPre` for the address field. -/
def wd_addressFieldPre (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat) : Prop :=
  ∃ hoff : srcOff < srcBytes.length,
    srcBase.toNat + srcOff < 2 ^ 64 ∧
    isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true ∧
    BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true ∧
    ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
    BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
    (srcBytes[srcOff]'hoff).toNat - 0x80 = 20 ∧
    BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
    srcOff + 21 ≤ srcBytes.length ∧
    srcBase.toNat + (srcOff + 21) ≤ 2 ^ 64 ∧
    (∀ k, k < 20 → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)

/-- **Scalar-field precondition bundle.** The five side-conditions a scalar-field body dispatcher
    (`wd_decode_field{0,1,3}Body_unified_regOwn`) requires at its entry offset `srcOff`: the offset
    is in range, the source pointer does not overflow, the byte access is valid, the cursor is still
    before the list end, and the prefix byte classifies as one of the three accepted scalar forms
    (single byte / short canonical string / empty string). Bundling them lets the inter-field seam
    hypothesis (`hf1`/`hf3`/…) — which the capstone discharges from `decodeWithdrawal = some` — be
    stated concisely against the *existential* next-offset produced by the previous field. -/
def wd_scalarFieldPre (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat) : Prop :=
  ∃ hoff : srcOff < srcBytes.length,
    srcBase.toNat + srcOff < 2 ^ 64 ∧
    isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true ∧
    BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true ∧
    ((BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0))

/-- **Scalar-field precondition from the encode structure (reverse-decode form).** If the suffix
    at `off` is `encodeBytes D ++ rest` for a canonical scalar `D` (`headD 1 ≠ 0`, `length ≤ 8`),
    then `off` satisfies `wd_scalarFieldPre`: the prefix byte classifies as one of the three
    accepted scalar forms (single byte `<0x80`; short canonical string; empty `0x80`), and all
    bounds hold. The byte form follows from `encodeBytes D`'s shape; the bounds from source-region
    validity and `off + |encodeBytes D| ≤ length`. The reverse-decode discharger for the success
    leaf's `hform0`/`hf1`/`hf3` (after `decodeAux` determinism pins the existential offset). -/
theorem wd_scalarFieldPre_of_encodeBytes
    (srcBase srcLen : Word) (srcBytes : List Byte) (off : Nat) (D rest : List Byte)
    (hsvalid : ∀ k, k < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hnowrap : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsrclen : srcLen = BitVec.ofNat 64 srcBytes.length)
    (hdrop : srcBytes.drop off = encodeBytes D ++ rest)
    (hc : D.headD 1 ≠ 0) (hl : D.length ≤ 8) :
    wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes off := by
  subst hsrclen
  have hpos : 0 < (encodeBytes D).length := encodeBytes_nonempty D
  have hdroplen : srcBytes.length - off = (encodeBytes D).length + rest.length := by
    have := congrArg List.length hdrop
    simpa [List.length_drop, List.length_append] using this
  have hoff : off < srcBytes.length := by omega
  have hfit : off + (encodeBytes D).length ≤ srcBytes.length := by omega
  have hover : srcBase.toNat + off < 2 ^ 64 := by omega
  have hvalidoff : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true := hsvalid off hoff
  have hgetb : getByteAt srcBytes off = srcBytes[off]'hoff := by simp [getByteAt, hoff]
  have hcursor : BitVec.ult (srcBase + BitVec.ofNat 64 off)
      ((srcBase + BitVec.ofNat 64 0) + BitVec.ofNat 64 srcBytes.length) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hspanN : (((srcBase + BitVec.ofNat 64 0) + BitVec.ofNat 64 srcBytes.length) -
      (srcBase + BitVec.ofNat 64 off)).toNat = srcBytes.length - off := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h80 : (0x80 : Word).toNat = 128 := by decide
  have hb8 : (0xb8 : Word).toNat = 184 := by decide
  have hde : srcBytes.drop off = srcBytes[off]'hoff :: srcBytes.drop (off + 1) :=
    List.drop_eq_getElem_cons hoff
  rw [hde] at hdrop
  refine ⟨hoff, hover, hvalidoff, hcursor, ?_⟩
  rcases D with _ | ⟨b, _ | ⟨b1, t⟩⟩
  · -- D = []: empty form (0x80)
    rw [show encodeBytes ([] : List Byte) = [BitVec.ofNat 8 0x80] from by decide,
        List.singleton_append, List.cons.injEq] at hdrop
    obtain ⟨hbyte, _⟩ := hdrop
    exact Or.inr (Or.inr ⟨by rw [hbyte]; decide, by rw [hbyte]; decide, by rw [hbyte]; decide⟩)
  · -- D = [b]: single byte (b < 0x80) or short len-1 string (b ≥ 0x80)
    by_cases hb : b.toNat < 0x80
    · -- single byte
      rw [show encodeBytes [b] = [b] from by simp [encodeBytes, hb],
          List.singleton_append, List.cons.injEq] at hdrop
      obtain ⟨hbyte, _⟩ := hdrop
      have hbz : ((srcBytes[off]'hoff).zeroExtend 64).toNat = (srcBytes[off]'hoff).toNat := by
        have := (srcBytes[off]'hoff).isLt; bv_omega
      have hbt : (srcBytes[off]'hoff).toNat < 128 := by rw [hbyte]; exact hb
      refine Or.inl ⟨?_, ?_⟩
      · simp only [BitVec.ult, decide_eq_true_eq, hbz, h80]; omega
      · rw [hgetb, hbyte]; simpa using hc
    · -- short string, len 1
      rw [Nat.not_lt] at hb
      have henc : encodeBytes [b] = [BitVec.ofNat 8 0x81, b] := by
        simp [encodeBytes, Nat.not_lt.mpr hb]
      have henclen : (encodeBytes [b]).length = 2 := by rw [henc]; rfl
      rw [henc, List.cons_append, List.cons_append, List.cons.injEq] at hdrop
      obtain ⟨hbyte, hrest1⟩ := hdrop
      have hnext1 : srcBytes[off + 1]? = some b := by
        have : (srcBytes.drop (off + 1))[0]? = some b := by rw [hrest1]; rfl
        rwa [List.getElem?_drop, Nat.add_zero] at this
      have hb1lt : off + 1 < srcBytes.length := by omega
      have hbtoNat : (srcBytes[off]'hoff).toNat = 0x81 := by rw [hbyte]; decide
      have hgetb1 : srcBytes[off + 1]'hb1lt = b := by
        rw [List.getElem?_eq_getElem hb1lt] at hnext1; exact Option.some.inj hnext1
      have hbz : ((srcBytes[off]'hoff).zeroExtend 64).toNat = (srcBytes[off]'hoff).toNat := by
        have := (srcBytes[off]'hoff).isLt; bv_omega
      have hsubN : ((srcBytes[off]'hoff).zeroExtend 64 - 0x80).toNat
          = (srcBytes[off]'hoff).toNat - 0x80 := by
        have := (srcBytes[off]'hoff).isLt; bv_omega
      refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbtoNat, h80]; omega
      · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbtoNat, hb8]; omega
      · intro _
        refine ⟨b, hnext1, ?_⟩
        have hbz' : (b.zeroExtend 64).toNat = b.toNat := by have := b.isLt; bv_omega
        simp only [BitVec.ult, decide_eq_true_eq, hbz', h80]; omega
      · simp only [BitVec.ult, decide_eq_true_eq, hsubN, hspanN, hbtoNat]; omega
      · rw [hbtoNat]; omega
      · rw [hbtoNat]; omega
      · intro k hk
        rw [hbtoNat] at hk
        have hk0 : k = 0 := by omega
        subst hk0; simpa using hsvalid (off + 1) hb1lt
      · rw [hbtoNat]; omega
      · rw [show getByteAt srcBytes (off + 1) = srcBytes[off + 1]'hb1lt from by simp [getByteAt, hb1lt],
            hgetb1]
        rintro rfl; revert hb; decide
      · rw [hbtoNat]; omega
  · -- D = b :: b1 :: t: short string, len ≥ 2
    set len := (b :: b1 :: t).length with hlendef
    have hlen2 : 2 ≤ len := by simp [hlendef]
    have hle8 : len ≤ 8 := hl
    have henc : encodeBytes (b :: b1 :: t) = BitVec.ofNat 8 (0x80 + len) :: (b :: b1 :: t) := by
      rw [encodeBytes_short_of_length_ne_one (b :: b1 :: t) (by omega) (by simp)]
      simp [hlendef]
    have henclen : (encodeBytes (b :: b1 :: t)).length = 1 + len := by
      rw [henc, List.length_cons, ← hlendef]; omega
    rw [henc, List.cons_append, List.cons.injEq] at hdrop
    obtain ⟨hbyte, hrest1⟩ := hdrop
    have hbtoNat : (srcBytes[off]'hoff).toNat = 0x80 + len := by
      rw [hbyte, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hb1lt : off + 1 < srcBytes.length := by omega
    have hgetb1 : srcBytes[off + 1]'hb1lt = b := by
      have : (srcBytes.drop (off + 1))[0]? = some b := by rw [hrest1]; rfl
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hb1lt] at this
      exact Option.some.inj this
    have hbz : ((srcBytes[off]'hoff).zeroExtend 64).toNat = (srcBytes[off]'hoff).toNat := by
      have := (srcBytes[off]'hoff).isLt; bv_omega
    have hsubN : ((srcBytes[off]'hoff).zeroExtend 64 - 0x80).toNat
        = (srcBytes[off]'hoff).toNat - 0x80 := by
      have := (srcBytes[off]'hoff).isLt; bv_omega
    refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbtoNat, h80]; omega
    · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbtoNat, hb8]; omega
    · intro h1
      exfalso
      have h2 := congrArg BitVec.toNat h1
      rw [hsubN, hbtoNat] at h2
      simp only [show ((1 : BitVec 64).toNat) = 1 from rfl] at h2
      omega
    · simp only [BitVec.ult, decide_eq_true_eq, hsubN, hspanN, hbtoNat]; omega
    · rw [hbtoNat]; omega
    · rw [hbtoNat]; omega
    · intro k hk
      rw [hbtoNat] at hk
      exact hsvalid (off + 1 + k) (by omega)
    · rw [hbtoNat]; omega
    · rw [show getByteAt srcBytes (off + 1) = srcBytes[off + 1]'hb1lt from by simp [getByteAt, hb1lt],
          hgetb1]
      simpa using hc
    · rw [hbtoNat]; omega

/-- **Address-field precondition from the encode structure (reverse-decode form).** The address is
    a fixed 20-byte short string (`encodeBytes D = 0x94 :: D` when `|D| = 20`), so the prefix `0x94`
    classifies unambiguously: `¬ult 0x80`, `ult 0xb8`, content length `0x94 - 0x80 = 20`, the 21-byte
    span fits and is accessible. The reverse-decode discharger for the success leaf's `hf2`. -/
theorem wd_addressFieldPre_of_encodeBytes
    (srcBase srcLen : Word) (srcBytes : List Byte) (off : Nat) (D rest : List Byte)
    (hsvalid : ∀ k, k < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hnowrap : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsrclen : srcLen = BitVec.ofNat 64 srcBytes.length)
    (hdrop : srcBytes.drop off = encodeBytes D ++ rest)
    (hlen20 : D.length = 20) :
    wd_addressFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes off := by
  subst hsrclen
  have henc : encodeBytes D = BitVec.ofNat 8 (0x80 + 20) :: D := by
    rw [encodeBytes_short_of_length_ne_one D (by omega) (by omega), hlen20]; rfl
  have henclen : (encodeBytes D).length = 21 := by rw [henc]; simp [hlen20]
  have hdroplen : srcBytes.length - off = (encodeBytes D).length + rest.length := by
    have := congrArg List.length hdrop
    simpa [List.length_drop, List.length_append] using this
  have hoff : off < srcBytes.length := by omega
  have hfit : off + 21 ≤ srcBytes.length := by omega
  have hover : srcBase.toNat + off < 2 ^ 64 := by omega
  have hvalidoff : isValidByteAccess (srcBase + BitVec.ofNat 64 off) = true := hsvalid off hoff
  have hcursor : BitVec.ult (srcBase + BitVec.ofNat 64 off)
      ((srcBase + BitVec.ofNat 64 0) + BitVec.ofNat 64 srcBytes.length) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hspanN : (((srcBase + BitVec.ofNat 64 0) + BitVec.ofNat 64 srcBytes.length) -
      (srcBase + BitVec.ofNat 64 off)).toNat = srcBytes.length - off := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h80 : (0x80 : Word).toNat = 128 := by decide
  have hb8 : (0xb8 : Word).toNat = 184 := by decide
  have hde : srcBytes.drop off = srcBytes[off]'hoff :: srcBytes.drop (off + 1) :=
    List.drop_eq_getElem_cons hoff
  rw [hde, henc, List.cons_append, List.cons.injEq] at hdrop
  obtain ⟨hbyte, _⟩ := hdrop
  have hbtoNat : (srcBytes[off]'hoff).toNat = 0x94 := by rw [hbyte]; decide
  have hbz : ((srcBytes[off]'hoff).zeroExtend 64).toNat = (srcBytes[off]'hoff).toNat := by
    have := (srcBytes[off]'hoff).isLt; bv_omega
  have hsubN : ((srcBytes[off]'hoff).zeroExtend 64 - 0x80).toNat
      = (srcBytes[off]'hoff).toNat - 0x80 := by
    have := (srcBytes[off]'hoff).isLt; bv_omega
  refine ⟨hoff, hover, hvalidoff, hcursor, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbtoNat, h80]; omega
  · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbtoNat, hb8]; omega
  · omega
  · simp only [BitVec.ult, decide_eq_true_eq, hsubN, hspanN, hbtoNat]; omega
  · omega
  · omega
  · intro k hk; exact hsvalid (off + 1 + k) (by omega)

/-- A byte string of length ≤ 55 encodes to at most `length + 1` bytes (1-byte header). -/
theorem encodeBytes_length_le_succ (d : List Byte) (h : d.length ≤ 55) :
    (encodeBytes d).length ≤ d.length + 1 := by
  rcases d with _ | ⟨b, _ | ⟨b1, t⟩⟩
  · simp [encodeBytes]
  · by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
  · rw [encodeBytes_short_of_length_ne_one (b :: b1 :: t) h (by simp)]; simp

/-- **Withdrawal payload decomposition.** The RLP encoding of the four-field withdrawal is a
    one-byte short-list header `0xC0 + |payload|` followed by the concatenated field encodings,
    with `|payload| ≤ 48 ≤ 55` (so the list is genuinely short). Feeds the success-case reverse
    bridge: `srcBytes.drop 1` is exactly the payload, peelable field-by-field via
    `wd_decodeAux_of_encodeBytes_drop`, and the header byte gives `walk_init`'s shortList facts. -/
theorem wd_encode4_payload (srcBytes : List Byte) (d0 d1 d2 d3 : List Byte)
    (hsrc : srcBytes = encode (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]))
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8) (h20 : d2.length = 20) (hl3 : d3.length ≤ 8) :
    srcBytes = BitVec.ofNat 8 (0xC0 +
        (encodeBytes d0 ++ (encodeBytes d1 ++ (encodeBytes d2 ++ encodeBytes d3))).length)
        :: (encodeBytes d0 ++ (encodeBytes d1 ++ (encodeBytes d2 ++ encodeBytes d3)))
      ∧ (encodeBytes d0 ++ (encodeBytes d1 ++ (encodeBytes d2 ++ encodeBytes d3))).length ≤ 48 := by
  have hpayload : encode.encodeItems [RLPItem.bytes d0, .bytes d1, .bytes d2, .bytes d3]
      = encodeBytes d0 ++ (encodeBytes d1 ++ (encodeBytes d2 ++ encodeBytes d3)) := by
    simp [encode.encodeItems, encode]
  have hP : (encodeBytes d0 ++ (encodeBytes d1 ++ (encodeBytes d2 ++ encodeBytes d3))).length ≤ 48 := by
    have e0 := encodeBytes_length_le_succ d0 (by omega)
    have e1 := encodeBytes_length_le_succ d1 (by omega)
    have e2 : (encodeBytes d2).length = 21 := by
      rw [encodeBytes_short_of_length_ne_one d2 (by omega) (by omega)]; simp [h20]
    have e3 := encodeBytes_length_le_succ d3 (by omega)
    simp only [List.length_append]; omega
  refine ⟨?_, hP⟩
  rw [hsrc, encode_list_short _ (by rw [hpayload]; omega), hpayload]

/-- **Decode determinism pin.** The runtime `walk_next` reports some `(d, nextOff)` for the item at
    `off`; if the suffix there is `encodeBytes D ++ rest`, then `decodeAux`'s determinism forces
    `d = D` and `srcBytes.drop nextOff = rest`. This is how the success leaf's *existential*
    next-offsets (`nextOff0`/`nextOff1`/`nextOff3`) get pinned to the encode-derived tails, so each
    field's precondition (`wd_scalarFieldPre`/`wd_addressFieldPre`) can be discharged at it. -/
theorem wd_drop_pin (srcBytes : List Byte) (off nextOff : Nat) (d D rest : List Byte)
    (hrt : ∀ m, decodeAux (m + 1) (srcBytes.drop off) = some (.bytes d, srcBytes.drop nextOff))
    (hdrop : srcBytes.drop off = encodeBytes D ++ rest) (hlen : D.length < 256 ^ 8) :
    d = D ∧ srcBytes.drop nextOff = rest := by
  have hpeel := wd_decodeAux_of_encodeBytes_drop srcBytes off D rest hdrop hlen
  have heq := (hrt 0).symm.trans (hpeel.1 0)
  rw [Option.some.injEq, Prod.mk.injEq] at heq
  exact ⟨by injection heq.1, heq.2.trans hpeel.2⟩

/-- **`walk_init` short-list facts from the payload header.** The one-byte header `0xC0 + |P|`
    (with `|P| ≤ 48`) classifies as a short list whose span is exactly `srcLen = |srcBytes|`: the
    three facts `walk_init`'s short-success arm exposes (`h_ge`: `≥ 0xc0`; `h_hi`: `< 0xf8`;
    `h_exact`: cursor-end span match). Discharges the success leaf's `h_ge`/`h_hi`/`h_exact`. -/
theorem wd_walkInit_facts (srcBase srcLen : Word) (srcBytes P : List Byte) (h0 : 0 < srcBytes.length)
    (hsrc : srcBytes = BitVec.ofNat 8 (0xC0 + P.length) :: P)
    (hP48 : P.length ≤ 48) (hsrclen : srcLen = BitVec.ofNat 64 srcBytes.length) :
    (¬ BitVec.ult ((srcBytes[0]'h0).zeroExtend 64) (0xc0 : Word) = true) ∧
    BitVec.ult ((srcBytes[0]'h0).zeroExtend 64) (0xf8 : Word) = true ∧
    (srcBase + BitVec.ofNat 64 0) +
        (((srcBytes[0]'h0).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (srcBase + BitVec.ofNat 64 0) + srcLen := by
  have hb0 : srcBytes[0]'h0 = BitVec.ofNat 8 (0xC0 + P.length) := by simp [hsrc]
  have hlen1 : srcBytes.length = P.length + 1 := by rw [hsrc]; simp
  have hbN : (srcBytes[0]'h0).toNat = 0xC0 + P.length := by
    rw [hb0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbz : ((srcBytes[0]'h0).zeroExtend 64).toNat = (srcBytes[0]'h0).toNat := by
    have := (srcBytes[0]'h0).isLt; bv_omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbN, show (0xc0 : Word).toNat = 192 from by decide]
    omega
  · simp only [BitVec.ult, decide_eq_true_eq, hbz, hbN, show (0xf8 : Word).toNat = 248 from by decide]
    omega
  · rw [hsrclen, hlen1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hbz, hbN,
      show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show ((0xc0 : Word).toNat) = 192 from by decide, show ((1 : Word).toNat) = 1 from by decide]
    omega

/-- **Success-case field preconditions (reverse bridge bundle).** From `decodeWithdrawal srcBytes =
    some w`, discharge the four dependent hypotheses the success leaf needs (`hf1`/`hf2`/`hf3`/`h_end`).
    Each peels the encode payload with `wd_drop_pin` (pinning the runtime next-offset to the
    encode-derived tail) then applies the matching form lemma. `h_end` closes because the d3-facts now
    carry `nextOff3 ≤ length`, which with `drop nextOff3 = []` (⟹ `≥ length`) pins `nextOff3 = length`. -/
theorem wd_decode_success_field_hyps (srcBase srcLen : Word) (srcBytes : List Byte) (w : Withdrawal)
    (hsvalid : ∀ k, k < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hnowrap : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsrclen : srcLen = BitVec.ofNat 64 srcBytes.length)
    (hdec : decodeWithdrawal srcBytes = some w) :
    (∀ (d0 : List Byte) (nextOff0 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop nextOff0)) ∧
          nextOff0 ≤ srcBytes.length) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0) ∧
    (∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop nextOff0)) ∧
          nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) = some (.bytes d1, srcBytes.drop nextOff1)) ∧
          nextOff1 ≤ srcBytes.length) →
      wd_addressFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff1) ∧
    (∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop nextOff0)) ∧
          nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) = some (.bytes d1, srcBytes.drop nextOff1)) ∧
          nextOff1 ≤ srcBytes.length) →
      (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21)) ∧
    (∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat) (d3 : List Byte) (nextOff3 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop nextOff0)) ∧
          nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) = some (.bytes d1, srcBytes.drop nextOff1)) ∧
          nextOff1 ≤ srcBytes.length) →
      (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) →
      (d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop (nextOff1 + 21)) =
          some (.bytes d3, srcBytes.drop nextOff3)) ∧ nextOff3 ≤ srcBytes.length) →
      ¬ BitVec.ult (srcBase + BitVec.ofNat 64 nextOff3) ((srcBase + BitVec.ofNat 64 0) + srcLen)) := by
  obtain ⟨D0, D1, D2, D3, hsrc, hc0, hl0, hc1, hl1, h20, hc3, hl3, _, _, _, _⟩ :=
    wd_srcBytes_eq_encode srcBytes w hdec
  obtain ⟨hsrc2, _⟩ := wd_encode4_payload srcBytes D0 D1 D2 D3 hsrc hl0 hl1 h20 hl3
  have hdrop1 : srcBytes.drop 1 =
      encodeBytes D0 ++ (encodeBytes D1 ++ (encodeBytes D2 ++ encodeBytes D3)) := by rw [hsrc2]; rfl
  have big0 : D0.length < 256 ^ 8 := lt_of_le_of_lt hl0 (by norm_num)
  have big1 : D1.length < 256 ^ 8 := lt_of_le_of_lt hl1 (by norm_num)
  have big2 : D2.length < 256 ^ 8 := by rw [h20]; norm_num
  have big3 : D3.length < 256 ^ 8 := lt_of_le_of_lt hl3 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro d0 nextOff0 ⟨_, _, hdec0, _⟩
    obtain ⟨_, hd1⟩ := wd_drop_pin srcBytes 1 nextOff0 d0 D0 _ hdec0 hdrop1 big0
    exact wd_scalarFieldPre_of_encodeBytes srcBase srcLen srcBytes nextOff0 D1
      (encodeBytes D2 ++ encodeBytes D3) hsvalid hnowrap hsrclen hd1 hc1 hl1
  · rintro d0 nextOff0 d1 nextOff1 ⟨_, _, hdec0, _⟩ ⟨_, _, hdec1, _⟩
    obtain ⟨_, hd1⟩ := wd_drop_pin srcBytes 1 nextOff0 d0 D0 _ hdec0 hdrop1 big0
    obtain ⟨_, hd2⟩ := wd_drop_pin srcBytes nextOff0 nextOff1 d1 D1 _ hdec1 hd1 big1
    exact wd_addressFieldPre_of_encodeBytes srcBase srcLen srcBytes nextOff1 D2
      (encodeBytes D3) hsvalid hnowrap hsrclen hd2 h20
  · rintro d0 nextOff0 d1 nextOff1 ⟨_, _, hdec0, _⟩ ⟨_, _, hdec1, _⟩ hdec2
    obtain ⟨_, hd1⟩ := wd_drop_pin srcBytes 1 nextOff0 d0 D0 _ hdec0 hdrop1 big0
    obtain ⟨_, hd2⟩ := wd_drop_pin srcBytes nextOff0 nextOff1 d1 D1 _ hdec1 hd1 big1
    obtain ⟨_, hd3⟩ := wd_drop_pin srcBytes nextOff1 (nextOff1 + 21) _ D2 (encodeBytes D3) hdec2 hd2 big2
    exact wd_scalarFieldPre_of_encodeBytes srcBase srcLen srcBytes (nextOff1 + 21) D3 []
      hsvalid hnowrap hsrclen (by rw [hd3, List.append_nil]) hc3 hl3
  · rintro d0 nextOff0 d1 nextOff1 d3 nextOff3 ⟨_, _, hdec0, _⟩ ⟨_, _, hdec1, _⟩ hdec2 ⟨_, _, hdec3, hbound3⟩
    obtain ⟨_, hd1⟩ := wd_drop_pin srcBytes 1 nextOff0 d0 D0 _ hdec0 hdrop1 big0
    obtain ⟨_, hd2⟩ := wd_drop_pin srcBytes nextOff0 nextOff1 d1 D1 _ hdec1 hd1 big1
    obtain ⟨_, hd3⟩ := wd_drop_pin srcBytes nextOff1 (nextOff1 + 21) _ D2 (encodeBytes D3) hdec2 hd2 big2
    obtain ⟨_, hd4⟩ := wd_drop_pin srcBytes (nextOff1 + 21) nextOff3 d3 D3 []
      hdec3 (by rw [hd3, List.append_nil]) big3
    have hlen0 := congrArg List.length hd4
    rw [List.length_drop] at hlen0
    simp only [List.length_nil] at hlen0
    have heq : nextOff3 = srcBytes.length := by omega
    subst hsrclen
    rw [heq]
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- **Field-2 seam-consumer per-witness post.** Field 2's native body post (cursor advanced to
    `nextOff1 + 21`, the 20-byte address copied into `struct+16`, prefix in `x5`, the messy
    leftover registers), with field 1's written `struct+8` cell carried, plus field 2's `decodeAux`
    step (`d2 = (drop (nextOff1+1)).take 20`) and the carried `d1`-facts as pure conjuncts. Named so
    the field1 ⨾ field2 assembly can reference it without re-transcribing the (large) sepConj. -/
def wd_field2ConsumePost (base srcBase srcLen structPtr : Word)
    (srcBytes dstBytes : List (BitVec 8)) (off1 : Nat) (d1 : List Byte) (nextOff1 : Nat) :
    Assertion :=
  (((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (nextOff1 + 21))) ** (.x8 ↦ᵣ structPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (nextOff1 + 21))) ** regOwn .x12 **
        (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
        (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
        (.x5 ↦ᵣ ((srcBytes[nextOff1]?.getD 0).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
        bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
        ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝) **
      ((.x18 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x11 ↦ᵣ (0 : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) **
    ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1))) **
    ⌜∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
      some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))⌝) **
    ⌜d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
      (∀ m, decodeAux (m + 1) (srcBytes.drop off1) =
        some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length⌝

/-- **Field-1 ⨾ field-2 seam consumer** (base+152 → base+220): runs field 2's body on field 1's
    *existential* output. Field 2 sits at field 1's next-offset `nextOff1`, so its preconditions
    (`wd_addressFieldPre` at `nextOff1`) are taken as the dependent hypothesis `hf2` (discharged by
    the capstone from `decodeWithdrawal = some`). Mirrors `headField01`'s per-witness body: threads
    `(d1, nextOff1)` through field 2 via `cpsTripleWithin_exists_pre`, extracts field 1's `d1`-facts
    from the unified post's pure with `cpsTripleWithin_pure_pre`, frames field 1's written `struct+8`
    cell through field 2, and exposes field 2's `decodeAux` step (`d2 = (drop (nextOff1+1)).take 20`)
    plus the carried `d1`-facts in the post. The address-copy registers `x13/x14/x15` and the
    `struct+16` output region are supplied as the extra inputs field 2 consumes. -/
theorem wd_field2_consume
    (base srcBase srcLen structPtr x13Old x14Old cnt : Word) (off1 : Nat)
    (dstBytes : List (BitVec 8))
    (halign164 : (base + 164) &&& ~~~1 = base + 164)
    (hdisjW160 : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign204 : (base + 204) &&& ~~~1 = base + 204)
    (hsalign : srcBase.toNat % 8 = 0) (hstalign : structPtr.toNat % 8 = 0)
    (hbase : base.toNat + 1444 < 2 ^ 64)
    (hdlen : dstBytes.length = 20) (hdov : (structPtr + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length →
      isValidByteAccess ((structPtr + 16) + BitVec.ofNat 64 i) = true)
    (srcBytes : List (BitVec 8))
    (hsover' : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hf2 : ∀ (d1 : List Byte) (nextOff1 : Nat),
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop off1) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      wd_addressFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff1) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (3 + 111)) (base + 152) (base + 220)
      (withdrawal_decode_code base)
      (fun h => ∃ d1 nextOff1,
        (wd_scalarFieldUnifiedPost (base + 144) structPtr (8 : BitVec 12) srcBase
            ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes off1 d1 nextOff1 **
          ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
            bytesRegion (structPtr + 16) dstBytes)) h)
      (fun h => ∃ d1 nextOff1,
        wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes off1 d1 nextOff1 h) := by
  -- pre is `∃ d1 nextOff1, (field1's unified post ** field-2 extra inputs)`; run per witness.
  refine cpsTripleWithin_exists_pre (fun d1 => ?_)
  refine cpsTripleWithin_exists_pre (fun nextOff1 => ?_)
  refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => hq)
    (cpsTripleWithin_pure_pre
      (P := ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 nextOff1)) **
        (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE d1)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ BitVec.ofNat 64 d1.length) ** (.x8 ↦ᵣ structPtr) ** (.x1 ↦ᵣ (base + 144)) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        bytesRegion srcBase srcBytes **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1)) **
        (.x18 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31) ** ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion (structPtr + 16) dstBytes))
      (fun (hfacts : d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
          (∀ m, decodeAux (m + 1) (srcBytes.drop off1) =
            some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) => ?_))
  · simp only [wd_scalarFieldUnifiedPost] at hs
    xperm_hyp hs
  · obtain ⟨hoff', hover', hvalid', hin', hlo', hhi', hlen20', hfit', hcontentlen',
      hcontentover', hcontentvalid'⟩ := hf2 d1 nextOff1 hfacts
    have hd2dec := wd_field2_decodeAux srcBytes nextOff1 hoff' hlo' hhi' hlen20' hcontentlen'
    have hbyteEq : (srcBytes[nextOff1]'hoff').zeroExtend 64 = (srcBytes[nextOff1]?.getD 0).zeroExtend 64 := by
      rw [List.getElem?_eq_getElem hoff']; rfl
    have hF2base := wd_decode_field2Body_regOwn base srcBase
      ((srcBase + BitVec.ofNat 64 0) + srcLen) (base + 144)
      (BitVec.ofNat 64 (Nat.fromBytesBE d1)) (0 : Word) (BitVec.ofNat 64 d1.length)
      structPtr x13Old x14Old cnt srcBytes dstBytes nextOff1
      halign164 hdisjW160 halign204 hsalign hstalign hoff' hover' hvalid' hin' hlo' hhi'
      hlen20' hfit' hcontentlen' hcontentover' hcontentvalid' hsover' hsvalid hdlen hdov hdval hbase
    have hF2framed := cpsTripleWithin_frameR
      ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1))
      (by pcFree) hF2base
    refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => ?_) hF2framed
    · xperm_hyp hs
    · rw [hbyteEq] at hq
      exact (sepConj_pure_right s).mpr ⟨(sepConj_pure_right s).mpr ⟨hq, hd2dec⟩, hfacts⟩

/-! ## M3 proof — success-spine tail: arity ⨾ aritySuccessReturn

A first divide-and-conquer segment of the success spine (built from the return end). The
exact-arity check (`wd_decode_arity`, base+276→292, the 5th `walk_next` reports end-of-list when
the cursor sits at the list end) composes directly with the success return
(`wd_decode_aritySuccessReturn`, base+292→ret) at the `x11=2 ∧ x6=2` seam — a clean two-block
seq, no form branching. The full spine becomes `… ⨾ field3 ⨾ wd_decode_aritySuccessTail`. -/

/-- **Arity-success tail** (`arity ⨾ aritySuccessReturn`, base+276 → ret): the cursor `s1` after
    field 3 equals the list end (`h_end : ¬ ult cursor endPtr`), so the 5th `walk_next` reports
    end-of-list (status 2), the arity `bne` falls through, `a0 ← 0`, and the routine restores the
    frame and returns. Frames the saved-register/stack-frame state through the arity block and the
    `t1`-scratch (`x12`/`x0`) through the return; composed at the `x11=2 ∧ x6=2` seam. -/
theorem wd_decode_aritySuccessTail
    (base cursor endPtr a0Old a1Old vOld a2Old t1Old spF s0Clob raSaved s0Saved s1Saved s2Saved :
      Word)
    (h_end : ¬ BitVec.ult cursor endPtr)
    (halign288 : (base + 288) &&& ~~~1 = base + 288)
    (hdisj : (CodeReq.singleton (base + 284) (.JAL .x1 (260 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hinstr : withdrawal_decode_prog.get
        ⟨73, by rw [withdrawal_decode_prog_length]; norm_num⟩ = .BNE .x11 .x6 (12 : BitVec 13)) :
    cpsTripleWithin ((2 + ((1 + 4) + 1)) + (1 + 8)) (base + 276) (raSaved &&& ~~~1)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ t1Old)) **
        ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ s0Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) **
          ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved)))
      (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** ⌜(2 : Word) = (2 : Word)⌝) **
          ((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (spF + signExtend12 (32 : BitVec 12))) **
            (.x1 ↦ᵣ raSaved) ** (.x8 ↦ᵣ s0Saved) ** (.x9 ↦ᵣ s1Saved) ** (.x18 ↦ᵣ s2Saved) **
            (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
            ((spF + 24) ↦ₘ s2Saved)))) := by
  have harity := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ s0Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) **
      ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved)) (by pcFree)
    (wd_decode_arity base cursor endPtr a0Old a1Old vOld a2Old t1Old h_end halign288 hdisj)
  have hret := cpsTripleWithin_frameL ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree)
    (wd_decode_aritySuccessReturn base spF raSaved s0Saved s1Saved s2Saved (base + 288) s0Clob
      cursor endPtr cursor hinstr)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) harity hret

/-- **Arity-success tail, regOwn-`x6` input.** Same as `wd_decode_aritySuccessTail` but takes `x6`
    as `regOwn` instead of `regIs t1Old` — matching the success field chain's output (field 3 leaves
    `x6` `regOwn`) at the arity seam. The arity block clobbers `x6` (`li t1,2`), so the post is
    unchanged; built by one `regIs → regOwn` peel. -/
theorem wd_decode_aritySuccessTail_regOwn6
    (base cursor endPtr a0Old a1Old vOld a2Old spF s0Clob raSaved s0Saved s1Saved s2Saved : Word)
    (h_end : ¬ BitVec.ult cursor endPtr)
    (halign288 : (base + 288) &&& ~~~1 = base + 288)
    (hdisj : (CodeReq.singleton (base + 284) (.JAL .x1 (260 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hinstr : withdrawal_decode_prog.get
        ⟨73, by rw [withdrawal_decode_prog_length]; norm_num⟩ = .BNE .x11 .x6 (12 : BitVec 13)) :
    cpsTripleWithin ((2 + ((1 + 4) + 1)) + (1 + 8)) (base + 276) (raSaved &&& ~~~1)
      (withdrawal_decode_code base)
      (((.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ vOld) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x6) **
        ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ s0Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) **
          ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved)))
      (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** ⌜(2 : Word) = (2 : Word)⌝) **
          ((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (spF + signExtend12 (32 : BitVec 12))) **
            (.x1 ↦ᵣ raSaved) ** (.x8 ↦ᵣ s0Saved) ** (.x9 ↦ᵣ s1Saved) ** (.x18 ↦ᵣ s2Saved) **
            (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) **
            ((spF + 24) ↦ₘ s2Saved)))) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := ((.x9 ↦ᵣ cursor) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ s0Clob) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0Saved) ** ((spF + 16) ↦ₘ s1Saved) ** ((spF + 24) ↦ₘ s2Saved))))
      (r := .x6) (fun t1Old => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (wd_decode_aritySuccessTail base cursor endPtr a0Old a1Old vOld a2Old t1Old spF s0Clob
      raSaved s0Saved s1Saved s2Saved h_end halign288 hdisj hinstr)

/-! ## M3 proof — field-0 body dispatcher (form-independent)

Collapses the three per-form unified bodies into ONE triple keyed on a form disjunction
(`hform`), so the success chain composes the four field bodies without a 3³ form explosion. The
output is `∃ N, …` (the forms have distinct step counts); the chain destructs and sums. -/

/-- **Field-0 body dispatcher.** Given the field decodes as one of the three canonical scalar
    forms (`hform`: single-byte `b<0x80 ∧ b≠0`; short `0x80≤b<0xb8` + content facts; empty `b=0x80`
    + content-availability), runs base+40→96 to the form-independent `wd_scalarFieldUnifiedPost`
    (structOff 0, x1Val base+88). Dispatches to the matching `wd_decode_field0Body*_unified`. -/
theorem wd_decode_field0Body_unified
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    ∃ N, cpsTripleWithin N (base + 40) (base + 96) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 88) struct (0 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  rcases hform with ⟨hsingle, hbyte⟩ |
    ⟨hlo, hhi, hcanon, hfit, hcl, hco, hcv, hpos, hbyte, hlen8⟩ |
    ⟨hlo, hhi, hempty⟩
  · exact ⟨_, wd_decode_field0BodySingleByte_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign52 hdisjW
      halign88 hdisjC hsalign hoff hover hvalid hin hsingle hbyte⟩
  · exact ⟨_, wd_decode_field0BodyShortBytes_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign52 hdisjW
      halign88 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit hcl hco hcv hpos hbyte
      hlen8⟩
  · exact ⟨_, wd_decode_field0BodyEmpty_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign52 hdisjW
      halign88 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty⟩

/-- **Field-1 body dispatcher.** Given the field decodes as one of the three canonical scalar
    forms (`hform`: single-byte `b<0x80 ∧ b≠0`; short `0x80≤b<0xb8` + content facts; empty `b=0x80`
    + content-availability), runs base+96→152 to the form-independent `wd_scalarFieldUnifiedPost`
    (structOff 8, x1Val base+144). Dispatches to the matching `wd_decode_field1Body*_unified`. -/
theorem wd_decode_field1Body_unified
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    ∃ N, cpsTripleWithin N (base + 96) (base + 152) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 144) struct (8 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  rcases hform with ⟨hsingle, hbyte⟩ |
    ⟨hlo, hhi, hcanon, hfit, hcl, hco, hcv, hpos, hbyte, hlen8⟩ |
    ⟨hlo, hhi, hempty⟩
  · exact ⟨_, wd_decode_field1BodySingleByte_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign108 hdisjW
      halign144 hdisjC hsalign hoff hover hvalid hin hsingle hbyte⟩
  · exact ⟨_, wd_decode_field1BodyShortBytes_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign108 hdisjW
      halign144 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit hcl hco hcv hpos hbyte
      hlen8⟩
  · exact ⟨_, wd_decode_field1BodyEmpty_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign108 hdisjW
      halign144 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty⟩

/-- **Field-3 body dispatcher.** Given the field decodes as one of the three canonical scalar
    forms (`hform`: single-byte `b<0x80 ∧ b≠0`; short `0x80≤b<0xb8` + content facts; empty `b=0x80`
    + content-availability), runs base+220→276 to the form-independent `wd_scalarFieldUnifiedPost`
    (structOff 40, x1Val base+268). Dispatches to the matching `wd_decode_field3Body*_unified`. -/
theorem wd_decode_field3Body_unified
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    ∃ N, cpsTripleWithin N (base + 220) (base + 276) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 268) struct (40 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  rcases hform with ⟨hsingle, hbyte⟩ |
    ⟨hlo, hhi, hcanon, hfit, hcl, hco, hcv, hpos, hbyte, hlen8⟩ |
    ⟨hlo, hhi, hempty⟩
  · exact ⟨_, wd_decode_field3BodySingleByte_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign232 hdisjW
      halign268 hdisjC hsalign hoff hover hvalid hin hsingle hbyte⟩
  · exact ⟨_, wd_decode_field3BodyShortBytes_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign232 hdisjW
      halign268 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit hcl hco hcv hpos hbyte
      hlen8⟩
  · exact ⟨_, wd_decode_field3BodyEmpty_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign232 hdisjW
      halign268 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty⟩

/-- **Call block: `rlp_walk_init`.** A `jal ra` at `callerPC` into the verified `rlp_walk_init`
    (appended at `calleeEntry`) classifies the RLP list header and returns to `callerPC + 4` with the
    9-way status result (short/long success `a2 = 0`, or status 1..7 on not-a-list/empty/malformed).
    Mirrors `wd_call_walk_next`; used at the single `walk_init` call site (idx 6). -/
theorem wd_call_walk_init
    (callerPC calleeEntry listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old vOld : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_init_code calleeEntry))
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hll_len : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ listBytes.length)
    (hll_over : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listBase.toNat + (listOff + 1 +
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 81) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_walk_init_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase listBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (callerPC + 4)) ** bytesRegion listBase listBytes) **
       (fun h =>
         -- empty (a2 = 2)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ (2 : Word)) ** ⌜listLen = (0 : Word)⌝) h) ∨
         -- not-a-list (a2 = 1)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
         -- short success (a2 = 0)
         (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              (listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
                = (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
         -- short mismatch (a2 = 3)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (3 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              (listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
                ≠ (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
         -- long header truncated (a2 = 4)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (4 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true⌝) h) ∨
         -- long leading zero (a2 = 5): header fits, but the first length byte is 0
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (5 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              listBytes[listOff + 1]? = some (0 : BitVec 8)⌝) h) ∨
         -- long non-minimal (a2 = 6): header fits, decoded length < 56
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (6 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true⌝) h) ∨
         -- long mismatch (a2 = 7): decoded ≥ 56 but cursor + decoded ≠ end
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (7 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
              ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
                  BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                    ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                ≠ (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
         -- long success (a2 = 0): decoded ≥ 56 and cursor + decoded = end
         (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
              (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
              ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
                  BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                    ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                = (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h))) := by
  have hcallee := rlp_walk_init_spec_within calleeEntry listBase (callerPC + 4) listLen a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBytes listOff hsalign hoff hover hvalid
    hll_len hll_over hll_valid
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee)

/-! ## M3 proof — fixed-step-bound field dispatchers (regOwn-seam prerequisite)

The `∃ N` dispatchers are re-expressed with a single concrete step bound (the L=8 maximum,
mono-bumped per form), so `cpsTripleWithin_of_forall_regIs_to_regOwn` (which needs a fixed bound)
can later lift the clobbered scratch registers to `regOwn` for the inter-field seam. -/

/-- **Field-0 body dispatcher (fixed step bound).** Given the field decodes as one of the three canonical scalar
    forms (`hform`: single-byte `b<0x80 ∧ b≠0`; short `0x80≤b<0xb8` + content facts; empty `b=0x80`
    + content-availability), runs base+40→96 to the form-independent `wd_scalarFieldUnifiedPost`
    (structOff 0, x1Val base+88). Dispatches to the matching `wd_decode_field0Body*_unified`. -/
theorem wd_decode_field0Body_unified_fixedN
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 40) (base + 96) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 88) struct (0 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  rcases hform with ⟨hsingle, hbyte⟩ |
    ⟨hlo, hhi, hcanon, hfit, hcl, hco, hcv, hpos, hbyte, hlen8⟩ |
    ⟨hlo, hhi, hempty⟩
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field0BodySingleByte_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign52 hdisjW
      halign88 hdisjC hsalign hoff hover hvalid hin hsingle hbyte)
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field0BodyShortBytes_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign52 hdisjW
      halign88 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit hcl hco hcv hpos hbyte
      hlen8)
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field0BodyEmpty_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign52 hdisjW
      halign88 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty)

/-- **Field-1 body dispatcher (fixed step bound).** Given the field decodes as one of the three canonical scalar
    forms (`hform`: single-byte `b<0x80 ∧ b≠0`; short `0x80≤b<0xb8` + content facts; empty `b=0x80`
    + content-availability), runs base+96→152 to the form-independent `wd_scalarFieldUnifiedPost`
    (structOff 8, x1Val base+144). Dispatches to the matching `wd_decode_field1Body*_unified`. -/
theorem wd_decode_field1Body_unified_fixedN
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 96) (base + 152) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 144) struct (8 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  rcases hform with ⟨hsingle, hbyte⟩ |
    ⟨hlo, hhi, hcanon, hfit, hcl, hco, hcv, hpos, hbyte, hlen8⟩ |
    ⟨hlo, hhi, hempty⟩
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field1BodySingleByte_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign108 hdisjW
      halign144 hdisjC hsalign hoff hover hvalid hin hsingle hbyte)
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field1BodyShortBytes_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign108 hdisjW
      halign144 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit hcl hco hcv hpos hbyte
      hlen8)
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field1BodyEmpty_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign108 hdisjW
      halign144 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty)

/-- **Field-3 body dispatcher (fixed step bound).** Given the field decodes as one of the three canonical scalar
    forms (`hform`: single-byte `b<0x80 ∧ b≠0`; short `0x80≤b<0xb8` + content facts; empty `b=0x80`
    + content-availability), runs base+220→276 to the form-independent `wd_scalarFieldUnifiedPost`
    (structOff 40, x1Val base+268). Dispatches to the matching `wd_decode_field3Body*_unified`. -/
theorem wd_decode_field3Body_unified_fixedN
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 220) (base + 276) (withdrawal_decode_code base)
      (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
        (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
        ((.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld)))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 268) struct (40 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  rcases hform with ⟨hsingle, hbyte⟩ |
    ⟨hlo, hhi, hcanon, hfit, hcl, hco, hcv, hpos, hbyte, hlen8⟩ |
    ⟨hlo, hhi, hempty⟩
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field3BodySingleByte_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign232 hdisjW
      halign268 hdisjC hsalign hoff hover hvalid hin hsingle hbyte)
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field3BodyShortBytes_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign232 hdisjW
      halign268 hdisjC hsalign hoff hover hvalid hin hlo hhi hcanon hfit hcl hco hcv hpos hbyte
      hlen8)
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (wd_decode_field3BodyEmpty_unified base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff halign232 hdisjW
      halign268 hdisjC hsalign hoff hover hvalid hin hlo hhi hempty)

/-- **Field-1 body dispatcher, regOwn-input.** The seven clobbered scratch registers
    (`x5/x6/x7/x28/x29/x30/x31`) are exposed as `regOwn` instead of `regIs`, so this field's PRE
    matches the previous field's `regOwn` POST at the inter-field seam. Built from the fixed-step
    dispatcher by peeling one register at a time (`cpsTripleWithin_of_forall_regIs_to_regOwn`),
    mirroring `divK_fastDigit_own_spec_within_v6`. -/
theorem wd_decode_field1Body_unified_regOwn
    (base srcBase endPtr vOld a0Old a1Old a2Old struct mOld : Word)
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 96) (base + 152) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 144) struct (8 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hfull := fun (t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word) =>
    wd_decode_field1Body_unified_fixedN base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
      halign108 hdisjW halign144 hdisjC hsalign hoff hover hvalid hin hform
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x5) (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x6) (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x28) (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** regOwn .x30 ** regOwn .x31)
      (r := .x29) (fun v29 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** regOwn .x31)
      (r := .x30) (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (8 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30))
      (r := .x31) (fun v31 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hfull v5 v6 v7 v28 v29 v30 v31)

/-- **Field-0 body dispatcher, regOwn-input.** The seven clobbered scratch registers
    (`x5/x6/x7/x28/x29/x30/x31`) are exposed as `regOwn` instead of `regIs`, so this field's PRE
    matches the previous field's `regOwn` POST at the inter-field seam. Built from the fixed-step
    dispatcher by peeling one register at a time (`cpsTripleWithin_of_forall_regIs_to_regOwn`),
    mirroring `divK_fastDigit_own_spec_within_v6`. -/
theorem wd_decode_field0Body_unified_regOwn
    (base srcBase endPtr vOld a0Old a1Old a2Old struct mOld : Word)
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 40) (base + 96) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 88) struct (0 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hfull := fun (t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word) =>
    wd_decode_field0Body_unified_fixedN base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
      halign52 hdisjW halign88 hdisjC hsalign hoff hover hvalid hin hform
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x5) (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x6) (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x28) (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** regOwn .x30 ** regOwn .x31)
      (r := .x29) (fun v29 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** regOwn .x31)
      (r := .x30) (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30))
      (r := .x31) (fun v31 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hfull v5 v6 v7 v28 v29 v30 v31)

/-- **Field-3 body dispatcher, regOwn-input.** The seven clobbered scratch registers
    (`x5/x6/x7/x28/x29/x30/x31`) are exposed as `regOwn` instead of `regIs`, so this field's PRE
    matches the previous field's `regOwn` POST at the inter-field seam. Built from the fixed-step
    dispatcher by peeling one register at a time (`cpsTripleWithin_of_forall_regIs_to_regOwn`),
    mirroring `divK_fastDigit_own_spec_within_v6`. -/
theorem wd_decode_field3Body_unified_regOwn
    (base srcBase endPtr vOld a0Old a1Old a2Old struct mOld : Word)
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 220) (base + 276) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 268) struct (40 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hfull := fun (t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word) =>
    wd_decode_field3Body_unified_fixedN base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
      halign232 hdisjW halign268 hdisjC hsalign hoff hover hvalid hin hform
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x5) (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x6) (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x28) (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** regOwn .x30 ** regOwn .x31)
      (r := .x29) (fun v29 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** regOwn .x31)
      (r := .x30) (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30))
      (r := .x31) (fun v31 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hfull v5 v6 v7 v28 v29 v30 v31)

/-- **Field-3 body dispatcher, field2-seam shape.** Tuned to match field 2's output at the
    field2 ⨾ field3 seam: `x5`/`x6` (field 2 leaves them concrete: prefix / 20) and `x10`/`x11`
    stay `regIs` params (instantiated with field 2's concrete values), while `x7`/`x12`/`x28`/`x29`/
    `x30`/`x31` are `regOwn` (field 2 leaves them `regOwn`). Avoids any `regIs → regOwn` weaken in
    the seam — a plain permutation suffices. Built off the fixed-step dispatcher by peeling the six
    scratch registers. -/
theorem wd_decode_field3Body_unified_seam
    (base srcBase endPtr vOld a0Old a1Old t0Old t1Old struct mOld : Word)
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 220) (base + 276)
      (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) **
        (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
        (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** regOwn .x7 ** regOwn .x12 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 268) struct (40 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hfull := fun (a2Old t2Old t3Old t4Old t5Old t6Old : Word) =>
    wd_decode_field3Body_unified_fixedN base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
      halign232 hdisjW halign268 hdisjC hsalign hoff hover hvalid hin hform
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ v7) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x12) (fun v12 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ v7) ** (.x12 ↦ᵣ v12) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (r := .x28) (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ v7) ** (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) ** regOwn .x30 ** regOwn .x31)
      (r := .x29) (fun v29 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ v7) ** (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** regOwn .x31)
      (r := .x30) (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (40 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ v7) ** (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30))
      (r := .x31) (fun v31 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hfull v12 v7 v28 v29 v30 v31)

/-- **Field-3 seam-consumer per-witness post.** Field 3's unified scalar post (∃ d3 nextOff3, written
    `struct+40`, cursor at field 3's next-offset) with field 2's leftover registers/cells framed
    through (`x13`/`x14`/`x15`, the `struct+16` address region, `struct+8`, the `⌜prefix<192⌝`), and
    field 2's `decodeAux` step + field 1's `d1`-facts carried as pure conjuncts. Named so the
    field2 ⨾ field3 assembly can reference it without re-transcribing the sepConj. -/
def wd_field3ConsumePost (base srcBase srcLen structPtr : Word)
    (srcBytes dstBytes : List (BitVec 8)) (off1 : Nat) (d1 : List Byte) (nextOff1 : Nat) :
    Assertion :=
  (((fun h => ∃ d3 nextOff3,
        wd_scalarFieldUnifiedPost (base + 268) structPtr (40 : BitVec 12) srcBase
          ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21) d3 nextOff3 h) **
      ((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
        (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
        bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
        ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1)))) **
      ⌜∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))⌝) **
      ⌜d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop off1) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length⌝

/-- **Field-2 ⨾ field-3 seam consumer** (base+220 → base+276): runs field 3's body on field 2's
    existential output. Field 3 sits at the determined offset `nextOff1 + 21` (field 2's next-offset).
    Its scalar preconditions are taken via `hf3` (discharged by the capstone from
    `decodeWithdrawal = some`), which depends on both field 1's `d1`-facts and field 2's `decodeAux`
    step — both extracted from `wd_field2ConsumePost`'s two pure conjuncts via nested
    `cpsTripleWithin_pure_pre`. Uses the field2-seam-shaped dispatcher
    (`wd_decode_field3Body_unified_seam`) so the reshape is a plain permutation, frames field 2's
    leftover registers/cells through field 3, and re-attaches both pures in the post. -/
theorem wd_field3_consume
    (base srcBase srcLen structPtr mOld3 : Word) (off1 : Nat)
    (srcBytes dstBytes : List (BitVec 8))
    (halign232 : (base + 232) &&& ~~~1 = base + 232)
    (hdisjW228 : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisjC264 : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hsalign : srcBase.toNat % 8 = 0)
    (hf3 : ∀ (d1 : List Byte) (nextOff1 : Nat),
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop off1) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 220) (base + 276)
      (withdrawal_decode_code base)
      (fun h => ∃ d1 nextOff1,
        (wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes off1 d1 nextOff1 **
          ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3)) h)
      (fun h => ∃ d1 nextOff1,
        wd_field3ConsumePost base srcBase srcLen structPtr srcBytes dstBytes off1 d1 nextOff1 h) := by
  refine cpsTripleWithin_exists_pre (fun d1 => ?_)
  refine cpsTripleWithin_exists_pre (fun nextOff1 => ?_)
  -- `field2post ** struct40` — extract `⌜d1facts⌝` (outermost), then `⌜d2dec⌝`.
  refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => hq)
    (cpsTripleWithin_pure_pre
      (P := (((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (nextOff1 + 21))) ** (.x8 ↦ᵣ structPtr) **
            (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
            (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (nextOff1 + 21))) ** regOwn .x12 **
            (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
            (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
            (.x5 ↦ᵣ ((srcBytes[nextOff1]?.getD 0).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
            bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
            ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝) **
          ((.x18 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x11 ↦ᵣ (0 : Word)) **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1))) **
        ⌜∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
          some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))⌝) **
        ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3))
      (fun (hd1facts : d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
          (∀ m, decodeAux (m + 1) (srcBytes.drop off1) =
            some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) => ?_))
  · simp only [wd_field2ConsumePost] at hs
    xperm_hyp hs
  refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => hq)
    (cpsTripleWithin_pure_pre
      (P := ((((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 (nextOff1 + 21))) ** (.x8 ↦ᵣ structPtr) **
            (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (20 : Word)) ** (.x1 ↦ᵣ (base + 204)) **
            (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 (nextOff1 + 21))) ** regOwn .x12 **
            (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
            (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
            (.x5 ↦ᵣ ((srcBytes[nextOff1]?.getD 0).zeroExtend 64)) ** bytesRegion srcBase srcBytes **
            bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
            ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝) **
          ((.x18 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x11 ↦ᵣ (0 : Word)) **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1))) **
        ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3))
      (fun (hd2dec : ∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
          some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) =>
        ?_))
  · xperm_hyp hs
  -- spatial pre now; build field 3 at offset `nextOff1 + 21`, frame field 2's leftovers.
  obtain ⟨hoff3, hover3, hvalid3, hin3, hform3⟩ := hf3 d1 nextOff1 hd1facts hd2dec
  have hF3 := wd_decode_field3Body_unified_seam base srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen)
    (base + 204) (srcBase + BitVec.ofNat 64 (nextOff1 + 21)) (0 : Word)
    ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (20 : Word) structPtr mOld3 srcBytes (nextOff1 + 21)
    halign232 hdisjW228 halign268 hdisjC264 hsalign hoff3 hover3 hvalid3 hin3 hform3
  have hF3framed := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
      (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
      bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
      ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
      ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1)))
    (by pcFree) hF3
  refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => ?_) hF3framed
  · xperm_hyp hs
  · exact (sepConj_pure_right s).mpr ⟨(sepConj_pure_right s).mpr ⟨hq, hd2dec⟩, hd1facts⟩

/-! ## M3 proof — success-spine front: prologue ⨾ walk_init call (base+0 → base+28)

The first linear segment of the spine (no branching): the prologue (`wd_decode_prologue`,
base+0→24, saving ra/s0/s1/s2 and `s0 := a2`) composes with the `rlp_walk_init` call block
(`wd_call_walk_init` lifted to the program, base+24→28). The call's `walk_init` arguments
(`a0 = srcBase`, `a1 = srcLen`, scratch, the input region) are framed through the prologue; the
prologue's saved-register/stack-frame state is framed through the call. Exit at base+28 carries
`walk_init`'s 9-way classification post, ready for the guard (`bnez a2`) in `wd_decode_walkInitSetup`. -/

/-- **Prologue ⨾ walk_init call** (base+0 → base+28). -/
theorem wd_decode_prologueWalkInit
    (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 : Word)
    (srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8))
    (halign : (base + 28) &&& ~~~1 = base + 28)
    (hdisj : (CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : 0 < srcBytes.length)
    (hover : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (hll_len : ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        0 + 1 + ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ srcBytes.length)
    (hll_over : ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcBase.toNat + (0 + 1 + ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ∀ k, k < ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (0 + 1 + k)) = true) :
    cpsTripleWithin (6 + (1 + 81)) base (base + 28) (withdrawal_decode_code base)
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
          (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes))
      ((
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 28)) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         -- empty (a2 = 2)
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ (2 : Word)) ** ⌜srcLen = (0 : Word)⌝) h) ∨
         -- not-a-list (a2 = 1)
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (1 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
         -- short success (a2 = 0)
         (((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + signExtend12 (1 : BitVec 12))) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (0 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              (srcBase + BitVec.ofNat 64 0) +
                (((srcBytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
                = (srcBase + BitVec.ofNat 64 0) + srcLen⌝) h) ∨
         -- short mismatch (a2 = 3)
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (3 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              (srcBase + BitVec.ofNat 64 0) +
                (((srcBytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
                ≠ (srcBase + BitVec.ofNat 64 0) + srcLen⌝) h) ∨
         -- long header truncated (a2 = 4)
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (4 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              BitVec.ult ((srcBase + BitVec.ofNat 64 0) + srcLen)
                ((srcBase + BitVec.ofNat 64 0) +
                  (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true⌝) h) ∨
         -- long leading zero (a2 = 5): header fits, but the first length byte is 0
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (5 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((srcBase + BitVec.ofNat 64 0) + srcLen)
                ((srcBase + BitVec.ofNat 64 0) +
                  (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              srcBytes[0 + 1]? = some (0 : BitVec 8)⌝) h) ∨
         -- long non-minimal (a2 = 6): header fits, decoded length < 56
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (6 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((srcBase + BitVec.ofNat 64 0) + srcLen)
                ((srcBase + BitVec.ofNat 64 0) +
                  (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (0 + 1)).take
                ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true⌝) h) ∨
         -- long mismatch (a2 = 7): decoded ≥ 56 but cursor + decoded ≠ end
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (7 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((srcBase + BitVec.ofNat 64 0) + srcLen)
                ((srcBase + BitVec.ofNat 64 0) +
                  (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (0 + 1)).take
                ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
              ((srcBase + BitVec.ofNat 64 0) +
                  (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
                  BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (0 + 1)).take
                    ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                ≠ (srcBase + BitVec.ofNat 64 0) + srcLen⌝) h) ∨
         -- long success (a2 = 0): decoded ≥ 56 and cursor + decoded = end
         (((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) +
              (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
            (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (0 : Word)) **
            ⌜srcLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((srcBase + BitVec.ofNat 64 0) + srcLen)
                ((srcBase + BitVec.ofNat 64 0) +
                  (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (0 + 1)).take
                ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
              ((srcBase + BitVec.ofNat 64 0) +
                  (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
                  BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (0 + 1)).take
                    ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                = (srcBase + BitVec.ofNat 64 0) + srcLen⌝) h)))
       ) **
       ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x8 ↦ᵣ structPtr) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))) := by
  have hpro := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
      (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wd_decode_prologue base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3)
  have hoffset : (base + 24) + signExtend21 (308 : BitVec 21) = base + 332 := by
    rw [show signExtend21 (308 : BitVec 21) = (308 : Word) from by decide]; bv_omega
  have hcall := cpsTripleWithin_extend_code (wd_walkinit_code_sub base)
    (wd_call_walk_init (base + 24) (base + 332) srcBase srcLen structPtr t0Old t1Old t2Old t3Old
      t4Old t5Old t6Old raVal srcBytes 0 (308 : BitVec 21) hoffset
      (by rw [show base + 24 + 4 = base + 28 from by bv_omega]; exact halign) hdisj
      hsalign hoff hover hvalid hll_len hll_over hll_valid)
  rw [show base + 24 + 4 = base + 28 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x8 ↦ᵣ structPtr) ** (.x9 ↦ᵣ s1Old) **
      (.x18 ↦ᵣ s2Old) ** ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) (by pcFree) hcall
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro hcallF

/-- **Call block: `rlp_walk_init`, short-list-success arm.** Like `wd_call_walk_init` but uses the
    single-arm short-success leaf (`rlp_walk_init_short_spec_within`, 15 steps) under the short-list
    facts (`hlen`/`h_ge`/`h_hi`/`h_exact`), so the post is just the success result (cursor =
    listBase+listOff+1, end = listBase+listOff+listLen, status 0) — no 9-way disjunction. Isolating
    this keeps the front composition's elaboration light. -/
theorem wd_call_walk_init_short
    (callerPC calleeEntry listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old vOld : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_init_code calleeEntry))
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin (1 + 15) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_walk_init_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes))
      ((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (callerPC + 4)) ** bytesRegion listBase listBytes) := by
  have hcallee := rlp_walk_init_short_spec_within calleeEntry listBase (callerPC + 4) listLen a2Old
    t0Old t1Old t2Old t3Old t4Old listBytes listOff hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee)

/-! ## M3 proof — success-spine head: prologue ⨾ walk_init (short-success) ⨾ setup (base+0→40) -/

/-- **Success-spine head** (base+0 → base+40, short-list outer): saves `s1 := cursor = srcBase+1`,
    `s2 := end = srcBase + srcLen`. Composes prologue ⨾ `wd_call_walk_init_short` (lifted) ⨾
    `wd_decode_walkInitSetup`, on the canonical short-list path. -/
theorem wd_decode_walkInitSuccess
    (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 : Word)
    (srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8))
    (halign : (base + 28) &&& ~~~1 = base + 28)
    (hdisj : (CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332)))
    (hsalign : srcBase.toNat % 8 = 0) (hoff : 0 < srcBytes.length)
    (hover : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (hlen : srcLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (srcBase + BitVec.ofNat 64 0) +
        (((srcBytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (srcBase + BitVec.ofNat 64 0) + srcLen) :
    cpsTripleWithin ((6 + (1 + 15)) + 3) base (base + 40) (withdrawal_decode_code base)
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
          (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes))
      (((.x9 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + signExtend12 (1 : BitVec 12))) **
        (.x18 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝) **
        ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x8 ↦ᵣ structPtr) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x1 ↦ᵣ (base + 28)) ** bytesRegion srcBase srcBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))) := by
  have hpro := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
      (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wd_decode_prologue base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3)
  have hoffset : (base + 24) + signExtend21 (308 : BitVec 21) = base + 332 := by
    rw [show signExtend21 (308 : BitVec 21) = (308 : Word) from by decide]; bv_omega
  have hcall := cpsTripleWithin_extend_code (wd_walkinit_code_sub base)
    (wd_call_walk_init_short (base + 24) (base + 332) srcBase srcLen structPtr t0Old t1Old t2Old
      t3Old t4Old raVal srcBytes 0 (308 : BitVec 21) hoffset
      (by rw [show base + 24 + 4 = base + 28 from by bv_omega]; exact halign) hdisj
      hsalign hoff hover hvalid hlen h_ge h_hi h_exact)
  rw [show base + 24 + 4 = base + 28 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x8 ↦ᵣ structPtr) ** (.x9 ↦ᵣ s1Old) **
      (.x18 ↦ᵣ s2Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) (by pcFree) hcall
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro hcallF
  have hsetup := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x8 ↦ᵣ structPtr) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x1 ↦ᵣ (base + 28)) ** bytesRegion srcBase srcBytes **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) (by pcFree)
    (wd_decode_walkInitSetup base ((srcBase + BitVec.ofNat 64 0) + signExtend12 (1 : BitVec 12))
      ((srcBase + BitVec.ofNat 64 0) + srcLen) s1Old s2Old)
  refine cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hAB hsetup)

theorem wd_decode_field0Body_unified_regOwn5
    (base srcBase endPtr vOld a0Old a1Old a2Old t5Old t6Old struct mOld : Word)
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
    (hform :
      (BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes srcOff ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true ∧
        srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 + ((srcBytes[srcOff]'hoff).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[srcOff]'hoff).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) ∧
        0 < (srcBytes[srcOff]'hoff).toNat - 0x80 ∧
        getByteAt srcBytes (srcOff + 1) ≠ 0 ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[srcOff]'hoff).toNat - 0x80 = 0)) :
    cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)) (base + 40) (base + 96) (withdrawal_decode_code base)
      ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
      (fun h => ∃ d0 nextOff,
        wd_scalarFieldUnifiedPost (base + 88) struct (0 : BitVec 12) srcBase endPtr
          srcBytes srcOff d0 nextOff h) := by
  have hfull := fun (t0Old t1Old t2Old t3Old t4Old : Word) =>
    wd_decode_field0Body_unified_fixedN base srcBase endPtr vOld a0Old a1Old a2Old
      t0Old t1Old t2Old t3Old t4Old t5Old t6Old struct mOld srcBytes srcOff
      halign52 hdisjW halign88 hdisjC hsalign hoff hover hvalid hin hform
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
      (r := .x5) (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
      (r := .x6) (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x28 ** regOwn .x29 ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x29 ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
      (r := .x28) (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ vOld) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ struct) ** ((struct + signExtend12 (0 : BitVec 12)) ↦ₘ mOld) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
      (r := .x29) (fun v29 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hfull v5 v6 v7 v28 v29)

/-! ## M3 proof — success spine: HEAD ⨾ field0 (base+0 → base+96) -/

/-- **Head ⨾ field 0** (base+0 → base+96): extends the assembled head by field 0's body. Field 0
    sits at the fixed offset 1 (first content byte after the 1-byte short-list prefix), so this link
    is form-dependency-free: `hform0` is field 0's form disjunction at offset 1. Uses the 5-scratch
    regOwn dispatcher (`…_regOwn5`) so the head's concrete `x30`/`x31` (untouched by walk_init-short)
    match without a weakening; the output `struct+0` cell is framed through the head, the head's
    saved-frame leftovers through field 0. -/
theorem wd_decode_headField0
    (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 : Word)
    (srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8))
    (halign28 : (base + 28) &&& ~~~1 = base + 28)
    (hdisjWI : (CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332)))
    (hsalign : srcBase.toNat % 8 = 0) (hsrcLen0 : 0 < srcBytes.length)
    (hover0 : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (hlen : srcLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (srcBase + BitVec.ofNat 64 0) +
        (((srcBytes[0]'hsrcLen0).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (srcBase + BitVec.ofNat 64 0) + srcLen)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW48 : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC84 : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hoff1 : 1 < srcBytes.length) (hover1 : srcBase.toNat + 1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 1) = true)
    (hin1 : BitVec.ult (srcBase + BitVec.ofNat 64 1) ((srcBase + BitVec.ofNat 64 0) + srcLen) = true)
    (hform0 :
      (BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes 1 ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[1 + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word))
          (((srcBase + BitVec.ofNat 64 0) + srcLen) - (srcBase + BitVec.ofNat 64 1)) = true ∧
        1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[1]'hoff1).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (1 + 1 + k)) = true) ∧
        0 < (srcBytes[1]'hoff1).toNat - 0x80 ∧
        getByteAt srcBytes (1 + 1) ≠ 0 ∧
        (srcBytes[1]'hoff1).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[1]'hoff1).toNat - 0x80 = 0)) :
    cpsTripleWithin ((((6 + (1 + 15)) + 3)) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))) base (base + 96)
      (withdrawal_decode_code base)
      ((((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
          (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)) ** ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ mOld0))
      ((fun h => ∃ d0 nextOff, wd_scalarFieldUnifiedPost (base + 88) structPtr (0 : BitVec 12)
          srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes 1 d0 nextOff h) **
        (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
      ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))) := by
  have hcur : (srcBase + BitVec.ofNat 64 0) + signExtend12 (1 : BitVec 12) =
      srcBase + BitVec.ofNat 64 1 := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]; bv_omega
  have hHEAD := cpsTripleWithin_frameR ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ mOld0)
    (by pcFree)
    (wd_decode_walkInitSuccess base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3
      srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes
      halign28 hdisjWI hsalign hsrcLen0 hover0 hvalid0 hlen h_ge h_hi h_exact)
  have hfield0 := cpsTripleWithin_frameR (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
      ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) (by pcFree)
    (wd_decode_field0Body_unified_regOwn5 base srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen)
      (base + 28) (srcBase + BitVec.ofNat 64 1) ((srcBase + BitVec.ofNat 64 0) + srcLen) (0 : Word)
      t5Old t6Old structPtr mOld0 srcBytes 1 halign52 hdisjW48 halign88 hdisjC84 hsalign hoff1
      hover1 hvalid1 hin1 hform0)
  exact cpsTripleWithin_seq_perm_same_cr (fun s hp => by rw [hcur] at hp; xperm_hyp hp)
    hHEAD hfield0

/-! ## M3 proof — success spine: field0 ⨾ field1 -/

/-- **Head ⨾ field 0 ⨾ field 1** (base+0 → base+152): extends `wd_decode_headField0` by field 1's
    body. This is the **form-dependency crux**: field 1 sits at field 0's *existential* next-offset
    `nextOff0`, so its preconditions (`wd_scalarFieldPre` at `nextOff0`) cannot be derived from field
    0's output alone — they are taken as the dependent hypothesis `hf1` (which the capstone will
    discharge from `decodeWithdrawal = some`, where the input structure pins each field's form).
    The proof threads the existential `(d0, nextOff0)` through field 1 via
    `cpsTripleWithin_exists_pre`, extracts field 0's `d0`-facts from the unified post's pure with
    `cpsTripleWithin_pure_pre`, frames field 0's written `struct+0` cell through field 1, and carries
    the head's saved-frame leftovers around the whole field-1 segment. -/
theorem wd_decode_headField01
    (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 mOld1 : Word)
    (srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8))
    (halign28 : (base + 28) &&& ~~~1 = base + 28)
    (hdisjWI : (CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332)))
    (hsalign : srcBase.toNat % 8 = 0) (hsrcLen0 : 0 < srcBytes.length)
    (hover0 : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (hlen : srcLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (srcBase + BitVec.ofNat 64 0) +
        (((srcBytes[0]'hsrcLen0).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (srcBase + BitVec.ofNat 64 0) + srcLen)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW48 : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC84 : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hoff1 : 1 < srcBytes.length) (hover1 : srcBase.toNat + 1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 1) = true)
    (hin1 : BitVec.ult (srcBase + BitVec.ofNat 64 1) ((srcBase + BitVec.ofNat 64 0) + srcLen) = true)
    (hform0 :
      (BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes 1 ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[1 + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word))
          (((srcBase + BitVec.ofNat 64 0) + srcLen) - (srcBase + BitVec.ofNat 64 1)) = true ∧
        1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[1]'hoff1).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (1 + 1 + k)) = true) ∧
        0 < (srcBytes[1]'hoff1).toNat - 0x80 ∧
        getByteAt srcBytes (1 + 1) ≠ 0 ∧
        (srcBytes[1]'hoff1).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[1]'hoff1).toNat - 0x80 = 0))
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisjW104 : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisjC140 : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hf1 : ∀ (d0 : List Byte) (nextOff0 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0) :
    cpsTripleWithin (((((6 + (1 + 15)) + 3)) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)))
      base (base + 152) (withdrawal_decode_code base)
      (((((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
          (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)) **
        ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ mOld0)) **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1))
      ((fun h => ∃ d0 nextOff0,
          (((fun h' => ∃ d1 nextOff1,
              wd_scalarFieldUnifiedPost (base + 144) structPtr (8 : BitVec 12) srcBase
                ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0 d1 nextOff1 h') **
            ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ
              BitVec.ofNat 64 (Nat.fromBytesBE d0))) **
            ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
              (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
                some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) h) **
        (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
          ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))) := by
  -- Field 0's output post (the existential-`(d0,nextOff0)` unified post), abbreviated.
  have hHF0 := cpsTripleWithin_frameR ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1)
    (by pcFree)
    (wd_decode_headField0 base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0
      srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes
      halign28 hdisjWI hsalign hsrcLen0 hover0 hvalid0 hlen h_ge h_hi h_exact
      halign52 hdisjW48 halign88 hdisjC84 hoff1 hover1 hvalid1 hin1 hform0)
  -- Per-witness field-1 body: from field 0's unified post (+ the framed struct+8 cell), run field 1.
  have hbody : ∀ (d0 : List Byte) (nextOff0 : Nat),
      cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))
        (base + 96) (base + 152) (withdrawal_decode_code base)
        (wd_scalarFieldUnifiedPost (base + 88) structPtr (0 : BitVec 12) srcBase
            ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes 1 d0 nextOff0 **
          ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1))
        ((((fun h' => ∃ d1 nextOff1,
              wd_scalarFieldUnifiedPost (base + 144) structPtr (8 : BitVec 12) srcBase
                ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0 d1 nextOff1 h') **
            ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ
              BitVec.ofNat 64 (Nat.fromBytesBE d0))) **
            ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
              (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
                some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝)) := by
    intro d0 nextOff0
    refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => hq)
      (cpsTripleWithin_pure_pre
        (P := ((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 nextOff0)) **
          (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE d0)) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x12 ↦ᵣ BitVec.ofNat 64 d0.length) ** (.x8 ↦ᵣ structPtr) ** (.x1 ↦ᵣ (base + 88)) **
          (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          bytesRegion srcBase srcBytes **
          ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
          (.x18 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31) ** ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1))
        (fun (hfacts : d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) => ?_))
    · -- reshape: `USP0 ** struct8cell` ⟶ `(USP0_spatial ** struct8cell) ** ⌜facts⌝`
      simp only [wd_scalarFieldUnifiedPost] at hs
      xperm_hyp hs
    · -- with field-0 facts in hand, apply `hf1` and run field 1, framing struct+0 forward.
      obtain ⟨hoff', hover', hvalid', hin', hform'⟩ := hf1 d0 nextOff0 hfacts
      have hF1base := wd_decode_field1Body_unified_regOwn base srcBase
        ((srcBase + BitVec.ofNat 64 0) + srcLen) (base + 88)
        (BitVec.ofNat 64 (Nat.fromBytesBE d0)) (0 : Word) (BitVec.ofNat 64 d0.length)
        structPtr mOld1 srcBytes nextOff0
        halign108 hdisjW104 halign144 hdisjC140 hsalign hoff' hover' hvalid' hin' hform'
      have hF1framed := cpsTripleWithin_frameR
        ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0))
        (by pcFree) hF1base
      refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => ?_) hF1framed
      · xperm_hyp hs
      · exact (sepConj_pure_right s).mpr ⟨hq, hfacts⟩
  -- Thread the existential `(d0, nextOff0)` through field 1, then frame the head leftovers.
  have hF1core := cpsTripleWithin_exists_pre (fun d0 =>
    cpsTripleWithin_exists_pre (fun nextOff0 => hbody d0 nextOff0))
  have hF1 := cpsTripleWithin_frameR
    (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
      ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) (by pcFree) hF1core
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hHF0 hF1
  -- Seam: field 0's post has the `struct+8` cell *outside* the existential; `hF1core` consumes it
  -- *inside* — pull it in via `sepConj_exists_left` (twice, for the nested `(d0, nextOff0)`).
  have hp2 : (((fun s => ∃ d0 nextOff,
      wd_scalarFieldUnifiedPost (base + 88) structPtr (0 : BitVec 12) srcBase
        ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes 1 d0 nextOff s) **
      ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1)) **
      (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))) s := by
    xperm_hyp hp
  obtain ⟨hac, hhl, hdisj, hunion, hAC, hHL⟩ := hp2
  obtain ⟨d0, hAC1⟩ := sepConj_exists_left hAC
  obtain ⟨nextOff0, hAC2⟩ := sepConj_exists_left hAC1
  exact ⟨hac, hhl, hdisj, hunion, ⟨d0, nextOff0, hAC2⟩, hHL⟩

/-! ## M3 proof — success spine: head ⨾ field0 ⨾ field1 ⨾ field2 (base+0 → base+220) -/

/-- **Head ⨾ field0 ⨾ field1 ⨾ field2** (base+0 → base+220): extends `wd_decode_headField01` by
    field 2's body via the seam consumer `wd_field2_consume`. Three of the four fields are now
    verified-assembled. Field 2 sits at field 1's *existential* next-offset `nextOff0`'s field-1
    output `nextOff1`, so its address-field preconditions are taken via the doubly-dependent
    hypothesis `hf2` (discharged by the capstone from `decodeWithdrawal = some`). The proof frames
    the field-2 inputs (`x13/x14/x15`, `struct+16` region) onto `headField01`, threads the
    `(d0,nextOff0)` layer with `cpsTripleWithin_exists_pre`, extracts field 0's `d0`-facts to build
    field 2's `hf2′`, frames field 0's written `struct+0` cell and the head leftovers around field
    2, and exposes the carried `d0`-facts in the post. -/
theorem wd_decode_headField012
    (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 mOld1 : Word)
    (srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8))
    (x13Old x14Old cnt : Word) (dstBytes : List (BitVec 8))
    (halign28 : (base + 28) &&& ~~~1 = base + 28)
    (hdisjWI : (CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332)))
    (hsalign : srcBase.toNat % 8 = 0) (hsrcLen0 : 0 < srcBytes.length)
    (hover0 : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (hlen : srcLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (srcBase + BitVec.ofNat 64 0) +
        (((srcBytes[0]'hsrcLen0).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (srcBase + BitVec.ofNat 64 0) + srcLen)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW48 : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC84 : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hoff1 : 1 < srcBytes.length) (hover1 : srcBase.toNat + 1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 1) = true)
    (hin1 : BitVec.ult (srcBase + BitVec.ofNat 64 1) ((srcBase + BitVec.ofNat 64 0) + srcLen) = true)
    (hform0 :
      (BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes 1 ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[1 + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word))
          (((srcBase + BitVec.ofNat 64 0) + srcLen) - (srcBase + BitVec.ofNat 64 1)) = true ∧
        1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[1]'hoff1).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (1 + 1 + k)) = true) ∧
        0 < (srcBytes[1]'hoff1).toNat - 0x80 ∧
        getByteAt srcBytes (1 + 1) ≠ 0 ∧
        (srcBytes[1]'hoff1).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[1]'hoff1).toNat - 0x80 = 0))
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisjW104 : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisjC140 : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hf1 : ∀ (d0 : List Byte) (nextOff0 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0)
    (halign164 : (base + 164) &&& ~~~1 = base + 164)
    (hdisjW160 : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign204 : (base + 204) &&& ~~~1 = base + 204)
    (hstalign : structPtr.toNat % 8 = 0) (hbase : base.toNat + 1444 < 2 ^ 64)
    (hdlen : dstBytes.length = 20) (hdov : (structPtr + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length →
      isValidByteAccess ((structPtr + 16) + BitVec.ofNat 64 i) = true)
    (hsover' : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hf2 : ∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      wd_addressFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff1) :
    cpsTripleWithin (((((((6 + (1 + 15)) + 3)) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)))) +
        ((2 + (1 + 87) + 1) + (3 + 111)))
      base (base + 220) (withdrawal_decode_code base)
      ((((((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
          (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)) **
        ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ mOld0)) **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1)) **
        ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion (structPtr + 16) dstBytes))
      (fun h => ∃ d0 nextOff0,
        (((fun h'' => ∃ d1 nextOff1,
            wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
              d1 nextOff1 h'') **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
          ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) h) := by
  have hHF01ext := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) ** bytesRegion (structPtr + 16) dstBytes)
    (by pcFree)
    (wd_decode_headField01 base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 mOld1
      srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes
      halign28 hdisjWI hsalign hsrcLen0 hover0 hvalid0 hlen h_ge h_hi h_exact
      halign52 hdisjW48 halign88 hdisjC84 hoff1 hover1 hvalid1 hin1 hform0
      halign108 hdisjW104 halign144 hdisjC140 hf1)
  -- field-2 segment over field0's `(d0,nextOff0)` layer, distributed form.
  have hseg : cpsTripleWithin ((2 + (1 + 87) + 1) + (3 + 111)) (base + 152) (base + 220)
      (withdrawal_decode_code base)
      (fun s => ∃ d0 nextOff0,
        ((((fun h' => ∃ d1 nextOff1,
              wd_scalarFieldUnifiedPost (base + 144) structPtr (8 : BitVec 12) srcBase
                ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0 d1 nextOff1 h') **
            ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0))) **
            ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
              (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
                some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) **
          ((⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
            ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
              bytesRegion (structPtr + 16) dstBytes))) s)
      (fun h => ∃ d0 nextOff0,
        (((fun h'' => ∃ d1 nextOff1,
            wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
              d1 nextOff1 h'') **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
          ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) h) := by
    refine cpsTripleWithin_exists_pre (fun d0 => ?_)
    refine cpsTripleWithin_exists_pre (fun nextOff0 => ?_)
    refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => hq)
      (cpsTripleWithin_pure_pre
        (P := (((fun h' => ∃ d1 nextOff1,
              wd_scalarFieldUnifiedPost (base + 144) structPtr (8 : BitVec 12) srcBase
                ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0 d1 nextOff1 h') **
            ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0))) **
          ((⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
            ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
              bytesRegion (structPtr + 16) dstBytes))))
        (fun (hd0facts : d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) => ?_))
    · xperm_hyp hs
    · have hcons := wd_field2_consume base srcBase srcLen structPtr x13Old x14Old cnt nextOff0
        dstBytes halign164 hdisjW160 halign204 hsalign hstalign hbase hdlen hdov hdval srcBytes
        hsover' hsvalid (fun d1 nextOff1 hd1f => hf2 d0 nextOff0 d1 nextOff1 hd0facts hd1f)
      have hconsF := cpsTripleWithin_frameR
        (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
          (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
            ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))) (by pcFree) hcons
      refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => ?_) hconsF
      · have hs' : (((fun s => ∃ d1 nextOff1,
              wd_scalarFieldUnifiedPost (base + 144) structPtr (8 : BitVec 12) srcBase
                ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0 d1 nextOff1 s) **
            ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
              bytesRegion (structPtr + 16) dstBytes)) **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) s := by
          xperm_hyp hs
        obtain ⟨h1, h2, hd, hu, hAX, hrest⟩ := hs'
        obtain ⟨d1, hAX1⟩ := sepConj_exists_left hAX
        obtain ⟨nextOff1, hAX2⟩ := sepConj_exists_left hAX1
        exact ⟨h1, h2, hd, hu, ⟨d1, nextOff1, hAX2⟩, hrest⟩
      · exact (sepConj_pure_right s).mpr ⟨hq, hd0facts⟩
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hHF01ext hseg
  have hp' : ((fun s => ∃ d0 nextOff0,
        (((fun h' => ∃ d1 nextOff1,
            wd_scalarFieldUnifiedPost (base + 144) structPtr (8 : BitVec 12) srcBase
              ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0 d1 nextOff1 h') **
          ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0))) **
          ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) s) **
      ((⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
          ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
        ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion (structPtr + 16) dstBytes))) s := by
    xperm_hyp hp
  obtain ⟨h1, h2, hd, hu, hQ, hHLX2⟩ := hp'
  obtain ⟨d0, nextOff0, hQc⟩ := hQ
  exact ⟨d0, nextOff0, h1, h2, hd, hu, hQc, hHLX2⟩

/-! ## M3 proof — success spine: head ⨾ field0 ⨾ field1 ⨾ field2 ⨾ field3 (base+0 → base+276) -/

/-- **Head ⨾ field0 ⨾ field1 ⨾ field2 ⨾ field3** (base+0 → base+276): extends
    `wd_decode_headField012` by field 3's body via `wd_field3_consume`. This completes the verified
    success **field chain** (all four fields); composed with the already-proven success-spine tail
    (`wd_decode_aritySuccessTail`, base+276→ret) it covers the entire success path. Field 3's scalar
    preconditions are taken via the triply-dependent `hf3` (on field 0/1's `d`-facts and field 2's
    `decodeAux` step), which the capstone discharges from `decodeWithdrawal = some`. Mirrors
    `headField012`: frames `struct+40` onto `headField012`, threads field 0's `(d0,nextOff0)` layer
    with `cpsTripleWithin_exists_pre`, extracts `d0`-facts to build field 3's `hf3′`, frames field 0's
    `struct+0` cell and the head leftovers around field 3. -/
theorem wd_decode_headField0123
    (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 mOld1 mOld3 : Word)
    (srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8))
    (x13Old x14Old cnt : Word) (dstBytes : List (BitVec 8))
    (halign28 : (base + 28) &&& ~~~1 = base + 28)
    (hdisjWI : (CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332)))
    (hsalign : srcBase.toNat % 8 = 0) (hsrcLen0 : 0 < srcBytes.length)
    (hover0 : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (hlen : srcLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (srcBase + BitVec.ofNat 64 0) +
        (((srcBytes[0]'hsrcLen0).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (srcBase + BitVec.ofNat 64 0) + srcLen)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW48 : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC84 : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hoff1 : 1 < srcBytes.length) (hover1 : srcBase.toNat + 1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 1) = true)
    (hin1 : BitVec.ult (srcBase + BitVec.ofNat 64 1) ((srcBase + BitVec.ofNat 64 0) + srcLen) = true)
    (hform0 :
      (BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes 1 ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[1 + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word))
          (((srcBase + BitVec.ofNat 64 0) + srcLen) - (srcBase + BitVec.ofNat 64 1)) = true ∧
        1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[1]'hoff1).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (1 + 1 + k)) = true) ∧
        0 < (srcBytes[1]'hoff1).toNat - 0x80 ∧
        getByteAt srcBytes (1 + 1) ≠ 0 ∧
        (srcBytes[1]'hoff1).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[1]'hoff1).toNat - 0x80 = 0))
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisjW104 : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisjC140 : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hf1 : ∀ (d0 : List Byte) (nextOff0 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0)
    (halign164 : (base + 164) &&& ~~~1 = base + 164)
    (hdisjW160 : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign204 : (base + 204) &&& ~~~1 = base + 204)
    (hstalign : structPtr.toNat % 8 = 0) (hbase : base.toNat + 1444 < 2 ^ 64)
    (hdlen : dstBytes.length = 20) (hdov : (structPtr + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length →
      isValidByteAccess ((structPtr + 16) + BitVec.ofNat 64 i) = true)
    (hsover' : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hf2 : ∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      wd_addressFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff1)
    (halign232 : (base + 232) &&& ~~~1 = base + 232)
    (hdisjW228 : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisjC264 : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hf3 : ∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21)) :
    cpsTripleWithin ((((((((6 + (1 + 15)) + 3)) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)))) +
        ((2 + (1 + 87) + 1) + (3 + 111))) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)))
      base (base + 276) (withdrawal_decode_code base)
      (((((((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
          (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)) **
        ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ mOld0)) **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1)) **
        ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion (structPtr + 16) dstBytes)) **
        ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3))
      (fun h => ∃ d0 nextOff0,
        (((fun h'' => ∃ d1 nextOff1,
            wd_field3ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
              d1 nextOff1 h'') **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
          ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) h) := by
  have hHF012ext := cpsTripleWithin_frameR
    ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3) (by pcFree)
    (wd_decode_headField012 base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 mOld1
      srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes x13Old x14Old cnt dstBytes
      halign28 hdisjWI hsalign hsrcLen0 hover0 hvalid0 hlen h_ge h_hi h_exact
      halign52 hdisjW48 halign88 hdisjC84 hoff1 hover1 hvalid1 hin1 hform0
      halign108 hdisjW104 halign144 hdisjC140 hf1 halign164 hdisjW160 halign204 hstalign hbase
      hdlen hdov hdval hsover' hsvalid hf2)
  -- field-3 segment over field0's `(d0,nextOff0)` layer, distributed form.
  have hseg : cpsTripleWithin ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))
      (base + 220) (base + 276) (withdrawal_decode_code base)
      (fun s => ∃ d0 nextOff0,
        ((((fun h'' => ∃ d1 nextOff1,
              wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
                d1 nextOff1 h'') **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
            ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
              (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
                some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) **
          ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3)) s)
      (fun h => ∃ d0 nextOff0,
        (((fun h'' => ∃ d1 nextOff1,
            wd_field3ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
              d1 nextOff1 h'') **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
          ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) h) := by
    refine cpsTripleWithin_exists_pre (fun d0 => ?_)
    refine cpsTripleWithin_exists_pre (fun nextOff0 => ?_)
    refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => hq)
      (cpsTripleWithin_pure_pre
        (P := (((fun h'' => ∃ d1 nextOff1,
              wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
                d1 nextOff1 h'') **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
          ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3)))
        (fun (hd0facts : d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) => ?_))
    · xperm_hyp hs
    · have hcons := wd_field3_consume base srcBase srcLen structPtr mOld3 nextOff0 srcBytes dstBytes
        halign232 hdisjW228 halign268 hdisjC264 hsalign
        (fun d1 nextOff1 hd1f hd2 => hf3 d0 nextOff0 d1 nextOff1 hd0facts hd1f hd2)
      have hconsF := cpsTripleWithin_frameR
        (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
          (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
            ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))) (by pcFree) hcons
      refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => ?_) hconsF
      · have hs' : (((fun s => ∃ d1 nextOff1,
              wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
                d1 nextOff1 s) ** ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3)) **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) s := by
          xperm_hyp hs
        obtain ⟨h1, h2, hd, hu, hAX, hrest⟩ := hs'
        obtain ⟨d1, hAX1⟩ := sepConj_exists_left hAX
        obtain ⟨nextOff1, hAX2⟩ := sepConj_exists_left hAX1
        exact ⟨h1, h2, hd, hu, ⟨d1, nextOff1, hAX2⟩, hrest⟩
      · exact (sepConj_pure_right s).mpr ⟨hq, hd0facts⟩
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => ?_) hHF012ext hseg
  have hp' : ((fun s => ∃ d0 nextOff0,
        (((fun h'' => ∃ d1 nextOff1,
            wd_field2ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
              d1 nextOff1 h'') **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
          ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) s) **
      ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3)) s := by
    xperm_hyp hp
  obtain ⟨h1, h2, hd, hu, hQ, hC40⟩ := hp'
  obtain ⟨d0, nextOff0, hQc⟩ := hQ
  exact ⟨d0, nextOff0, h1, h2, hd, hu, hQc, hC40⟩

/-! ## M3 proof — arity seam (success leaf): `headField0123 ⨾ arity-success tail`

The success field chain (`wd_decode_headField0123`, base+0→276) leaves field 3's content in the
unified post `wd_scalarFieldUnifiedPost` (struct off 40), with the head frame (`x2` + the
`sp0-32` stack cells) and the field 0/1 output cells / address bytes framed alongside, all under
six nested existentials (`d0,nextOff0,d1,nextOff1,d3,nextOff3`). The arity-success tail
(`wd_decode_aritySuccessTail_regOwn6`, base+276→ret) runs the final `walk_next` end-of-list
check and the success return. This seam composes them.

It is built bottom-up: the innermost `_d3layer` consumer runs the tail against field 3's unified
post + the head frame (one `frameR` + `xperm` reshape); the outer wrappers peel the `d1` and
`d0` existential layers (framing each layer's leftover cells); the top theorem `seq`s the chain
onto `headField0123` and threads `h_end` (cursor = list end) as a dependent hypothesis the
capstone discharges from the 4-item span. -/

/-- **Arity-success tail, field-3 layer consumer.** Runs the arity check + success return on
    field 3's unified post (`wd_scalarFieldUnifiedPost` at struct off 40) together with the saved
    head frame `HL` (`x2` + the four `sp0-32` stack cells). The tail consumes field 3's
    `x9/x10/x11/x12/x8/x1/x0` + `regOwn x6` and the head frame; field 3's leftover scratch regs,
    the `srcBase` byte region, the field-3 output cell, and the `⌜d3 facts⌝` pure are framed
    through. `h_end` (cursor = list end) is taken directly; the capstone derives it from the
    4-item span. -/
theorem wd_decode_aritySuccessTail_d3layer
    (base sp0 raVal s0Old s1Old s2Old structPtr srcBase srcLen : Word)
    (srcBytes : List (BitVec 8)) (off3 : Nat)
    (d3 : List Byte) (nextOff3 : Nat)
    (h_end : ¬ BitVec.ult (srcBase + BitVec.ofNat 64 nextOff3)
      ((srcBase + BitVec.ofNat 64 0) + srcLen))
    (halign288 : (base + 288) &&& ~~~1 = base + 288)
    (hdisj : (CodeReq.singleton (base + 284) (.JAL .x1 (260 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hinstr : withdrawal_decode_prog.get
        ⟨73, by rw [withdrawal_decode_prog_length]; norm_num⟩ = .BNE .x11 .x6 (12 : BitVec 13)) :
    cpsTripleWithin ((2 + ((1 + 4) + 1)) + (1 + 8)) (base + 276) (raVal &&& ~~~1)
      (withdrawal_decode_code base)
      (wd_scalarFieldUnifiedPost (base + 268) structPtr (40 : BitVec 12) srcBase
          ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes off3 d3 nextOff3 **
        ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
          ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))
      (((((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** ⌜(2 : Word) = (2 : Word)⌝) **
          ((.x10 ↦ᵣ (0 : Word)) **
            (.x2 ↦ᵣ ((sp0 + signExtend12 (-32 : BitVec 12)) + signExtend12 (32 : BitVec 12))) **
            (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
        (regOwn .x5 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion srcBase srcBytes **
          ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d3)) **
          ⌜d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop off3) =
              some (.bytes d3, srcBytes.drop nextOff3)) ∧ nextOff3 ≤ srcBytes.length⌝))) := by
  have htail := wd_decode_aritySuccessTail_regOwn6 base (srcBase + BitVec.ofNat 64 nextOff3)
    ((srcBase + BitVec.ofNat 64 0) + srcLen) (BitVec.ofNat 64 (Nat.fromBytesBE d3)) (0 : Word)
    (base + 268) (BitVec.ofNat 64 d3.length) (sp0 + signExtend12 (-32 : BitVec 12)) structPtr
    raVal s0Old s1Old s2Old h_end halign288 hdisj hinstr
  have htailF := cpsTripleWithin_frameR
    (regOwn .x5 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion srcBase srcBytes **
      ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d3)) **
      ⌜d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop off3) =
          some (.bytes d3, srcBytes.drop nextOff3)) ∧ nextOff3 ≤ srcBytes.length⌝)
    (by pcFree) htail
  refine cpsTripleWithin_weaken (fun s hs => ?_) (fun s hq => ?_) htailF
  · simp only [wd_scalarFieldUnifiedPost] at hs
    xperm_hyp hs
  · xperm_hyp hq

/-- **Success-leaf post** (base+0 → ret success): what the whole success path produces. The arity
    tail's success return (`a0 = x10 = 0`, callee-saved restored, stack popped) plus the framed
    output cells — field 0/1/3 scalars at struct off 0/8/40, the 20-byte address copy at struct+16
    — and the four `decodeAux` facts (`d0/d1/d2/d3`) the capstone feeds to
    `wd_decodeWithdrawal_some_of_srcFacts` to conclude `decodeWithdrawal = some w` and that the
    output region holds `w`. -/
def wd_successLeafPost (sp0 raVal s0Old s1Old s2Old structPtr srcBase : Word)
    (srcBytes dstBytes : List (BitVec 8)) : Assertion :=
  fun h => ∃ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat)
      (d3 : List Byte) (nextOff3 : Nat),
    ((((((((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (((.x11 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** ⌜(2 : Word) = (2 : Word)⌝) **
          ((.x10 ↦ᵣ (0 : Word)) **
            (.x2 ↦ᵣ ((sp0 + signExtend12 (-32 : BitVec 12)) + signExtend12 (32 : BitVec 12))) **
            (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
        (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
          ⌜(0 : Word) = (0 : Word)⌝ **
          ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1)) **
          ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d3)) **
          (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
          (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
          bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
          ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
          regOwn .x5 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion srcBase srcBytes)) **
        ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
          (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
            some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) **
        ⌜d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
          (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
            some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length⌝) **
        ⌜∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
          some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))⌝) **
        ⌜d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
          (∀ m, decodeAux (m + 1) (srcBytes.drop (nextOff1 + 21)) =
            some (.bytes d3, srcBytes.drop nextOff3)) ∧ nextOff3 ≤ srcBytes.length⌝) h

/-- **Arity-tail consumer** (base+276 → ret): consumes the success field chain's post
    (`wd_decode_headField0123`'s output) and runs the arity-success tail, producing
    `wd_successLeafPost`. Peels the six nested existentials (`d0,nextOff0,d1,nextOff1,d3,nextOff3`),
    extracts the four `decodeAux` facts to discharge `h_end` (taken as a dependent hypothesis the
    capstone proves from the 4-item span), frames the output cells / address bytes / leftover regs
    through the tail, and re-attaches the four facts in the post. -/
theorem wd_decode_arityTail_consume
    (base sp0 raVal s0Old s1Old s2Old structPtr srcBase srcLen : Word)
    (srcBytes dstBytes : List (BitVec 8))
    (halign288 : (base + 288) &&& ~~~1 = base + 288)
    (hdisj284 : (CodeReq.singleton (base + 284) (.JAL .x1 (260 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hinstr : withdrawal_decode_prog.get
        ⟨73, by rw [withdrawal_decode_prog_length]; norm_num⟩ = .BNE .x11 .x6 (12 : BitVec 13))
    (h_end : ∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat)
        (d3 : List Byte) (nextOff3 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) →
      (d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop (nextOff1 + 21)) =
          some (.bytes d3, srcBytes.drop nextOff3)) ∧ nextOff3 ≤ srcBytes.length) →
      ¬ BitVec.ult (srcBase + BitVec.ofNat 64 nextOff3)
        ((srcBase + BitVec.ofNat 64 0) + srcLen)) :
    cpsTripleWithin ((2 + ((1 + 4) + 1)) + (1 + 8)) (base + 276) (raVal &&& ~~~1)
      (withdrawal_decode_code base)
      (fun h => ∃ d0 nextOff0,
        (((fun h'' => ∃ d1 nextOff1,
            wd_field3ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0
              d1 nextOff1 h'') **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) **
          ⌜d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
              some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length⌝) h)
      (wd_successLeafPost sp0 raVal s0Old s1Old s2Old structPtr srcBase srcBytes dstBytes) := by
  unfold wd_successLeafPost
  refine cpsTripleWithin_exists_pre (fun d0 => ?_)
  refine cpsTripleWithin_exists_pre (fun nextOff0 => ?_)
  refine cpsTripleWithin_pure_pre (fun hd0facts => ?_)
  refine cpsTripleWithin_weaken
    (fun s hs => ((by
      obtain ⟨d1, h1⟩ := sepConj_exists_left hs
      obtain ⟨nextOff1, h2⟩ := sepConj_exists_left h1
      exact ⟨d1, nextOff1, h2⟩) :
      ∃ d1 nextOff1,
        (wd_field3ConsumePost base srcBase srcLen structPtr srcBytes dstBytes nextOff0 d1 nextOff1 **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))) s))
    (fun s hq => hq) ?_
  refine cpsTripleWithin_exists_pre (fun d1 => ?_)
  refine cpsTripleWithin_exists_pre (fun nextOff1 => ?_)
  unfold wd_field3ConsumePost
  refine cpsTripleWithin_weaken (fun s hs => by xperm_hyp hs) (fun s hq => hq)
    (cpsTripleWithin_pure_pre
      (P := ((((fun h => ∃ d3 nextOff3,
              wd_scalarFieldUnifiedPost (base + 268) structPtr (40 : BitVec 12) srcBase
                ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21) d3 nextOff3 h) **
            ((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
              (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
              bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
              ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
              ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1)))) **
            ⌜∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
              some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))⌝) **
          (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
            (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
              ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
              ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))))
      (fun (hd1facts : d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
          (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
            some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) => ?_))
  refine cpsTripleWithin_weaken (fun s hs => by xperm_hyp hs) (fun s hq => hq)
    (cpsTripleWithin_pure_pre
      (P := (((fun h => ∃ d3 nextOff3,
              wd_scalarFieldUnifiedPost (base + 268) structPtr (40 : BitVec 12) srcBase
                ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21) d3 nextOff3 h) **
            ((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
              (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
              bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
              ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
              ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1)))) **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)))))
      (fun (hd2dec : ∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
          some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) =>
        ?_))
  refine cpsTripleWithin_weaken
    (fun s hs => ((by
      have hs' : ((fun h => ∃ d3 nextOff3,
          wd_scalarFieldUnifiedPost (base + 268) structPtr (40 : BitVec 12) srcBase
            ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21) d3 nextOff3 h) **
          (((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
              (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
              bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
              ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
              ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1))) **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))))) s := by xperm_hyp hs
      obtain ⟨d3, h1⟩ := sepConj_exists_left hs'
      obtain ⟨nextOff3, h2⟩ := sepConj_exists_left h1
      exact ⟨d3, nextOff3, h2⟩) :
      ∃ d3 nextOff3,
        (wd_scalarFieldUnifiedPost (base + 268) structPtr (40 : BitVec 12) srcBase
            ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21) d3 nextOff3 **
          (((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
              (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
              bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
              ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
              ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1))) **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))))) s))
    (fun s hq => hq) ?_
  refine cpsTripleWithin_exists_pre (fun d3 => ?_)
  refine cpsTripleWithin_exists_pre (fun nextOff3 => ?_)
  unfold wd_scalarFieldUnifiedPost
  refine cpsTripleWithin_weaken (fun s hs => by xperm_hyp hs) (fun s hq => hq)
    (cpsTripleWithin_pure_pre
      (P := (((.x9 ↦ᵣ (srcBase + BitVec.ofNat 64 nextOff3)) **
            (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE d3)) ** (.x11 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ BitVec.ofNat 64 d3.length) ** (.x8 ↦ᵣ structPtr) ** (.x1 ↦ᵣ (base + 268)) **
            (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            bytesRegion srcBase srcBytes **
            ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d3)) **
            (.x18 ↦ᵣ ((srcBase + BitVec.ofNat 64 0) + srcLen)) ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31) **
          (((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
              (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
              bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
              ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
              ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1))) **
            (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
              (⌜(0 : Word) = (0 : Word)⌝ ** (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
                ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
                ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old))))))
      (fun (hd3facts : d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
          (∀ m, decodeAux (m + 1) (srcBytes.drop (nextOff1 + 21)) =
            some (.bytes d3, srcBytes.drop nextOff3)) ∧ nextOff3 ≤ srcBytes.length) => ?_))
  have hend' := h_end d0 nextOff0 d1 nextOff1 d3 nextOff3 hd0facts hd1facts hd2dec hd3facts
  have htail := wd_decode_aritySuccessTail_regOwn6 base (srcBase + BitVec.ofNat 64 nextOff3)
    ((srcBase + BitVec.ofNat 64 0) + srcLen) (BitVec.ofNat 64 (Nat.fromBytesBE d3)) (0 : Word)
    (base + 268) (BitVec.ofNat 64 d3.length) (sp0 + signExtend12 (-32 : BitVec 12)) structPtr
    raVal s0Old s1Old s2Old hend' halign288 hdisj284 hinstr
  have htailF := cpsTripleWithin_frameR
    (((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d0)) **
      ⌜(0 : Word) = (0 : Word)⌝ **
      ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d1)) **
      ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE d3)) **
      (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 ((nextOff1 + 1) + 20))) **
      (.x14 ↦ᵣ ((structPtr + 16) + BitVec.ofNat 64 (0 + 20))) ** regOwn .x15 **
      bytesRegion (structPtr + 16) (copyRangeGen dstBytes srcBytes (nextOff1 + 1) 0 20) **
      ⌜BitVec.ult ((srcBytes[nextOff1]?.getD 0).zeroExtend 64) (192 : Word)⌝ **
      regOwn .x5 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion srcBase srcBytes)
    (by pcFree) htail
  refine cpsTripleWithin_weaken (fun s hs => by xperm_hyp hs) (fun s hq => ?_) htailF
  exact (sepConj_pure_right s).mpr ⟨(sepConj_pure_right s).mpr ⟨(sepConj_pure_right s).mpr
    ⟨(sepConj_pure_right s).mpr ⟨hq, hd0facts⟩, hd1facts⟩, hd2dec⟩, hd3facts⟩

/-- **Success leaf** (base+0 → ret): the entire success path. Sequences the success field chain
    (`wd_decode_headField0123`, base+0 → 276) with the arity-tail consumer
    (`wd_decode_arityTail_consume`, base+276 → ret). The consumer's pre is exactly the field
    chain's post, so the seam permutation is the identity. The result is the full drop-in
    success triple: from the entry state (input region, owned output region, callee-saved + ra),
    on a valid 4-field withdrawal it runs to the success return (`a0 = 0`) with the output region
    holding the decoded fields and the four `decodeAux` facts exposed. `h_end` (the final
    `walk_next` reports end-of-list, i.e. the 4 items span the payload) is taken as a dependent
    hypothesis the capstone discharges from `decodeWithdrawal = some`. -/
theorem wd_decode_successLeaf
    (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 mOld1 mOld3 : Word)
    (srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8))
    (x13Old x14Old cnt : Word) (dstBytes : List (BitVec 8))
    (halign28 : (base + 28) &&& ~~~1 = base + 28)
    (hdisjWI : (CodeReq.singleton (base + 24) (.JAL .x1 (308 : BitVec 21))).Disjoint
      (rlp_walk_init_code (base + 332)))
    (hsalign : srcBase.toNat % 8 = 0) (hsrcLen0 : 0 < srcBytes.length)
    (hover0 : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (hlen : srcLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (srcBase + BitVec.ofNat 64 0) +
        (((srcBytes[0]'hsrcLen0).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (srcBase + BitVec.ofNat 64 0) + srcLen)
    (halign52 : (base + 52) &&& ~~~1 = base + 52)
    (hdisjW48 : (CodeReq.singleton (base + 48) (.JAL .x1 (496 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign88 : (base + 88) &&& ~~~1 = base + 88)
    (hdisjC84 : (CodeReq.singleton (base + 84) (.JAL .x1 (872 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hoff1 : 1 < srcBytes.length) (hover1 : srcBase.toNat + 1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 1) = true)
    (hin1 : BitVec.ult (srcBase + BitVec.ofNat 64 1) ((srcBase + BitVec.ofNat 64 0) + srcLen) = true)
    (hform0 :
      (BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        getByteAt srcBytes 1 ≠ 0) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, srcBytes[1 + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64 - (0x80 : Word))
          (((srcBase + BitVec.ofNat 64 0) + srcLen) - (srcBase + BitVec.ofNat 64 1)) = true ∧
        1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80) ≤ srcBytes.length ∧
        srcBase.toNat + (1 + 1 + ((srcBytes[1]'hoff1).toNat - 0x80)) ≤ 2 ^ 64 ∧
        (∀ k, k < (srcBytes[1]'hoff1).toNat - 0x80 →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (1 + 1 + k)) = true) ∧
        0 < (srcBytes[1]'hoff1).toNat - 0x80 ∧
        getByteAt srcBytes (1 + 1) ≠ 0 ∧
        (srcBytes[1]'hoff1).toNat - 0x80 ≤ 8) ∨
      (¬ BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult ((srcBytes[1]'hoff1).zeroExtend 64) (0xb8 : Word) = true ∧
        (srcBytes[1]'hoff1).toNat - 0x80 = 0))
    (halign108 : (base + 108) &&& ~~~1 = base + 108)
    (hdisjW104 : (CodeReq.singleton (base + 104) (.JAL .x1 (440 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign144 : (base + 144) &&& ~~~1 = base + 144)
    (hdisjC140 : (CodeReq.singleton (base + 140) (.JAL .x1 (816 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hf1 : ∀ (d0 : List Byte) (nextOff0 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff0)
    (halign164 : (base + 164) &&& ~~~1 = base + 164)
    (hdisjW160 : (CodeReq.singleton (base + 160) (.JAL .x1 (384 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign204 : (base + 204) &&& ~~~1 = base + 204)
    (hstalign : structPtr.toNat % 8 = 0) (hbase : base.toNat + 1444 < 2 ^ 64)
    (hdlen : dstBytes.length = 20) (hdov : (structPtr + 16).toNat + 20 < 2 ^ 64)
    (hdval : ∀ i, i < dstBytes.length →
      isValidByteAccess ((structPtr + 16) + BitVec.ofNat 64 i) = true)
    (hsover' : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hf2 : ∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      wd_addressFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes nextOff1)
    (halign232 : (base + 232) &&& ~~~1 = base + 232)
    (hdisjW228 : (CodeReq.singleton (base + 228) (.JAL .x1 (316 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (halign268 : (base + 268) &&& ~~~1 = base + 268)
    (hdisjC264 : (CodeReq.singleton (base + 264) (.JAL .x1 (692 : BitVec 21))).Disjoint
      (rlp_content_to_u64_code (base + 956)))
    (hf3 : ∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) =
          some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) →
      wd_scalarFieldPre srcBase ((srcBase + BitVec.ofNat 64 0) + srcLen) srcBytes (nextOff1 + 21))
    (halign288 : (base + 288) &&& ~~~1 = base + 288)
    (hdisj284 : (CodeReq.singleton (base + 284) (.JAL .x1 (260 : BitVec 21))).Disjoint
      (rlp_walk_next_code (base + 544)))
    (hinstr : withdrawal_decode_prog.get
        ⟨73, by rw [withdrawal_decode_prog_length]; norm_num⟩ = .BNE .x11 .x6 (12 : BitVec 13))
    (h_end : ∀ (d0 : List Byte) (nextOff0 : Nat) (d1 : List Byte) (nextOff1 : Nat)
        (d3 : List Byte) (nextOff3 : Nat),
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop nextOff0)) ∧ nextOff0 ≤ srcBytes.length) →
      (d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) =
          some (.bytes d1, srcBytes.drop nextOff1)) ∧ nextOff1 ≤ srcBytes.length) →
      (∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
        some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21))) →
      (d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 ∧
        (∀ m, decodeAux (m + 1) (srcBytes.drop (nextOff1 + 21)) =
          some (.bytes d3, srcBytes.drop nextOff3)) ∧ nextOff3 ≤ srcBytes.length) →
      ¬ BitVec.ult (srcBase + BitVec.ofNat 64 nextOff3)
        ((srcBase + BitVec.ofNat 64 0) + srcLen)) :
    cpsTripleWithin (((((((((6 + (1 + 15)) + 3)) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2)))) +
        ((2 + (1 + 87) + 1) + (3 + 111))) +
        ((2 + (1 + 87) + 1) + (7 + (1 + (7 * 8 + 11)) + 2))) +
        ((2 + ((1 + 4) + 1)) + (1 + 8)))
      base (raVal &&& ~~~1) (withdrawal_decode_code base)
      (((((((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ srcLen) ** (.x5 ↦ᵣ t0Old) **
          (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)) **
        ((structPtr + signExtend12 (0 : BitVec 12)) ↦ₘ mOld0)) **
        ((structPtr + signExtend12 (8 : BitVec 12)) ↦ₘ mOld1)) **
        ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
          bytesRegion (structPtr + 16) dstBytes)) **
        ((structPtr + signExtend12 (40 : BitVec 12)) ↦ₘ mOld3))
      (wd_successLeafPost sp0 raVal s0Old s1Old s2Old structPtr srcBase srcBytes dstBytes) := by
  exact cpsTripleWithin_seq_perm_same_cr (fun s hp => hp)
    (wd_decode_headField0123 base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 mOld0 mOld1
      mOld3 srcBase srcLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes x13Old x14Old cnt
      dstBytes halign28 hdisjWI hsalign hsrcLen0 hover0 hvalid0 hlen h_ge h_hi h_exact
      halign52 hdisjW48 halign88 hdisjC84 hoff1 hover1 hvalid1 hin1 hform0
      halign108 hdisjW104 halign144 hdisjC140 hf1 halign164 hdisjW160 halign204 hstalign hbase
      hdlen hdov hdval hsover' hsvalid hf2 halign232 hdisjW228 halign268 hdisjC264 hf3)
    (wd_decode_arityTail_consume base sp0 raVal s0Old s1Old s2Old structPtr srcBase srcLen
      srcBytes dstBytes halign288 hdisj284 hinstr h_end)

/-! ## M3 proof — output carving: the address copy holds field 2's content -/

/-- **`getElem?` of a byte-copy chain.** Position `j` of `copyRangeGen dst src si0 di0 N` is the
    copied source byte when `j ∈ [di0, di0+N)` (and in range), else the untouched `dst[j]?`. -/
theorem wd_copyRangeGen_getElem? (src : List (BitVec 8)) :
    ∀ (dst : List (BitVec 8)) (si0 di0 N j : Nat),
      (copyRangeGen dst src si0 di0 N)[j]? =
        if di0 ≤ j ∧ j < di0 + N ∧ j < dst.length then some (getByteAt src (si0 + (j - di0)))
        else dst[j]? := by
  intro dst si0 di0 N
  induction N generalizing dst si0 di0 with
  | zero => intro j; simp only [copyRangeGen, Nat.add_zero]; rw [if_neg (by omega)]
  | succ n ih =>
    intro j
    rw [copyRangeGen, ih, List.getElem?_set, List.length_set]
    split_ifs <;>
      first
        | rfl
        | omega
        | rw [List.getElem?_eq_none (by omega)]
        | (congr 2; omega)

/-- **Byte-copy chain = take/drop of source.** With the destination holding exactly `N` slots and the
    source range in bounds, copying `N` bytes from `src[si0..]` into all of `dst` (`di0 = 0`) yields
    exactly `(src.drop si0).take N`. The carving fact for the address field: the 20-byte output region
    holds field 2's content `d2 = (drop (off+1)).take 20`. -/
theorem wd_copyRangeGen_eq_take_drop (src dst : List (BitVec 8)) (si0 N : Nat)
    (hdst : dst.length = N) (hsrc : si0 + N ≤ src.length) :
    copyRangeGen dst src si0 0 N = (src.drop si0).take N := by
  apply List.ext_getElem?
  intro j
  rw [wd_copyRangeGen_getElem?, hdst, List.getElem?_take]
  simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and, and_self]
  by_cases hj : j < N
  · rw [if_pos hj, if_pos hj, getByteAt, dif_pos (show si0 + j < src.length by omega),
      List.getElem?_drop, List.getElem?_eq_getElem (show si0 + j < src.length by omega)]
  · rw [if_neg hj, if_neg hj, List.getElem?_eq_none (by omega)]

/-- **Output-region carve.** The pre-zeroed 48-byte output struct splits into the field-0/1 scalar
    dwords (`@0`, `@8`), the 20-byte address sub-region (`@16`, rounding to dwords `@16/@24/@32`),
    and the field-3 scalar dword (`@40`) — exactly the shape `wd_decode_successLeaf`'s pre wants
    (with `dstBytes := replicate 20 0`). Used by the capstone to convert its
    `bytesRegion outPtr (replicate 48 0)` precondition into the success-leaf input. -/
theorem wd_outRegion_carve (outPtr : Word) :
    bytesRegion outPtr (List.replicate 48 (0 : BitVec 8))
      = ((outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
         bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) **
         ((outPtr + 40) ↦ₘ (0 : Word))) := by
  have hpk8 : packBytes [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] = (0 : Word) := by decide
  have hpk4 : packBytes [0#8, 0#8, 0#8, 0#8] = (0 : Word) := by decide
  have hL : bytesRegion outPtr (List.replicate 48 (0 : BitVec 8))
      = ((outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
         ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word)) **
         ((outPtr + 32) ↦ₘ (0 : Word)) ** ((outPtr + 40) ↦ₘ (0 : Word))) := by
    rw [bytesRegion_eq_cons outPtr _ (by decide),
        bytesRegion_eq_cons (outPtr + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8 + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8 + 8 + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8 + 8 + 8 + 8) _ (by decide),
        show (outPtr + 8 + 8 + 8 + 8 + 8 : Word) = outPtr + 40 from by bv_omega,
        show (outPtr + 8 + 8 + 8 + 8 : Word) = outPtr + 32 from by bv_omega,
        show (outPtr + 8 + 8 + 8 : Word) = outPtr + 24 from by bv_omega,
        show (outPtr + 8 + 8 : Word) = outPtr + 16 from by bv_omega]
    simp [hpk8, sepConj_emp_right']
  have hR : bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8))
      = (((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word)) **
         ((outPtr + 32) ↦ₘ (0 : Word))) := by
    rw [bytesRegion_eq_cons (outPtr + 16) _ (by decide),
        bytesRegion_eq_cons (outPtr + 16 + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 16 + 8 + 8) _ (by decide),
        show (outPtr + 16 + 8 + 8 : Word) = outPtr + 32 from by bv_omega,
        show (outPtr + 16 + 8 : Word) = outPtr + 24 from by bv_omega]
    simp [hpk8, hpk4, sepConj_emp_right']
  rw [hL, hR]
  simp only [sepConj_assoc']

/-- **Success-leaf field identities.** From `decodeWithdrawal srcBytes = some w` and the four
    `decodeAux` facts the success-leaf post carries (for runtime bytes `d0/d1/d3` and address copy),
    pin (by `decodeAux` determinism against `w`'s encode structure) the stored scalar values to
    `w`'s fields, the address copy to `w`'s 20-byte address, and the cursor end to `|srcBytes|`. The
    semantic bridge from the success-leaf post's existential bytes to `wd_outHolds outPtr w …`. -/
theorem wd_successLeaf_field_ids
    (srcBytes : List Byte) (w : Withdrawal) (d0 d1 d3 : List Byte) (nextOff0 nextOff1 nextOff3 : Nat)
    (hdec : decodeWithdrawal srcBytes = some w)
    (hd0f : ∀ m, decodeAux (m + 1) (srcBytes.drop 1) = some (.bytes d0, srcBytes.drop nextOff0))
    (hd1f : ∀ m, decodeAux (m + 1) (srcBytes.drop nextOff0) = some (.bytes d1, srcBytes.drop nextOff1))
    (hd2dec : ∀ m, decodeAux (m + 1) (srcBytes.drop nextOff1) =
      some (.bytes ((srcBytes.drop (nextOff1 + 1)).take 20), srcBytes.drop (nextOff1 + 21)))
    (hd3f : ∀ m, decodeAux (m + 1) (srcBytes.drop (nextOff1 + 21)) =
      some (.bytes d3, srcBytes.drop nextOff3)) :
    Nat.fromBytesBE d0 = w.index ∧ Nat.fromBytesBE d1 = w.validatorIndex ∧
    Nat.fromBytesBE d3 = w.amount ∧
    w.address = BitVec.ofNat 160 (Nat.fromBytesBE ((srcBytes.drop (nextOff1 + 1)).take 20)) ∧
    ((srcBytes.drop (nextOff1 + 1)).take 20).length = 20 ∧
    nextOff1 + 21 ≤ srcBytes.length := by
  obtain ⟨D0, D1, D2, D3, hsrc, hc0, hl0, hc1, hl1, h20, hc3, hl3, hidx, hvi, haddr, hamt⟩ :=
    wd_srcBytes_eq_encode srcBytes w hdec
  obtain ⟨hsrc2, _⟩ := wd_encode4_payload srcBytes D0 D1 D2 D3 hsrc hl0 hl1 h20 hl3
  have hdrop1 : srcBytes.drop 1 =
      encodeBytes D0 ++ (encodeBytes D1 ++ (encodeBytes D2 ++ encodeBytes D3)) := by rw [hsrc2]; rfl
  have big0 : D0.length < 256 ^ 8 := lt_of_le_of_lt hl0 (by norm_num)
  have big1 : D1.length < 256 ^ 8 := lt_of_le_of_lt hl1 (by norm_num)
  have big2 : D2.length < 256 ^ 8 := by rw [h20]; norm_num
  have big3 : D3.length < 256 ^ 8 := lt_of_le_of_lt hl3 (by norm_num)
  obtain ⟨hd0eq, hr1⟩ := wd_drop_pin srcBytes 1 nextOff0 d0 D0 _ hd0f hdrop1 big0
  obtain ⟨hd1eq, hr2⟩ := wd_drop_pin srcBytes nextOff0 nextOff1 d1 D1 _ hd1f hr1 big1
  obtain ⟨hd2eq, hr3⟩ :=
    wd_drop_pin srcBytes nextOff1 (nextOff1 + 21) _ D2 (encodeBytes D3) hd2dec hr2 big2
  obtain ⟨hd3eq, _⟩ := wd_drop_pin srcBytes (nextOff1 + 21) nextOff3 d3 D3 []
    hd3f (by rw [hr3, List.append_nil]) big3
  have hencD2 : (encodeBytes D2).length = 21 := by
    rw [encodeBytes_short_of_length_ne_one D2 (by omega) (by omega)]; simp [h20]
  have hbound : nextOff1 + 21 ≤ srcBytes.length := by
    have hl := congrArg List.length hr2
    rw [List.length_drop, List.length_append, hencD2] at hl
    omega
  refine ⟨by rw [hd0eq, hidx], by rw [hd1eq, hvi], by rw [hd3eq, hamt], ?_, ?_, hbound⟩
  · rw [hd2eq, haddr]
  · rw [hd2eq, h20]

/-- **Success-leaf post → capstone success disjunct (spatial reshape).** Given
    `decodeWithdrawal srcBytes = some w`, the success-leaf post (run with the pre-zeroed 20-byte
    address region) maps to the capstone's shared frame conjoined with the *success* branch of
    the post disjunction. The reshape: pin the stored scalar/address values to `w`'s fields via
    `wd_successLeaf_field_ids`, fold the address byte-copy via `wd_copyRangeGen_eq_take_drop`,
    weaken the clobbered concrete registers/cells to ownership tokens, drop the inert pures, and
    permute into the shared-frame / `wd_outHolds` shape. -/
theorem wd_successLeafPost_to_success
    (sp0 raVal s0Old s1Old s2Old outPtr srcBase : Word)
    (srcBytes : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal srcBytes = some w) :
    ∀ h, wd_successLeafPost sp0 raVal s0Old s1Old s2Old outPtr srcBase srcBytes
        (List.replicate 20 (0 : BitVec 8)) h →
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w' d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w' d2 **
            ⌜decodeWithdrawal srcBytes = some w' ∧
              w'.address = BitVec.ofNat 160 (Nat.fromBytesBE d2) ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) h := by
  have pdrop : ∀ (P : Prop) (h : PartialState), (⌜P⌝ : Assertion) h → empAssertion h :=
    fun _ _ hq => hq.1
  intro h hp
  unfold wd_successLeafPost at hp
  obtain ⟨d0, nextOff0, d1, nextOff1, d3, nextOff3, hp⟩ := hp
  obtain ⟨hp, hd3f⟩ := (sepConj_pure_right h).mp hp
  obtain ⟨hp, hd2dec⟩ := (sepConj_pure_right h).mp hp
  obtain ⟨hp, hd1f⟩ := (sepConj_pure_right h).mp hp
  obtain ⟨hp, hd0f⟩ := (sepConj_pure_right h).mp hp
  obtain ⟨hi0, hi1, hi3, haddr2, hd2len, hbound⟩ :=
    wd_successLeaf_field_ids srcBytes w d0 d1 d3 nextOff0 nextOff1 nextOff3 hdec
      hd0f.2.2.1 hd1f.2.2.1 hd2dec hd3f.2.2.1
  have hcopy : copyRangeGen (List.replicate 20 (0 : BitVec 8)) srcBytes (nextOff1 + 1) 0 20
      = (srcBytes.drop (nextOff1 + 1)).take 20 :=
    wd_copyRangeGen_eq_take_drop srcBytes (List.replicate 20 (0 : BitVec 8)) (nextOff1 + 1) 20
      (by simp) (by omega)
  rw [hi0, hi1, hi3, hcopy,
      show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at hp
  rw [show ((sp0 + (-32 : Word)) + 32) = sp0 from by bv_omega,
      show ((sp0 + (-32 : Word)) + 8) = sp0 - 24 from by bv_omega,
      show ((sp0 + (-32 : Word)) + 16) = sp0 - 16 from by bv_omega,
      show ((sp0 + (-32 : Word)) + 24) = sp0 - 8 from by bv_omega,
      show (sp0 + (-32 : Word)) = sp0 - 32 from by bv_omega,
      show (outPtr + (0 : Word)) = outPtr from by bv_omega] at hp
  have hpw := sepConj_mono
    (sepConj_mono (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x)) (sepConj_mono (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x6) (pdrop _))) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))))))))))
    (sepConj_mono (fun _ x => x) (sepConj_mono (pdrop _) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x13) (sepConj_mono (regIs_implies_regOwn .x14) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (pdrop _) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (fun _ x => x))))))))))))))))
    h hp
  simp only [sepConj_emp_left', sepConj_emp_right'] at hpw
  have hfacts : decodeWithdrawal srcBytes = some w ∧
      w.address = BitVec.ofNat 160 (Nat.fromBytesBE ((srcBytes.drop (nextOff1 + 1)).take 20)) ∧
      ((srcBytes.drop (nextOff1 + 1)).take 20).length = 20 := ⟨hdec, haddr2, hd2len⟩
  have hp3 := (sepConj_pure_right h).mpr ⟨hpw, hfacts⟩
  refine sepConj_mono_right
    (fun s hs => Or.inl ⟨w, (srcBytes.drop (nextOff1 + 1)).take 20, hs⟩) h ?_
  unfold wd_scratchOwned wd_frameOwned wd_outHolds
  xperm_hyp hp3

/-- **Capstone-PRE peel.** Converts the capstone precondition (callee-owned scratch/frame
    tokens + a pre-zeroed 48-byte output struct) into the success-leaf precondition family: peel
    the seven scratch registers, `a3`/`a4`/`a5`, and the four stack-frame cells to universally
    quantified concrete values, and carve the output `bytesRegion` into its dword/address cells
    (via `wd_outRegion_carve`). Given the success-leaf triple for *every* concretization, the
    triple holds over the capstone precondition. -/
theorem wd_capstonePre_peel {N : Nat} {Q : Assertion}
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte)
    (hleaf : ∀ (m0 m1 m2 m3 t0Old t1Old t2Old t3Old t4Old t5Old t6Old x13Old x14Old cnt : Word),
      cpsTripleWithin N base (raVal &&& ~~~1) (withdrawal_decode_code base)
        (((((((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
          (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ outPtr) **
          ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3)) **
          ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) **
            (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
            (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes)) **
          ((outPtr + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word))) **
          ((outPtr + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word))) **
          ((.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ cnt) **
            bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)))) **
          ((outPtr + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)))
        Q) :
    cpsTripleWithin N base (raVal &&& ~~~1) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))
      Q := by
  refine cpsTripleWithin_weaken (fun h hp => by unfold wd_scratchOwned wd_frameOwned at hp; rw [wd_outRegion_carve] at hp; xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x5) (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x6) (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x28) (fun v28 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x29) (fun v29 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x30) (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x31) (fun v31 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x14 ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x13) (fun v13 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** regOwn .x15 ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x14) (fun v14 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** memOwn (sp0 - 32) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (r := .x15) (fun v15 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (a := sp0 - 32) (fun vm0 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** ((sp0 - 32) ↦ₘ vm0) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (a := sp0 - 24) (fun vm1 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** ((sp0 - 32) ↦ₘ vm0) ** ((sp0 - 24) ↦ₘ vm1) ** memOwn (sp0 - 8))
      (a := sp0 - 16) (fun vm2 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) ** bytesRegion (outPtr + 16) (List.replicate 20 (0 : BitVec 8)) ** ((outPtr + 40) ↦ₘ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** ((sp0 - 32) ↦ₘ vm0) ** ((sp0 - 24) ↦ₘ vm1) ** ((sp0 - 16) ↦ₘ vm2))
      (a := sp0 - 8) (fun vm3 => ?_))
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [show srcBase + BitVec.ofNat 64 0 = srcBase from by bv_omega,
          show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
          show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
          show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
          show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
          show (sp0 + (-32 : Word)) + 8 = sp0 - 24 from by bv_omega,
          show (sp0 + (-32 : Word)) + 16 = sp0 - 16 from by bv_omega,
          show (sp0 + (-32 : Word)) + 24 = sp0 - 8 from by bv_omega,
          show sp0 + (-32 : Word) = sp0 - 32 from by bv_omega,
          show outPtr + (0 : Word) = outPtr from by bv_omega]
      xperm_hyp hp)
    (fun _ hq => hq)
    (hleaf vm0 vm1 vm2 vm3 v5 v6 v7 v28 v29 v30 v31 v13 v14 v15)

/-- **Capstone success case.** When `decodeWithdrawal srcBytes = some w`, the program runs the
    success path: discharge every hypothesis of `wd_decode_successLeaf` from the well-formedness
    side-conditions and the reverse-decode bridge (`wd_walkInit_facts`,
    `wd_scalarFieldPre_of_encodeBytes`, `wd_decode_success_field_hyps`, the align/disjoint
    bundles), peel the capstone precondition into the success-leaf family (`wd_capstonePre_peel`),
    and map the success-leaf post onto the capstone's success disjunct
    (`wd_successLeafPost_to_success`). -/
theorem wd_decode_successCase
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte) (w : Withdrawal)
    (hbe : base &&& 1 = 0) (hbase : base.toNat + 1444 < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0) (hostalign : outPtr.toNat % 8 = 0)
    (hsrclt : srcBytes.length < 2 ^ 64) (hnowrap : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hout48 : outPtr.toNat + 48 < 2 ^ 64)
    (hsvalid : ∀ k, k < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 48 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hdec : decodeWithdrawal srcBytes = some w) :
    cpsTripleWithin 2048 base (raVal &&& ~~~1) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : Byte)))
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
            ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
              ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) := by
  obtain ⟨D0, D1, D2, D3, hsrc, hc0, hl0, hc1, hl1, h20, hc3, hl3, hidx, hvi, haddr, hamt⟩ :=
    wd_srcBytes_eq_encode srcBytes w hdec
  obtain ⟨hsrc2, hP48⟩ := wd_encode4_payload srcBytes D0 D1 D2 D3 hsrc hl0 hl1 h20 hl3
  have hsrcLen0 : 0 < srcBytes.length := by rw [hsrc2]; simp
  have hdrop1 : srcBytes.drop 1 =
      encodeBytes D0 ++ (encodeBytes D1 ++ (encodeBytes D2 ++ encodeBytes D3)) := by
    rw [hsrc2]; rfl
  obtain ⟨h_ge, h_hi, h_exact⟩ :=
    wd_walkInit_facts srcBase (BitVec.ofNat 64 srcBytes.length) srcBytes
      (encodeBytes D0 ++ (encodeBytes D1 ++ (encodeBytes D2 ++ encodeBytes D3)))
      hsrcLen0 hsrc2 hP48 rfl
  obtain ⟨hoff1, hover1, hvalid1, hin1, hform0⟩ :=
    wd_scalarFieldPre_of_encodeBytes srcBase (BitVec.ofNat 64 srcBytes.length) srcBytes 1 D0
      (encodeBytes D1 ++ (encodeBytes D2 ++ encodeBytes D3)) hsvalid hnowrap rfl hdrop1 hc0 hl0
  obtain ⟨hf1, hf2, hf3, h_end⟩ :=
    wd_decode_success_field_hyps srcBase (BitVec.ofNat 64 srcBytes.length) srcBytes w
      hsvalid hnowrap rfl hdec
  obtain ⟨halign28, halign52, halign88, halign108, halign144, halign164, halign204, halign232,
    halign268, halign288⟩ := wd_decode_align_facts base hbe
  obtain ⟨hdisjWI, hdisjW48, hdisjC84, hdisjW104, hdisjC140, hdisjW160, hdisjW228, hdisjC264,
    hdisj284⟩ := wd_decode_disjoint_facts base hbase
  have hover0 : srcBase.toNat + 0 < 2 ^ 64 := by have := srcBase.isLt; omega
  have hlen : BitVec.ofNat 64 srcBytes.length ≠ (0 : Word) := by
    have ht : (BitVec.ofNat 64 srcBytes.length).toNat = srcBytes.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hsrclt
    intro hc; rw [hc] at ht; simp at ht; omega
  have hdlen : (List.replicate 20 (0 : BitVec 8)).length = 20 := by simp
  have hdov : (outPtr + 16).toNat + 20 < 2 ^ 64 := by bv_omega
  have hofadd : ∀ (a b : Nat),
      BitVec.ofNat 64 (a + b) = BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
    intro a b; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
  have hdval : ∀ i, i < (List.replicate 20 (0 : BitVec 8)).length →
      isValidByteAccess ((outPtr + 16) + BitVec.ofNat 64 i) = true := by
    intro i hi; rw [List.length_replicate] at hi
    have hv := houtvalid (16 + i) (by omega)
    rwa [hofadd 16 i, ← BitVec.add_assoc] at hv
  have hinstr : withdrawal_decode_prog.get
      ⟨73, by rw [withdrawal_decode_prog_length]; norm_num⟩ = .BNE .x11 .x6 (12 : BitVec 13) := by
    decide
  exact cpsTripleWithin_mono_nSteps (by norm_num)
    (cpsTripleWithin_weaken (fun _ hp => hp)
    (wd_successLeafPost_to_success sp0 raVal s0Old s1Old s2Old outPtr srcBase srcBytes w hdec)
    (wd_capstonePre_peel base srcBase outPtr raVal sp0 s0Old s1Old s2Old srcBytes
      (fun m0 m1 m2 m3 t0Old t1Old t2Old t3Old t4Old t5Old t6Old x13Old x14Old cnt =>
        wd_decode_successLeaf base sp0 raVal s0Old s1Old s2Old outPtr m0 m1 m2 m3 0 0 0
          srcBase (BitVec.ofNat 64 srcBytes.length) t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          srcBytes x13Old x14Old cnt (List.replicate 20 (0 : BitVec 8))
          halign28 hdisjWI hsalign hsrcLen0 hover0 (hsvalid 0 hsrcLen0) hlen h_ge h_hi h_exact
          halign52 hdisjW48 halign88 hdisjC84 hoff1 hover1 hvalid1 hin1 hform0
          halign108 hdisjW104 halign144 hdisjC140 hf1 halign164 hdisjW160 halign204
          hostalign hbase hdlen hdov hdval hnowrap hsvalid hf2 halign232 hdisjW228 halign268
          hdisjC264 hf3 halign288 hdisj284 hinstr h_end)))

/-- **Fail endpoint** (base+304 → ret): once any guard has rejected and control reached the
    `failReturn` block with the saved stack frame intact (and the clobbered scratch / output region
    surrendered as ownership tokens), the program restores the callee-saved registers, pops the
    frame, sets `a0 = 1`, and returns — landing in the capstone's *failure* disjunct. The
    `⌜decodeWithdrawal srcBytes = none⌝` is supplied directly (the capstone's `none` case). -/
theorem wd_decode_failEndpoint
    (base sp0 raVal s0Old s1Old s2Old outPtr srcBase : Word) (srcBytes : List Byte)
    (raClob s0Clob s1Clob s2Clob a0Old : Word)
    (hdec : decodeWithdrawal srcBytes = none) :
    cpsTripleWithin 7 (base + 304) (raVal &&& ~~~1) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ a0Old) **
        ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
          (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) **
          ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
          ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 ** wd_scratchOwned **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** bytesRegion srcBase srcBytes **
          wd_outOwned outPtr))
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
            ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
              ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) := by
  have hfr := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 ** wd_scratchOwned **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** bytesRegion srcBase srcBytes **
      wd_outOwned outPtr) (by unfold wd_scratchOwned wd_outOwned; pcFree)
    (wd_decode_failReturn base (sp0 + signExtend12 (-32 : BitVec 12)) raVal s0Old s1Old s2Old
      raClob s0Clob s1Clob s2Clob a0Old)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hfr
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
      show (sp0 + (-32 : Word)) + 32 = sp0 from by bv_omega,
      show (sp0 + (-32 : Word)) + 8 = sp0 - 24 from by bv_omega,
      show (sp0 + (-32 : Word)) + 16 = sp0 - 16 from by bv_omega,
      show (sp0 + (-32 : Word)) + 24 = sp0 - 8 from by bv_omega,
      show sp0 + (-32 : Word) = sp0 - 32 from by bv_omega] at hp
  have hp2 := sepConj_mono
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))))))))
    (fun _ x => x) h hp
  refine sepConj_mono_right (fun s hs => Or.inr hs) h ?_
  unfold wd_frameOwned
  have hp3 := (sepConj_pure_right h).mpr ⟨hp2, hdec⟩
  xperm_hyp hp3

/-- **Status-guard reject (a2 status, e.g. walk_init).** A `bnez statusReg, fail` whose status
    register is `a2` (`.x12`) and whose offset resolves to the `failReturn` block (`base+304`),
    taken on a nonzero status `v`: one branch step to `base+304`, then the fail endpoint. The
    reusable reject arm for the `walk_init` status guard (idx 7). -/
theorem wd_decode_failViaBnez12
    (base sp0 raVal s0Old s1Old s2Old outPtr srcBase : Word) (srcBytes : List Byte)
    (raClob s0Clob s1Clob s2Clob a0Old v : Word) (idx : Nat) (failOff : BitVec 13)
    (hv : v ≠ (0 : Word))
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE .x12 .x0 failOff)
    (hfail : (base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff = base + 304)
    (hdec : decodeWithdrawal srcBytes = none) :
    cpsTripleWithin (1 + 7) (base + BitVec.ofNat 64 (4 * idx)) (raVal &&& ~~~1)
      (withdrawal_decode_code base)
      (((.x12 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ a0Old) **
          ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
            (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) **
            ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
          regOwn .x11 ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          bytesRegion srcBase srcBytes ** wd_outOwned outPtr))
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
            ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
              ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) := by
  have hbnez := wd_bnez_taken base idx .x12 failOff v hv hidx hinstr
  rw [hfail] at hbnez
  have hbf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0Old) **
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
        (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
      regOwn .x11 ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
      bytesRegion srcBase srcBytes ** wd_outOwned outPtr)
    (by unfold wd_scratchOwned wd_outOwned; pcFree) hbnez
  exact cpsTripleWithin_seq_perm_same_cr
    (fun s hp => by
      have hp2 := sepConj_mono_left
        (sepConj_mono (regIs_implies_regOwn .x12)
          (fun s' h' => ((sepConj_pure_right s').1 h').1)) s hp
      xperm_hyp hp2)
    hbf
    (wd_decode_failEndpoint base sp0 raVal s0Old s1Old s2Old outPtr srcBase srcBytes
      raClob s0Clob s1Clob s2Clob a0Old hdec)

/-- **Status-guard reject (a1 status, e.g. walk_next / content_to_u64).** A `bnez statusReg, fail` whose status
    register is `a1` (`.x11`) and whose offset resolves to the `failReturn` block (`base+304`),
    taken on a nonzero status `v`: one branch step to `base+304`, then the fail endpoint. The
    reusable reject arm for every `walk_next` / `content_to_u64` status guard. -/
theorem wd_decode_failViaBnez11
    (base sp0 raVal s0Old s1Old s2Old outPtr srcBase : Word) (srcBytes : List Byte)
    (raClob s0Clob s1Clob s2Clob a0Old v : Word) (idx : Nat) (failOff : BitVec 13)
    (hv : v ≠ (0 : Word))
    (hidx : idx < withdrawal_decode_prog.length)
    (hinstr : withdrawal_decode_prog.get ⟨idx, hidx⟩ = .BNE .x11 .x0 failOff)
    (hfail : (base + BitVec.ofNat 64 (4 * idx)) + signExtend13 failOff = base + 304)
    (hdec : decodeWithdrawal srcBytes = none) :
    cpsTripleWithin (1 + 7) (base + BitVec.ofNat 64 (4 * idx)) (raVal &&& ~~~1)
      (withdrawal_decode_code base)
      (((.x11 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ a0Old) **
          ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
            (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) **
            ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
            ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
          regOwn .x12 ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          bytesRegion srcBase srcBytes ** wd_outOwned outPtr))
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
            ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
              ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) := by
  have hbnez := wd_bnez_taken base idx .x11 failOff v hv hidx hinstr
  rw [hfail] at hbnez
  have hbf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0Old) **
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raClob) ** (.x8 ↦ᵣ s0Clob) **
        (.x9 ↦ᵣ s1Clob) ** (.x18 ↦ᵣ s2Clob) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
      regOwn .x12 ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
      bytesRegion srcBase srcBytes ** wd_outOwned outPtr)
    (by unfold wd_scratchOwned wd_outOwned; pcFree) hbnez
  exact cpsTripleWithin_seq_perm_same_cr
    (fun s hp => by
      have hp2 := sepConj_mono_left
        (sepConj_mono (regIs_implies_regOwn .x11)
          (fun s' h' => ((sepConj_pure_right s').1 h').1)) s hp
      xperm_hyp hp2)
    hbf
    (wd_decode_failEndpoint base sp0 raVal s0Old s1Old s2Old outPtr srcBase srcBytes
      raClob s0Clob s1Clob s2Clob a0Old hdec)

/-- **Pre-zeroed output region ⟹ owned.** The untouched 48-byte output struct weakens to the
    six-dword ownership tokens `wd_outOwned` — what the fail disjunct (and any reject before a field
    write) needs. The byte-granular `bytesRegion` is carved into its six dwords and each weakened to
    `memOwn`. -/
theorem wd_outOwned_of_zeroRegion (outPtr : Word) :
    ∀ h, bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)) h → wd_outOwned outPtr h := by
  have hpk8 : packBytes [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] = (0 : Word) := by decide
  have hL : bytesRegion outPtr (List.replicate 48 (0 : BitVec 8))
      = ((outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
         ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word)) **
         ((outPtr + 32) ↦ₘ (0 : Word)) ** ((outPtr + 40) ↦ₘ (0 : Word))) := by
    rw [bytesRegion_eq_cons outPtr _ (by decide),
        bytesRegion_eq_cons (outPtr + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8 + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8 + 8 + 8) _ (by decide),
        bytesRegion_eq_cons (outPtr + 8 + 8 + 8 + 8 + 8) _ (by decide),
        show (outPtr + 8 + 8 + 8 + 8 + 8 : Word) = outPtr + 40 from by bv_omega,
        show (outPtr + 8 + 8 + 8 + 8 : Word) = outPtr + 32 from by bv_omega,
        show (outPtr + 8 + 8 + 8 : Word) = outPtr + 24 from by bv_omega,
        show (outPtr + 8 + 8 : Word) = outPtr + 16 from by bv_omega]
    simp [hpk8, sepConj_emp_right']
  intro h hp
  rw [hL] at hp
  unfold wd_outOwned
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))))
    h hp

/-- **walk_init fail arm.** One of the seven nonzero-status arms of the `walk_init` 9-way post
    (a2 = v ≠ 0: empty / not-a-list / short-mismatch / long-{truncated,leading-zero,non-minimal,
    mismatch}) routes through the status guard (idx 7) to the fail endpoint. Uniform over the arm's
    cursor/end values `c`/`e` and its residual fact `P`. Used for all seven fail arms of the
    walk_init dispatch. -/
theorem wd_decode_walkInitFailArm
    (base sp0 raVal s0Old s1Old s2Old structPtr outPtr srcBase : Word) (srcBytes : List Byte)
    (c e v : Word) (P : Prop) (hv : v ≠ (0 : Word))
    (hdec : decodeWithdrawal srcBytes = none) :
    cpsTripleWithin (1 + 7) (base + 28) (raVal &&& ~~~1) (withdrawal_decode_code base)
      (⌜P⌝ **
        ((.x12 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ c) ** (.x1 ↦ᵣ (base + 28)) **
         (.x8 ↦ᵣ structPtr) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
         (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
         ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
         ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
         ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
         ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old) **
         wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
         bytesRegion srcBase srcBytes ** (.x11 ↦ᵣ e) **
         bytesRegion outPtr (List.replicate 48 (0 : BitVec 8))))
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
            ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
              ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) := by
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ x => x)
    (wd_decode_failViaBnez12 base sp0 raVal s0Old s1Old s2Old outPtr srcBase srcBytes
      (base + 28) structPtr s1Old s2Old c v 7 (276 : BitVec 13) hv
      (by rw [withdrawal_decode_prog_length]; norm_num)
      (by decide)
      (by rw [show (4 * 7 : Nat) = 28 from rfl,
              show signExtend13 (276 : BitVec 13) = (276 : Word) from by decide]; bv_omega)
      hdec)
  have hp1 := ((sepConj_pure_left s).1 hp).2
  have hp2 := (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x11) (wd_outOwned_of_zeroRegion outPtr))))))))))))))))))) s hp1
  xperm_hyp hp2

/-- **Triple or-elimination.** The straight-line analogue of `cpsBranchWithin_or_pre`: if both
    `P1` and `P2` run to the same exit/post `Q`, their disjunction does too. Used to route a leaf
    call's disjunctive status post (after `sepConj_or_elim` distributes the frame) — each disjunct
    to its handler (reject arm or success continuation). -/
theorem cpsTripleWithin_or_pre {n : Nat} {e1 e2 : Word} {cr : CodeReq} {P1 P2 Q : Assertion}
    (h1 : cpsTripleWithin n e1 e2 cr P1 Q) (h2 : cpsTripleWithin n e1 e2 cr P2 Q) :
    cpsTripleWithin n e1 e2 cr (fun h => P1 h ∨ P2 h) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hh, hcompat, a, b, hab, hu, hPor, hRb⟩ := hPR
  rcases hPor with hP1 | hP2
  · exact h1 R hR s hcr ⟨hh, hcompat, a, b, hab, hu, hP1, hRb⟩ hpc
  · exact h2 R hR s hcr ⟨hh, hcompat, a, b, hab, hu, hP2, hRb⟩ hpc

/-- **Capstone meta-wiring.** `withdrawal_decode_characterization` reduces to the two decode cases:
    the `some w` case is `wd_decode_successCase` (proven); the `none` case is supplied as `hfail`
    (the forward fail-tree triple). Casing on `decodeWithdrawal srcBytes` dispatches; each case
    provides its own `N`. This isolates the remaining work to exactly the `none`-case triple. -/
theorem wd_decode_characterization_of_failCase
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte)
    (hfail : base &&& 1 = 0 → base.toNat + 1444 < 2 ^ 64 → srcBase.toNat % 8 = 0 →
      outPtr.toNat % 8 = 0 → srcBytes.length < 2 ^ 64 → srcBase.toNat + srcBytes.length < 2 ^ 64 →
      outPtr.toNat + 48 < 2 ^ 64 →
      (∀ k, k < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) →
      (∀ k, k < 48 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) →
      decodeWithdrawal srcBytes = none →
      cpsTripleWithin 2048 base (raVal &&& ~~~1) (withdrawal_decode_code base)
        ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
          (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
          (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          wd_frameOwned sp0 **
          bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : Byte)))
        (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
          (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
          wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          wd_frameOwned sp0 **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
              ⌜decodeWithdrawal srcBytes = some w ∧
                w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2) ∧ d2.length = 20⌝) h)) ∨
           (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
              ⌜decodeWithdrawal srcBytes = none⌝) h)))) :
    withdrawal_decode_characterization base srcBase outPtr raVal sp0 s0Old s1Old s2Old srcBytes := by
  unfold withdrawal_decode_characterization
  intro hbe hbase hsalign hostalign hsrclt hnowrap hout48 hsvalid houtvalid
  by_cases hd : decodeWithdrawal srcBytes = none
  · exact hfail hbe hbase hsalign hostalign hsrclt hnowrap hout48 hsvalid houtvalid hd
  · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hd
    exact wd_decode_successCase base srcBase outPtr raVal sp0 s0Old s1Old s2Old srcBytes w
      hbe hbase hsalign hostalign hsrclt hnowrap hout48 hsvalid houtvalid hw

/-- **Call block: `rlp_walk_init`, empty-list arm.** Like `wd_call_walk_init_short` but uses the
    `len = 0` leaf (`rlp_walk_init_empty_spec_within`, 3 steps): when `a1 = list_len = 0` the routine
    returns status `a2 = 2` (empty) without reading any bytes. The reusable walk_init call for the
    `|srcBytes| = 0` fail path. -/
theorem wd_call_walk_init_empty
    (callerPC calleeEntry a2Old vOld : Word) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_init_code calleeEntry)) :
    cpsTripleWithin (1 + 3) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_walk_init_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word))))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (2 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (callerPC + 4))) := by
  have hcallee := rlp_walk_init_empty_spec_within calleeEntry (callerPC + 4) a2Old
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) hcallee)

/-- **Fail-path front-entry: peel + prologue** (base+0 → base+24). Converts the capstone
    precondition into the prologue's post (callee-saved registers spilled to the 32-byte frame)
    with the rest framed as ownership tokens. Peels `wd_frameOwned`'s four cells to the prologue's
    `memIs` slots; everything else (scratch, a3/a4/a5, a0/a1, output region, input region) rides
    as a frame. Shared by every walk_init fail path (empty / per-arm). -/
theorem wd_decode_failPrologue
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte) :
    cpsTripleWithin 6 base (base + 24) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))
      (((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raVal) **
        (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ outPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) **
        (wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** (.x10 ↦ᵣ srcBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))) := by
  refine cpsTripleWithin_weaken (fun h hp => by unfold wd_frameOwned at hp; xperm_hyp hp) (fun _ x => x)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)) ** memOwn (sp0 - 24) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (a := sp0 - 32) (fun m0 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)) ** ((sp0 - 32) ↦ₘ m0) ** memOwn (sp0 - 16) ** memOwn (sp0 - 8))
      (a := sp0 - 24) (fun m1 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)) ** ((sp0 - 32) ↦ₘ m0) ** ((sp0 - 24) ↦ₘ m1) ** memOwn (sp0 - 8))
      (a := sp0 - 16) (fun m2 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)) ** ((sp0 - 32) ↦ₘ m0) ** ((sp0 - 24) ↦ₘ m1) ** ((sp0 - 16) ↦ₘ m2))
      (a := sp0 - 8) (fun m3 => ?_))
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
          show (sp0 + (-32 : Word)) + 8 = sp0 - 24 from by bv_omega,
          show (sp0 + (-32 : Word)) + 16 = sp0 - 16 from by bv_omega,
          show (sp0 + (-32 : Word)) + 24 = sp0 - 8 from by bv_omega,
          show sp0 + (-32 : Word) = sp0 - 32 from by bv_omega]
      xperm_hyp hp)
    (fun _ x => x)
    (cpsTripleWithin_frameR
      (wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** (.x10 ↦ᵣ srcBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))
      (by unfold wd_scratchOwned; pcFree)
      (wd_decode_prologue base sp0 raVal s0Old s1Old s2Old outPtr m0 m1 m2 m3))

/-- **Fail path: empty input** (`|srcBytes| = 0`). The program runs prologue ⨾ walk_init (which
    returns the empty status `a2 = 2` without reading bytes) ⨾ status guard (rejects) ⨾ failReturn,
    landing in the capstone failure disjunct. `decodeWithdrawal [] = none` is supplied. -/
theorem wd_decode_failEmpty
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte)
    (hbe : base &&& 1 = 0) (hbase : base.toNat + 1444 < 2 ^ 64)
    (hlen0 : srcBytes.length = 0) (hdec : decodeWithdrawal srcBytes = none) :
    cpsTripleWithin (6 + (4 + 8)) base (raVal &&& ~~~1) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
            ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
              ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) := by
  have hpro := wd_decode_failPrologue base srcBase outPtr raVal sp0 s0Old s1Old s2Old srcBytes
  have hoffset : (base + 24) + signExtend21 (308 : BitVec 21) = base + 332 := by
    rw [show signExtend21 (308 : BitVec 21) = (308 : Word) from by decide]; bv_omega
  have hcall0 := cpsTripleWithin_extend_code (wd_walkinit_code_sub base)
    (wd_call_walk_init_empty (base + 24) (base + 332) outPtr raVal (308 : BitVec 21) hoffset
      (by rw [show base + 24 + 4 = base + 28 from by bv_omega]
          exact BitAux.word_add_even_andn_one hbe (by decide))
      (wd_decode_disjoint_facts base hbase).1)
  rw [show base + 24 + 4 = base + 28 from by bv_omega] at hcall0
  have hcall := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) **
      (.x18 ↦ᵣ s2Old) ** ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old) **
      wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** (.x10 ↦ᵣ srcBase) **
      bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))
    (by unfold wd_scratchOwned; pcFree) hcall0
  have hreject := wd_decode_walkInitFailArm base sp0 raVal s0Old s1Old s2Old outPtr outPtr srcBase
    srcBytes srcBase 0 2 True (by decide) hdec
  refine cpsTripleWithin_seq_perm_same_cr
    (fun s hp => by
      rw [hlen0, show BitVec.ofNat 64 0 = (0 : Word) from rfl] at hp
      xperm_hyp hp)
    hpro
    (cpsTripleWithin_seq_perm_same_cr
      (fun s hp => by
        refine (sepConj_pure_left s).mpr ⟨trivial, ?_⟩
        xperm_hyp hp)
      hcall hreject)

/-- **Call block: `rlp_walk_init`, not-a-list arm.** Uses the `prefix < 0xc0` leaf
    (`rlp_walk_init_notlist_spec_within`, 7 steps): a non-list RLP item → status `a2 = 1`. The
    reusable walk_init call for the not-a-list fail path. -/
theorem wd_call_walk_init_notlist
    (callerPC calleeEntry listBase listLen a2Old t0Old t1Old vOld : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_init_code calleeEntry))
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_notlist : BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin (1 + 7) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_walk_init_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes))
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (callerPC + 4)) **
        bytesRegion listBase listBytes) := by
  have hcallee := rlp_walk_init_notlist_spec_within calleeEntry listBase (callerPC + 4) listLen
    a2Old t0Old t1Old listBytes listOff hsalign hoff hover hvalid hlen h_notlist
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) hcallee)

/-- **Fail path: not-a-list prefix** (`prefix < 0xc0`). prologue ⨾ walk_init (not-a-list arm,
    a2=1) ⨾ status guard (rejects) ⨾ failReturn → capstone failure disjunct. Peels x5/x6 from the
    scratch frame for the walk_init call; the prefix hypotheses come from the dispatch's case-split. -/
theorem wd_decode_failNotlist
    (base srcBase outPtr raVal sp0 s0Old s1Old s2Old : Word) (srcBytes : List Byte)
    (hbe : base &&& 1 = 0) (hbase : base.toNat + 1444 < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0) (hsrcLen0 : 0 < srcBytes.length)
    (hsrclt : srcBytes.length < 2 ^ 64) (hover0 : srcBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (srcBase + BitVec.ofNat 64 0) = true)
    (h_notlist : BitVec.ult ((srcBytes[0]'hsrcLen0).zeroExtend 64) (0xc0 : Word) = true)
    (hdec : decodeWithdrawal srcBytes = none) :
    cpsTripleWithin (6 + (8 + 8)) base (raVal &&& ~~~1) (withdrawal_decode_code base)
      ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ outPtr) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))
      (((.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 **
        wd_scratchOwned ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        wd_frameOwned sp0 **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (∃ w d2, (((.x10 ↦ᵣ (0 : Word)) ** wd_outHolds outPtr w d2 **
            ⌜decodeWithdrawal srcBytes = some w ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
              ∧ d2.length = 20⌝) h)) ∨
         (((.x10 ↦ᵣ (1 : Word)) ** wd_outOwned outPtr **
            ⌜decodeWithdrawal srcBytes = none⌝) h))) := by
  have hlen : BitVec.ofNat 64 srcBytes.length ≠ (0 : Word) := by
    have ht : (BitVec.ofNat 64 srcBytes.length).toNat = srcBytes.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hsrclt
    intro hc; rw [hc] at ht; simp at ht; omega
  have hoffset : (base + 24) + signExtend21 (308 : BitVec 21) = base + 332 := by
    rw [show signExtend21 (308 : BitVec 21) = (308 : Word) from by decide]; bv_omega
  have halignC : (base + 24 + 4) &&& ~~~1 = base + 24 + 4 := by
    rw [show base + 24 + 4 = base + 28 from by bv_omega]
    exact BitAux.word_add_even_andn_one hbe (by decide)
  refine cpsTripleWithin_seq_perm_same_cr (fun s hp => hp)
    (wd_decode_failPrologue base srcBase outPtr raVal sp0 s0Old s1Old s2Old srcBytes) ?_
  refine cpsTripleWithin_weaken (fun h hp => by unfold wd_scratchOwned at hp; xperm_hyp hp)
    (fun _ x => x)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (P := (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ outPtr) ** ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) ** ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) ** ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) ** ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8))) (r := .x5) (fun t0Old => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (P := (.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ outPtr) ** ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) ** ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) ** ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) ** ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old) ** (.x5 ↦ᵣ t0Old) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** bytesRegion outPtr (List.replicate 48 (0 : BitVec 8))) (r := .x6) (fun t1Old => ?_))
  have hcall0 := cpsTripleWithin_extend_code (wd_walkinit_code_sub base)
    (wd_call_walk_init_notlist (base + 24) (base + 332) srcBase (BitVec.ofNat 64 srcBytes.length)
      outPtr t0Old t1Old raVal srcBytes 0 (308 : BitVec 21) hoffset halignC
      (wd_decode_disjoint_facts base hbase).1 hsalign hsrcLen0 hover0 hvalid0 hlen h_notlist)
  rw [show base + 24 + 4 = base + 28 from by bv_omega] at hcall0
  have hcall := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x8 ↦ᵣ outPtr) ** (.x9 ↦ᵣ s1Old) **
      (.x18 ↦ᵣ s2Old) ** ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
      ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old) **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
      bytesRegion outPtr (List.replicate 48 (0 : BitVec 8)))
    (by pcFree) hcall0
  exact cpsTripleWithin_weaken
    (fun h hp => by rw [show srcBase + BitVec.ofNat 64 0 = srcBase from by bv_omega]; xperm_hyp hp)
    (fun _ x => x)
    (cpsTripleWithin_seq_perm_same_cr
      (fun s hp => by
        refine (sepConj_pure_left s).mpr ⟨trivial, ?_⟩
        unfold wd_scratchOwned
        xperm_hyp hp)
      hcall
      (wd_decode_walkInitFailArm base sp0 raVal s0Old s1Old s2Old outPtr outPtr srcBase srcBytes
        (srcBase + BitVec.ofNat 64 0)
        ((srcBase + BitVec.ofNat 64 0) + BitVec.ofNat 64 srcBytes.length) 1 True (by decide) hdec))

/-- **Call block: `rlp_walk_init`, short-list span-mismatch arm.** Uses the short-list-mismatch leaf
    (`rlp_walk_init_smism_spec_within`, 14 steps): a short-list header whose declared payload span
    doesn't match the input → status `a2 = 3`. The reusable walk_init call for the short-mismatch
    fail path (5 scratch registers, like short-success). -/
theorem wd_call_walk_init_smism
    (callerPC calleeEntry listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old vOld : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_init_code calleeEntry))
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_smism : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      ≠ (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin (1 + 14) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_walk_init_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes))
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (3 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (callerPC + 4)) ** bytesRegion listBase listBytes) := by
  have hcallee := rlp_walk_init_smism_spec_within calleeEntry listBase (callerPC + 4) listLen
    a2Old t0Old t1Old t2Old t3Old t4Old listBytes listOff hsalign hoff hover hvalid hlen h_ge h_hi h_smism
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) hcallee)

end EvmAsm.Rv64.RLP
