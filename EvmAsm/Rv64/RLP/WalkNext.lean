/-
  EvmAsm.Rv64.RLP.WalkNext

  A verified RISC-V leaf subroutine: a CPS drop-in for the codegen guest function
  `rlp_walk_next` emitted by `EvmAsm/Codegen/Programs/RlpWalk.lean`.

  `rlp_walk_next` decodes the single RLP item at the cursor, advances the cursor
  past it, and reports the item's content length. The content pointer is derived
  by the caller as `advanced_cursor - content_length`.

  This is the **strict** (execution-specs-equivalent) version: in addition to the
  per-form classification it enforces, with a distinct failure status each:

    * **bound** (`a1 = 3`) — the item's header or content runs past `end`;
    * **non-minimal** (`a1 = 4`) — a long form whose decoded length is `< 56`;
    * **leading zero** (`a1 = 5`) — a long form whose first length byte is `0`;
    * **single-byte non-canonical** (`a1 = 6`) — a 1-byte short string whose
      content byte is `< 0x80` (it must be the bare byte).

  These are **structural** canonicality/bounds, distinct from the **scalar**
  canonicality enforced in `ContentToU256Be`/`ContentToU64`.

  ## Caller-facing contract (LP64)

  Frameless leaf: reached by `jal ra, rlp_walk_next`, returns via `ret`.

  ### Inputs
  * `a0` (`x10`) — cursor (current item, absolute pointer).
  * `a1` (`x11`) — end (exclusive, absolute pointer).

  ### Outputs
  * `a0` (`x10`) — advanced cursor (next item); `= cursor` on every fail path.
  * `a1` (`x11`) — **status**: `0` ok / `2` end-of-list / `3` bound / `4` non-minimal
    / `5` leading zero / `6` single-byte non-canonical.
  * `a2` (`x12`) — content length (`0` on every fail path).

  Scratch `t0..t6` (`x5`,`x6`,`x7`,`x28`,`x29`,`x30`,`x31`) clobbered; `ra` preserved.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP

/--
The verified drop-in body for the codegen guest `rlp_walk_next` (strict, 103
instructions). Register map: `a0=x10`, `a1=x11`, `a2=x12`, `t0=x5`, `t1=x6`,
`t2=x7`, `t3=x28`, `t4=x29`, `t5=x30`, `t6=x31`, `ra=x1`.

Dispatch (idx 0..9): end-of-list / single / short string / long string / short
list / long list. Each form computes its advanced cursor in a temp, then checks
`advanced ≤ end` (bound, idx 91); long forms additionally check the header fits
before the length-field loop, reject a leading-zero length byte (idx 97) and a
non-minimal decoded length (idx 94); the short-string form rejects a non-canonical
single byte (idx 100). Fail blocks (idx 88..102) set the status and `a2 = 0`,
leaving `a0 = cursor`.
-/
def rlp_walk_next_prog : List Instr :=
  [ .BGEU .x10 .x11 (352 : BitVec 13),   -- 0  cursor >= end -> end (idx 88)
    .LBU .x5 .x10 0,                      -- 1  prefix
    .LI .x6 (0x80 : Word),                -- 2
    .BLTU .x5 .x6 (288 : BitVec 13),      -- 3  < 0x80 -> single (idx 75)
    .LI .x6 (0xb8 : Word),                -- 4
    .BLTU .x5 .x6 (228 : BitVec 13),      -- 5  < 0xb8 -> short string (idx 62)
    .LI .x6 (0xc0 : Word),                -- 6
    .BLTU .x5 .x6 (120 : BitVec 13),      -- 7  < 0xc0 -> long string (idx 37)
    .LI .x6 (0xf8 : Word),                -- 8
    .BLTU .x5 .x6 (280 : BitVec 13),      -- 9  < 0xf8 -> short list (idx 79)
    .LI .x6 (0xf7 : Word),                -- 10 long list: lol = prefix - 0xf7
    .SUB .x7 .x5 .x6,                     -- 11 lol
    .ADDI .x6 .x7 (1 : BitVec 12),        -- 12 1 + lol
    .ADD .x29 .x10 .x6,                   -- 13 header_end = cursor + 1 + lol
    .BLTU .x11 .x29 (308 : BitVec 13),    -- 14 header > end -> bound (idx 91)
    .ADDI .x30 .x10 (1 : BitVec 12),      -- 15 length-field ptr
    .LBU .x31 .x30 0,                     -- 16 first length byte
    .BEQ .x31 .x0 (320 : BitVec 13),      -- 17 leading zero -> lz (idx 97)
    .LI .x28 (0 : Word),                  -- 18 acc
    .MV .x6 .x7,                          -- 19 count = lol
    .BEQ .x6 .x0 (28 : BitVec 13),        -- 20 ll loop head: count == 0 -> ll_done (idx 27)
    .SLLI .x28 .x28 (8 : BitVec 6),       -- 21
    .LBU .x31 .x30 0,                     -- 22
    .OR .x28 .x28 .x31,                   -- 23
    .ADDI .x30 .x30 (1 : BitVec 12),      -- 24
    .ADDI .x6 .x6 (-1 : BitVec 12),       -- 25
    .JAL .x0 (-24 : BitVec 21),           -- 26 -> idx 20
    .LI .x6 (56 : Word),                  -- 27 ll_done
    .BLTU .x28 .x6 (264 : BitVec 13),     -- 28 decoded < 56 -> nonmin (idx 94)
    .ADD .x31 .x7 .x28,                   -- 29 lol + decoded
    .ADDI .x31 .x31 (1 : BitVec 12),      -- 30 full span = 1 + lol + decoded
    .ADD .x6 .x10 .x31,                   -- 31 advanced (temp)
    .BLTU .x11 .x6 (236 : BitVec 13),     -- 32 advanced > end -> bound (idx 91)
    .MV .x10 .x6,                         -- 33 advanced cursor
    .MV .x12 .x31,                        -- 34 content length = full span
    .LI .x11 (0 : Word),                  -- 35
    .JALR .x0 .x1 0,                      -- 36 ret
    .LI .x6 (0xb7 : Word),                -- 37 long string: lol = prefix - 0xb7
    .SUB .x7 .x5 .x6,                     -- 38 lol
    .ADDI .x6 .x7 (1 : BitVec 12),        -- 39 1 + lol
    .ADD .x29 .x10 .x6,                   -- 40 header_end
    .BLTU .x11 .x29 (200 : BitVec 13),    -- 41 header > end -> bound (idx 91)
    .ADDI .x30 .x10 (1 : BitVec 12),      -- 42 length-field ptr
    .LBU .x31 .x30 0,                     -- 43 first length byte
    .BEQ .x31 .x0 (212 : BitVec 13),      -- 44 leading zero -> lz (idx 97)
    .LI .x28 (0 : Word),                  -- 45 acc
    .MV .x6 .x7,                          -- 46 count = lol
    .BEQ .x6 .x0 (28 : BitVec 13),        -- 47 ls loop head: count == 0 -> ls_done (idx 54)
    .SLLI .x28 .x28 (8 : BitVec 6),       -- 48
    .LBU .x31 .x30 0,                     -- 49
    .OR .x28 .x28 .x31,                   -- 50
    .ADDI .x30 .x30 (1 : BitVec 12),      -- 51
    .ADDI .x6 .x6 (-1 : BitVec 12),       -- 52
    .JAL .x0 (-24 : BitVec 21),           -- 53 -> idx 47
    .LI .x6 (56 : Word),                  -- 54 ls_done
    .BLTU .x28 .x6 (156 : BitVec 13),     -- 55 decoded < 56 -> nonmin (idx 94)
    .ADD .x6 .x29 .x28,                   -- 56 advanced = header_end + decoded (temp)
    .BLTU .x11 .x6 (136 : BitVec 13),     -- 57 advanced > end -> bound (idx 91)
    .MV .x10 .x6,                         -- 58 advanced cursor
    .MV .x12 .x28,                        -- 59 content length = decoded
    .LI .x11 (0 : Word),                  -- 60
    .JALR .x0 .x1 0,                      -- 61 ret
    .LI .x6 (0x80 : Word),                -- 62 short string
    .SUB .x12 .x5 .x6,                    -- 63 len = prefix - 0x80
    .ADDI .x7 .x10 (1 : BitVec 12),       -- 64 content start = cursor + 1
    .ADD .x28 .x7 .x12,                   -- 65 advanced = cursor + 1 + len (temp)
    .BLTU .x11 .x28 (100 : BitVec 13),    -- 66 advanced > end -> bound (idx 91)
    .LI .x6 (1 : Word),                   -- 67
    .BNE .x12 .x6 (16 : BitVec 13),       -- 68 len != 1 -> ss_ok (idx 72)
    .LBU .x6 .x7 0,                       -- 69 content[0]
    .LI .x29 (0x80 : Word),               -- 70
    .BLTU .x6 .x29 (116 : BitVec 13),     -- 71 content[0] < 0x80 -> noncanon (idx 100)
    .MV .x10 .x28,                        -- 72 ss_ok: advanced cursor
    .LI .x11 (0 : Word),                  -- 73
    .JALR .x0 .x1 0,                      -- 74 ret
    .ADDI .x10 .x10 (1 : BitVec 12),      -- 75 single: advanced cursor
    .LI .x12 (1 : Word),                  -- 76 content length = 1
    .LI .x11 (0 : Word),                  -- 77
    .JALR .x0 .x1 0,                      -- 78 ret
    .LI .x6 (0xc0 : Word),                -- 79 short list
    .SUB .x31 .x5 .x6,                    -- 80 prefix - 0xc0
    .ADDI .x31 .x31 (1 : BitVec 12),      -- 81 full span = 1 + (prefix - 0xc0)
    .ADD .x6 .x10 .x31,                   -- 82 advanced (temp)
    .BLTU .x11 .x6 (32 : BitVec 13),      -- 83 advanced > end -> bound (idx 91)
    .MV .x10 .x6,                         -- 84 advanced cursor
    .MV .x12 .x31,                        -- 85 content length = full span
    .LI .x11 (0 : Word),                  -- 86
    .JALR .x0 .x1 0,                      -- 87 ret
    .LI .x11 (2 : Word),                  -- 88 end: status 2
    .LI .x12 (0 : Word),                  -- 89
    .JALR .x0 .x1 0,                      -- 90 ret
    .LI .x11 (3 : Word),                  -- 91 bound: status 3
    .LI .x12 (0 : Word),                  -- 92
    .JALR .x0 .x1 0,                      -- 93 ret
    .LI .x11 (4 : Word),                  -- 94 nonmin: status 4
    .LI .x12 (0 : Word),                  -- 95
    .JALR .x0 .x1 0,                      -- 96 ret
    .LI .x11 (5 : Word),                  -- 97 lz: status 5
    .LI .x12 (0 : Word),                  -- 98
    .JALR .x0 .x1 0,                      -- 99 ret
    .LI .x11 (6 : Word),                  -- 100 noncanon: status 6
    .LI .x12 (0 : Word),                  -- 101
    .JALR .x0 .x1 0 ]                     -- 102 ret

theorem rlp_walk_next_prog_length : rlp_walk_next_prog.length = 103 := rfl

abbrev rlp_walk_next_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_walk_next_prog

instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/-- **end-of-list** (`cursor ≥ end`): status `a1 = 2`, cursor unchanged. -/
theorem rlp_walk_next_end_spec_within
    (base cursor endPtr raVal a2Old : Word)
    (h_end : ¬ BitVec.ult cursor endPtr) :
    cpsTripleWithin 4 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal)) := by
  have hbgeu := bgeu_spec_gen_within .x10 .x11 (352 : BitVec 13) cursor endPtr base
  rw [show base + signExtend13 (352 : BitVec 13) = base + 352 from by
        rw [show signExtend13 (352 : BitVec 13) = (352 : Word) from by decide]] at hbgeu
  have hmono0 : ∀ a i, CodeReq.singleton base (.BGEU .x10 .x11 (352 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 0 base
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hB := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono0 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      (by pcFree) hbgeu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact h_end ((sepConj_pure_right _).1 h_pure).2)
  have hLI2 := li_spec_gen_within .x11 endPtr (2 : Word) (base + 352) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 356) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 360)
  simp only [signExtend12_0] at hRet
  have hC : cpsTripleWithin 3 (base + 352) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI2 hLI0 hRet
  have hC' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) hC
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) hB hC'
  rw [show (1 + 3) = 4 from rfl] at s1
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s1

/-- Helper: `BGEU x10 x11` NOT taken (in-bounds), idx 0, `base → base+4`. -/
private theorem wn_bgeu_ntaken (base srcBase endPtr : Word)
    (srcOff : Nat) (R : Assertion) (hR : R.pcFree)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    cpsTripleWithin 1 base (base + 4) (rlp_walk_next_code base)
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr)) ** R)
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr)) ** R) := by
  have hbgeu := bgeu_spec_gen_within .x10 .x11 (352 : BitVec 13)
    (srcBase + BitVec.ofNat 64 srcOff) endPtr base
  have hmono0 : ∀ a i, CodeReq.singleton base (.BGEU .x10 .x11 (352 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 0 base
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have h := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono0 (cpsBranchWithin_frameR R hR hbgeu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 h_inb)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h' hp => sepConj_mono_left (sepConj_mono_right
      (fun h'' hp'' => ((sepConj_pure_right h'').1 hp'').1)) h' hp) h

/-- **single-byte item** (`prefix < 0x80`): cursor `+1`, `a2 = 1`, `a1 = 0`. -/
theorem rlp_walk_next_single_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_single : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true) :
    cpsTripleWithin 8 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  have hlbu := bytesRegion_lbu_within .x5 .x10 srcBase t0Old (base + 4) srcBytes srcOff
    (by decide) hsalign hoff hover hvalid
  have hLI := li_spec_gen_within .x6 t1Old (0x80 : Word) (base + 8) (by decide)
  have hB : cpsTripleWithin 2 (base + 4) (base + 12) (rlp_walk_next_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ (0x80 : Word)) **
        bytesRegion srcBase srcBytes) := by
    runBlock hlbu hLI
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  have hbltu := bltu_spec_gen_within .x5 .x6 (288 : BitVec 13)
    ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) (base + 12)
  rw [show (base + 12) + signExtend13 (288 : BitVec 13) = base + 300 from by
        rw [show signExtend13 (288 : BitVec 13) = (288 : Word) from by decide]; bv_omega,
      show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbltu
  have hmono3 : ∀ a i, CodeReq.singleton (base + 12) (.BLTU .x5 .x6 (288 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 3 (base + 12)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hC := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono3 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_single)
  have haddi := addi_spec_gen_same_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 300) (by decide)
  have hLI1 := li_spec_gen_within .x12 a2Old (1 : Word) (base + 304) (by decide)
  have hLI0 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 308) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 312)
  simp only [signExtend12_0] at hRet
  have hD : cpsTripleWithin 4 (base + 300) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x11 ↦ᵣ endPtr) **
        (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x12 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock haddi hLI1 hLI0 hRet
  have hD' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0x80 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hD
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hD'
  rw [show (1 + 2 + 1 + 4) = 8 from rfl] at s3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s3
  have hp' := sepConj_mono_right (sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6) (fun _ x => x))) h hp
  xperm_hyp hp'

/-- Cascade prefix read: `LBU x5 x10 0 ; LI x6 0x80` (idx 1,2), `base+4 → base+12`. -/
private theorem wn_lbu_li80 (base srcBase : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (t0Old t1Old : Word) (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin 2 (base + 4) (base + 12) (rlp_walk_next_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ (0x80 : Word)) **
        bytesRegion srcBase srcBytes) := by
  have hlbu := bytesRegion_lbu_within .x5 .x10 srcBase t0Old (base + 4) srcBytes srcOff
    (by decide) hsalign hoff hover hvalid
  have hLIc := li_spec_gen_within .x6 t1Old (0x80 : Word) (base + 8) (by decide)
  runBlock hlbu hLIc

/-- One "BLTU x5 x6 off NOT taken (prefix ≥ thr)" cascade step over framed scratch
    `F`, leaving `x6` unchanged. -/
private theorem wn_cascade_step (base : Word) (off : BitVec 13) (idx : Nat) (a : Word)
    (pfx thr : Word) (F : Assertion) (hF : F.pcFree)
    (haddr : a = base + BitVec.ofNat 64 (4 * idx)) (hidx : idx < 103)
    (hinstr : rlp_walk_next_prog[idx]? = some (.BLTU .x5 .x6 off))
    (h_ge : ¬ BitVec.ult pfx thr = true) :
    cpsTripleWithin 1 a (a + 4) (rlp_walk_next_code base)
      (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ thr)) ** F)
      (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ thr)) ** F) := by
  have hbltu := bltu_spec_gen_within .x5 .x6 off pfx thr a
  have hmono : ∀ x i, CodeReq.singleton a (.BLTU .x5 .x6 off) x = some i
      → rlp_walk_next_code base x = some i :=
    CodeReq.singleton_mono (by
      have hlk := CodeReq.ofProg_lookup_addr base rlp_walk_next_prog idx a hidx
        (by rw [rlp_walk_next_prog_length]; norm_num) haddr
      have hget : rlp_walk_next_prog.get ⟨idx, hidx⟩ = .BLTU .x5 .x6 off := by
        rw [List.get_eq_getElem]
        have he := List.getElem?_eq_getElem
          (show idx < rlp_walk_next_prog.length by rw [rlp_walk_next_prog_length]; exact hidx)
        rw [hinstr] at he
        exact (Option.some.inj he).symm
      rw [hget] at hlk; exact hlk)
  have hnt := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR F hF hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_ge ((sepConj_pure_right _).1 h_pure).2)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h' hp => sepConj_mono_left (sepConj_mono_right
      (fun h'' hp'' => ((sepConj_pure_right h'').1 hp'').1)) h' hp) hnt

/-- Cascade to the short-list block (idx 0..9), `base → base+316` (idx 79).
    `0xc0 ≤ prefix < 0xf8`. Leaves `x5 = prefix`, `x6 = 0xf8`. -/
private theorem wn_to_short_list (base srcBase endPtr a2Old t0Old t1Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (raVal : Word)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true) :
    cpsTripleWithin 10 base (base + 316) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xf8 : Word))) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)) := by
  have h_lo80 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0x80 : Word).toNat = 128 from by decide,
      show (0xc0 : Word).toNat = 192 from by decide] at h_lo ⊢
    omega
  have h_lob8 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0xb8 : Word).toNat = 184 from by decide,
      show (0xc0 : Word).toNat = 192 from by decide] at h_lo ⊢
    omega
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  have hB := wn_lbu_li80 base srcBase srcBytes srcOff t0Old t1Old hsalign hoff hover hvalid
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hB
  let F : Assertion := (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
    (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
    bytesRegion srcBase srcBytes
  have hC := wn_cascade_step base (288 : BitVec 13) 3 (base + 12) pfx (0x80 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo80)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hC
  have hLI8 := li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 16) (by decide)
  have hmonoD : ∀ a i, CodeReq.singleton (base + 16) (.LI .x6 (0xb8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 4 (base + 16)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hD := cpsTripleWithin_extend_code hmonoD (cpsTripleWithin_frameR
    (((.x5 ↦ᵣ pfx)) ** F) (by pcFree) hLI8)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hD
  have hE := wn_cascade_step base (228 : BitVec 13) 5 (base + 20) pfx (0xb8 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lob8)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hE
  have hLIc := li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 24) (by decide)
  have hmonoF : ∀ a i, CodeReq.singleton (base + 24) (.LI .x6 (0xc0 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 6 (base + 24)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hF2 := cpsTripleWithin_extend_code hmonoF (cpsTripleWithin_frameR
    (((.x5 ↦ᵣ pfx)) ** F) (by pcFree) hLIc)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hF2
  have hG := wn_cascade_step base (120 : BitVec 13) 7 (base + 28) pfx (0xc0 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hG
  have hLIf := li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 32) (by decide)
  have hmonoH : ∀ a i, CodeReq.singleton (base + 32) (.LI .x6 (0xf8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 8 (base + 32)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hH := cpsTripleWithin_extend_code hmonoH (cpsTripleWithin_frameR
    (((.x5 ↦ᵣ pfx)) ** F) (by pcFree) hLIf)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hH
  have hbltu := bltu_spec_gen_within .x5 .x6 (280 : BitVec 13) pfx (0xf8 : Word) (base + 36)
  rw [show (base + 36) + signExtend13 (280 : BitVec 13) = base + 316 from by
        rw [show signExtend13 (280 : BitVec 13) = (280 : Word) from by decide]; bv_omega,
      show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hbltu
  have hmonoI : ∀ a i, CodeReq.singleton (base + 36) (.BLTU .x5 .x6 (280 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 9 (base + 36)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hI := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmonoI (cpsBranchWithin_frameR F (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hi)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hE
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hF2
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hG
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hH
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hI
  rw [show (1 + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = 10 from rfl] at s8
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8

/-- **short list — accept** (`0xc0 ≤ prefix < 0xf8`, span fits): `a2 = full span`,
    cursor advances by the span, `a1 = 0`. -/
theorem rlp_walk_next_short_list_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t6Old : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_bound : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) +
          (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set span := (pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12) with hspan
  have hcasc := wn_to_short_list base srcBase endPtr a2Old t0Old t1Old t6Old srcBytes srcOff
    hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  -- idx 79..82: LI x6 0xc0 ; SUB x31 ; ADDI x31 ; ADD x6 x10 x31 (advanced in x6).
  have hLIc := li_spec_gen_within .x6 (0xf8 : Word) (0xc0 : Word) (base + 316) (by decide)
  have hsub := sub_spec_gen_within .x31 .x5 .x6 pfx (0xc0 : Word) t6Old (base + 320) (by decide)
  have haddi := addi_spec_gen_same_within .x31 (pfx - (0xc0 : Word)) (1 : BitVec 12) (base + 324)
    (by decide)
  rw [← hspan] at haddi
  have hadd := add_spec_gen_within .x6 .x10 .x31 (srcBase + BitVec.ofNat 64 srcOff) span (0xc0 : Word)
    (base + 328) (by decide)
  have hblk : cpsTripleWithin 4 (base + 316) (base + 332) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ t6Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)))
      ((.x6 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + span)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff))) := by
    runBlock hLIc hsub haddi hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 83: BLTU x11 x6 32 NOT taken (advanced ≤ end).  base+332 → base+336.
  have hbltu := bltu_spec_gen_within .x11 .x6 (32 : BitVec 13) endPtr
    ((srcBase + BitVec.ofNat 64 srcOff) + span) (base + 332)
  rw [show (base + 332 : Word) + 4 = base + 336 from by bv_omega] at hbltu
  have hmono83 : ∀ a i, CodeReq.singleton (base + 332) (.BLTU .x11 .x6 (32 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 83 (base + 332)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono83 (cpsBranchWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_bound ((sepConj_pure_right _).1 h_pure).2)
  -- idx 84..87: MV x10 x6 ; MV x12 x31 ; LI x11 0 ; ret.  base+336 → ra.
  have hmv10 := mv_spec_gen_within .x10 .x6 ((srcBase + BitVec.ofNat 64 srcOff) + span)
    (srcBase + BitVec.ofNat 64 srcOff) (base + 336) (by decide)
  have hmv12 := mv_spec_gen_within .x12 .x31 span a2Old (base + 340) (by decide)
  have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 344) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 348)
  simp only [signExtend12_0] at hRet
  have hret : cpsTripleWithin 4 (base + 336) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + span)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ span) **
        (.x11 ↦ᵣ endPtr) ** (.x1 ↦ᵣ raVal))
      ((.x6 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + span)) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + span)) ** (.x12 ↦ᵣ span) ** (.x31 ↦ᵣ span) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hmv10 hmv12 hLI11 hRet
  have hret' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree) hret
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hret'
  rw [show (10 + 4 + 1 + 4) = 19 from rfl] at c3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c3
  have hp' := sepConj_mono
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x)))))
    (sepConj_mono (regIs_implies_regOwn .x5) (fun _ x => x)) h hp
  xperm_hyp hp'

/-- The bound-fail block (idx 91..93), `base+364 → ra`: status `a1 = 3`, `a2 = 0`. -/
private theorem wn_bound_block (base raVal a1Old a2Old : Word) :
    cpsTripleWithin 3 (base + 364) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hLI3 := li_spec_gen_within .x11 a1Old (3 : Word) (base + 364) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 368) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 372)
  simp only [signExtend12_0] at hRet
  runBlock hLI3 hLI0 hRet

/-- **short list — bound** (`0xc0 ≤ prefix < 0xf8`, span runs past `end`): `a1 = 3`. -/
theorem rlp_walk_next_short_list_bound_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t6Old : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_bound : BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) = true) :
    cpsTripleWithin 18 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set span := (pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12) with hspan
  have hcasc := wn_to_short_list base srcBase endPtr a2Old t0Old t1Old t6Old srcBytes srcOff
    hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLIc := li_spec_gen_within .x6 (0xf8 : Word) (0xc0 : Word) (base + 316) (by decide)
  have hsub := sub_spec_gen_within .x31 .x5 .x6 pfx (0xc0 : Word) t6Old (base + 320) (by decide)
  have haddi := addi_spec_gen_same_within .x31 (pfx - (0xc0 : Word)) (1 : BitVec 12) (base + 324)
    (by decide)
  rw [← hspan] at haddi
  have hadd := add_spec_gen_within .x6 .x10 .x31 (srcBase + BitVec.ofNat 64 srcOff) span (0xc0 : Word)
    (base + 328) (by decide)
  have hblk : cpsTripleWithin 4 (base + 316) (base + 332) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ t6Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)))
      ((.x6 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + span)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff))) := by
    runBlock hLIc hsub haddi hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 83: BLTU x11 x6 32 TAKEN (advanced > end).  base+332 → base+364 (bound).
  have hbltu := bltu_spec_gen_within .x11 .x6 (32 : BitVec 13) endPtr
    ((srcBase + BitVec.ofNat 64 srcOff) + span) (base + 332)
  rw [show (base + 332) + signExtend13 (32 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega,
      show (base + 332 : Word) + 4 = base + 336 from by bv_omega] at hbltu
  have hmono83 : ∀ a i, CodeReq.singleton (base + 332) (.BLTU .x11 .x6 (32 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 83 (base + 332)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono83 (cpsBranchWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_bound)
  have hfail := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + span)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_bound_block base raVal endPtr a2Old)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hfail
  rw [show (10 + 4 + 1 + 3) = 18 from rfl] at c3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c3
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x31) (sepConj_mono (fun _ x => x)
        (fun _ x => x))))) h hp
  xperm_hyp hp'

/-- Cascade to the short-string block (idx 0..5), `base → base+248` (idx 62).
    `0x80 ≤ prefix < 0xb8`. Leaves `x5 = prefix`, `x6 = 0xb8`. -/
private theorem wn_to_short_string (base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) (raVal : Word)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true) :
    cpsTripleWithin 6 base (base + 248) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xb8 : Word))) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)) := by
  have h_lo80 := h_lo
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
    (by pcFree) h_inb
  have hB := wn_lbu_li80 base srcBase srcBytes srcOff t0Old t1Old hsalign hoff hover hvalid
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  let F : Assertion := (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
    (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes
  have hC := wn_cascade_step base (288 : BitVec 13) 3 (base + 12) pfx (0x80 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo80)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hC
  have hLI8 := li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 16) (by decide)
  have hmonoD : ∀ a i, CodeReq.singleton (base + 16) (.LI .x6 (0xb8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 4 (base + 16)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hD := cpsTripleWithin_extend_code hmonoD (cpsTripleWithin_frameR
    (((.x5 ↦ᵣ pfx)) ** F) (by pcFree) hLI8)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hD
  have hbltu := bltu_spec_gen_within .x5 .x6 (228 : BitVec 13) pfx (0xb8 : Word) (base + 20)
  rw [show (base + 20) + signExtend13 (228 : BitVec 13) = base + 248 from by
        rw [show signExtend13 (228 : BitVec 13) = (228 : Word) from by decide]; bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbltu
  have hmonoE : ∀ a i, CodeReq.singleton (base + 20) (.BLTU .x5 .x6 (228 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 5 (base + 20)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hE := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmonoE (cpsBranchWithin_frameR F (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hi)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hE
  rw [show (1 + 2 + 1 + 1 + 1) = 6 from rfl] at s4
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4

/-- **short string — bound** (`0x80 ≤ prefix < 0xb8`, content runs past `end`): `a1 = 3`. -/
theorem rlp_walk_next_short_string_bound_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_bound : BitVec.ult endPtr (((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) = true) :
    cpsTripleWithin 14 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set cst := (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) with hcst
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  -- idx 62..65: LI x6 0x80 ; SUB x12 ; ADDI x7 (content start) ; ADD x28 (advanced).
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 256) (by decide)
  rw [← hcst] at ha7
  have hadd := add_spec_gen_within .x28 .x7 .x12 cst (pfx - (0x80 : Word)) t3Old (base + 260)
    (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cst) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x28 ↦ᵣ (cst + (pfx - (0x80 : Word))))) := by
    runBlock hLI80 hsub ha7 hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 66: BLTU x11 x28 100 TAKEN (advanced > end).  base+264 → base+364 (bound).
  have hbltu := bltu_spec_gen_within .x11 .x28 (100 : BitVec 13) endPtr
    (cst + (pfx - (0x80 : Word))) (base + 264)
  rw [show (base + 264) + signExtend13 (100 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]; bv_omega,
      show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hbltu
  have hmono66 : ∀ a i, CodeReq.singleton (base + 264) (.BLTU .x11 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cst) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by rw [hcst]; exact h_bound))
  have hfail := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (cst + (pfx - (0x80 : Word)))) ** (.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ cst) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_bound_block base raVal endPtr (pfx - (0x80 : Word)))
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hfail
  rw [show (6 + 4 + 1 + 3) = 14 from rfl] at c3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c3
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x))))))) h hp
  xperm_hyp hp'

/-- The single-byte-non-canonical fail block (idx 100..102), `base+400 → ra`: `a1 = 6`. -/
private theorem wn_noncanon_block (base raVal a1Old a2Old : Word) :
    cpsTripleWithin 3 (base + 400) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (6 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hLI6 := li_spec_gen_within .x11 a1Old (6 : Word) (base + 400) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 404) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 408)
  simp only [signExtend12_0] at hRet
  runBlock hLI6 hLI0 hRet

/-- **short string — non-canonical single byte** (`prefix = 0x81`, `content[0] < 0x80`,
    span fits): the 1-byte string should have been the bare byte → `a1 = 6`. -/
theorem rlp_walk_next_short_string_noncanon_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64) (hover1 : srcBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_bound : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 (srcOff + 1)) +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) = true)
    (h_len1 : (srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word))
    (h_content : BitVec.ult ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0x80 : Word) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set cp1 := srcBase + BitVec.ofNat 64 (srcOff + 1) with hcp1
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  -- idx 62..65: LI x6 0x80 ; SUB x12 (len) ; ADDI x7 (content ptr) ; ADD x28 (advanced).
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 256) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha7
  have hadd := add_spec_gen_within .x28 .x7 .x12 cp1 (pfx - (0x80 : Word)) t3Old (base + 260)
    (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word))))) := by
    runBlock hLI80 hsub ha7 hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 66: BLTU x11 x28 100 NOT taken (advanced ≤ end).  base+264 → base+268.
  have hb66 := bltu_spec_gen_within .x11 .x28 (100 : BitVec 13) endPtr
    (cp1 + (pfx - (0x80 : Word))) (base + 264)
  rw [show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hb66
  have hm66 : ∀ a i, CodeReq.singleton (base + 264) (.BLTU .x11 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr66 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb66))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_bound ((sepConj_pure_right _).1 h_pure).2)
  -- idx 67..68: LI x6 1 ; BNE x12 x6 16 NOT taken (len == 1).  base+268 → base+276.
  have hLI1 := li_spec_gen_within .x6 (0x80 : Word) (1 : Word) (base + 268) (by decide)
  have hm68 : ∀ a i, CodeReq.singleton (base + 272) (.BNE .x12 .x6 (16 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 68 (base + 272)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbne := bne_spec_gen_within .x12 .x6 (16 : BitVec 13) (pfx - (0x80 : Word)) (1 : Word)
    (base + 272)
  rw [show (base + 272 : Word) + 4 = base + 276 from by bv_omega] at hbne
  have hLI1blk : cpsTripleWithin 1 (base + 268) (base + 272) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))))
      ((.x6 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word)))) := by runBlock hLI1
  have hLI1blk' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x29 ↦ᵣ t4Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI1blk
  have hbr68 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm68 (cpsBranchWithin_frameR
      ((.x7 ↦ᵣ cp1) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbne))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 (by rw [h_len1]))
  -- idx 69..71: LBU x6 x7 0 (content[0]) ; LI x29 0x80 ; BLTU x6 x29 116 TAKEN.
  have hlbu := bytesRegion_lbu_within .x6 .x7 srcBase (1 : Word) (base + 276) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 hover1 hvalid1
  have hLI80b := li_spec_gen_within .x29 t4Old (0x80 : Word) (base + 280) (by decide)
  have hlbublk : cpsTripleWithin 2 (base + 276) (base + 284) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ cp1) ** (.x29 ↦ᵣ t4Old) ** bytesRegion srcBase srcBytes)
      ((.x6 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x7 ↦ᵣ cp1) **
        (.x29 ↦ᵣ (0x80 : Word)) ** bytesRegion srcBase srcBytes) := by
    runBlock hlbu hLI80b
  have hlbublk' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hlbublk
  have hb71 := bltu_spec_gen_within .x6 .x29 (116 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0x80 : Word) (base + 284)
  rw [show (base + 284) + signExtend13 (116 : BitVec 13) = base + 400 from by
        rw [show signExtend13 (116 : BitVec 13) = (116 : Word) from by decide]; bv_omega,
      show (base + 284 : Word) + 4 = base + 288 from by bv_omega] at hb71
  have hm71 : ∀ a i, CodeReq.singleton (base + 284) (.BLTU .x6 .x29 (116 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 71 (base + 284)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr71 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm71 (cpsBranchWithin_frameR
      ((.x7 ↦ᵣ cp1) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb71))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_content)
  have hfail := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x29 ↦ᵣ (0x80 : Word)) ** (.x7 ↦ᵣ cp1) **
      (.x5 ↦ᵣ pfx) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_noncanon_block base raVal endPtr (pfx - (0x80 : Word)))
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr66
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hLI1blk'
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3 hbr68
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c4 hlbublk'
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c5 hbr71
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c6 hfail
  rw [show (6 + 4 + 1 + 1 + 1 + 2 + 1 + 3) = 19 from rfl] at c7
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c7
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x29)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x5)
        (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (fun _ x => x) (fun _ x => x))))))) h hp
  xperm_hyp hp'

/-- The short-string accept tail `ss_ok` (idx 72..74), `base+288 → ra`:
    `a0 ← advanced`, `a1 = 0`. -/
private theorem wn_ss_ok_block (base raVal advanced cursorOld a1Old : Word) :
    cpsTripleWithin 3 (base + 288) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ advanced) ** (.x10 ↦ᵣ cursorOld) ** (.x11 ↦ᵣ a1Old) ** (.x1 ↦ᵣ raVal))
      ((.x28 ↦ᵣ advanced) ** (.x10 ↦ᵣ advanced) ** (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hmv := mv_spec_gen_within .x10 .x28 advanced cursorOld (base + 288) (by decide)
  have hLI0 := li_spec_gen_within .x11 a1Old (0 : Word) (base + 292) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 296)
  simp only [signExtend12_0] at hRet
  runBlock hmv hLI0 hRet

/-- **short string — accept, multi-byte** (`0x80 ≤ prefix < 0xb8`, `len ≠ 1`, span fits):
    `a2 = len = prefix - 0x80`, cursor advances by `1 + len`, `a1 = 0`. -/
theorem rlp_walk_next_short_string_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_bound : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 (srcOff + 1)) +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) = true)
    (hover1 : srcBase.toNat + (srcOff + 1) < 2 ^ 64)
    (h_lenne : ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)) ≠ (1 : Word)) :
    cpsTripleWithin 16 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 (srcOff + 1)) +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set cp1 := srcBase + BitVec.ofNat 64 (srcOff + 1) with hcp1
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 256) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha7
  have hadd := add_spec_gen_within .x28 .x7 .x12 cp1 (pfx - (0x80 : Word)) t3Old (base + 260)
    (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word))))) := by
    runBlock hLI80 hsub ha7 hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  have hb66 := bltu_spec_gen_within .x11 .x28 (100 : BitVec 13) endPtr
    (cp1 + (pfx - (0x80 : Word))) (base + 264)
  rw [show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hb66
  have hm66 : ∀ a i, CodeReq.singleton (base + 264) (.BLTU .x11 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr66 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb66))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_bound ((sepConj_pure_right _).1 h_pure).2)
  have hLI1 := li_spec_gen_within .x6 (0x80 : Word) (1 : Word) (base + 268) (by decide)
  have hLI1blk : cpsTripleWithin 1 (base + 268) (base + 272) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))))
      ((.x6 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word)))) := by runBlock hLI1
  have hLI1blk' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x29 ↦ᵣ t4Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI1blk
  -- idx 68: BNE x12 x6 16 TAKEN (len ≠ 1).  base+272 → base+288 (ss_ok).
  have hbne := bne_spec_gen_within .x12 .x6 (16 : BitVec 13) (pfx - (0x80 : Word)) (1 : Word)
    (base + 272)
  rw [show (base + 272) + signExtend13 (16 : BitVec 13) = base + 288 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 272 : Word) + 4 = base + 276 from by bv_omega] at hbne
  have hm68 : ∀ a i, CodeReq.singleton (base + 272) (.BNE .x12 .x6 (16 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 68 (base + 272)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr68 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm68 (cpsBranchWithin_frameR
      ((.x7 ↦ᵣ cp1) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbne))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact h_lenne ((sepConj_pure_right _).1 h_pure).2)
  have hok := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
      (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_ss_ok_block base raVal (cp1 + (pfx - (0x80 : Word)))
      (srcBase + BitVec.ofNat 64 srcOff) endPtr)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr66
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hLI1blk'
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3 hbr68
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c4 hok
  rw [show (6 + 4 + 1 + 1 + 1 + 3) = 16 from rfl] at c5
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c5
  have hp' := sepConj_mono
    (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x))
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x)))))) h hp
  xperm_hyp hp'

/-- **short string — accept, canonical single byte** (`prefix = 0x81`, `content[0] ≥ 0x80`,
    span fits): `a2 = 1`, cursor advances by `2`, `a1 = 0`. -/
theorem rlp_walk_next_short_string_single_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64) (hover1 : srcBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_bound : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 (srcOff + 1)) +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) = true)
    (h_len1 : (srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word))
    (h_content : ¬ BitVec.ult ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0x80 : Word) = true) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 (srcOff + 1)) +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set cp1 := srcBase + BitVec.ofNat 64 (srcOff + 1) with hcp1
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 256) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha7
  have hadd := add_spec_gen_within .x28 .x7 .x12 cp1 (pfx - (0x80 : Word)) t3Old (base + 260)
    (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word))))) := by
    runBlock hLI80 hsub ha7 hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  have hb66 := bltu_spec_gen_within .x11 .x28 (100 : BitVec 13) endPtr
    (cp1 + (pfx - (0x80 : Word))) (base + 264)
  rw [show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hb66
  have hm66 : ∀ a i, CodeReq.singleton (base + 264) (.BLTU .x11 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr66 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb66))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_bound ((sepConj_pure_right _).1 h_pure).2)
  have hLI1 := li_spec_gen_within .x6 (0x80 : Word) (1 : Word) (base + 268) (by decide)
  have hLI1blk : cpsTripleWithin 1 (base + 268) (base + 272) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))))
      ((.x6 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word)))) := by runBlock hLI1
  have hLI1blk' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x29 ↦ᵣ t4Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI1blk
  have hbne := bne_spec_gen_within .x12 .x6 (16 : BitVec 13) (pfx - (0x80 : Word)) (1 : Word)
    (base + 272)
  rw [show (base + 272 : Word) + 4 = base + 276 from by bv_omega] at hbne
  have hm68 : ∀ a i, CodeReq.singleton (base + 272) (.BNE .x12 .x6 (16 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 68 (base + 272)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr68 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm68 (cpsBranchWithin_frameR
      ((.x7 ↦ᵣ cp1) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbne))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 (by rw [h_len1]))
  have hlbu := bytesRegion_lbu_within .x6 .x7 srcBase (1 : Word) (base + 276) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 hover1 hvalid1
  have hLI80b := li_spec_gen_within .x29 t4Old (0x80 : Word) (base + 280) (by decide)
  have hlbublk : cpsTripleWithin 2 (base + 276) (base + 284) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ cp1) ** (.x29 ↦ᵣ t4Old) ** bytesRegion srcBase srcBytes)
      ((.x6 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x7 ↦ᵣ cp1) **
        (.x29 ↦ᵣ (0x80 : Word)) ** bytesRegion srcBase srcBytes) := by
    runBlock hlbu hLI80b
  have hlbublk' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hlbublk
  -- idx 71: BLTU x6 x29 116 NOT taken (content[0] ≥ 0x80).  base+284 → base+288 (ss_ok).
  have hb71 := bltu_spec_gen_within .x6 .x29 (116 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0x80 : Word) (base + 284)
  rw [show (base + 284 : Word) + 4 = base + 288 from by bv_omega] at hb71
  have hm71 : ∀ a i, CodeReq.singleton (base + 284) (.BLTU .x6 .x29 (116 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 71 (base + 284)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr71 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm71 (cpsBranchWithin_frameR
      ((.x7 ↦ᵣ cp1) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x28 ↦ᵣ (cp1 + (pfx - (0x80 : Word)))) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb71))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_content ((sepConj_pure_right _).1 h_pure).2)
  have hok := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x5 ↦ᵣ pfx) **
      (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) ** (.x29 ↦ᵣ (0x80 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_ss_ok_block base raVal (cp1 + (pfx - (0x80 : Word)))
      (srcBase + BitVec.ofNat 64 srcOff) endPtr)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr66
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hLI1blk'
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3 hbr68
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c4 hlbublk'
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c5 hbr71
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c6 hok
  rw [show (6 + 4 + 1 + 1 + 1 + 2 + 1 + 3) = 19 from rfl] at c7
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c7
  have hp' := sepConj_mono
    (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x))
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x)))))) h hp
  xperm_hyp hp'

end EvmAsm.Rv64.RLP
