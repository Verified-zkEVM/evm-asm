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

end EvmAsm.Rv64.RLP
