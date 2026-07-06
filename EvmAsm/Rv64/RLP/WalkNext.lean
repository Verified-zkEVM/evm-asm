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

  ## Verification status

  All 18 per-form execution paths are proved as complete leaf-function `cpsTripleWithin`
  Hoare triples (axiom-clean: `propext`/`Classical.choice`/`Quot.sound` only):
    * end-of-list; single byte;
    * short string — accept (multi-byte), accept (canonical single), bound, non-canonical;
    * long string — accept, header-bound, leading-zero, non-minimal, content-bound;
    * short list — accept, bound;
    * long list — accept, header-bound, leading-zero, non-minimal, content-bound.
  The two big-endian length loops are proved by induction (`wn_ls_loop`/`wn_ll_loop`).
  Together these per-form triples establish correctness of the strict body on every
  input: each reachable execution path is a proved leaf-function triple, so the program
  advances/rejects exactly as specified for every prefix byte and every check outcome.

  These are combined into a single unified dispatch theorem `rlp_walk_next_spec_within`
  (bound `87`): from the common static preconditions it lands in exactly one of six
  outcomes distinguished by the status `a1` (`0/2/3/4/5/6`). The `a1 = 0` (ok) outcome is
  the single pure predicate `rlpWalkNextOk` relating the advanced cursor `a0` and reported
  length `a2` to the prefix-indicated decode (`rlpItemDecode`); the long-form decode also
  certifies canonical length encoding (no leading `0x00`, decoded length `≥ 56`) and the
  short-form decode the single-byte rule (a 1-byte string's content is `≥ 0x80`).
  The canonicality-reject outcomes (`a1 = 4` non-minimal, `5` leading-zero, `6` single-byte
  non-canonical) additionally carry `⌜¬ ∃ next len, rlpItemDecode …⌝`: no canonical RLP item
  decodes at the cursor. (The `a1 = 3` bound outcome is a fit failure, not a decode failure —
  a canonical item may decode but run past `end` — so it carries no decode negation.)
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
    .SUB .x6 .x11 .x29,                   -- 31 avail2 = end - header_end
    .BLTU .x6 .x28 (236 : BitVec 13),     -- 32 avail2 < decoded -> bound (idx 91); fits iff decoded <= avail2
    .ADD .x10 .x31 .x10,                  -- 33 advanced cursor = span + cursor
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
    .SUB .x6 .x11 .x29,                   -- 56 avail2 = end - header_end
    .BLTU .x6 .x28 (136 : BitVec 13),     -- 57 avail2 < decoded -> bound (idx 91); fits iff decoded <= avail2
    .ADD .x10 .x29 .x28,                  -- 58 advanced cursor = header_end + decoded
    .MV .x12 .x28,                        -- 59 content length = decoded
    .LI .x11 (0 : Word),                  -- 60
    .JALR .x0 .x1 0,                      -- 61 ret
    .LI .x6 (0x80 : Word),                -- 62 short string
    .SUB .x12 .x5 .x6,                    -- 63 len = prefix - 0x80
    .ADDI .x7 .x10 (1 : BitVec 12),       -- 64 content start = cursor + 1
    .SUB .x28 .x11 .x10,                  -- 65 avail = end - cursor
    .BGEU .x12 .x28 (100 : BitVec 13),    -- 66 len >= avail -> bound (idx 91); fits iff len < avail
    .LI .x6 (1 : Word),                   -- 67
    .BNE .x12 .x6 (16 : BitVec 13),       -- 68 len != 1 -> ss_ok (idx 72)
    .LBU .x6 .x7 0,                       -- 69 content[0]
    .LI .x29 (0x80 : Word),               -- 70
    .BLTU .x6 .x29 (116 : BitVec 13),     -- 71 content[0] < 0x80 -> noncanon (idx 100)
    .ADD .x10 .x7 .x12,                   -- 72 ss_ok: advanced cursor = content start + len
    .LI .x11 (0 : Word),                  -- 73
    .JALR .x0 .x1 0,                      -- 74 ret
    .ADDI .x10 .x10 (1 : BitVec 12),      -- 75 single: advanced cursor
    .LI .x12 (1 : Word),                  -- 76 content length = 1
    .LI .x11 (0 : Word),                  -- 77
    .JALR .x0 .x1 0,                      -- 78 ret
    .LI .x6 (0xc0 : Word),                -- 79 short list
    .SUB .x31 .x5 .x6,                    -- 80 prefix - 0xc0
    .ADDI .x31 .x31 (1 : BitVec 12),      -- 81 full span = 1 + (prefix - 0xc0)
    .SUB .x6 .x11 .x10,                   -- 82 avail = end - cursor
    .BLTU .x6 .x31 (32 : BitVec 13),      -- 83 avail < span -> bound (idx 91); fits iff span <= avail
    .ADD .x10 .x31 .x10,                  -- 84 advanced cursor = span + cursor
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
    (h_bound : ¬ BitVec.ult (endPtr - (srcBase + BitVec.ofNat 64 srcOff))
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) = true) :
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
  set cur := srcBase + BitVec.ofNat 64 srcOff with hcur
  have hcasc := wn_to_short_list base srcBase endPtr a2Old t0Old t1Old t6Old srcBytes srcOff
    hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  -- idx 79..82: LI x6 0xc0 ; SUB x31 ; ADDI x31 ; SUB x6 x11 x10 (avail in x6).
  have hLIc := li_spec_gen_within .x6 (0xf8 : Word) (0xc0 : Word) (base + 316) (by decide)
  have hsub := sub_spec_gen_within .x31 .x5 .x6 pfx (0xc0 : Word) t6Old (base + 320) (by decide)
  have haddi := addi_spec_gen_same_within .x31 (pfx - (0xc0 : Word)) (1 : BitVec 12) (base + 324)
    (by decide)
  rw [← hspan] at haddi
  have hsubA := sub_spec_gen_within .x6 .x11 .x10 endPtr cur (0xc0 : Word) (base + 328) (by decide)
  have hblk : cpsTripleWithin 4 (base + 316) (base + 332) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ t6Old) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur))
      ((.x6 ↦ᵣ (endPtr - cur)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur)) := by
    runBlock hLIc hsub haddi hsubA
  have hblk' := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 83: BLTU x6 x31 32 NOT taken (avail ≥ span).  base+332 → base+336.
  have hbltu := bltu_spec_gen_within .x6 .x31 (32 : BitVec 13) (endPtr - cur) span (base + 332)
  rw [show (base + 332 : Word) + 4 = base + 336 from by bv_omega] at hbltu
  have hmono83 : ∀ a i, CodeReq.singleton (base + 332) (.BLTU .x6 .x31 (32 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 83 (base + 332)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono83 (cpsBranchWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_bound ((sepConj_pure_right _).1 h_pure).2)
  -- idx 84..87: ADD x10 x31 x10 ; MV x12 x31 ; LI x11 0 ; ret.  base+336 → ra.
  have hadd10 := add_spec_gen_rd_eq_rs2_within .x10 .x31 span cur (base + 336) (by decide)
  have hmv12 := mv_spec_gen_within .x12 .x31 span a2Old (base + 340) (by decide)
  have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 344) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 348)
  simp only [signExtend12_0] at hRet
  have hret : cpsTripleWithin 4 (base + 336) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x31 ↦ᵣ span) ** (.x10 ↦ᵣ cur) ** (.x12 ↦ᵣ a2Old) **
        (.x11 ↦ᵣ endPtr) ** (.x1 ↦ᵣ raVal))
      ((.x31 ↦ᵣ span) ** (.x10 ↦ᵣ (span + cur)) ** (.x12 ↦ᵣ span) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hadd10 hmv12 hLI11 hRet
  have hret' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (endPtr - cur)) ** (.x5 ↦ᵣ pfx) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hret
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hret'
  rw [show (10 + 4 + 1 + 4) = 19 from rfl] at c3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c3
  rw [show cur + span = span + cur from by bv_omega]
  have hp' := sepConj_mono
    (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x))
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5) (fun _ x => x)))
    h hp
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
    (h_bound : BitVec.ult (endPtr - (srcBase + BitVec.ofNat 64 srcOff))
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) = true) :
    cpsTripleWithin 18 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set span := (pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12) with hspan
  set cur := srcBase + BitVec.ofNat 64 srcOff with hcur
  have hcasc := wn_to_short_list base srcBase endPtr a2Old t0Old t1Old t6Old srcBytes srcOff
    hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLIc := li_spec_gen_within .x6 (0xf8 : Word) (0xc0 : Word) (base + 316) (by decide)
  have hsub := sub_spec_gen_within .x31 .x5 .x6 pfx (0xc0 : Word) t6Old (base + 320) (by decide)
  have haddi := addi_spec_gen_same_within .x31 (pfx - (0xc0 : Word)) (1 : BitVec 12) (base + 324)
    (by decide)
  rw [← hspan] at haddi
  have hsubA := sub_spec_gen_within .x6 .x11 .x10 endPtr cur (0xc0 : Word) (base + 328) (by decide)
  have hblk : cpsTripleWithin 4 (base + 316) (base + 332) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ t6Old) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur))
      ((.x6 ↦ᵣ (endPtr - cur)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur)) := by
    runBlock hLIc hsub haddi hsubA
  have hblk' := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 83: BLTU x6 x31 32 TAKEN (avail < span).  base+332 → base+364 (bound).
  have hbltu := bltu_spec_gen_within .x6 .x31 (32 : BitVec 13) (endPtr - cur) span (base + 332)
  rw [show (base + 332) + signExtend13 (32 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega,
      show (base + 332 : Word) + 4 = base + 336 from by bv_omega] at hbltu
  have hmono83 : ∀ a i, CodeReq.singleton (base + 332) (.BLTU .x6 .x31 (32 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 83 (base + 332)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono83 (cpsBranchWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_bound)
  have hfail := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (endPtr - cur)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ span) **
      (.x10 ↦ᵣ cur) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
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
    (h_bound : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true) :
    cpsTripleWithin 14 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set cur := srcBase + BitVec.ofNat 64 srcOff with hcur
  set cst := cur + signExtend12 (1 : BitVec 12) with hcst
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  -- idx 62..65: LI x6 0x80 ; SUB x12 ; ADDI x7 (content start) ; SUB x28 (avail).
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old cur (1 : BitVec 12) (base + 256) (by decide)
  rw [← hcst] at ha7
  have hsubA := sub_spec_gen_within .x28 .x11 .x10 endPtr cur t3Old (base + 260) (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cst) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cur) ** (.x28 ↦ᵣ (endPtr - cur))) := by
    runBlock hLI80 hsub ha7 hsubA
  have hblk' := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 66: BGEU x12 x28 100 TAKEN (len ≥ avail).  base+264 → base+364 (bound).
  have hbge := bgeu_spec_gen_within .x12 .x28 (100 : BitVec 13) (pfx - (0x80 : Word))
    (endPtr - cur) (base + 264)
  rw [show (base + 264) + signExtend13 (100 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]; bv_omega,
      show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hbge
  have hmono66 : ∀ a i, CodeReq.singleton (base + 264) (.BGEU .x12 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cst) ** (.x11 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ cur) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbge))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact h_bound ((sepConj_pure_right _).1 h_pure).2)
  have hfail := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (endPtr - cur)) ** (.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ cst) ** (.x10 ↦ᵣ cur) **
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
    (h_bound : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true)
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
  set avail := endPtr - (srcBase + BitVec.ofNat 64 srcOff) with havail
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  -- idx 62..65: LI x6 0x80 ; SUB x12 (len) ; ADDI x7 (content ptr) ; SUB x28 (avail).
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 256) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha7
  have hsubA := sub_spec_gen_within .x28 .x11 .x10 endPtr (srcBase + BitVec.ofNat 64 srcOff) t3Old
    (base + 260) (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ avail)) := by
    runBlock hLI80 hsub ha7 hsubA
  have hblk' := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 66: BGEU x12 x28 100 NOT taken (len < avail).  base+264 → base+268.
  have hb66 := bgeu_spec_gen_within .x12 .x28 (100 : BitVec 13) (pfx - (0x80 : Word)) avail (base + 264)
  rw [show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hb66
  have hm66 : ∀ a i, CodeReq.singleton (base + 264) (.BGEU .x12 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr66 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x11 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb66))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 h_bound)
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
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x29 ↦ᵣ t4Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI1blk
  have hbr68 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm68 (cpsBranchWithin_frameR
      ((.x7 ↦ᵣ cp1) ** (.x5 ↦ᵣ pfx) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x29 ↦ᵣ t4Old) **
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
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x0 ↦ᵣ (0 : Word)) **
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
        (.x28 ↦ᵣ avail) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb71))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_content)
  have hfail := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x29 ↦ᵣ (0x80 : Word)) ** (.x7 ↦ᵣ cp1) **
      (.x5 ↦ᵣ pfx) ** (.x28 ↦ᵣ avail) **
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
    `a0 ← content_start + len` (= advanced), `a1 = 0`. -/
private theorem wn_ss_ok_block (base raVal contentStart len cursorOld a1Old : Word) :
    cpsTripleWithin 3 (base + 288) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x7 ↦ᵣ contentStart) ** (.x12 ↦ᵣ len) ** (.x10 ↦ᵣ cursorOld) ** (.x11 ↦ᵣ a1Old) **
        (.x1 ↦ᵣ raVal))
      ((.x7 ↦ᵣ contentStart) ** (.x12 ↦ᵣ len) ** (.x10 ↦ᵣ (contentStart + len)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hadd := add_spec_gen_within .x10 .x7 .x12 contentStart len cursorOld (base + 288) (by decide)
  have hLI0 := li_spec_gen_within .x11 a1Old (0 : Word) (base + 292) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 296)
  simp only [signExtend12_0] at hRet
  runBlock hadd hLI0 hRet

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
    (h_bound : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true)
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
  set avail := endPtr - (srcBase + BitVec.ofNat 64 srcOff) with havail
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 256) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha7
  have hsubA := sub_spec_gen_within .x28 .x11 .x10 endPtr (srcBase + BitVec.ofNat 64 srcOff) t3Old
    (base + 260) (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ avail)) := by
    runBlock hLI80 hsub ha7 hsubA
  have hblk' := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  have hb66 := bgeu_spec_gen_within .x12 .x28 (100 : BitVec 13) (pfx - (0x80 : Word)) avail (base + 264)
  rw [show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hb66
  have hm66 : ∀ a i, CodeReq.singleton (base + 264) (.BGEU .x12 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr66 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x11 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb66))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 h_bound)
  have hLI1 := li_spec_gen_within .x6 (0x80 : Word) (1 : Word) (base + 268) (by decide)
  have hLI1blk : cpsTripleWithin 1 (base + 268) (base + 272) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))))
      ((.x6 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word)))) := by runBlock hLI1
  have hLI1blk' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x29 ↦ᵣ t4Old) **
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
        (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbne))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact h_lenne ((sepConj_pure_right _).1 h_pure).2)
  have hok := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x28 ↦ᵣ avail) **
      (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_ss_ok_block base raVal cp1 (pfx - (0x80 : Word))
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
    (sepConj_mono (regIs_implies_regOwn .x7) (fun _ x => x))
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
        (fun _ x => x))))) h hp
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
    (h_bound : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true)
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
  set avail := endPtr - (srcBase + BitVec.ofNat 64 srcOff) with havail
  have hcasc := wn_to_short_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old srcBytes
    srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 248) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 pfx (0x80 : Word) a2Old (base + 252) (by decide)
  have ha7 := addi_spec_gen_within .x7 .x10 t2Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 256) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha7
  have hsubA := sub_spec_gen_within .x28 .x11 .x10 endPtr (srcBase + BitVec.ofNat 64 srcOff) t3Old
    (base + 260) (by decide)
  have hblk : cpsTripleWithin 4 (base + 248) (base + 264) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ t3Old))
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))) ** (.x7 ↦ᵣ cp1) **
        (.x11 ↦ᵣ endPtr) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ avail)) := by
    runBlock hLI80 hsub ha7 hsubA
  have hblk' := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hblk
  have hb66 := bgeu_spec_gen_within .x12 .x28 (100 : BitVec 13) (pfx - (0x80 : Word)) avail (base + 264)
  rw [show (base + 264 : Word) + 4 = base + 268 from by bv_omega] at hb66
  have hm66 : ∀ a i, CodeReq.singleton (base + 264) (.BGEU .x12 .x28 (100 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 66 (base + 264)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr66 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm66 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x11 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb66))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 h_bound)
  have hLI1 := li_spec_gen_within .x6 (0x80 : Word) (1 : Word) (base + 268) (by decide)
  have hLI1blk : cpsTripleWithin 1 (base + 268) (base + 272) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0x80 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word))))
      ((.x6 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (pfx - (0x80 : Word)))) := by runBlock hLI1
  have hLI1blk' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x29 ↦ᵣ t4Old) **
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
        (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x29 ↦ᵣ t4Old) **
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
      (.x11 ↦ᵣ endPtr) ** (.x28 ↦ᵣ avail) ** (.x0 ↦ᵣ (0 : Word)) **
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
        (.x28 ↦ᵣ avail) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb71))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_content ((sepConj_pure_right _).1 h_pure).2)
  have hok := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x5 ↦ᵣ pfx) **
      (.x28 ↦ᵣ avail) ** (.x29 ↦ᵣ (0x80 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_ss_ok_block base raVal cp1 (pfx - (0x80 : Word))
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
    (sepConj_mono (regIs_implies_regOwn .x7) (fun _ x => x))
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
        (fun _ x => x))))) h hp
  xperm_hyp hp'

/-- One iteration of the long-string length loop (idx 48..52), `base+192 → base+212`.
    Count register is `x6` (the strict prog keeps `header_end` in `x29`). -/
theorem wn_ls_body (base srcBase x28Old x31Old x6Val : Word) (srcBytes : List (BitVec 8)) (si : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hsi : si < srcBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true) :
    cpsTripleWithin 5 (base + 192) (base + 212) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ x28Old) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x31 ↦ᵣ x31Old) **
       (.x6 ↦ᵣ x6Val) ** bytesRegion srcBase srcBytes)
      ((.x28 ↦ᵣ ((x28Old <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi))) **
       (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi)) **
       (.x6 ↦ᵣ (x6Val + signExtend12 (-1 : BitVec 12))) ** bytesRegion srcBase srcBytes) := by
  have hslli := slli_spec_gen_same_within .x28 x28Old (8 : BitVec 6) (base + 192) (by nofun)
  rw [show (8 : BitVec 6).toNat = 8 from by decide] at hslli
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase x31Old (base + 196) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have hor := or_spec_gen_rd_eq_rs1_within .x28 .x31 (x28Old <<< (8 : Nat))
    (BitVec.setWidth 64 (srcBytes[si]'hsi)) (base + 200) (by nofun)
  have ha30 := addi_spec_gen_same_within .x30 (srcBase + BitVec.ofNat 64 si) 1 (base + 204) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have ha6 := addi_spec_gen_same_within .x6 x6Val (-1 : BitVec 12) (base + 208) (by nofun)
  runBlock hslli hlbu hor ha30 ha6

set_option maxRecDepth 8000 in
/-- The long-string length loop (idx 47..53), `base+188 → base+216`, by induction.
    Count register is `x6`. -/
theorem wn_ls_loop (base srcBase x31Old : Word) (srcBytes pre : List (BitVec 8)) (si n : Nat)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hbound : pre.length + n ≤ 8)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 188) (base + 216) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ BitVec.ofNat 64 n) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))) **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 188) (.BEQ .x6 .x0 (28 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 47 (base + 188)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have ha_t : (base + 188) + signExtend13 (28 : BitVec 13) = base + 216 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 188 : Word) + 4 = base + 192 := by bv_omega
  induction n generalizing si pre x31Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 188)
    rw [ha_t, ha_f] at hbeq
    have htaken := cpsBranchWithin_takenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htaken
    rw [show (0#64 : Word) = 0 from by decide] at hq
    simp only [Nat.add_zero, List.take_zero, List.append_nil]
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    have hq2 := sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x31)))) h hq1
    xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 188)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hsi0 : si < srcBytes.length := by omega
    have hprelt : Nat.fromBytesBE pre < 2 ^ 56 := by
      have := Nat.fromBytesBE_lt pre
      have hpl : pre.length ≤ 7 := by omega
      calc Nat.fromBytesBE pre < 256 ^ pre.length := this
        _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hpl
        _ = 2 ^ 56 := by norm_num
    have hx28tn : (BitVec.ofNat 64 (Nat.fromBytesBE pre)).toNat = Nat.fromBytesBE pre := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have body := wn_ls_body base srcBase (BitVec.ofNat 64 (Nat.fromBytesBE pre)) x31Old
      (BitVec.ofNat 64 (k + 1)) srcBytes si hsalign hsi0 (by omega) (hsvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have hbnd : Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 2 ^ 64 := by
      have h := Nat.fromBytesBE_lt (pre ++ [srcBytes[si]'hsi0])
      simp only [List.length_append, List.length_singleton] at h
      calc Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 256 ^ (pre.length + 1) := h
        _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 64 := by norm_num
    have hacc : ((BitVec.ofNat 64 (Nat.fromBytesBE pre) <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi0))
        = BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0])) := by
      apply BitVec.eq_of_toNat_eq
      rw [cu64_step _ _ (by rw [hx28tn]; exact hprelt), hx28tn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbnd, Nat.fromBytesBE_snoc]
    rw [hacc] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 212)
    have ha_back : (base + 212) + signExtend21 (-24 : BitVec 21) = base + 188 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 212) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_walk_next_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 53 (base + 212)
        (by rw [rlp_walk_next_prog_length]; norm_num)
        (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 212) (base + 188) (rlp_walk_next_code base)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
           (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
          (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k → isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have ihspec := ih (si := si + 1) (pre := pre ++ [srcBytes[si]'hsi0])
      (x31Old := BitVec.setWidth 64 (srcBytes[si]'hsi0)) (by omega) (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega) hsvalid'
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hA1 body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hslice : pre ++ (srcBytes.drop si).take (k + 1)
        = (pre ++ [srcBytes[si]'hsi0]) ++ (srcBytes.drop (si + 1)).take k := by
      rw [List.drop_eq_getElem_cons hsi0, List.take_succ_cons, List.append_assoc,
        List.singleton_append]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega, hslice]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s1234

/-- One iteration of the long-list length loop (idx 21..25), `base+84 → base+104`.
    Count register is `x6`. -/
theorem wn_ll_body (base srcBase x28Old x31Old x6Val : Word) (srcBytes : List (BitVec 8)) (si : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hsi : si < srcBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true) :
    cpsTripleWithin 5 (base + 84) (base + 104) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ x28Old) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x31 ↦ᵣ x31Old) **
       (.x6 ↦ᵣ x6Val) ** bytesRegion srcBase srcBytes)
      ((.x28 ↦ᵣ ((x28Old <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi))) **
       (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi)) **
       (.x6 ↦ᵣ (x6Val + signExtend12 (-1 : BitVec 12))) ** bytesRegion srcBase srcBytes) := by
  have hslli := slli_spec_gen_same_within .x28 x28Old (8 : BitVec 6) (base + 84) (by nofun)
  rw [show (8 : BitVec 6).toNat = 8 from by decide] at hslli
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase x31Old (base + 88) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have hor := or_spec_gen_rd_eq_rs1_within .x28 .x31 (x28Old <<< (8 : Nat))
    (BitVec.setWidth 64 (srcBytes[si]'hsi)) (base + 92) (by nofun)
  have ha30 := addi_spec_gen_same_within .x30 (srcBase + BitVec.ofNat 64 si) 1 (base + 96) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have ha6 := addi_spec_gen_same_within .x6 x6Val (-1 : BitVec 12) (base + 100) (by nofun)
  runBlock hslli hlbu hor ha30 ha6

set_option maxRecDepth 8000 in
/-- The long-list length loop (idx 20..26), `base+80 → base+108`, by induction.
    Count register is `x6`. -/
theorem wn_ll_loop (base srcBase x31Old : Word) (srcBytes pre : List (BitVec 8)) (si n : Nat)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hbound : pre.length + n ≤ 8)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 80) (base + 108) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ BitVec.ofNat 64 n) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))) **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 80) (.BEQ .x6 .x0 (28 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 20 (base + 80)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have ha_t : (base + 80) + signExtend13 (28 : BitVec 13) = base + 108 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 80 : Word) + 4 = base + 84 := by bv_omega
  induction n generalizing si pre x31Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 80)
    rw [ha_t, ha_f] at hbeq
    have htaken := cpsBranchWithin_takenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htaken
    rw [show (0#64 : Word) = 0 from by decide] at hq
    simp only [Nat.add_zero, List.take_zero, List.append_nil]
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    have hq2 := sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x31)))) h hq1
    xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 80)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hsi0 : si < srcBytes.length := by omega
    have hprelt : Nat.fromBytesBE pre < 2 ^ 56 := by
      have := Nat.fromBytesBE_lt pre
      have hpl : pre.length ≤ 7 := by omega
      calc Nat.fromBytesBE pre < 256 ^ pre.length := this
        _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hpl
        _ = 2 ^ 56 := by norm_num
    have hx28tn : (BitVec.ofNat 64 (Nat.fromBytesBE pre)).toNat = Nat.fromBytesBE pre := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have body := wn_ll_body base srcBase (BitVec.ofNat 64 (Nat.fromBytesBE pre)) x31Old
      (BitVec.ofNat 64 (k + 1)) srcBytes si hsalign hsi0 (by omega) (hsvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have hbnd : Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 2 ^ 64 := by
      have h := Nat.fromBytesBE_lt (pre ++ [srcBytes[si]'hsi0])
      simp only [List.length_append, List.length_singleton] at h
      calc Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 256 ^ (pre.length + 1) := h
        _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 64 := by norm_num
    have hacc : ((BitVec.ofNat 64 (Nat.fromBytesBE pre) <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi0))
        = BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0])) := by
      apply BitVec.eq_of_toNat_eq
      rw [cu64_step _ _ (by rw [hx28tn]; exact hprelt), hx28tn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbnd, Nat.fromBytesBE_snoc]
    rw [hacc] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 104)
    have ha_back : (base + 104) + signExtend21 (-24 : BitVec 21) = base + 80 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 104) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_walk_next_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 26 (base + 104)
        (by rw [rlp_walk_next_prog_length]; norm_num)
        (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 104) (base + 80) (rlp_walk_next_code base)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
           (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
          (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k → isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have ihspec := ih (si := si + 1) (pre := pre ++ [srcBytes[si]'hsi0])
      (x31Old := BitVec.setWidth 64 (srcBytes[si]'hsi0)) (by omega) (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega) hsvalid'
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hA1 body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hslice : pre ++ (srcBytes.drop si).take (k + 1)
        = (pre ++ [srcBytes[si]'hsi0]) ++ (srcBytes.drop (si + 1)).take k := by
      rw [List.drop_eq_getElem_cons hsi0, List.take_succ_cons, List.append_assoc,
        List.singleton_append]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega, hslice]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s1234

/-- Cascade to the long-string block (idx 0..7), `base → base+148` (idx 37).
    `0xb8 ≤ prefix < 0xc0`. Leaves `x5 = prefix`, `x6 = 0xc0`. -/
private theorem wn_to_long_string (base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) (raVal : Word)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 8 base (base + 148) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      (((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xc0 : Word))) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
          (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)) := by
  have h_lo80 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0x80 : Word).toNat = 128 from by decide,
      show (0xb8 : Word).toNat = 184 from by decide] at h_lo ⊢
    omega
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  have hB := wn_lbu_li80 base srcBase srcBytes srcOff t0Old t1Old hsalign hoff hover hvalid
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  let F : Assertion := (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
    (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
    (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes
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
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo)
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
  have hbltu := bltu_spec_gen_within .x5 .x6 (120 : BitVec 13) pfx (0xc0 : Word) (base + 28)
  rw [show (base + 28) + signExtend13 (120 : BitVec 13) = base + 148 from by
        rw [show signExtend13 (120 : BitVec 13) = (120 : Word) from by decide]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbltu
  have hmonoG : ∀ a i, CodeReq.singleton (base + 28) (.BLTU .x5 .x6 (120 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 7 (base + 28)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hG := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmonoG (cpsBranchWithin_frameR F (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hi)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hE
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hF2
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hG
  rw [show (1 + 2 + 1 + 1 + 1 + 1 + 1) = 8 from rfl] at s6
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s6

/-- **long string — header bound** (`0xb8 ≤ prefix < 0xc0`, `1 + lol` runs past `end`):
    the length field doesn't fit → `a1 = 3`. -/
theorem rlp_walk_next_long_string_header_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hdr : BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) = true) :
    cpsTripleWithin 16 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set lol1 := (pfx - (0xb7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  have hcasc := wn_to_long_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI := li_spec_gen_within .x6 (0xc0 : Word) (0xb7 : Word) (base + 148) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xb7 : Word) t2Old (base + 152) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xb7 : Word) (pfx - (0xb7 : Word)) (1 : BitVec 12)
    (base + 156) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 160) (by decide)
  have hblk : cpsTripleWithin 4 (base + 148) (base + 164) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1))) := by
    runBlock hLI hsub haddi hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 41: BLTU x11 x29 200 TAKEN (header > end).  base+164 → base+364 (bound).
  have hbltu := bltu_spec_gen_within .x11 .x29 (200 : BitVec 13) endPtr
    ((srcBase + BitVec.ofNat 64 srcOff) + lol1) (base + 164)
  rw [show (base + 164) + signExtend13 (200 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (200 : BitVec 13) = (200 : Word) from by decide]; bv_omega,
      show (base + 164 : Word) + 4 = base + 168 from by bv_omega] at hbltu
  have hmono41 : ∀ a i, CodeReq.singleton (base + 164) (.BLTU .x11 .x29 (200 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 41 (base + 164)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono41 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hdr)
  have hfail := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes) (by pcFree) (wn_bound_block base raVal endPtr a2Old)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hfail
  rw [show (8 + 4 + 1 + 3) = 16 from rfl] at c3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c3
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
            (fun _ x => x))))))))) h hp
  xperm_hyp hp'

/-- The leading-zero fail block (idx 97..99), `base+388 → ra`: `a1 = 5`. -/
private theorem wn_lz_block (base raVal a1Old a2Old : Word) :
    cpsTripleWithin 3 (base + 388) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (5 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hLI5 := li_spec_gen_within .x11 a1Old (5 : Word) (base + 388) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 392) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 396)
  simp only [signExtend12_0] at hRet
  runBlock hLI5 hLI0 hRet

/-- **long string — leading zero** (`0xb8 ≤ prefix < 0xc0`, header fits, `len[0] = 0`):
    non-canonical length field → `a1 = 5`. -/
theorem rlp_walk_next_long_string_lz_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64) (hover1 : srcBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_lz : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 = (0 : Word)) :
    cpsTripleWithin 19 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set lol1 := (pfx - (0xb7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set cp1 := srcBase + BitVec.ofNat 64 (srcOff + 1) with hcp1
  have hcasc := wn_to_long_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI := li_spec_gen_within .x6 (0xc0 : Word) (0xb7 : Word) (base + 148) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xb7 : Word) t2Old (base + 152) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xb7 : Word) (pfx - (0xb7 : Word)) (1 : BitVec 12)
    (base + 156) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 160) (by decide)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 168) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 172) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 hover1 hvalid1
  have hblk : cpsTripleWithin 4 (base + 148) (base + 164) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1))) := by
    runBlock hLI hsub haddi hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk
  -- idx 41: BLTU x11 x29 200 NOT taken (header fits).  base+164 → base+168.
  have hb41 := bltu_spec_gen_within .x11 .x29 (200 : BitVec 13) endPtr
    ((srcBase + BitVec.ofNat 64 srcOff) + lol1) (base + 164)
  rw [show (base + 164 : Word) + 4 = base + 168 from by bv_omega] at hb41
  have hm41 : ∀ a i, CodeReq.singleton (base + 164) (.BLTU .x11 .x29 (200 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 41 (base + 164)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr41 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm41 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb41))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  -- idx 42..43: ADDI x30 x10 1 (length-field ptr) ; LBU x31 x30 0 (first byte).
  have hptrblk : cpsTripleWithin 2 (base + 168) (base + 176) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  -- idx 44: BEQ x31 x0 212 TAKEN (first byte == 0).  base+176 → base+388 (lz).
  have hbeq := beq_spec_gen_within .x31 .x0 (212 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 176)
  rw [show (base + 176) + signExtend13 (212 : BitVec 13) = base + 388 from by
        rw [show signExtend13 (212 : BitVec 13) = (212 : Word) from by decide]; bv_omega,
      show (base + 176 : Word) + 4 = base + 180 from by bv_omega] at hbeq
  have hm44 : ∀ a i, CodeReq.singleton (base + 176) (.BEQ .x31 .x0 (212 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 44 (base + 176)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr44 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm44 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) **
        (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbeq))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by rw [h_lz]))
  have hfail := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x30 ↦ᵣ cp1) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_lz_block base raVal endPtr a2Old)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr41
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hptrblk'
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3 hbr44
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c4 hfail
  rw [show (8 + 4 + 1 + 2 + 1 + 3) = 19 from rfl] at c5
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c5
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x31) (sepConj_mono (regIs_implies_regOwn .x30)
      (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
          (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x28)
            (fun _ x => x))))))))) h hp
  xperm_hyp hp'

set_option maxRecDepth 8000 in
/-- **long string — accept** (`0xb8 ≤ prefix < 0xc0`, header fits, `len[0] ≠ 0`,
    `decoded ≥ 56`, content fits): `a2 = decoded` (stripped), cursor advances to
    `header_end + decoded`, `a1 = 0`. -/
theorem rlp_walk_next_long_string_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) (56 : Word) = true)
    (h_content : ¬ BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat + 27) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) +
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xb7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  set lol1 := (pfx - (0xb7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set hend := (srcBase + BitVec.ofNat 64 srcOff) + lol1 with hhend
  have hxn : pfx - (0xb7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : 0 < n := by
    have hge : 184 ≤ pfx.toNat := by
      have h := h_lo
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xb8 : Word).toNat = 184 from by decide] at h
      exact h
    rw [hn, BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]
    omega
  have hn8 : n ≤ 8 := by
    have hge : 184 ≤ pfx.toNat := by
      have h := h_lo
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xb8 : Word).toNat = 184 from by decide] at h
      exact h
    have hlt : pfx.toNat < 192 := by
      have h := h_hi
      simpa only [BitVec.ult, decide_eq_true_eq,
        show (0xc0 : Word).toNat = 192 from by decide] using h
    rw [hn, BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
  have hcasc := wn_to_long_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  -- idx 37..40: LI x6 0xb7 ; SUB x7 ; ADDI x6 (1+lol) ; ADD x29 (header_end).
  have hLI := li_spec_gen_within .x6 (0xc0 : Word) (0xb7 : Word) (base + 148) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xb7 : Word) t2Old (base + 152) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xb7 : Word) (pfx - (0xb7 : Word)) (1 : BitVec 12)
    (base + 156) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 160) (by decide)
  rw [← hhend] at hadd
  have hblk1 : cpsTripleWithin 4 (base + 148) (base + 164) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ hend)) := by
    runBlock hLI hsub haddi hadd
  have hblk1' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk1
  -- idx 41: BLTU x11 x29 NT (header fits).  base+164 → base+168.
  have hb41 := bltu_spec_gen_within .x11 .x29 (200 : BitVec 13) endPtr hend (base + 164)
  rw [show (base + 164 : Word) + 4 = base + 168 from by bv_omega] at hb41
  have hm41 : ∀ a i, CodeReq.singleton (base + 164) (.BLTU .x11 .x29 (200 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 41 (base + 164)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr41 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm41 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb41))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  -- idx 42..43: ADDI x30 x10 1 (ptr) ; LBU x31 x30 0 (first byte).
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 168) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 172) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 (by omega) (hlvalid 0 hn1)
  have hptrblk : cpsTripleWithin 2 (base + 168) (base + 176) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  -- idx 44: BEQ x31 x0 NT (first byte ≠ 0).  base+176 → base+180.
  have hbeq := beq_spec_gen_within .x31 .x0 (212 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 176)
  rw [show (base + 176 : Word) + 4 = base + 180 from by bv_omega] at hbeq
  have hm44 : ∀ a i, CodeReq.singleton (base + 176) (.BEQ .x31 .x0 (212 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 44 (base + 176)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr44 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm44 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fb ((sepConj_pure_right _).1 h_pure).2)
  -- idx 45..46: LI x28 0 (acc) ; MV x6 x7 (count = lol = ofNat n).
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 180) (by decide)
  have hmv6 := mv_spec_gen_within .x6 .x7 (pfx - (0xb7 : Word)) lol1 (base + 184) (by decide)
  have hcntblk : cpsTripleWithin 2 (base + 180) (base + 188) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ t3Old) ** (.x6 ↦ᵣ lol1) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word)))) := by
    runBlock hLI28 hmv6
  have hcntblk' := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hcntblk
  -- loop (idx 47..53): x28 = decoded, x6 = 0, x30 = ptr_end.
  have hloop := wn_ls_loop base srcBase ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) srcBytes []
    (srcOff + 1) n hsalign (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover)
    (by simp; omega) (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hdec, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  -- idx 54: LI x6 56.  base+216 → base+220.
  have hLI56 := li_spec_gen_within .x6 (0 : Word) (56 : Word) (base + 216) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 216) (base + 220) (rlp_walk_next_code base)
      (.x6 ↦ᵣ (0 : Word)) (.x6 ↦ᵣ (56 : Word)) := by runBlock hLI56
  have hLI56blk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI56blk
  -- idx 55: BLTU x28 x6 NT (decoded ≥ 56).  base+220 → base+224.
  have hb55 := bltu_spec_gen_within .x28 .x6 (156 : BitVec 13) dec (56 : Word) (base + 220)
  rw [show (base + 220 : Word) + 4 = base + 224 from by bv_omega] at hb55
  have hm55 : ∀ a i, CodeReq.singleton (base + 220) (.BLTU .x28 .x6 (156 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 55 (base + 220)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr55 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm55 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb55))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_nonmin ((sepConj_pure_right _).1 h_pure).2)
  -- idx 56: SUB x6 x11 x29 (avail2 = end - header_end).  base+224 → base+228.
  have hsubA2 := sub_spec_gen_within .x6 .x11 .x29 endPtr hend (56 : Word) (base + 224) (by decide)
  have hadvblk : cpsTripleWithin 1 (base + 224) (base + 228) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (56 : Word)) ** (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend))
      ((.x6 ↦ᵣ (endPtr - hend)) ** (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend)) := by runBlock hsubA2
  have hadvblk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hadvblk
  -- idx 57: BLTU x6 x28 NT (avail2 ≥ dec).  base+228 → base+232.
  have hb57 := bltu_spec_gen_within .x6 .x28 (136 : BitVec 13) (endPtr - hend) dec (base + 228)
  rw [show (base + 228 : Word) + 4 = base + 232 from by bv_omega] at hb57
  have hm57 : ∀ a i, CodeReq.singleton (base + 228) (.BLTU .x6 .x28 (136 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 57 (base + 228)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr57 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm57 (cpsBranchWithin_frameR
      ((.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb57))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_content ((sepConj_pure_right _).1 h_pure).2)
  -- idx 58..61: ADD x10 x29 x28 (advanced) ; MV x12 x28 (decoded) ; LI x11 0 ; ret.  base+232 → ra.
  have hadd10 := add_spec_gen_within .x10 .x29 .x28 hend dec (srcBase + BitVec.ofNat 64 srcOff)
    (base + 232) (by decide)
  have hmv12 := mv_spec_gen_within .x12 .x28 dec a2Old (base + 236) (by decide)
  have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 240) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 244)
  simp only [signExtend12_0] at hRet
  have hPost : cpsTripleWithin 4 (base + 232) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x29 ↦ᵣ hend) ** (.x28 ↦ᵣ dec) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x12 ↦ᵣ a2Old) ** (.x11 ↦ᵣ endPtr) ** (.x1 ↦ᵣ raVal))
      ((.x29 ↦ᵣ hend) ** (.x28 ↦ᵣ dec) ** (.x10 ↦ᵣ (hend + dec)) ** (.x12 ↦ᵣ dec) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hadd10 hmv12 hLI11 hRet
  have hPost' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (endPtr - hend)) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      bytesRegion srcBase srcBytes) (by pcFree) hPost
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk1'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hbr41
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hptrblk'
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hbr44
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hcntblk'
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hloop'
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hLI56blk'
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hbr55
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8 hadvblk'
  have s10 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s9 hbr57
  have s11 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s10 hPost'
  rw [show (8 + 4 + 1 + 2 + 1 + 2 + (7 * n + 1) + 1 + 1 + 1 + 1 + 4) = 7 * n + 27 from by ring] at s11
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s11
  have hp' := sepConj_mono
    (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)))
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x30)
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
          (fun _ x => x))))))) h hp
  xperm_hyp hp'

/-- The non-minimal fail block (idx 94..96), `base+376 → ra`: `a1 = 4`. -/
private theorem wn_nonmin_block (base raVal a1Old a2Old : Word) :
    cpsTripleWithin 3 (base + 376) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (4 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hLI4 := li_spec_gen_within .x11 a1Old (4 : Word) (base + 376) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 380) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 384)
  simp only [signExtend12_0] at hRet
  runBlock hLI4 hLI0 hRet

set_option maxRecDepth 8000 in
/-- **long string — non-minimal** (`0xb8 ≤ prefix < 0xc0`, header fits, `len[0] ≠ 0`,
    `decoded < 56`): the long form is non-canonical (must use short form) → `a1 = 4`. -/
theorem rlp_walk_next_long_string_nonmin_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) (56 : Word) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat + 24) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xb7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  set lol1 := (pfx - (0xb7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set hend := (srcBase + BitVec.ofNat 64 srcOff) + lol1 with hhend
  have hxn : pfx - (0xb7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : 0 < n := by
    have hge : 184 ≤ pfx.toNat := by
      have h := h_lo
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xb8 : Word).toNat = 184 from by decide] at h
      exact h
    rw [hn, BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
  have hn8 : n ≤ 8 := by
    have hge : 184 ≤ pfx.toNat := by
      have h := h_lo
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xb8 : Word).toNat = 184 from by decide] at h
      exact h
    have hlt : pfx.toNat < 192 := by
      have h := h_hi
      simpa only [BitVec.ult, decide_eq_true_eq,
        show (0xc0 : Word).toNat = 192 from by decide] using h
    rw [hn, BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
  have hcasc := wn_to_long_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI := li_spec_gen_within .x6 (0xc0 : Word) (0xb7 : Word) (base + 148) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xb7 : Word) t2Old (base + 152) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xb7 : Word) (pfx - (0xb7 : Word)) (1 : BitVec 12)
    (base + 156) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 160) (by decide)
  rw [← hhend] at hadd
  have hblk1 : cpsTripleWithin 4 (base + 148) (base + 164) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ hend)) := by
    runBlock hLI hsub haddi hadd
  have hblk1' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk1
  have hb41 := bltu_spec_gen_within .x11 .x29 (200 : BitVec 13) endPtr hend (base + 164)
  rw [show (base + 164 : Word) + 4 = base + 168 from by bv_omega] at hb41
  have hm41 : ∀ a i, CodeReq.singleton (base + 164) (.BLTU .x11 .x29 (200 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 41 (base + 164)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr41 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm41 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb41))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 168) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 172) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 (by omega) (hlvalid 0 hn1)
  have hptrblk : cpsTripleWithin 2 (base + 168) (base + 176) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  have hbeq := beq_spec_gen_within .x31 .x0 (212 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 176)
  rw [show (base + 176 : Word) + 4 = base + 180 from by bv_omega] at hbeq
  have hm44 : ∀ a i, CodeReq.singleton (base + 176) (.BEQ .x31 .x0 (212 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 44 (base + 176)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr44 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm44 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fb ((sepConj_pure_right _).1 h_pure).2)
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 180) (by decide)
  have hmv6 := mv_spec_gen_within .x6 .x7 (pfx - (0xb7 : Word)) lol1 (base + 184) (by decide)
  have hcntblk : cpsTripleWithin 2 (base + 180) (base + 188) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ t3Old) ** (.x6 ↦ᵣ lol1) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word)))) := by
    runBlock hLI28 hmv6
  have hcntblk' := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hcntblk
  have hloop := wn_ls_loop base srcBase ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) srcBytes []
    (srcOff + 1) n hsalign (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover)
    (by simp; omega) (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hdec, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  have hLI56 := li_spec_gen_within .x6 (0 : Word) (56 : Word) (base + 216) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 216) (base + 220) (rlp_walk_next_code base)
      (.x6 ↦ᵣ (0 : Word)) (.x6 ↦ᵣ (56 : Word)) := by runBlock hLI56
  have hLI56blk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI56blk
  -- idx 55: BLTU x28 x6 156 TAKEN (decoded < 56).  base+220 → base+376 (nonmin).
  have hb55 := bltu_spec_gen_within .x28 .x6 (156 : BitVec 13) dec (56 : Word) (base + 220)
  rw [show (base + 220) + signExtend13 (156 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (156 : BitVec 13) = (156 : Word) from by decide]; bv_omega,
      show (base + 220 : Word) + 4 = base + 224 from by bv_omega] at hb55
  have hm55 : ∀ a i, CodeReq.singleton (base + 220) (.BLTU .x28 .x6 (156 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 55 (base + 220)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr55 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm55 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb55))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_nonmin)
  have hfail := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x6 ↦ᵣ (56 : Word)) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) **
      regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_nonmin_block base raVal endPtr a2Old)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk1'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hbr41
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hptrblk'
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hbr44
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hcntblk'
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hloop'
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hLI56blk'
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hbr55
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8 hfail
  rw [show (8 + 4 + 1 + 2 + 1 + 2 + (7 * n + 1) + 1 + 1 + 3) = 7 * n + 24 from by ring] at s9
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s9
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
            (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x)))))))))) h hp
  xperm_hyp hp'

set_option maxRecDepth 8000 in
/-- **long string — content bound** (`0xb8 ≤ prefix < 0xc0`, header fits, `len[0] ≠ 0`,
    `decoded ≥ 56`, content runs past `end`): the payload doesn't fit → `a1 = 3`. -/
theorem rlp_walk_next_long_string_content_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) (56 : Word) = true)
    (h_content : BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat + 26) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xb7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  set lol1 := (pfx - (0xb7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set hend := (srcBase + BitVec.ofNat 64 srcOff) + lol1 with hhend
  have hxn : pfx - (0xb7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : 0 < n := by
    have hge : 184 ≤ pfx.toNat := by
      have h := h_lo
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xb8 : Word).toNat = 184 from by decide] at h
      exact h
    rw [hn, BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
  have hn8 : n ≤ 8 := by
    have hge : 184 ≤ pfx.toNat := by
      have h := h_lo
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xb8 : Word).toNat = 184 from by decide] at h
      exact h
    have hlt : pfx.toNat < 192 := by
      have h := h_hi
      simpa only [BitVec.ult, decide_eq_true_eq,
        show (0xc0 : Word).toNat = 192 from by decide] using h
    rw [hn, BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
  have hcasc := wn_to_long_string base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_lo h_hi
  have hLI := li_spec_gen_within .x6 (0xc0 : Word) (0xb7 : Word) (base + 148) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xb7 : Word) t2Old (base + 152) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xb7 : Word) (pfx - (0xb7 : Word)) (1 : BitVec 12)
    (base + 156) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 160) (by decide)
  rw [← hhend] at hadd
  have hblk1 : cpsTripleWithin 4 (base + 148) (base + 164) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ hend)) := by
    runBlock hLI hsub haddi hadd
  have hblk1' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk1
  have hb41 := bltu_spec_gen_within .x11 .x29 (200 : BitVec 13) endPtr hend (base + 164)
  rw [show (base + 164 : Word) + 4 = base + 168 from by bv_omega] at hb41
  have hm41 : ∀ a i, CodeReq.singleton (base + 164) (.BLTU .x11 .x29 (200 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 41 (base + 164)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr41 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm41 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb41))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 168) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 172) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 (by omega) (hlvalid 0 hn1)
  have hptrblk : cpsTripleWithin 2 (base + 168) (base + 176) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  have hbeq := beq_spec_gen_within .x31 .x0 (212 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 176)
  rw [show (base + 176 : Word) + 4 = base + 180 from by bv_omega] at hbeq
  have hm44 : ∀ a i, CodeReq.singleton (base + 176) (.BEQ .x31 .x0 (212 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 44 (base + 176)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr44 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm44 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fb ((sepConj_pure_right _).1 h_pure).2)
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 180) (by decide)
  have hmv6 := mv_spec_gen_within .x6 .x7 (pfx - (0xb7 : Word)) lol1 (base + 184) (by decide)
  have hcntblk : cpsTripleWithin 2 (base + 180) (base + 188) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ t3Old) ** (.x6 ↦ᵣ lol1) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word)))) := by
    runBlock hLI28 hmv6
  have hcntblk' := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hcntblk
  have hloop := wn_ls_loop base srcBase ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) srcBytes []
    (srcOff + 1) n hsalign (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover)
    (by simp; omega) (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hdec, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  have hLI56 := li_spec_gen_within .x6 (0 : Word) (56 : Word) (base + 216) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 216) (base + 220) (rlp_walk_next_code base)
      (.x6 ↦ᵣ (0 : Word)) (.x6 ↦ᵣ (56 : Word)) := by runBlock hLI56
  have hLI56blk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI56blk
  have hb55 := bltu_spec_gen_within .x28 .x6 (156 : BitVec 13) dec (56 : Word) (base + 220)
  rw [show (base + 220 : Word) + 4 = base + 224 from by bv_omega] at hb55
  have hm55 : ∀ a i, CodeReq.singleton (base + 220) (.BLTU .x28 .x6 (156 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 55 (base + 220)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr55 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm55 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb55))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_nonmin ((sepConj_pure_right _).1 h_pure).2)
  have hsubA2 := sub_spec_gen_within .x6 .x11 .x29 endPtr hend (56 : Word) (base + 224) (by decide)
  have hadvblk : cpsTripleWithin 1 (base + 224) (base + 228) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (56 : Word)) ** (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend))
      ((.x6 ↦ᵣ (endPtr - hend)) ** (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend)) := by runBlock hsubA2
  have hadvblk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hadvblk
  -- idx 57: BLTU x6 x28 136 TAKEN (avail2 < dec).  base+228 → base+364 (bound).
  have hb57 := bltu_spec_gen_within .x6 .x28 (136 : BitVec 13) (endPtr - hend) dec (base + 228)
  rw [show (base + 228) + signExtend13 (136 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (136 : BitVec 13) = (136 : Word) from by decide]; bv_omega,
      show (base + 228 : Word) + 4 = base + 232 from by bv_omega] at hb57
  have hm57 : ∀ a i, CodeReq.singleton (base + 228) (.BLTU .x6 .x28 (136 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 57 (base + 228)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr57 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm57 (cpsBranchWithin_frameR
      ((.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb57))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_content)
  have hfail := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (endPtr - hend)) ** (.x29 ↦ᵣ hend) ** (.x28 ↦ᵣ dec) **
      (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      bytesRegion srcBase srcBytes) (by pcFree) (wn_bound_block base raVal endPtr a2Old)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk1'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hbr41
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hptrblk'
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hbr44
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hcntblk'
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hloop'
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hLI56blk'
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hbr55
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8 hadvblk'
  have s10 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s9 hbr57
  have s11 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s10 hfail
  rw [show (8 + 4 + 1 + 2 + 1 + 2 + (7 * n + 1) + 1 + 1 + 1 + 1 + 3) = 7 * n + 26 from by ring] at s11
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s11
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x29)
      (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x30)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x7) (fun _ x => x)))))))))) h hp
  xperm_hyp hp'

/-- Cascade to the long-list block (idx 0..9, all branches fall through), `base → base+40`
    (idx 10). `prefix ≥ 0xf8`. Leaves `x5 = prefix`, `x6 = 0xf8`. -/
private theorem wn_to_long_list (base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) (raVal : Word)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_ge : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true) :
    cpsTripleWithin 10 base (base + 40) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      (((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xf8 : Word))) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
          (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)) := by
  have hge2 : 248 ≤ ((srcBytes[srcOff]'hoff).zeroExtend 64).toNat := by
    have h := h_ge
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
      show (0xf8 : Word).toNat = 248 from by decide] at h
    exact h
  have h_lo80 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
      show (0x80 : Word).toNat = 128 from by decide]; omega
  have h_lob8 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
      show (0xb8 : Word).toNat = 184 from by decide]; omega
  have h_loc0 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
      show (0xc0 : Word).toNat = 192 from by decide]; omega
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  have hB := wn_lbu_li80 base srcBase srcBytes srcOff t0Old t1Old hsalign hoff hover hvalid
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  let F : Assertion := (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
    (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
    (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes
  have hC := wn_cascade_step base (288 : BitVec 13) 3 (base + 12) pfx (0x80 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo80)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hC
  have hLI8 := li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 16) (by decide)
  have hmonoD : ∀ a i, CodeReq.singleton (base + 16) (.LI .x6 (0xb8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 4 (base + 16)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hD := cpsTripleWithin_extend_code hmonoD (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLI8)
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
  have hF2 := cpsTripleWithin_extend_code hmonoF (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLIc)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hF2
  have hG := wn_cascade_step base (120 : BitVec 13) 7 (base + 28) pfx (0xc0 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_loc0)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hG
  have hLIf := li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 32) (by decide)
  have hmonoH : ∀ a i, CodeReq.singleton (base + 32) (.LI .x6 (0xf8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 8 (base + 32)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hH := cpsTripleWithin_extend_code hmonoH (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLIf)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hH
  have hI := wn_cascade_step base (280 : BitVec 13) 9 (base + 36) pfx (0xf8 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_ge)
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hI
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
    rw [hpfx]; xperm_hyp hp) s8

/-- **long list — header bound** (`prefix ≥ 0xf8`, `1 + lol` runs past `end`): `a1 = 3`. -/
theorem rlp_walk_next_long_list_header_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_ge : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_hdr : BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true) :
    cpsTripleWithin 18 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set lol1 := (pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  have hcasc := wn_to_long_list base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_ge
  have hLI := li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 40) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xf7 : Word) t2Old (base + 44) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xf7 : Word) (pfx - (0xf7 : Word)) (1 : BitVec 12)
    (base + 48) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 52) (by decide)
  have hblk : cpsTripleWithin 4 (base + 40) (base + 56) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1))) := by
    runBlock hLI hsub haddi hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk
  have hbltu := bltu_spec_gen_within .x11 .x29 (308 : BitVec 13) endPtr
    ((srcBase + BitVec.ofNat 64 srcOff) + lol1) (base + 56)
  rw [show (base + 56) + signExtend13 (308 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (308 : BitVec 13) = (308 : Word) from by decide]; bv_omega,
      show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hbltu
  have hmono14 : ∀ a i, CodeReq.singleton (base + 56) (.BLTU .x11 .x29 (308 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 14 (base + 56)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono14 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hdr)
  have hfail := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes) (by pcFree) (wn_bound_block base raVal endPtr a2Old)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hfail
  rw [show (10 + 4 + 1 + 3) = 18 from rfl] at c3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c3
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
            (fun _ x => x))))))))) h hp
  xperm_hyp hp'

/-- **long list — leading zero** (`prefix ≥ 0xf8`, header fits, `len[0] = 0`): `a1 = 5`. -/
theorem rlp_walk_next_long_list_lz_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64) (hover1 : srcBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_ge : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_lz : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 = (0 : Word)) :
    cpsTripleWithin 21 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set lol1 := (pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set cp1 := srcBase + BitVec.ofNat 64 (srcOff + 1) with hcp1
  have hcasc := wn_to_long_list base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_ge
  have hLI := li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 40) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xf7 : Word) t2Old (base + 44) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xf7 : Word) (pfx - (0xf7 : Word)) (1 : BitVec 12)
    (base + 48) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 52) (by decide)
  have hblk : cpsTripleWithin 4 (base + 40) (base + 56) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1))) := by
    runBlock hLI hsub haddi hadd
  have hblk' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk
  have hb14 := bltu_spec_gen_within .x11 .x29 (308 : BitVec 13) endPtr
    ((srcBase + BitVec.ofNat 64 srcOff) + lol1) (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hb14
  have hm14 : ∀ a i, CodeReq.singleton (base + 56) (.BLTU .x11 .x29 (308 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 14 (base + 56)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr14 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm14 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb14))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 60) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12) = cp1 from by
        rw [hcp1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 64) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 hover1 hvalid1
  have hptrblk : cpsTripleWithin 2 (base + 60) (base + 68) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  have hbeq := beq_spec_gen_within .x31 .x0 (320 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 68)
  rw [show (base + 68) + signExtend13 (320 : BitVec 13) = base + 388 from by
        rw [show signExtend13 (320 : BitVec 13) = (320 : Word) from by decide]; bv_omega,
      show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at hbeq
  have hm17 : ∀ a i, CodeReq.singleton (base + 68) (.BEQ .x31 .x0 (320 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 17 (base + 68)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr17 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm17 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ cp1) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) **
        (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbeq))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by rw [h_lz]))
  have hfail := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** (.x30 ↦ᵣ cp1) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + lol1)) **
      (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_lz_block base raVal endPtr a2Old)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk'
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hbr14
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c2 hptrblk'
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3 hbr17
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) c4 hfail
  rw [show (10 + 4 + 1 + 2 + 1 + 3) = 21 from rfl] at c5
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c5
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x31) (sepConj_mono (regIs_implies_regOwn .x30)
      (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
          (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x28)
            (fun _ x => x))))))))) h hp
  xperm_hyp hp'

set_option maxRecDepth 8000 in
/-- **long list — accept** (`prefix ≥ 0xf8`, header fits, `len[0] ≠ 0`, `decoded ≥ 56`,
    content fits): `a2 = full span = 1 + lol + decoded`, cursor advances by the span,
    `a1 = 0` (sub-list returned whole). -/
theorem rlp_walk_next_long_list_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_ge : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_content : ¬ BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 31) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) +
              signExtend12 (1 : BitVec 12)))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) +
              signExtend12 (1 : BitVec 12))) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xf7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  set lol1 := (pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set hend := (srcBase + BitVec.ofNat 64 srcOff) + lol1 with hhend
  set span := ((pfx - (0xf7 : Word)) + dec) + signExtend12 (1 : BitVec 12) with hspan
  have hxn : pfx - (0xf7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : 0 < n := by
    have hge : 248 ≤ pfx.toNat := by
      have h := h_ge
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xf8 : Word).toNat = 248 from by decide] at h
      exact h
    rw [hn, BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hn8 : n ≤ 8 := by
    have hge : 248 ≤ pfx.toNat := by
      have h := h_ge
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xf8 : Word).toNat = 248 from by decide] at h
      exact h
    have hlt : pfx.toNat < 256 := by
      have h8 := (srcBytes[srcOff]'hoff).isLt
      rw [hpfx, BitVec.toNat_setWidth]; omega
    rw [hn, BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hcasc := wn_to_long_list base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_ge
  have hLI := li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 40) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xf7 : Word) t2Old (base + 44) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xf7 : Word) (pfx - (0xf7 : Word)) (1 : BitVec 12)
    (base + 48) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 52) (by decide)
  rw [← hhend] at hadd
  have hblk1 : cpsTripleWithin 4 (base + 40) (base + 56) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ hend)) := by
    runBlock hLI hsub haddi hadd
  have hblk1' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk1
  have hb14 := bltu_spec_gen_within .x11 .x29 (308 : BitVec 13) endPtr hend (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hb14
  have hm14 : ∀ a i, CodeReq.singleton (base + 56) (.BLTU .x11 .x29 (308 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 14 (base + 56)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr14 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm14 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb14))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 60) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 64) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 (by omega) (hlvalid 0 hn1)
  have hptrblk : cpsTripleWithin 2 (base + 60) (base + 68) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  have hbeq := beq_spec_gen_within .x31 .x0 (320 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 68)
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at hbeq
  have hm17 : ∀ a i, CodeReq.singleton (base + 68) (.BEQ .x31 .x0 (320 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 17 (base + 68)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr17 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm17 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fb ((sepConj_pure_right _).1 h_pure).2)
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 72) (by decide)
  have hmv6 := mv_spec_gen_within .x6 .x7 (pfx - (0xf7 : Word)) lol1 (base + 76) (by decide)
  have hcntblk : cpsTripleWithin 2 (base + 72) (base + 80) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ t3Old) ** (.x6 ↦ᵣ lol1) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word)))) := by
    runBlock hLI28 hmv6
  have hcntblk' := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hcntblk
  have hloop := wn_ll_loop base srcBase ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) srcBytes []
    (srcOff + 1) n hsalign (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover)
    (by simp; omega) (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hdec, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  have hLI56 := li_spec_gen_within .x6 (0 : Word) (56 : Word) (base + 108) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 108) (base + 112) (rlp_walk_next_code base)
      (.x6 ↦ᵣ (0 : Word)) (.x6 ↦ᵣ (56 : Word)) := by runBlock hLI56
  have hLI56blk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI56blk
  have hb28 := bltu_spec_gen_within .x28 .x6 (264 : BitVec 13) dec (56 : Word) (base + 112)
  rw [show (base + 112 : Word) + 4 = base + 116 from by bv_omega] at hb28
  have hm28 : ∀ a i, CodeReq.singleton (base + 112) (.BLTU .x28 .x6 (264 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 28 (base + 112)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr28 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm28 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb28))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_nonmin ((sepConj_pure_right _).1 h_pure).2)
  -- idx 29..31: ADD x31 x7 x28 (lol+decoded) ; ADDI x31 (full span) ; SUB x6 x11 x29 (avail2).
  -- x31 is owned after the loop; open the ownership to write it.
  have hspanblk : cpsTripleWithin 3 (base + 116) (base + 128) (rlp_walk_next_code base)
      (((.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) ** (.x6 ↦ᵣ (56 : Word)) **
        (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend)) ** regOwn .x31)
      ((.x31 ↦ᵣ span) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) **
        (.x6 ↦ᵣ (endPtr - hend)) ** (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend)) := by
    apply cpsTripleWithin_of_forall_regIs_to_regOwn
    intro v
    have hadd1 := add_spec_gen_within .x31 .x7 .x28 (pfx - (0xf7 : Word)) dec v (base + 116)
      (by decide)
    have haddi2 := addi_spec_gen_same_within .x31 ((pfx - (0xf7 : Word)) + dec) (1 : BitVec 12)
      (base + 120) (by decide)
    rw [← hspan] at haddi2
    have hsubA3 := sub_spec_gen_within .x6 .x11 .x29 endPtr hend (56 : Word) (base + 124) (by decide)
    runBlock hadd1 haddi2 hsubA3
  have hspanblk' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x5 ↦ᵣ pfx) **
      (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hspanblk
  -- idx 32: BLTU x6 x28 236 NT (avail2 ≥ dec).  base+128 → base+132.
  have hb32 := bltu_spec_gen_within .x6 .x28 (236 : BitVec 13) (endPtr - hend) dec (base + 128)
  rw [show (base + 128 : Word) + 4 = base + 132 from by bv_omega] at hb32
  have hm32 : ∀ a i, CodeReq.singleton (base + 128) (.BLTU .x6 .x28 (236 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 32 (base + 128)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr32 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm32 (cpsBranchWithin_frameR
      ((.x31 ↦ᵣ span) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x11 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hb32))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_content ((sepConj_pure_right _).1 h_pure).2)
  -- idx 33..36: ADD x10 x31 x10 (advanced) ; MV x12 x31 ; LI x11 0 ; ret.  base+132 → ra.
  have hadd10 := add_spec_gen_rd_eq_rs2_within .x10 .x31 span (srcBase + BitVec.ofNat 64 srcOff)
    (base + 132) (by decide)
  have hmv12 := mv_spec_gen_within .x12 .x31 span a2Old (base + 136) (by decide)
  have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 140) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 144)
  simp only [signExtend12_0] at hRet
  have hPost : cpsTripleWithin 4 (base + 132) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x31 ↦ᵣ span) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) **
        (.x11 ↦ᵣ endPtr) ** (.x1 ↦ᵣ raVal))
      ((.x31 ↦ᵣ span) ** (.x10 ↦ᵣ (span + (srcBase + BitVec.ofNat 64 srcOff))) ** (.x12 ↦ᵣ span) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hadd10 hmv12 hLI11 hRet
  have hPost' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (endPtr - hend)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) **
      (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree) hPost
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk1'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hbr14
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hptrblk'
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hbr17
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hcntblk'
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hloop'
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hLI56blk'
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hbr28
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8 hspanblk'
  have s10 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s9 hbr32
  have s11 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s10 hPost'
  rw [show (10 + 4 + 1 + 2 + 1 + 2 + (7 * n + 1) + 1 + 1 + 3 + 1 + 4) = 7 * n + 31 from by ring] at s11
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s11
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + span = span + (srcBase + BitVec.ofNat 64 srcOff)
      from by bv_omega]
  have hp' := sepConj_mono
    (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x))
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
      (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x30)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x29)
          (fun _ x => x))))))) h hp
  xperm_hyp hp'

set_option maxRecDepth 8000 in
/-- **long list — non-minimal** (`prefix ≥ 0xf8`, header fits, `len[0] ≠ 0`, `decoded < 56`):
    `a1 = 4`. -/
theorem rlp_walk_next_long_list_nonmin_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_ge : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 26) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xf7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  set lol1 := (pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set hend := (srcBase + BitVec.ofNat 64 srcOff) + lol1 with hhend
  have hxn : pfx - (0xf7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : 0 < n := by
    have hge : 248 ≤ pfx.toNat := by
      have h := h_ge
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xf8 : Word).toNat = 248 from by decide] at h
      exact h
    rw [hn, BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hn8 : n ≤ 8 := by
    have hge : 248 ≤ pfx.toNat := by
      have h := h_ge
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xf8 : Word).toNat = 248 from by decide] at h
      exact h
    have hlt : pfx.toNat < 256 := by
      have h8 := (srcBytes[srcOff]'hoff).isLt
      rw [hpfx, BitVec.toNat_setWidth]; omega
    rw [hn, BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hcasc := wn_to_long_list base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_ge
  have hLI := li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 40) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xf7 : Word) t2Old (base + 44) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xf7 : Word) (pfx - (0xf7 : Word)) (1 : BitVec 12)
    (base + 48) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 52) (by decide)
  rw [← hhend] at hadd
  have hblk1 : cpsTripleWithin 4 (base + 40) (base + 56) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ hend)) := by
    runBlock hLI hsub haddi hadd
  have hblk1' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk1
  have hb14 := bltu_spec_gen_within .x11 .x29 (308 : BitVec 13) endPtr hend (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hb14
  have hm14 : ∀ a i, CodeReq.singleton (base + 56) (.BLTU .x11 .x29 (308 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 14 (base + 56)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr14 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm14 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb14))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 60) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 64) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 (by omega) (hlvalid 0 hn1)
  have hptrblk : cpsTripleWithin 2 (base + 60) (base + 68) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  have hbeq := beq_spec_gen_within .x31 .x0 (320 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 68)
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at hbeq
  have hm17 : ∀ a i, CodeReq.singleton (base + 68) (.BEQ .x31 .x0 (320 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 17 (base + 68)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr17 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm17 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fb ((sepConj_pure_right _).1 h_pure).2)
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 72) (by decide)
  have hmv6 := mv_spec_gen_within .x6 .x7 (pfx - (0xf7 : Word)) lol1 (base + 76) (by decide)
  have hcntblk : cpsTripleWithin 2 (base + 72) (base + 80) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ t3Old) ** (.x6 ↦ᵣ lol1) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word)))) := by
    runBlock hLI28 hmv6
  have hcntblk' := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hcntblk
  have hloop := wn_ll_loop base srcBase ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) srcBytes []
    (srcOff + 1) n hsalign (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover)
    (by simp; omega) (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hdec, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  have hLI56 := li_spec_gen_within .x6 (0 : Word) (56 : Word) (base + 108) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 108) (base + 112) (rlp_walk_next_code base)
      (.x6 ↦ᵣ (0 : Word)) (.x6 ↦ᵣ (56 : Word)) := by runBlock hLI56
  have hLI56blk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI56blk
  have hb28 := bltu_spec_gen_within .x28 .x6 (264 : BitVec 13) dec (56 : Word) (base + 112)
  rw [show (base + 112) + signExtend13 (264 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (264 : BitVec 13) = (264 : Word) from by decide]; bv_omega,
      show (base + 112 : Word) + 4 = base + 116 from by bv_omega] at hb28
  have hm28 : ∀ a i, CodeReq.singleton (base + 112) (.BLTU .x28 .x6 (264 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 28 (base + 112)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr28 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm28 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb28))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_nonmin)
  have hfail := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x6 ↦ᵣ (56 : Word)) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) **
      regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** bytesRegion srcBase srcBytes)
    (by pcFree) (wn_nonmin_block base raVal endPtr a2Old)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk1'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hbr14
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hptrblk'
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hbr17
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hcntblk'
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hloop'
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hLI56blk'
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hbr28
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8 hfail
  rw [show (10 + 4 + 1 + 2 + 1 + 2 + (7 * n + 1) + 1 + 1 + 3) = 7 * n + 26 from by ring] at s9
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s9
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
            (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x)))))))))) h hp
  xperm_hyp hp'

set_option maxRecDepth 8000 in
/-- **long list — content bound** (`prefix ≥ 0xf8`, header fits, `len[0] ≠ 0`, `decoded ≥ 56`,
    content runs past `end`): `a1 = 3`. -/
theorem rlp_walk_next_long_list_content_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hoff1 : srcOff + 1 < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_ge : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_content : BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 30) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xf7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  set lol1 := (pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12) with hlol1
  set hend := (srcBase + BitVec.ofNat 64 srcOff) + lol1 with hhend
  set span := ((pfx - (0xf7 : Word)) + dec) + signExtend12 (1 : BitVec 12) with hspan
  have hxn : pfx - (0xf7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : 0 < n := by
    have hge : 248 ≤ pfx.toNat := by
      have h := h_ge
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xf8 : Word).toNat = 248 from by decide] at h
      exact h
    rw [hn, BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hn8 : n ≤ 8 := by
    have hge : 248 ≤ pfx.toNat := by
      have h := h_ge
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xf8 : Word).toNat = 248 from by decide] at h
      exact h
    have hlt : pfx.toNat < 256 := by
      have h8 := (srcBytes[srcOff]'hoff).isLt
      rw [hpfx, BitVec.toNat_setWidth]; omega
    rw [hn, BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hcasc := wn_to_long_list base srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid raVal h_inb h_ge
  have hLI := li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 40) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xf7 : Word) t2Old (base + 44) (by decide)
  have haddi := addi_spec_gen_within .x6 .x7 (0xf7 : Word) (pfx - (0xf7 : Word)) (1 : BitVec 12)
    (base + 48) (by decide)
  rw [← hlol1] at haddi
  have hadd := add_spec_gen_within .x29 .x10 .x6 (srcBase + BitVec.ofNat 64 srcOff) lol1 t4Old
    (base + 52) (by decide)
  rw [← hhend] at hadd
  have hblk1 : cpsTripleWithin 4 (base + 40) (base + 56) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x29 ↦ᵣ hend)) := by
    runBlock hLI hsub haddi hadd
  have hblk1' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hblk1
  have hb14 := bltu_spec_gen_within .x11 .x29 (308 : BitVec 13) endPtr hend (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hb14
  have hm14 : ∀ a i, CodeReq.singleton (base + 56) (.BLTU .x11 .x29 (308 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 14 (base + 56)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr14 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm14 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) (by pcFree) hb14))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_hdr ((sepConj_pure_right _).1 h_pure).2)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 60) (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase t6Old (base + 64) srcBytes (srcOff + 1)
    (by decide) hsalign hoff1 (by omega) (hlvalid 0 hn1)
  have hptrblk : cpsTripleWithin 2 (base + 60) (base + 68) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x31 ↦ᵣ t6Old) **
        bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) ** bytesRegion srcBase srcBytes) := by
    runBlock ha30 hlbu
  have hptrblk' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hptrblk
  have hbeq := beq_spec_gen_within .x31 .x0 (320 : BitVec 13)
    ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 68)
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at hbeq
  have hm17 : ∀ a i, CodeReq.singleton (base + 68) (.BEQ .x31 .x0 (320 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 17 (base + 68)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr17 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm17 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ lol1) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fb ((sepConj_pure_right _).1 h_pure).2)
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 72) (by decide)
  have hmv6 := mv_spec_gen_within .x6 .x7 (pfx - (0xf7 : Word)) lol1 (base + 76) (by decide)
  have hcntblk : cpsTripleWithin 2 (base + 72) (base + 80) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ t3Old) ** (.x6 ↦ᵣ lol1) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word)))) := by
    runBlock hLI28 hmv6
  have hcntblk' := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ (srcBytes[srcOff + 1]'hoff1).zeroExtend 64) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hcntblk
  have hloop := wn_ll_loop base srcBase ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) srcBytes []
    (srcOff + 1) n hsalign (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover)
    (by simp; omega) (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hdec, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  have hLI56 := li_spec_gen_within .x6 (0 : Word) (56 : Word) (base + 108) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 108) (base + 112) (rlp_walk_next_code base)
      (.x6 ↦ᵣ (0 : Word)) (.x6 ↦ᵣ (56 : Word)) := by runBlock hLI56
  have hLI56blk' := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ dec) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hLI56blk
  have hb28 := bltu_spec_gen_within .x28 .x6 (264 : BitVec 13) dec (56 : Word) (base + 112)
  rw [show (base + 112 : Word) + 4 = base + 116 from by bv_omega] at hb28
  have hm28 : ∀ a i, CodeReq.singleton (base + 112) (.BLTU .x28 .x6 (264 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 28 (base + 112)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr28 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hm28 (cpsBranchWithin_frameR
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x5 ↦ᵣ pfx) **
        (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x29 ↦ᵣ hend) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hb28))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_nonmin ((sepConj_pure_right _).1 h_pure).2)
  have hspanblk : cpsTripleWithin 3 (base + 116) (base + 128) (rlp_walk_next_code base)
      (((.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) ** (.x6 ↦ᵣ (56 : Word)) **
        (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend)) ** regOwn .x31)
      ((.x31 ↦ᵣ span) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) **
        (.x6 ↦ᵣ (endPtr - hend)) ** (.x11 ↦ᵣ endPtr) ** (.x29 ↦ᵣ hend)) := by
    apply cpsTripleWithin_of_forall_regIs_to_regOwn
    intro v
    have hadd1 := add_spec_gen_within .x31 .x7 .x28 (pfx - (0xf7 : Word)) dec v (base + 116)
      (by decide)
    have haddi2 := addi_spec_gen_same_within .x31 ((pfx - (0xf7 : Word)) + dec) (1 : BitVec 12)
      (base + 120) (by decide)
    rw [← hspan] at haddi2
    have hsubA3 := sub_spec_gen_within .x6 .x11 .x29 endPtr hend (56 : Word) (base + 124) (by decide)
    runBlock hadd1 haddi2 hsubA3
  have hspanblk' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x5 ↦ᵣ pfx) **
      (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes) (by pcFree) hspanblk
  -- idx 32: BLTU x6 x28 236 TAKEN (avail2 < dec).  base+128 → base+364 (bound).
  have hb32 := bltu_spec_gen_within .x6 .x28 (236 : BitVec 13) (endPtr - hend) dec (base + 128)
  rw [show (base + 128) + signExtend13 (236 : BitVec 13) = base + 364 from by
        rw [show signExtend13 (236 : BitVec 13) = (236 : Word) from by decide]; bv_omega,
      show (base + 128 : Word) + 4 = base + 132 from by bv_omega] at hb32
  have hm32 : ∀ a i, CodeReq.singleton (base + 128) (.BLTU .x6 .x28 (236 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 32 (base + 128)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hbr32 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hm32 (cpsBranchWithin_frameR
      ((.x31 ↦ᵣ span) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x11 ↦ᵣ endPtr) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hb32))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_content)
  have hfail := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (endPtr - hend)) ** (.x31 ↦ᵣ span) **
      (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x5 ↦ᵣ pfx) ** (.x29 ↦ᵣ hend) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree) (wn_bound_block base raVal endPtr a2Old)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcasc hblk1'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hbr14
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hptrblk'
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hbr17
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hcntblk'
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hloop'
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hLI56blk'
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hbr28
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8 hspanblk'
  have s10 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s9 hbr32
  have s11 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s10 hfail
  rw [show (10 + 4 + 1 + 2 + 1 + 2 + (7 * n + 1) + 1 + 1 + 3 + 1 + 3) = 7 * n + 30 from by ring] at s11
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s11
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x31)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
        (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x30)
          (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x29)
            (fun _ x => x))))))))) h hp
  xperm_hyp hp'

/-! ## Unified success predicate and dispatch

Collapse the six accept paths into a single `a1 = 0` outcome described by a pure decode
relation about the two outputs `a0` (advanced cursor) and `a2` (reported length). -/

/-- If `a < b` (unsigned) then `a + 1 ≤ b`, i.e. `¬ b < a + 1`: a one-byte item in bounds
    leaves room for its successor.  (`bv_omega` does not translate `BitVec.ult … = true`
    hypotheses, so reduce to `toNat`/`omega`.) -/
private theorem wn_ult_succ_le {a b : Word} (h : BitVec.ult a b = true) :
    ¬ BitVec.ult b (a + 1) = true := by
  simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h ⊢
  rw [BitVec.toNat_add]
  have h1 : BitVec.toNat (1 : Word) = 1 := by decide
  have := a.isLt; have := b.isLt
  omega

/-- `base + (off+1) = (base + off) + 1` as words (the `signExtend12 1 = 1` step folded). -/
private theorem wn_base_off_succ (srcBase : Word) (srcOff : Nat) :
    srcBase + BitVec.ofNat 64 (srcOff + 1) = (srcBase + BitVec.ofNat 64 srcOff) + 1 := by
  bv_omega

/-- Strict-RLP decode of the item at byte-offset `off` in `bytes`, read from a cursor
    pointing at the prefix byte. Pure relation pinning the two outputs of `rlp_walk_next`
    on success: `next` (the advanced cursor `a0`) and `len` (the reported length `a2`).
    The five disjuncts are the RLP prefix forms; `next - cursor` is the item's full span,
    and `len` is the content length (single byte / string) or the full span (list). For the
    long forms the length field is `(bytes.drop (off+1)).take lol` with `lol = p - 0xb7`
    (string) / `p - 0xf7` (list). The expressions match the per-form accept postconditions
    verbatim (the short-string `next` differs only by the `cursor+1 = base+(off+1)` identity). -/
def rlpItemDecode (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr next len : Word) : Prop :=
  ∃ b : BitVec 8, bytes[off]? = some b ∧
    ( -- single byte (p < 0x80): the one byte fits since the cursor is in bounds
      (BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult cursor endPtr = true ∧
        next = cursor + signExtend12 (1 : BitVec 12) ∧ len = (1 : Word)) ∨
      -- short string (0x80 ≤ p < 0xb8): canonical — a 1-byte string's content is ≥ 0x80
      -- (a byte < 0x80 must use the single-byte form).  Fit: len < available bytes.
      (¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
        BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
        (b.zeroExtend 64 - (0x80 : Word) = (1 : Word) →
          ∃ c : BitVec 8, bytes[off + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
        BitVec.ult (b.zeroExtend 64 - (0x80 : Word)) (endPtr - cursor) = true ∧
        next = (cursor + signExtend12 (1 : BitVec 12)) + (b.zeroExtend 64 - (0x80 : Word)) ∧
        len = b.zeroExtend 64 - (0x80 : Word)) ∨
      -- long string (0xb8 ≤ p < 0xc0): canonical — no leading 0x00, decoded length ≥ 56.
      -- Fit (overflow-free): header_end ≤ end and decoded length ≤ end - header_end.
      (¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
        BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true ∧
        (∃ b1 : BitVec 8, bytes[off + 1]? = some b1 ∧ b1.zeroExtend 64 ≠ (0 : Word)) ∧
        ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat))) (56 : Word) = true ∧
        ¬ BitVec.ult endPtr (cursor + ((b.zeroExtend 64 - (0xb7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true ∧
        ¬ BitVec.ult (endPtr - (cursor + ((b.zeroExtend 64 - (0xb7 : Word)) +
            signExtend12 (1 : BitVec 12))))
          (BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat))) = true ∧
        next = (cursor + ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) +
          BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat)) ∧
        len = BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xb7 : Word)).toNat))) ∨
      -- short list (0xc0 ≤ p < 0xf8).  Fit: span ≤ available bytes.
      (¬ BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true ∧
        BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true ∧
        ¬ BitVec.ult (endPtr - cursor)
          ((b.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) = true ∧
        next = cursor + ((b.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) ∧
        len = (b.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) ∨
      -- long list (p ≥ 0xf8): canonical — no leading 0x00, decoded length ≥ 56.
      -- Fit (overflow-free): header_end ≤ end and decoded length ≤ end - header_end.
      (¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true ∧
        (∃ b1 : BitVec 8, bytes[off + 1]? = some b1 ∧ b1.zeroExtend 64 ≠ (0 : Word)) ∧
        ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
        ¬ BitVec.ult endPtr (cursor + ((b.zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true ∧
        ¬ BitVec.ult (endPtr - (cursor + ((b.zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))))
          (BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xf7 : Word)).toNat))) = true ∧
        next = cursor + ((b.zeroExtend 64 - (0xf7 : Word)) +
          BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xf7 : Word)).toNat)) +
          signExtend12 (1 : BitVec 12)) ∧
        len = (b.zeroExtend 64 - (0xf7 : Word)) +
          BitVec.ofNat 64 (Nat.fromBytesBE
            ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xf7 : Word)).toNat)) +
          signExtend12 (1 : BitVec 12)) )

/-- Invert `rlpItemDecode`: any decode at `off` exposes its prefix form — the range guards,
    the long-form / single-byte canonicality conjuncts, and the per-form **fit** conjuncts
    (the overflow-safe bound checks the program performs) — with the prefix byte identified as
    `bytes[off]`. The `next`/`len` equations are dropped. Used to refute the existence of a
    canonical decode on every reject path: the canonicality conjuncts refute `a1 = 4/5/6`, and
    the fit conjuncts refute `a1 = 3` (each is the exact negation of a bound-leaf check). -/
private theorem rlpItemDecode_dichotomy {bytes : List (BitVec 8)} {off : Nat}
    (hoff : off < bytes.length) {cursor endPtr next len : Word}
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    (BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true) ∨
    (¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true ∧
      BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
      ((bytes[off]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
        ∃ c : BitVec 8, bytes[off + 1]? = some c ∧
          ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) ∧
      BitVec.ult ((bytes[off]'hoff).zeroExtend 64 - (0x80 : Word)) (endPtr - cursor) = true) ∨
    (¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xb8 : Word) = true ∧
      BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      (∃ b1 : BitVec 8, bytes[off + 1]? = some b1 ∧ b1.zeroExtend 64 ≠ (0 : Word)) ∧
      ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop (off + 1)).take
        ((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) (56 : Word) = true ∧
      ¬ BitVec.ult endPtr (cursor + ((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word) +
          signExtend12 (1 : BitVec 12))) = true ∧
      ¬ BitVec.ult (endPtr - (cursor + ((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word) +
          signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop (off + 1)).take
          ((bytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) = true) ∨
    (¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (endPtr - cursor)
        ((bytes[off]'hoff).zeroExtend 64 - (0xc0 : Word) + signExtend12 (1 : BitVec 12)) = true) ∨
    (¬ BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      (∃ b1 : BitVec 8, bytes[off + 1]? = some b1 ∧ b1.zeroExtend 64 ≠ (0 : Word)) ∧
      ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop (off + 1)).take
        ((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
      ¬ BitVec.ult endPtr (cursor + ((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word) +
          signExtend12 (1 : BitVec 12))) = true ∧
      ¬ BitVec.ult (endPtr - (cursor + ((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word) +
          signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop (off + 1)).take
          ((bytes[off]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) = true) := by
  obtain ⟨b, hb, hdisj⟩ := h
  have hbe : b = bytes[off]'hoff := by
    rw [List.getElem?_eq_getElem hoff] at hb; exact (Option.some.inj hb).symm
  subst hbe
  rcases hdisj with ⟨h1, _, _, _⟩ | ⟨h1, h2, h3, h4, _, _⟩ | ⟨h1, h2, h3, h4, h5, h6, _, _⟩ |
    ⟨h1, h2, h3, _, _⟩ | ⟨h1, h2, h3, h4, h5, _, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨h1, h2, h3, h4⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4, h5, h6⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, h5⟩)))

/-- Single `a1 = 0` (ok) outcome of `rlp_walk_next`: the advanced cursor `a0 = next`, the
    reported length `a2 = len`, and the decode is the prefix-indicated one (`rlpItemDecode`,
    whose per-form **fit** conjuncts record the overflow-safe bound checks that passed).
    Memory (`bytesRegion`) lives in the dispatch's common frame, not here. -/
def rlpWalkNextOk (cursor endPtr : Word) (bytes : List (BitVec 8)) (off : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
      ⌜rlpItemDecode bytes off cursor endPtr next len⌝) h

/-- Weaken the **single**-byte accept post (`a0 = cursor+1`, `a2 = 1`) to `rlpWalkNextOk`. -/
theorem rlpWalkNextOk_of_single (srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (hoff : srcOff < srcBytes.length)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_single : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true) :
    ∀ h, ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (1 : Word))) h
      → rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  intro h hp
  refine ⟨(srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12), (1 : Word), ?_⟩
  refine sepConj_mono_right (sepConj_mono_right (fun h' hx12 =>
    (sepConj_pure_right h').2 ⟨hx12, ?_⟩)) h hp
  exact ⟨srcBytes[srcOff]'hoff, List.getElem?_eq_getElem hoff, Or.inl ⟨h_single, h_inb, rfl, rfl⟩⟩

/-- Weaken the **short string** accept post (`a0 = base+(off+1)+(p-0x80)`, `a2 = p-0x80`) to
    `rlpWalkNextOk`.  Covers both the multi-byte and canonical single-byte accepts. -/
theorem rlpWalkNextOk_of_short_string (srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (hoff : srcOff < srcBytes.length)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hcanon : (srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word) = (1 : Word) →
      ∃ c : BitVec 8, srcBytes[srcOff + 1]? = some c ∧
        ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true)
    (h_bound : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true) :
    ∀ h, ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 (srcOff + 1)) +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)))) h
      → rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  intro h hp
  refine ⟨(srcBase + BitVec.ofNat 64 (srcOff + 1)) +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)),
    (srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word), ?_⟩
  refine sepConj_mono_right (sepConj_mono_right (fun h' hx12 =>
    (sepConj_pure_right h').2 ⟨hx12, ?_⟩)) h hp
  refine ⟨srcBytes[srcOff]'hoff, List.getElem?_eq_getElem hoff,
    Or.inr (Or.inl ⟨h_lo, h_hi, hcanon, h_bound, ?_, rfl⟩)⟩
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide, wn_base_off_succ]

/-- Weaken the **short list** accept post (`a0 = cursor+((p-0xc0)+1)`, `a2 = (p-0xc0)+1`) to
    `rlpWalkNextOk`. -/
theorem rlpWalkNextOk_of_short_list (srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (hoff : srcOff < srcBytes.length)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_bound : ¬ BitVec.ult (endPtr - (srcBase + BitVec.ofNat 64 srcOff))
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = true) :
    ∀ h, ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) +
          (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)))) h
      → rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  intro h hp
  refine ⟨(srcBase + BitVec.ofNat 64 srcOff) +
      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)),
    ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12), ?_⟩
  refine sepConj_mono_right (sepConj_mono_right (fun h' hx12 =>
    (sepConj_pure_right h').2 ⟨hx12, ?_⟩)) h hp
  exact ⟨srcBytes[srcOff]'hoff, List.getElem?_eq_getElem hoff,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨h_lo, h_hi, h_bound, rfl, rfl⟩)))⟩

/-- Weaken the **long string** accept post (`a0 = cursor+(lol+1)+dec`, `a2 = dec`) to
    `rlpWalkNextOk`. -/
theorem rlpWalkNextOk_of_long_string (srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (hoff : srcOff < srcBytes.length) (hoff1 : srcOff + 1 < srcBytes.length)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) (56 : Word) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)))
        = true)
    (h_content : ¬ BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) = true) :
    ∀ h, ((.x10 ↦ᵣ (((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) +
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat)))) h
      → rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  intro h hp
  refine ⟨((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12))) +
      BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat)),
    BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat)), ?_⟩
  refine sepConj_mono_right (sepConj_mono_right (fun h' hx12 =>
    (sepConj_pure_right h').2 ⟨hx12, ?_⟩)) h hp
  exact ⟨srcBytes[srcOff]'hoff, List.getElem?_eq_getElem hoff,
    Or.inr (Or.inr (Or.inl ⟨h_lo, h_hi,
      ⟨srcBytes[srcOff + 1]'hoff1, List.getElem?_eq_getElem hoff1, h_fb⟩, h_nonmin, h_hdr,
        h_content, rfl, rfl⟩))⟩

/-- Weaken the **long list** accept post (`a0 = cursor+((lol+dec)+1)`, `a2 = (lol+dec)+1`) to
    `rlpWalkNextOk`. -/
theorem rlpWalkNextOk_of_long_list (srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (hoff : srcOff < srcBytes.length) (hoff1 : srcOff + 1 < srcBytes.length)
    (h_ge : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_fb : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_nonmin : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_hdr : ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
        = true)
    (h_content : ¬ BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))))
        (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) = true) :
    ∀ h, ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) +
              signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) +
              signExtend12 (1 : BitVec 12)))) h
      → rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  intro h hp
  refine ⟨(srcBase + BitVec.ofNat 64 srcOff) +
        (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) +
          signExtend12 (1 : BitVec 12)),
    ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
      BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) +
      signExtend12 (1 : BitVec 12), ?_⟩
  refine sepConj_mono_right (sepConj_mono_right (fun h' hx12 =>
    (sepConj_pure_right h').2 ⟨hx12, ?_⟩)) h hp
  exact ⟨srcBytes[srcOff]'hoff, List.getElem?_eq_getElem hoff,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨h_ge,
      ⟨srcBytes[srcOff + 1]'hoff1, List.getElem?_eq_getElem hoff1, h_fb⟩, h_nonmin, h_hdr,
        h_content, rfl, rfl⟩)))⟩

/-- **Unified strict `rlp_walk_next` dispatch.**  Given the common static preconditions
    (alignment, prefix readable) and the per-form length-field validity (needed only when the
    prefix selects that form), the routine reaches `ra` in `≤ 87` steps, clobbers `t0..t6`,
    and lands in exactly one of six outcomes distinguished by the status `a1`:
    `0` ok (a single canonical RLP item; advanced cursor `a0` and reported length `a2`
    described by `rlpWalkNextOk`), `2` end-of-list, `3` bound, `4` non-minimal long form,
    `5` leading-zero long form, `6` single-byte non-canonical short string. -/
theorem rlp_walk_next_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
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
    cpsTripleWithin 87 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) **
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
  set ptr := srcBase + BitVec.ofNat 64 srcOff with hptr
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  by_cases hinb : BitVec.ult ptr endPtr = true
  · -- in bounds: read prefix and dispatch
    by_cases hp80 : BitVec.ult pfx (0x80 : Word) = true
    · -- single (a1 = 0)
      have ht := cpsTripleWithin_frameR
        ((.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
        (by pcFree)
        (rlp_walk_next_single_spec_within base srcBase endPtr raVal a2Old t0Old t1Old srcBytes srcOff
          hsalign hoff hover hvalid hinb hp80)
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
      have hp1 := sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x30)
            (regIs_implies_regOwn .x31))))) h hp
      refine sepConj_mono_right (fun h' hbody => Or.inl
        (rlpWalkNextOk_of_single srcBase endPtr srcBytes srcOff hoff hinb hp80 h' hbody)) h ?_
      xperm_hyp hp1
    · by_cases hpb8 : BitVec.ult pfx (0xb8 : Word) = true
      · -- short string
        by_cases hbnd : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
            (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true
        · -- not bound (item fits); len = 1?
          by_cases hlen1 : (pfx - (0x80 : Word)) = (1 : Word)
          · -- len = 1; content byte
            obtain ⟨hoff1, hover1, hvalid1⟩ := hss hp80 hpb8
            by_cases hcb : BitVec.ult ((srcBytes[srcOff + 1]'hoff1).zeroExtend 64) (0x80 : Word) = true
            · -- non-canonical single byte (a1 = 6)
              have ht := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old)) (by pcFree)
                (rlp_walk_next_short_string_noncanon_spec_within base srcBase endPtr raVal a2Old t0Old
                  t1Old t2Old t3Old t4Old srcBytes srcOff hsalign hoff hoff1 hover hover1 hvalid hvalid1
                  hinb hp80 hpb8 hbnd hlen1 hcb)
              refine cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
              have hp1 := sepConj_mono (fun _ x => x)
                (sepConj_mono (regIs_implies_regOwn .x30) (regIs_implies_regOwn .x31)) h hp
              have hno : ¬ ∃ next len,
                  rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                rintro ⟨next, len, hdec⟩
                rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                · exact hp80 hc
                · obtain ⟨c, hcget, hcge⟩ := hc.2.2.1 hlen1
                  rw [List.getElem?_eq_getElem hoff1] at hcget
                  obtain rfl := (Option.some.inj hcget).symm
                  exact hcge hcb
                · exact hc.1 hpb8
                · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                    show (0xb8 : Word).toNat = 184 from by decide,
                    show (0xc0 : Word).toNat = 192 from by decide] at hpb8 ⊢; omega)
                · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                    show (0xb8 : Word).toNat = 184 from by decide,
                    show (0xf8 : Word).toNat = 248 from by decide] at hpb8 ⊢; omega)
              refine sepConj_mono_right (fun h' hbody =>
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (sepConj_mono_right (sepConj_mono_right
                  (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))))) h ?_
              xperm_hyp hp1
            · -- canonical single byte accept (a1 = 0)
              have ht := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old)) (by pcFree)
                (rlp_walk_next_short_string_single_spec_within base srcBase endPtr raVal a2Old t0Old
                  t1Old t2Old t3Old t4Old srcBytes srcOff hsalign hoff hoff1 hover hover1 hvalid hvalid1
                  hinb hp80 hpb8 hbnd hlen1 hcb)
              refine cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
              have hp1 := sepConj_mono (fun _ x => x)
                (sepConj_mono (regIs_implies_regOwn .x30) (regIs_implies_regOwn .x31)) h hp
              refine sepConj_mono_right (fun h' hbody => Or.inl
                (rlpWalkNextOk_of_short_string srcBase endPtr srcBytes srcOff hoff hp80 hpb8
                  (fun _ => ⟨srcBytes[srcOff + 1]'hoff1, List.getElem?_eq_getElem hoff1, hcb⟩)
                  hbnd h' hbody)) h ?_
              xperm_hyp hp1
          · -- len ≠ 1; multi-byte accept (a1 = 0)
            have ht := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old)) (by pcFree)
              (rlp_walk_next_short_string_spec_within base srcBase endPtr raVal a2Old t0Old t1Old
                t2Old t3Old t4Old srcBytes srcOff hsalign hoff hover hvalid hinb hp80 hpb8 hbnd hlen1)
            refine cpsTripleWithin_mono_nSteps (by omega)
              (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
            have hp1 := sepConj_mono (fun _ x => x)
              (sepConj_mono (regIs_implies_regOwn .x30) (regIs_implies_regOwn .x31)) h hp
            refine sepConj_mono_right (fun h' hbody => Or.inl
              (rlpWalkNextOk_of_short_string srcBase endPtr srcBytes srcOff hoff hp80 hpb8
                (fun h1 => absurd h1 hlen1) hbnd h' hbody)) h ?_
            xperm_hyp hp1
        · -- bound (a1 = 3)
          have ht := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old)) (by pcFree)
            (rlp_walk_next_short_string_bound_spec_within base srcBase endPtr raVal a2Old t0Old t1Old
              t2Old t3Old t4Old srcBytes srcOff hsalign hoff hover hvalid hinb hp80 hpb8 hbnd)
          refine cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
          have hp1 := sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn .x30) (regIs_implies_regOwn .x31)) h hp
          have hno : ¬ ∃ next len,
              rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
            rintro ⟨next, len, hdec⟩
            rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
            · exact hp80 hc
            · exact hbnd hc.2.2.2
            · exact hc.1 hpb8
            · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                show (0xb8 : Word).toNat = 184 from by decide,
                show (0xc0 : Word).toNat = 192 from by decide] at hpb8 ⊢; omega)
            · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                show (0xb8 : Word).toNat = 184 from by decide,
                show (0xf8 : Word).toNat = 248 from by decide] at hpb8 ⊢; omega)
          refine sepConj_mono_right (fun h' hbody =>
            Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
              (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))) h ?_
          xperm_hyp hp1
      · by_cases hpc0 : BitVec.ult pfx (0xc0 : Word) = true
        · -- long string
          obtain ⟨hllen, hlover, hlvalid⟩ := hls hpb8 hpc0
          rw [hpfx] at hllen hlover hlvalid
          have hge : 184 ≤ pfx.toNat := by
            simpa only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
              show (0xb8 : Word).toNat = 184 from by decide] using hpb8
          have hlt : pfx.toNat < 192 := by
            simpa only [BitVec.ult, decide_eq_true_eq,
              show (0xc0 : Word).toNat = 192 from by decide] using hpc0
          rw [hpfx] at hge hlt
          have hn1 : 1 ≤ ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat := by
            rw [BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
          have hn8 : ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
            rw [BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
          have hoff1 : srcOff + 1 < srcBytes.length := by omega
          have hover1 : srcBase.toNat + (srcOff + 1) < 2 ^ 64 := by omega
          have hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true := by
            have := hlvalid 0 (by omega); simpa using this
          by_cases hhdr : BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
              (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)))
              = true
          · -- header bound (a1 = 3)
            have ht := rlp_walk_next_long_string_header_spec_within base srcBase endPtr raVal a2Old
              t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hover hvalid
              hinb hpb8 hpc0 hhdr
            have hno : ¬ ∃ next len,
                rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
              rintro ⟨next, len, hdec⟩
              rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
              · exact hp80 hc
              · exact hpb8 hc.2.1
              · exact hc.2.2.2.2.1 hhdr
              · exact hc.1 hpc0
              · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                  show (0xc0 : Word).toNat = 192 from by decide,
                  show (0xf8 : Word).toNat = 248 from by decide] at hpc0 ⊢; omega)
            refine cpsTripleWithin_mono_nSteps (by omega)
              (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
            refine sepConj_mono_right (fun h' hbody =>
              Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))) h ?_
            xperm_hyp hp
          · by_cases hlz : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 = (0 : Word)
            · -- leading zero (a1 = 5)
              have ht := rlp_walk_next_long_string_lz_spec_within base srcBase endPtr raVal a2Old
                t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hoff1 hover
                hover1 hvalid hvalid1 hinb hpb8 hpc0 hhdr hlz
              have hno : ¬ ∃ next len,
                  rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                rintro ⟨next, len, hdec⟩
                rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                · exact hp80 hc
                · exact hpb8 hc.2.1
                · obtain ⟨b1, hb1, hb1ne⟩ := hc.2.2.1
                  rw [List.getElem?_eq_getElem hoff1] at hb1
                  obtain rfl := (Option.some.inj hb1).symm
                  exact hb1ne hlz
                · exact hc.1 hpc0
                · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                    show (0xc0 : Word).toNat = 192 from by decide,
                    show (0xf8 : Word).toNat = 248 from by decide] at hpc0 ⊢; omega)
              refine cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
              refine sepConj_mono_right (fun h' hbody =>
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                  (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))))) h ?_
              xperm_hyp hp
            · by_cases hmin : BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                  ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) (56 : Word) = true
              · -- non-minimal (a1 = 4)
                have ht := rlp_walk_next_long_string_nonmin_spec_within base srcBase endPtr raVal a2Old
                  t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hoff1 hover
                  hvalid hinb hpb8 hpc0 hllen hlover hlvalid hhdr hlz hmin
                have hno : ¬ ∃ next len,
                    rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                  rintro ⟨next, len, hdec⟩
                  rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                  · exact hp80 hc
                  · exact hpb8 hc.2.1
                  · exact hc.2.2.2.1 hmin
                  · exact hc.1 hpc0
                  · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                      show (0xc0 : Word).toNat = 192 from by decide,
                      show (0xf8 : Word).toNat = 248 from by decide] at hpc0 ⊢; omega)
                refine cpsTripleWithin_mono_nSteps (by omega)
                  (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                refine sepConj_mono_right (fun h' hbody =>
                  Or.inr (Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                    (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody))))) h ?_
                xperm_hyp hp
              · by_cases hcont : BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
                    (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) +
                      signExtend12 (1 : BitVec 12))))
                    (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) = true
                · -- content bound (a1 = 3)
                  have ht := rlp_walk_next_long_string_content_spec_within base srcBase endPtr raVal
                    a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hoff1
                    hover hvalid hinb hpb8 hpc0 hllen hlover hlvalid hhdr hlz hmin hcont
                  have hno : ¬ ∃ next len,
                      rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                    rintro ⟨next, len, hdec⟩
                    rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                    · exact hp80 hc
                    · exact hpb8 hc.2.1
                    · exact hc.2.2.2.2.2 hcont
                    · exact hc.1 hpc0
                    · exact hc.1 (by simp only [hpfx, BitVec.ult, decide_eq_true_eq,
                        show (0xc0 : Word).toNat = 192 from by decide,
                        show (0xf8 : Word).toNat = 248 from by decide] at hpc0 ⊢; omega)
                  refine cpsTripleWithin_mono_nSteps (by omega)
                    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                  refine sepConj_mono_right (fun h' hbody =>
                    Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                      (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))) h ?_
                  xperm_hyp hp
                · -- accept (a1 = 0)
                  have ht := rlp_walk_next_long_string_spec_within base srcBase endPtr raVal a2Old
                    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hoff1 hover
                    hvalid hinb hpb8 hpc0 hllen hlover hlvalid hhdr hlz hmin hcont
                  refine cpsTripleWithin_mono_nSteps (by omega)
                    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                  refine sepConj_mono_right (fun h' hbody => Or.inl
                    (rlpWalkNextOk_of_long_string srcBase endPtr srcBytes srcOff hoff hoff1 hpb8 hpc0
                      hlz hmin hhdr hcont h' hbody)) h ?_
                  xperm_hyp hp
        · by_cases hpf8 : BitVec.ult pfx (0xf8 : Word) = true
          · -- short list
            by_cases hbnd : BitVec.ult (endPtr - (srcBase + BitVec.ofNat 64 srcOff))
                ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) = true
            · -- bound (a1 = 3)
              have ht := cpsTripleWithin_frameR
                ((.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old))
                (by pcFree)
                (rlp_walk_next_short_list_bound_spec_within base srcBase endPtr raVal a2Old t0Old t1Old
                  t6Old srcBytes srcOff hsalign hoff hover hvalid hinb hpc0 hpf8 hbnd)
              refine cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
              have hp1 := sepConj_mono (fun _ x => x)
                (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (regIs_implies_regOwn .x29) (regIs_implies_regOwn .x30)))) h hp
              have hno : ¬ ∃ next len,
                  rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                rintro ⟨next, len, hdec⟩
                rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                · exact hp80 hc
                · exact hpb8 hc.2.1
                · exact hpc0 hc.2.1
                · exact hc.2.2 hbnd
                · exact hc.1 hpf8
              refine sepConj_mono_right (fun h' hbody =>
                Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                  (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))) h ?_
              xperm_hyp hp1
            · -- accept (a1 = 0)
              have ht := cpsTripleWithin_frameR
                ((.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old))
                (by pcFree)
                (rlp_walk_next_short_list_spec_within base srcBase endPtr raVal a2Old t0Old t1Old
                  t6Old srcBytes srcOff hsalign hoff hover hvalid hinb hpc0 hpf8 hbnd)
              refine cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
              have hp1 := sepConj_mono (fun _ x => x)
                (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (regIs_implies_regOwn .x29) (regIs_implies_regOwn .x30)))) h hp
              refine sepConj_mono_right (fun h' hbody => Or.inl
                (rlpWalkNextOk_of_short_list srcBase endPtr srcBytes srcOff hoff hpc0 hpf8
                  hbnd h' hbody)) h ?_
              xperm_hyp hp1
          · -- long list
            obtain ⟨hllen, hlover, hlvalid⟩ := hll hpf8
            rw [hpfx] at hllen hlover hlvalid
            have hge : 248 ≤ pfx.toNat := by
              simpa only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
                show (0xf8 : Word).toNat = 248 from by decide] using hpf8
            have hlt : pfx.toNat < 256 := by
              rw [hpfx, BitVec.toNat_setWidth]; have := (srcBytes[srcOff]'hoff).isLt; omega
            rw [hpfx] at hge hlt
            have hn1 : 1 ≤ ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat := by
              rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
            have hn8 : ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
              rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
            have hoff1 : srcOff + 1 < srcBytes.length := by omega
            have hover1 : srcBase.toNat + (srcOff + 1) < 2 ^ 64 := by omega
            have hvalid1 : isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true := by
              have := hlvalid 0 (by omega); simpa using this
            by_cases hhdr : BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
                (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12))) = true
            · -- header bound (a1 = 3)
              have ht := rlp_walk_next_long_list_header_spec_within base srcBase endPtr raVal a2Old
                t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hover hvalid
                hinb hpf8 hhdr
              have hno : ¬ ∃ next len,
                  rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                rintro ⟨next, len, hdec⟩
                rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                · exact hp80 hc
                · exact hpb8 hc.2.1
                · exact hpc0 hc.2.1
                · exact hpf8 hc.2.1
                · exact hc.2.2.2.1 hhdr
              refine cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
              refine sepConj_mono_right (fun h' hbody =>
                Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                  (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))) h ?_
              xperm_hyp hp
            · by_cases hlz : (srcBytes[srcOff + 1]'hoff1).zeroExtend 64 = (0 : Word)
              · -- leading zero (a1 = 5)
                have ht := rlp_walk_next_long_list_lz_spec_within base srcBase endPtr raVal a2Old
                  t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hoff1 hover
                  hover1 hvalid hvalid1 hinb hpf8 hhdr hlz
                have hno : ¬ ∃ next len,
                    rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                  rintro ⟨next, len, hdec⟩
                  rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                  · exact hp80 hc
                  · exact hpb8 hc.2.1
                  · exact hpc0 hc.2.1
                  · exact hpf8 hc.2.1
                  · obtain ⟨b1, hb1, hb1ne⟩ := hc.2.1
                    rw [List.getElem?_eq_getElem hoff1] at hb1
                    obtain rfl := (Option.some.inj hb1).symm
                    exact hb1ne hlz
                refine cpsTripleWithin_mono_nSteps (by omega)
                  (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                refine sepConj_mono_right (fun h' hbody =>
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                    (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))))) h ?_
                xperm_hyp hp
              · by_cases hmin : BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                    ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true
                · -- non-minimal (a1 = 4)
                  have ht := rlp_walk_next_long_list_nonmin_spec_within base srcBase endPtr raVal a2Old
                    t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hoff1 hover
                    hvalid hinb hpf8 hllen hlover hlvalid hhdr hlz hmin
                  have hno : ¬ ∃ next len,
                      rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                    rintro ⟨next, len, hdec⟩
                    rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                    · exact hp80 hc
                    · exact hpb8 hc.2.1
                    · exact hpc0 hc.2.1
                    · exact hpf8 hc.2.1
                    · exact hc.2.2.1 hmin
                  refine cpsTripleWithin_mono_nSteps (by omega)
                    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                  refine sepConj_mono_right (fun h' hbody =>
                    Or.inr (Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                      (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody))))) h ?_
                  xperm_hyp hp
                · by_cases hcont : BitVec.ult (endPtr - ((srcBase + BitVec.ofNat 64 srcOff) +
                      (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                        signExtend12 (1 : BitVec 12))))
                      (BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
                        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) = true
                  · -- content bound (a1 = 3)
                    have ht := rlp_walk_next_long_list_content_spec_within base srcBase endPtr raVal
                      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff
                      hoff1 hover hvalid hinb hpf8 hllen hlover hlvalid hhdr hlz hmin hcont
                    have hno : ¬ ∃ next len,
                        rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len := by
                      rintro ⟨next, len, hdec⟩
                      rcases rlpItemDecode_dichotomy hoff hdec with hc | hc | hc | hc | hc
                      · exact hp80 hc
                      · exact hpb8 hc.2.1
                      · exact hpc0 hc.2.1
                      · exact hpf8 hc.2.1
                      · exact hc.2.2.2.2 hcont
                    refine cpsTripleWithin_mono_nSteps (by omega)
                      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                    refine sepConj_mono_right (fun h' hbody =>
                      Or.inr (Or.inr (Or.inl (sepConj_mono_right (sepConj_mono_right
                        (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hno⟩)) h' hbody)))) h ?_
                    xperm_hyp hp
                  · -- accept (a1 = 0)
                    have ht := rlp_walk_next_long_list_spec_within base srcBase endPtr raVal a2Old
                      t0Old t1Old t2Old t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hoff1
                      hover hvalid hinb hpf8 hllen hlover hlvalid hhdr hlz hmin hcont
                    refine cpsTripleWithin_mono_nSteps (by omega)
                      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                    refine sepConj_mono_right (fun h' hbody => Or.inl
                      (rlpWalkNextOk_of_long_list srcBase endPtr srcBytes srcOff hoff hoff1 hpf8
                        hlz hmin hhdr hcont h' hbody)) h ?_
                    xperm_hyp hp
  · -- end of list (a1 = 2)
    have ht := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** bytesRegion srcBase srcBytes) (by pcFree)
      (rlp_walk_next_end_spec_within base ptr endPtr raVal a2Old hinb)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
    have hp1 := sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x30)
            (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x)))))))) h hp
    refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inl
      (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
        (sepConj_pure_right h'').2 ⟨hb, hinb⟩)) h' hbody))) h ?_
    xperm_hyp hp1

end EvmAsm.Rv64.RLP
