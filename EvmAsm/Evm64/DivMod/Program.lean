/-
  EvmAsm.Evm64.DivMod

  256-bit EVM DIV and MOD as 64-bit RISC-V programs.
  DIV(a, b) pops a and b, pushes a / b (integer division).
  MOD(a, b) pops a and b, pushes a % b (modulo).
  If b = 0, both return 0 (EVM convention, no trap).

  Algorithm: Knuth Algorithm D (TAOCP Vol 2, §4.3.1) in base 2^64.
  Processes one 64-bit quotient digit per iteration (max 4 iterations).
  Uses hardware DIVU for trial quotient via 128/64-bit division subroutine
  (half-word decomposition, Hacker's Delight divlu).

  Memory layout (before pop):
    sp+0..sp+24:    a (4 LE limbs, dividend)
    sp+32..sp+56:   b (4 LE limbs, divisor)
  Scratch (negative offsets, unsigned BitVec 12):
    4088(-8)..4064(-32):   q[0..3] quotient
    4056(-40)..4024(-72):  u[0..4] normalized dividend
    4016(-80)..4000(-96):  u[5..7] padding (zero, for mul-sub overflow)
    3992(-104):            shift (CLZ amount)
    3984(-112):            n (number of significant limbs of b)
    3976(-120):            saved j (loop counter)
    3968(-128):            subroutine: saved return addr
    3960(-136):            subroutine: saved d
    3952(-144):            subroutine: saved dLo
    3944(-152):            subroutine: saved un0
  After: result at sp+32..sp+56, x12 = sp + 32.

  Register allocation:
    x12 = EVM stack pointer (preserved)
    x9  = loop counter j
    x1  = temp (used inside div128 subroutine)
    x2  = antiShift / subroutine return addr
    x5  = general temp
    x6  = general temp / uBase in mul-sub
    x7  = general temp
    x10 = general temp / carry in mul-sub
    x11 = general temp / qHat
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- 128/64-bit unsigned division subroutine
-- ============================================================================

/-- 128/64-bit unsigned division subroutine (Hacker's Delight divlu).
    Called via JAL x2, offset. Returns via JALR x0, x2, 0.
    Input: x7 = uHi (< d), x5 = uLo, x10 = d (normalized, >= 2^63)
    Output: x11 = floor((uHi * 2^64 + uLo) / d)
    Clobbers: .x9, x5, x6, x7, x10, x11. Preserves: x2, x12.
    Uses scratch memory at 3992, 3984, 3976, 3968 (offsets from x12). -/
def divK_div128 : Program :=
  -- Save return addr and d
  SD .x12 .x2 3968 ;;                         -- [0]  save return addr
  SD .x12 .x10 3960 ;;                        -- [1]  save d
  -- Split d: dHi = d >> 32, dLo = (d << 32) >> 32
  SRLI .x6 .x10 32 ;;                         -- [2]  x6 = dHi (>= 2^31)
  SLLI .x9 .x10 32 ;; SRLI .x9 .x9 32 ;;     -- [3,4] x9 = dLo
  SD .x12 .x9 3952 ;;                         -- [5]  save dLo
  -- Split uLo: un1 = uLo >> 32, un0 = (uLo << 32) >> 32
  SRLI .x11 .x5 32 ;;                         -- [6]  x11 = un1
  SLLI .x5 .x5 32 ;; SRLI .x5 .x5 32 ;;      -- [7,8] x5 = un0
  SD .x12 .x5 3944 ;;                         -- [9]  save un0
  -- Step 1: q1 = DIVU(uHi, dHi), rhat = uHi - q1*dHi
  -- x7 = uHi, x6 = dHi
  single (.DIVU .x10 .x7 .x6) ;;             -- [10] x10 = q1 (use x10 since we saved d)
  single (.MUL .x5 .x10 .x6) ;;              -- [11] x5 = q1 * dHi
  single (.SUB .x7 .x7 .x5) ;;               -- [12] x7 = rhat
  -- Refine q1: clamp to < 2^32
  SRLI .x5 .x10 32 ;;                         -- [13] test q1 >= 2^32
  single (.BEQ .x5 .x0 12) ;;                -- [14] skip if q1 < 2^32 → [17]
  ADDI .x10 .x10 4095 ;;                      -- [15] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [16] rhat += dHi
  -- [17] Product check: q1*dLo > rhat*2^32 + un1?
  LD .x9 .x12 3952 ;;                         -- [17] x9 = dLo
  single (.MUL .x5 .x10 .x9) ;;              -- [18] x5 = q1 * dLo
  SLLI .x9 .x7 32 ;;                          -- [19] x9 = rhat << 32
  single (.OR .x9 .x9 .x11) ;;               -- [20] x9 = rhat*2^32 + un1
  single (.BLTU .x9 .x5 8) ;;                -- [21] if rhs < lhs → correct [23]
  JAL .x0 12 ;;                                -- [22] skip → [25]
  ADDI .x10 .x10 4095 ;;                      -- [23] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [24] rhat += dHi
  -- Compute un21 = rhat*2^32 + un1 - q1*dLo
  LD .x9 .x12 3952 ;;                         -- [25] dLo
  SLLI .x5 .x7 32 ;;                          -- [26] rhat << 32
  single (.OR .x5 .x5 .x11) ;;               -- [27] x5 = rhat*2^32 + un1
  single (.MUL .x9 .x10 .x9) ;;              -- [28] x9 = q1 * dLo
  single (.SUB .x7 .x5 .x9) ;;               -- [29] x7 = un21
  -- Step 2: q0 = DIVU(un21, dHi), rhat2 = un21 - q0*dHi
  single (.DIVU .x5 .x7 .x6) ;;              -- [30] x5 = q0
  single (.MUL .x9 .x5 .x6) ;;               -- [31]
  single (.SUB .x11 .x7 .x9) ;;              -- [32] x11 = rhat2
  -- Refine q0: clamp
  SRLI .x9 .x5 32 ;;                          -- [33]
  single (.BEQ .x9 .x0 12) ;;                -- [34] skip if q0 < 2^32 → [37]
  ADDI .x5 .x5 4095 ;;                        -- [35] q0--
  single (.ADD .x11 .x11 .x6) ;;             -- [36] rhat2 += dHi
  -- [37] Phase 2b guard (Knuth TAOCP §4.3.1 Step D3): skip mul-check
  --      when rhat2c ≥ 2^32 to avoid Word `<< 32` truncation causing
  --      the BLTU to false-positive fire. See counterexample at
  --      `/home/zksecurity/.claude/plans/dynamic-strolling-riddle.md`.
  SRLI .x9 .x11 32 ;;                         -- [37] x9 = rhat2c >> 32
  single (.BNE .x9 .x0 36) ;;                -- [38] if nonzero → skip to [47]
  -- [39] Product check for q0 (only reached when rhat2c < 2^32)
  LD .x9 .x12 3952 ;;                         -- [39] dLo
  single (.MUL .x7 .x5 .x9) ;;               -- [40] x7 = q0 * dLo
  SLLI .x9 .x11 32 ;;                         -- [41] rhat2 << 32
  LD .x11 .x12 3944 ;;                        -- [42] un0
  single (.OR .x9 .x9 .x11) ;;               -- [43] x9 = rhat2*2^32 + un0
  single (.BLTU .x9 .x7 8) ;;                -- [44] if rhs < lhs → correct [46]
  JAL .x0 8 ;;                                 -- [45] skip → [47]
  ADDI .x5 .x5 4095 ;;                        -- [46] q0--
  -- Combine: q = q1*2^32 + q0
  SLLI .x11 .x10 32 ;;                        -- [47] q1 << 32
  single (.OR .x11 .x11 .x5) ;;              -- [48] x11 = q
  -- Restore and return
  LD .x2 .x12 3968 ;;                         -- [49] restore return addr
  JALR .x0 .x2 0                              -- [50] return
  -- Total: 51 instructions

/-- **FIXED** 128/64-bit unsigned division subroutine — same as `divK_div128`
    but with Knuth's classical 2nd D3 correction iteration added (TAOCP
    4.3.1). The 2nd correction has the `rhat < B` guard, mirroring the
    existing Phase 2b guard at lines 107-108.

    This fixes the algorithm correctness bug; see the deleted
    SpecCallAddbackBeq counterexample scaffolding and the matching Lean
    abstraction `div128Quot_v2` (in `LoopDefs/Iter.lean`).

    **Layout**:
    - [0..24]: same as `divK_div128` (initial split + Phase 1a + 1st D3).
    - **[25..34]: NEW — Phase 1b 2nd D3 correction (10 instructions)**.
      Mirrors Phase 2b's guarded D3 at [37..46] in `divK_div128`.
    - [35..60]: original [25..50] shifted by 10 (Phase 2 + finish).

    Total: 61 instructions (vs 51 in the buggy version).

    **Migration**: callers of `divK_div128` should be updated to call
    `divK_div128_v2` (this requires updating offsets in the main loop
    at `divK_loopBody`, since the subroutine moved). Once all use-sites
    migrate, the buggy `divK_div128` should be removed. -/
def divK_div128_v2 : Program :=
  -- Save return addr and d
  SD .x12 .x2 3968 ;;                         -- [0]  save return addr
  SD .x12 .x10 3960 ;;                        -- [1]  save d
  -- Split d: dHi = d >> 32, dLo = (d << 32) >> 32
  SRLI .x6 .x10 32 ;;                         -- [2]  x6 = dHi (>= 2^31)
  SLLI .x9 .x10 32 ;; SRLI .x9 .x9 32 ;;     -- [3,4] x9 = dLo
  SD .x12 .x9 3952 ;;                         -- [5]  save dLo
  -- Split uLo: un1 = uLo >> 32, un0 = (uLo << 32) >> 32
  SRLI .x11 .x5 32 ;;                         -- [6]  x11 = un1
  SLLI .x5 .x5 32 ;; SRLI .x5 .x5 32 ;;      -- [7,8] x5 = un0
  SD .x12 .x5 3944 ;;                         -- [9]  save un0
  -- Step 1: q1 = DIVU(uHi, dHi), rhat = uHi - q1*dHi
  single (.DIVU .x10 .x7 .x6) ;;             -- [10] x10 = q1
  single (.MUL .x5 .x10 .x6) ;;              -- [11] x5 = q1 * dHi
  single (.SUB .x7 .x7 .x5) ;;               -- [12] x7 = rhat
  -- Refine q1: clamp to < 2^32
  SRLI .x5 .x10 32 ;;                         -- [13] test q1 >= 2^32
  single (.BEQ .x5 .x0 12) ;;                -- [14] skip if q1 < 2^32 → [17]
  ADDI .x10 .x10 4095 ;;                      -- [15] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [16] rhat += dHi
  -- [17] Phase 1b 1st D3 correction: q1*dLo > rhat*2^32 + un1?
  LD .x9 .x12 3952 ;;                         -- [17] x9 = dLo
  single (.MUL .x5 .x10 .x9) ;;              -- [18] x5 = q1 * dLo
  SLLI .x9 .x7 32 ;;                          -- [19] x9 = rhat << 32
  single (.OR .x9 .x9 .x11) ;;               -- [20] x9 = rhat*2^32 + un1
  single (.BLTU .x9 .x5 8) ;;                -- [21] if rhs < lhs → correct [23]
  JAL .x0 12 ;;                                -- [22] skip → [25]
  ADDI .x10 .x10 4095 ;;                      -- [23] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [24] rhat += dHi
  -- [25] Phase 1b 2nd D3 correction (Knuth TAOCP §4.3.1 D3 loop, full).
  --      Guard: skip mul-check when rhat ≥ 2^32 (matches Phase 2b's guard
  --      at [47..48] below). Without this, BLTU would false-positive fire
  --      due to `<< 32` truncation. Mirrors Phase 2b structure.
  SRLI .x9 .x7 32 ;;                          -- [25] x9 = rhat >> 32
  single (.BNE .x9 .x0 36) ;;                -- [26] if nonzero → skip to [35]
  -- [27] 2nd D3 product check (only when rhat < 2^32)
  LD .x9 .x12 3952 ;;                         -- [27] dLo
  single (.MUL .x5 .x10 .x9) ;;              -- [28] x5 = q1 * dLo
  SLLI .x9 .x7 32 ;;                          -- [29] x9 = rhat << 32
  single (.OR .x9 .x9 .x11) ;;               -- [30] x9 = rhat*2^32 + un1
  single (.BLTU .x9 .x5 8) ;;                -- [31] if rhs < lhs → correct [33]
  JAL .x0 12 ;;                                -- [32] skip → [35]
  ADDI .x10 .x10 4095 ;;                      -- [33] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [34] rhat += dHi
  -- [35] Compute un21 = rhat*2^32 + un1 - q1*dLo
  LD .x9 .x12 3952 ;;                         -- [35] dLo
  SLLI .x5 .x7 32 ;;                          -- [36] rhat << 32
  single (.OR .x5 .x5 .x11) ;;               -- [37] x5 = rhat*2^32 + un1
  single (.MUL .x9 .x10 .x9) ;;              -- [38] x9 = q1 * dLo
  single (.SUB .x7 .x5 .x9) ;;               -- [39] x7 = un21
  -- Step 2: q0 = DIVU(un21, dHi), rhat2 = un21 - q0*dHi
  single (.DIVU .x5 .x7 .x6) ;;              -- [40] x5 = q0
  single (.MUL .x9 .x5 .x6) ;;               -- [41]
  single (.SUB .x11 .x7 .x9) ;;              -- [42] x11 = rhat2
  -- Refine q0: clamp
  SRLI .x9 .x5 32 ;;                          -- [43]
  single (.BEQ .x9 .x0 12) ;;                -- [44] skip if q0 < 2^32 → [47]
  ADDI .x5 .x5 4095 ;;                        -- [45] q0--
  single (.ADD .x11 .x11 .x6) ;;             -- [46] rhat2 += dHi
  -- [47] Phase 2b guard (rhat2c ≥ 2^32 ⟹ skip mul-check)
  SRLI .x9 .x11 32 ;;                         -- [47] x9 = rhat2c >> 32
  single (.BNE .x9 .x0 36) ;;                -- [48] if nonzero → skip to [57]
  -- [49] Product check for q0
  LD .x9 .x12 3952 ;;                         -- [49] dLo
  single (.MUL .x7 .x5 .x9) ;;               -- [50] x7 = q0 * dLo
  SLLI .x9 .x11 32 ;;                         -- [51] rhat2 << 32
  LD .x11 .x12 3944 ;;                        -- [52] un0
  single (.OR .x9 .x9 .x11) ;;               -- [53] x9 = rhat2*2^32 + un0
  single (.BLTU .x9 .x7 8) ;;                -- [54] if rhs < lhs → correct [56]
  JAL .x0 8 ;;                                 -- [55] skip → [57]
  ADDI .x5 .x5 4095 ;;                        -- [56] q0--
  -- Combine: q = q1*2^32 + q0
  SLLI .x11 .x10 32 ;;                        -- [57] q1 << 32
  single (.OR .x11 .x11 .x5) ;;              -- [58] x11 = q
  -- Restore and return
  LD .x2 .x12 3968 ;;                         -- [59] restore return addr
  JALR .x0 .x2 0                              -- [60] return
  -- Total: 61 instructions (51 + 10 for 2nd D3 correction)

/-- **FULL Knuth Algorithm D** 128/64-bit unsigned division subroutine.
    Same as `divK_div128_v2` but ALSO adds Phase 2b 2nd D3 correction.
    Matches the Lean abstraction `div128Quot_v4` in `LoopDefs/IterV4.lean`.

    With Phase 2b 2-correction, the trial quotient `qHat` equals
    `q*_full = ⌊(uHi*2^64 + uLo) / vTop⌋` exactly (no per-phase
    overshoot). This was the v4 closure route for the n=4 call-addback
    semantic target (proven in PR #1418, Layer 2a fwd/back + c3 sub-stub
    all closed).

    **Layout** (75 instructions total):
    - [0..46]: identical to `divK_div128_v2` (setup + Phase 1a + Phase
      1b 1st+2nd D3 + un21 + q0 init/clamp).
    - [47..70]: Phase 2b with BOTH 1st AND 2nd D3 corrections (24 inst,
      vs v2's 10-inst Phase 2b).
    - [71..74]: combine + restore + return.

    **Register-allocation note**: the existing v2 Phase 2b clobbers
    `rhat2c` (x11) at [52] when loading un0. For v4's 2nd D3 we need
    rhat2c again, so we save it to scratch slot 3936 before [52],
    then restore it after the 1st-correction path completes. This
    adds ~3 instructions vs the naive 10 for the 2nd D3 alone.

    **Migration**: callers should be updated to use `divK_div128_v4`.
    See `project_v2_to_v4_migration_plan` in the project memory. -/
def divK_div128_v4 : Program :=
  -- Save return addr and d
  SD .x12 .x2 3968 ;;                         -- [0]  save return addr
  SD .x12 .x10 3960 ;;                        -- [1]  save d
  -- Split d: dHi = d >> 32, dLo = (d << 32) >> 32
  SRLI .x6 .x10 32 ;;                         -- [2]  x6 = dHi (>= 2^31)
  SLLI .x9 .x10 32 ;; SRLI .x9 .x9 32 ;;     -- [3,4] x9 = dLo
  SD .x12 .x9 3952 ;;                         -- [5]  save dLo
  -- Split uLo: un1 = uLo >> 32, un0 = (uLo << 32) >> 32
  SRLI .x11 .x5 32 ;;                         -- [6]  x11 = un1
  SLLI .x5 .x5 32 ;; SRLI .x5 .x5 32 ;;      -- [7,8] x5 = un0
  SD .x12 .x5 3944 ;;                         -- [9]  save un0
  -- Step 1: q1 = DIVU(uHi, dHi), rhat = uHi - q1*dHi
  single (.DIVU .x10 .x7 .x6) ;;             -- [10] x10 = q1
  single (.MUL .x5 .x10 .x6) ;;              -- [11] x5 = q1 * dHi
  single (.SUB .x7 .x7 .x5) ;;               -- [12] x7 = rhat
  -- Refine q1: clamp to < 2^32
  SRLI .x5 .x10 32 ;;                         -- [13] test q1 >= 2^32
  single (.BEQ .x5 .x0 12) ;;                -- [14] skip if q1 < 2^32 → [17]
  ADDI .x10 .x10 4095 ;;                      -- [15] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [16] rhat += dHi
  -- [17] Phase 1b 1st D3 correction
  LD .x9 .x12 3952 ;;                         -- [17] x9 = dLo
  single (.MUL .x5 .x10 .x9) ;;              -- [18] x5 = q1 * dLo
  SLLI .x9 .x7 32 ;;                          -- [19] x9 = rhat << 32
  single (.OR .x9 .x9 .x11) ;;               -- [20] x9 = rhat*2^32 + un1
  single (.BLTU .x9 .x5 8) ;;                -- [21] if rhs < lhs → correct [23]
  JAL .x0 12 ;;                                -- [22] skip → [25]
  ADDI .x10 .x10 4095 ;;                      -- [23] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [24] rhat += dHi
  -- [25] Phase 1b 2nd D3 correction
  SRLI .x9 .x7 32 ;;                          -- [25] x9 = rhat >> 32
  single (.BNE .x9 .x0 36) ;;                -- [26] if nonzero → skip to [35]
  LD .x9 .x12 3952 ;;                         -- [27] dLo
  single (.MUL .x5 .x10 .x9) ;;              -- [28] x5 = q1 * dLo
  SLLI .x9 .x7 32 ;;                          -- [29] x9 = rhat << 32
  single (.OR .x9 .x9 .x11) ;;               -- [30] x9 = rhat*2^32 + un1
  single (.BLTU .x9 .x5 8) ;;                -- [31] if rhs < lhs → correct [33]
  JAL .x0 12 ;;                                -- [32] skip → [35]
  ADDI .x10 .x10 4095 ;;                      -- [33] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [34] rhat += dHi
  -- [35] Compute un21 = rhat*2^32 + un1 - q1*dLo
  LD .x9 .x12 3952 ;;                         -- [35] dLo
  SLLI .x5 .x7 32 ;;                          -- [36] rhat << 32
  single (.OR .x5 .x5 .x11) ;;               -- [37] x5 = rhat*2^32 + un1
  single (.MUL .x9 .x10 .x9) ;;              -- [38] x9 = q1 * dLo
  single (.SUB .x7 .x5 .x9) ;;               -- [39] x7 = un21
  -- Step 2: q0 = DIVU(un21, dHi), rhat2 = un21 - q0*dHi
  single (.DIVU .x5 .x7 .x6) ;;              -- [40] x5 = q0
  single (.MUL .x9 .x5 .x6) ;;               -- [41]
  single (.SUB .x11 .x7 .x9) ;;              -- [42] x11 = rhat2
  -- Refine q0: clamp
  SRLI .x9 .x5 32 ;;                          -- [43]
  single (.BEQ .x9 .x0 12) ;;                -- [44] skip if q0 < 2^32 → [47]
  ADDI .x5 .x5 4095 ;;                        -- [45] q0--
  single (.ADD .x11 .x11 .x6) ;;             -- [46] rhat2 += dHi
  -- [47] Phase 2b guard (rhat2c ≥ 2^32 ⟹ skip BOTH 1st and 2nd D3)
  SRLI .x9 .x11 32 ;;                         -- [47] x9 = rhat2c >> 32
  single (.BNE .x9 .x0 92) ;;                -- [48] if nonzero → skip to [71] (combine)
  -- [49] Phase 2b 1st D3 mul-check
  LD .x9 .x12 3952 ;;                         -- [49] dLo
  single (.MUL .x7 .x5 .x9) ;;               -- [50] x7 = q0 * dLo
  SLLI .x9 .x11 32 ;;                         -- [51] rhat2c << 32
  SD .x12 .x11 3936 ;;                        -- [52] save rhat2c (NEW in v4)
  LD .x11 .x12 3944 ;;                        -- [53] x11 = un0 (clobbers rhat2c)
  single (.OR .x9 .x9 .x11) ;;               -- [54] x9 = rhat2c*2^32 + un0
  single (.BLTU .x9 .x7 12) ;;               -- [55] if BLTU fires → correction [58]
  -- [56] No-correction path
  LD .x11 .x12 3936 ;;                        -- [56] restore rhat2c (unchanged)
  JAL .x0 16 ;;                                -- [57] skip correction → [61] (2nd D3 entry)
  -- [58] Correction path
  ADDI .x5 .x5 4095 ;;                        -- [58] q0--
  LD .x11 .x12 3936 ;;                        -- [59] restore rhat2c
  single (.ADD .x11 .x11 .x6) ;;             -- [60] rhat2c += dHi
  -- [61] Phase 2b 2nd D3 guarded mul-check (NEW in v4 vs v2)
  SRLI .x9 .x11 32 ;;                         -- [61] x9 = rhat2c >> 32 (post-1st-correction)
  single (.BNE .x9 .x0 36) ;;                -- [62] if nonzero → skip to [71] (combine)
  LD .x9 .x12 3952 ;;                         -- [63] dLo
  single (.MUL .x7 .x5 .x9) ;;               -- [64] x7 = q0 * dLo
  SLLI .x9 .x11 32 ;;                         -- [65] rhat2c << 32
  LD .x11 .x12 3944 ;;                        -- [66] x11 = un0 (last use of rhat2c, no save needed)
  single (.OR .x9 .x9 .x11) ;;               -- [67] x9 = rhat2c*2^32 + un0
  single (.BLTU .x9 .x7 8) ;;                -- [68] if BLTU fires → 2nd correction [70]
  JAL .x0 8 ;;                                 -- [69] skip → [71]
  ADDI .x5 .x5 4095 ;;                        -- [70] 2nd correction: q0--
  -- [71] Combine: q = q1*2^32 + q0
  SLLI .x11 .x10 32 ;;                        -- [71] q1 << 32
  single (.OR .x11 .x11 .x5) ;;              -- [72] x11 = q
  -- Restore and return
  LD .x2 .x12 3968 ;;                         -- [73] restore return addr
  JALR .x0 .x2 0                              -- [74] return
  -- Total: 75 instructions (61 v2 + 14 for Phase 2b 2nd D3 + save/restore)

/-- **v5** 128/64-bit unsigned division subroutine — repairs the two
    buggy ULTs in `divK_div128_v4` (PR #7077, PR #7080). Matches the
    math model `div128Quot_v5` in `LoopDefs/IterV5.lean`. Beads
    `evm-asm-wbc4i.3.1` (Phase-1a) and `evm-asm-wbc4i.3.2` (Phase-2a).

    **Phase-1a cap**: when `hi1 = q1 >> 32 ≠ 0`, cap `q1c := 0xFFFFFFFF`
    (instead of `q1 - 1`) and recompute `rhatc := rhat + (q1 - q1c)*dHi`
    (algebraically `uHi - q1c*dHi` since `rhat = uHi - q1*dHi`).

    **Phase-2a cap** (this bead): analogous — when `hi2 = q0 >> 32 ≠ 0`,
    cap `q0c := 0xFFFFFFFF` and recompute `rhat2c := rhat2 + (q0 - q0c)*dHi`.

    The two caps together guarantee `q1c, q0c < 2^32` unconditionally so
    that `q1c * dLo` and `q0c * dLo` cannot wrap mod 2^64. PR #7080's
    `cePlus2_*` and `ceUnd_*` inputs no longer violate the Knuth-A `+1`
    bound under this program (to be proven in beads `.4` and `.5`).

    **Phase-1b guard** (Knuth D3): after the Phase-1a cap sets `q1c := b-1`,
    the recomputed `rhatc = uHi - q1c*dHi` can be `≥ 2^32`. Knuth's D3 step
    repeats the product-test correction only while `r̂ < b`, so both Phase-1b
    corrections must be skipped when `rhatc ≥ 2^32`. v5 adds a leading guard
    (`SRLI; BNE` at [21..22]) mirroring the Phase-2b guard at [57..58]. Without
    it the 1st-correction ULT misfires on wide `rhatc` (the PR #7077 / #7080
    bug). This matches the `rhatc >>> 32 = 0` guard in `div128Quot_v5`.

    **Layout** (85 instructions = 75 v4 + 4 Phase-1a + 4 Phase-2a + 2 Phase-1b guard):
    - [0..12]: identical to v4 (setup + DIVU + rhat).
    - [13..20]: v5 Phase-1a cap block (8 inst, vs v4's 4 at [13..16]).
    - [21..22]: v5 Phase-1b leading guard (skip both corrections when rhatc ≥ 2^32).
    - [23..48]: v4 instructions [17..42] shifted by +6 indices.
    - [49..56]: v5 Phase-2a cap block (8 inst, vs v4's 4 at [43..46]).
    - [57..84]: v4 instructions [47..74] shifted by +10 indices.

    Forward branches either jump within a single shifted segment (relative
    offset preserved), are the [14] / [50] cap BEQs (offset 28, skip the
    6-inst cap body), or are the phase guards: [22] (offset 76 → compute_un21
    at [41]) and [58] (offset 92 → combine at [81]). -/
def divK_div128_v5 : Program :=
  -- Save return addr and d
  SD .x12 .x2 3968 ;;                         -- [0]  save return addr
  SD .x12 .x10 3960 ;;                        -- [1]  save d
  -- Split d: dHi = d >> 32, dLo = (d << 32) >> 32
  SRLI .x6 .x10 32 ;;                         -- [2]  x6 = dHi (>= 2^31)
  SLLI .x9 .x10 32 ;; SRLI .x9 .x9 32 ;;     -- [3,4] x9 = dLo
  SD .x12 .x9 3952 ;;                         -- [5]  save dLo
  -- Split uLo: un1 = uLo >> 32, un0 = (uLo << 32) >> 32
  SRLI .x11 .x5 32 ;;                         -- [6]  x11 = un1
  SLLI .x5 .x5 32 ;; SRLI .x5 .x5 32 ;;      -- [7,8] x5 = un0
  SD .x12 .x5 3944 ;;                         -- [9]  save un0
  -- Step 1: q1 = DIVU(uHi, dHi), rhat = uHi - q1*dHi
  single (.DIVU .x10 .x7 .x6) ;;             -- [10] x10 = q1
  single (.MUL .x5 .x10 .x6) ;;              -- [11] x5 = q1 * dHi
  single (.SUB .x7 .x7 .x5) ;;               -- [12] x7 = rhat
  -- [13] v5 Phase-1a cap: clamp q1c at 2^32 - 1, recompute rhatc.
  SRLI .x5 .x10 32 ;;                         -- [13] x5 = hi1 = q1 >> 32
  single (.BEQ .x5 .x0 28) ;;                -- [14] skip if hi1 == 0 → [21]
  ADDI .x5 .x0 4095 ;;                        -- [15] x5 = -1 = 0xFFFFFFFFFFFFFFFF
  SRLI .x5 .x5 32 ;;                          -- [16] x5 = 0xFFFFFFFF (q1cCap)
  single (.SUB .x9 .x10 .x5) ;;              -- [17] x9 = q1 - q1cCap (= q1 - 0xFFFFFFFF)
  single (.MUL .x9 .x9 .x6) ;;               -- [18] x9 = (q1 - q1cCap) * dHi
  single (.ADD .x7 .x7 .x9) ;;               -- [19] x7 = rhat + (q1 - q1cCap) * dHi = rhatc
  ADDI .x10 .x5 0 ;;                          -- [20] x10 = q1c = q1cCap (MV via ADDI 0)
  -- [21] v5 fix: Phase-1b leading guard. Knuth D3 repeats the product-test
  -- correction only while r̂ < b; after the cap, rhatc can be ≥ 2^32, so
  -- both corrections must be skipped in that regime (mirror of the Phase-2b
  -- guard at [57]). Without this guard the 1st-correction ULT misfires on
  -- wide rhatc (the PR #7077 / #7080 bug) — matches div128Quot_v5 (IterV5).
  SRLI .x9 .x7 32 ;;                          -- [21] x9 = rhatc >> 32
  single (.BNE .x9 .x0 76) ;;                -- [22] if rhatc ≥ 2^32 → skip both → [41]
  -- [23] Phase 1b 1st D3 correction (= v4 [17])
  LD .x9 .x12 3952 ;;                         -- [23] x9 = dLo
  single (.MUL .x5 .x10 .x9) ;;              -- [24] x5 = q1c * dLo
  SLLI .x9 .x7 32 ;;                          -- [25] x9 = rhatc << 32
  single (.OR .x9 .x9 .x11) ;;               -- [26] x9 = rhatc*2^32 + un1
  single (.BLTU .x9 .x5 8) ;;                -- [27] if rhs < lhs → correct [29]
  JAL .x0 12 ;;                                -- [28] skip → [31]
  ADDI .x10 .x10 4095 ;;                      -- [29] q1c--
  single (.ADD .x7 .x7 .x6) ;;               -- [30] rhatc += dHi
  -- [31] Phase 1b 2nd D3 correction (= v4 [25])
  SRLI .x9 .x7 32 ;;                          -- [31] x9 = rhatc >> 32
  single (.BNE .x9 .x0 36) ;;                -- [32] if nonzero → skip to [41]
  LD .x9 .x12 3952 ;;                         -- [33] dLo
  single (.MUL .x5 .x10 .x9) ;;              -- [34] x5 = q1c * dLo
  SLLI .x9 .x7 32 ;;                          -- [35] x9 = rhatc << 32
  single (.OR .x9 .x9 .x11) ;;               -- [36] x9 = rhatc*2^32 + un1
  single (.BLTU .x9 .x5 8) ;;                -- [37] if rhs < lhs → correct [39]
  JAL .x0 12 ;;                                -- [38] skip → [41]
  ADDI .x10 .x10 4095 ;;                      -- [39] q1c--
  single (.ADD .x7 .x7 .x6) ;;               -- [40] rhatc += dHi
  -- [41] Compute un21 = rhatc*2^32 + un1 - q1c*dLo (= v4 [35])
  LD .x9 .x12 3952 ;;                         -- [41] dLo
  SLLI .x5 .x7 32 ;;                          -- [42] rhatc << 32
  single (.OR .x5 .x5 .x11) ;;               -- [43] x5 = rhatc*2^32 + un1
  single (.MUL .x9 .x10 .x9) ;;              -- [44] x9 = q1c * dLo
  single (.SUB .x7 .x5 .x9) ;;               -- [45] x7 = un21
  -- Step 2: q0 = DIVU(un21, dHi), rhat2 = un21 - q0*dHi (= v4 [40])
  single (.DIVU .x5 .x7 .x6) ;;              -- [46] x5 = q0
  single (.MUL .x9 .x5 .x6) ;;               -- [47]
  single (.SUB .x11 .x7 .x9) ;;              -- [48] x11 = rhat2
  -- [49] v5 Phase-2a cap: clamp q0c at 2^32 - 1, recompute rhat2c.
  -- Mirror of Phase-1a above. Reuses x7 (= un21, dead from here on
  -- until [56] writes it) as the diff scratch.
  SRLI .x9 .x5 32 ;;                          -- [49] x9 = hi2 = q0 >> 32
  single (.BEQ .x9 .x0 28) ;;                -- [50] skip if hi2 == 0 → [57]
  ADDI .x9 .x0 4095 ;;                        -- [51] x9 = -1 = 0xFFFFFFFFFFFFFFFF
  SRLI .x9 .x9 32 ;;                          -- [52] x9 = 0xFFFFFFFF (q0cCap)
  single (.SUB .x7 .x5 .x9) ;;               -- [53] x7 = q0 - q0cCap
  single (.MUL .x7 .x7 .x6) ;;               -- [54] x7 = (q0 - q0cCap) * dHi
  single (.ADD .x11 .x11 .x7) ;;             -- [55] x11 = rhat2 + diff*dHi = rhat2c
  ADDI .x5 .x9 0 ;;                           -- [56] x5 = q0c = q0cCap (MV via ADDI 0)
  -- [57] Phase 2b guard (= v4 [47])
  SRLI .x9 .x11 32 ;;                         -- [57] x9 = rhat2c >> 32
  single (.BNE .x9 .x0 92) ;;                -- [58] if nonzero → skip to [81] (combine)
  -- [59] Phase 2b 1st D3 mul-check (= v4 [49])
  LD .x9 .x12 3952 ;;                         -- [59] dLo
  single (.MUL .x7 .x5 .x9) ;;               -- [60] x7 = q0c * dLo
  SLLI .x9 .x11 32 ;;                         -- [61] rhat2c << 32
  SD .x12 .x11 3936 ;;                        -- [62] save rhat2c
  LD .x11 .x12 3944 ;;                        -- [63] x11 = un0 (clobbers rhat2c)
  single (.OR .x9 .x9 .x11) ;;               -- [64] x9 = rhat2c*2^32 + un0
  single (.BLTU .x9 .x7 12) ;;               -- [65] if BLTU fires → correction [68]
  -- [66] No-correction path
  LD .x11 .x12 3936 ;;                        -- [66] restore rhat2c
  JAL .x0 16 ;;                                -- [67] skip correction → [71] (2nd D3 entry)
  -- [68] Correction path
  ADDI .x5 .x5 4095 ;;                        -- [68] q0c--
  LD .x11 .x12 3936 ;;                        -- [69] restore rhat2c
  single (.ADD .x11 .x11 .x6) ;;             -- [70] rhat2c += dHi
  -- [71] Phase 2b 2nd D3 guarded mul-check (= v4 [61])
  SRLI .x9 .x11 32 ;;                         -- [71] x9 = rhat2c >> 32 (post-1st-correction)
  single (.BNE .x9 .x0 36) ;;                -- [72] if nonzero → skip to [81] (combine)
  LD .x9 .x12 3952 ;;                         -- [73] dLo
  single (.MUL .x7 .x5 .x9) ;;               -- [74] x7 = q0c * dLo
  SLLI .x9 .x11 32 ;;                         -- [75] rhat2c << 32
  LD .x11 .x12 3944 ;;                        -- [76] x11 = un0
  single (.OR .x9 .x9 .x11) ;;               -- [77] x9 = rhat2c*2^32 + un0
  single (.BLTU .x9 .x7 8) ;;                -- [78] if BLTU fires → 2nd correction [80]
  JAL .x0 8 ;;                                 -- [79] skip → [81]
  ADDI .x5 .x5 4095 ;;                        -- [80] 2nd correction: q0c--
  -- [81] Combine: q = q1c*2^32 + q0c (= v4 [71])
  SLLI .x11 .x10 32 ;;                        -- [81] q1c << 32
  single (.OR .x11 .x11 .x5) ;;              -- [82] x11 = q
  -- Restore and return
  LD .x2 .x12 3968 ;;                         -- [83] restore return addr
  JALR .x0 .x2 0                              -- [84] return
  -- Total: 85 instructions (v4's 75 + 4 Phase-1a + 4 Phase-2a + 2 Phase-1b guard).

/-- Cap sanity check (Phase-1a and Phase-2a both): at the structural
    level, the cap immediate is `0xFFFFFFFF`. Constructed in-program
    as `(0xFF...FF) >>> 32` via `ADDI .x_ .x0 4095 ;; SRLI .x_ .x_ 32`. -/
theorem divK_div128_v5_cap_eq :
    ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat : BitVec 64) =
      (0xFFFFFFFF : BitVec 64) := by
  decide

-- ============================================================================
-- Main division program phases
-- ============================================================================

/-- Phase A: Check b=0. OR-reduce b[0..3], BEQ to zero_path.
    8 instructions. BEQ offset computed from zero_path position. -/
def divK_phaseA (beq_off : BitVec 13) : Program :=
  LD .x5  .x12 32 ;;
  LD .x10 .x12 40 ;; single (.OR .x5 .x5 .x10) ;;
  LD .x10 .x12 48 ;; single (.OR .x5 .x5 .x10) ;;
  LD .x10 .x12 56 ;; single (.OR .x5 .x5 .x10) ;;
  single (.BEQ .x5 .x0 beq_off)

/-- Phase B: Find n (cascade), init q=0, get leading limb.
    21 instructions. After: x5 = leading limb, n stored at 3984. -/
def divK_phaseB : Program :=
  -- Init q[0..3] = 0 and u[5..7] padding = 0
  SD .x12 .x0 4088 ;; SD .x12 .x0 4080 ;;
  SD .x12 .x0 4072 ;; SD .x12 .x0 4064 ;;
  SD .x12 .x0 4016 ;; SD .x12 .x0 4008 ;; SD .x12 .x0 4000 ;;
  -- Compute n = index of highest nonzero limb + 1 (cascade)
  -- x10 = b[3] from phaseA; load b[1], b[2]
  LD .x6 .x12 40 ;; LD .x7 .x12 48 ;;
  ADDI .x5 .x0 4 ;; single (.BNE .x10 .x0 24) ;; -- b[3]≠0 → n=4
  ADDI .x5 .x0 3 ;; single (.BNE .x7 .x0 16) ;;  -- b[2]≠0 → n=3
  ADDI .x5 .x0 2 ;; single (.BNE .x6 .x0 8) ;;   -- b[1]≠0 → n=2
  ADDI .x5 .x0 1 ;;                                -- n=1
  -- Store n and load leading limb b[n-1]
  SD .x12 .x5 3984 ;;
  ADDI .x5 .x5 4095 ;; SLLI .x5 .x5 3 ;;
  single (.ADD .x5 .x12 .x5) ;;
  LD .x5 .x5 32

/-- Phase C1: CLZ of value in x5. Result in x6 (0..63).
    24 instructions. 6-stage binary search. -/
def divK_clz : Program :=
  ADDI .x6 .x0 0 ;;
  SRLI .x7 .x5 32 ;; single (.BNE .x7 .x0 12) ;;
  SLLI .x5 .x5 32 ;; ADDI .x6 .x6 32 ;;
  SRLI .x7 .x5 48 ;; single (.BNE .x7 .x0 12) ;;
  SLLI .x5 .x5 16 ;; ADDI .x6 .x6 16 ;;
  SRLI .x7 .x5 56 ;; single (.BNE .x7 .x0 12) ;;
  SLLI .x5 .x5 8  ;; ADDI .x6 .x6 8 ;;
  SRLI .x7 .x5 60 ;; single (.BNE .x7 .x0 12) ;;
  SLLI .x5 .x5 4  ;; ADDI .x6 .x6 4 ;;
  SRLI .x7 .x5 62 ;; single (.BNE .x7 .x0 12) ;;
  SLLI .x5 .x5 2  ;; ADDI .x6 .x6 2 ;;
  SRLI .x7 .x5 63 ;; single (.BNE .x7 .x0 8) ;;
  ADDI .x6 .x6 1

/-- Phase C2: Store shift, compute antiShift, BEQ if shift=0.
    4 instructions. x6 = shift, x2 = antiShift. -/
def divK_phaseC2 (shift0_off : BitVec 13) : Program :=
  SD .x12 .x6 3992 ;;
  ADDI .x2 .x0 0 ;; single (.SUB .x2 .x2 .x6) ;;
  single (.BEQ .x6 .x0 shift0_off)

/-- Phase C3a: Normalize b in-place (shift > 0).
    21 instructions. x6 = shift, x2 = antiShift. -/
def divK_normB : Program :=
  LD .x5 .x12 56 ;; LD .x7 .x12 48 ;;
  single (.SLL .x5 .x5 .x6) ;; single (.SRL .x7 .x7 .x2) ;; single (.OR .x5 .x5 .x7) ;;
  SD .x12 .x5 56 ;;
  LD .x5 .x12 48 ;; LD .x7 .x12 40 ;;
  single (.SLL .x5 .x5 .x6) ;; single (.SRL .x7 .x7 .x2) ;; single (.OR .x5 .x5 .x7) ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x12 40 ;; LD .x7 .x12 32 ;;
  single (.SLL .x5 .x5 .x6) ;; single (.SRL .x7 .x7 .x2) ;; single (.OR .x5 .x5 .x7) ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x12 32 ;; single (.SLL .x5 .x5 .x6) ;; SD .x12 .x5 32

/-- Phase C3b: Normalize a → u[0..4] (shift > 0). Then JAL over shift=0 path.
    21 + 1 = 22 instructions. -/
def divK_normA (jal_off : BitVec 21) : Program :=
  LD .x5 .x12 24 ;;
  single (.SRL .x7 .x5 .x2) ;; SD .x12 .x7 4024 ;;
  LD .x7 .x12 16 ;;
  single (.SLL .x5 .x5 .x6) ;; single (.SRL .x10 .x7 .x2) ;; single (.OR .x5 .x5 .x10) ;;
  SD .x12 .x5 4032 ;;
  LD .x5 .x12 8 ;;
  single (.SLL .x7 .x7 .x6) ;; single (.SRL .x10 .x5 .x2) ;; single (.OR .x7 .x7 .x10) ;;
  SD .x12 .x7 4040 ;;
  LD .x7 .x12 0 ;;
  single (.SLL .x5 .x5 .x6) ;; single (.SRL .x10 .x7 .x2) ;; single (.OR .x5 .x5 .x10) ;;
  SD .x12 .x5 4048 ;;
  single (.SLL .x7 .x7 .x6) ;; SD .x12 .x7 4056 ;;
  JAL .x0 jal_off

/-- Phase C4: Copy a → u[0..4] unshifted (shift = 0).
    9 instructions. -/
def divK_copyAU : Program :=
  LD .x5 .x12 0  ;; SD .x12 .x5 4056 ;;
  LD .x5 .x12 8  ;; SD .x12 .x5 4048 ;;
  LD .x5 .x12 16 ;; SD .x12 .x5 4040 ;;
  LD .x5 .x12 24 ;; SD .x12 .x5 4032 ;;
  SD .x12 .x0 4024

/-- Loop setup: compute m = 4-n, j = m (start of loop counter).
    4 instructions. BLT if j < 0 (signed). -/
def divK_loopSetup (bltOff : BitVec 13) : Program :=
  LD .x5 .x12 3984 ;;
  ADDI .x9 .x0 4 ;; single (.SUB .x9 .x9 .x5) ;;
  single (.BLT .x9 .x0 bltOff)

/-- Loop body: trial quotient + multiply-subtract + correction + store q[j].
    Starts at loop_start. Includes save/restore of j.

    Layout within loop body (instruction indices relative to loop_start):
      [0]     SD save j
      [1..13] load u[j+n], u[j+n-1], vTop; check uHi>=vTop; call 128/64
      [14]    LD restore j
      [15..17] mul-sub setup (uBase, carry=0)
      [18..61] mul-sub 4 limbs (4 × 11 instrs)
      [62..65] subtract carry from u[j+4]
      [66]    BEQ skip correction
      [67..103] add-back correction (37 instrs)
      [104..107] store q[j]
      [108..109] loop control

    110 instructions per loop body. -/
def divK_loopBody (subr_off : BitVec 21) (loop_back_off : BitVec 13) : Program :=
  -- Save j
  SD .x12 .x9 3976 ;;                         -- [0]

  -- Load u[j+n] and u[j+n-1]
  LD .x5 .x12 3984 ;;                         -- [1] n
  single (.ADD .x7 .x9 .x5) ;;               -- [2] x7 = j+n
  SLLI .x7 .x7 3 ;;                           -- [3] (j+n)*8
  ADDI .x5 .x12 4056 ;;                       -- [4] sp-40 = &u[0]
  single (.SUB .x5 .x5 .x7) ;;               -- [5] &u[j+n]
  LD .x7 .x5 0 ;;                             -- [6] x7 = u[j+n] (hi)
  LD .x5 .x5 8 ;;                             -- [7] x5 = u[j+n-1] (lo)

  -- Load vTop = b[n-1]
  LD .x6 .x12 3984 ;;                         -- [8] n
  ADDI .x6 .x6 4095 ;;                        -- [9] n-1
  SLLI .x6 .x6 3 ;;                           -- [10] (n-1)*8
  single (.ADD .x6 .x12 .x6) ;;              -- [11] &b[n-1]
  LD .x10 .x6 32 ;;                            -- [12] x10 = vTop = b[n-1]

  -- Trial quotient
  single (.BLTU .x7 .x10 12) ;;              -- [13] uHi < vTop? → [16] call 128/64
  ADDI .x11 .x0 4095 ;;                       -- [14] qHat = MAX64
  JAL .x0 8 ;;                                 -- [15] skip call → [17]
  JAL .x2 subr_off ;;                          -- [16] call 128/64 subroutine

  -- Restore j, compute uBase
  LD .x9 .x12 3976 ;;                         -- [17] restore j
  SLLI .x5 .x9 3 ;;                           -- [18] j*8
  ADDI .x6 .x12 4056 ;;                       -- [19] sp-40
  single (.SUB .x6 .x6 .x5) ;;               -- [20] x6 = uBase = &u[j]

  -- Init carry = 0
  ADDI .x10 .x0 0 ;;                          -- [21] carry = 0

  -- MUL-SUB LIMB 0: v[0] at sp+32, u[j+0] at uBase+0
  LD .x5 .x12 32 ;;                           -- [22]
  single (.MUL .x7 .x11 .x5) ;;              -- [23] prod_lo
  single (.MULHU .x5 .x11 .x5) ;;            -- [24] prod_hi
  single (.ADD .x7 .x7 .x10) ;;              -- [25] full_sub = prod_lo + carry
  single (.SLTU .x10 .x7 .x10) ;;            -- [26] borrowAdd
  single (.ADD .x10 .x10 .x5) ;;             -- [27] partial_carry = borrow + prod_hi
  LD .x2 .x6 0 ;;                             -- [28] u[j+0]
  single (.SLTU .x5 .x2 .x7) ;;              -- [29] borrowSub
  single (.SUB .x2 .x2 .x7) ;;               -- [30] uNew
  single (.ADD .x10 .x10 .x5) ;;             -- [31] carryOut
  SD .x6 .x2 0 ;;                             -- [32] store u[j+0]

  -- MUL-SUB LIMB 1: v[1] at sp+40, u[j+1] at uBase-8 (4088)
  LD .x5 .x12 40 ;;                           -- [33]
  single (.MUL .x7 .x11 .x5) ;;              -- [34]
  single (.MULHU .x5 .x11 .x5) ;;            -- [35]
  single (.ADD .x7 .x7 .x10) ;;              -- [36]
  single (.SLTU .x10 .x7 .x10) ;;            -- [37]
  single (.ADD .x10 .x10 .x5) ;;             -- [38]
  LD .x2 .x6 4088 ;;                          -- [39] u[j+1]
  single (.SLTU .x5 .x2 .x7) ;;              -- [40]
  single (.SUB .x2 .x2 .x7) ;;               -- [41]
  single (.ADD .x10 .x10 .x5) ;;             -- [42]
  SD .x6 .x2 4088 ;;                          -- [43]

  -- MUL-SUB LIMB 2: v[2] at sp+48, u[j+2] at uBase-16 (4080)
  LD .x5 .x12 48 ;;                           -- [44]
  single (.MUL .x7 .x11 .x5) ;;              -- [45]
  single (.MULHU .x5 .x11 .x5) ;;            -- [46]
  single (.ADD .x7 .x7 .x10) ;;              -- [47]
  single (.SLTU .x10 .x7 .x10) ;;            -- [48]
  single (.ADD .x10 .x10 .x5) ;;             -- [49]
  LD .x2 .x6 4080 ;;                          -- [50] u[j+2]
  single (.SLTU .x5 .x2 .x7) ;;              -- [51]
  single (.SUB .x2 .x2 .x7) ;;               -- [52]
  single (.ADD .x10 .x10 .x5) ;;             -- [53]
  SD .x6 .x2 4080 ;;                          -- [54]

  -- MUL-SUB LIMB 3: v[3] at sp+56, u[j+3] at uBase-24 (4072)
  LD .x5 .x12 56 ;;                           -- [55]
  single (.MUL .x7 .x11 .x5) ;;              -- [56]
  single (.MULHU .x5 .x11 .x5) ;;            -- [57]
  single (.ADD .x7 .x7 .x10) ;;              -- [58]
  single (.SLTU .x10 .x7 .x10) ;;            -- [59]
  single (.ADD .x10 .x10 .x5) ;;             -- [60]
  LD .x2 .x6 4072 ;;                          -- [61] u[j+3]
  single (.SLTU .x5 .x2 .x7) ;;              -- [62]
  single (.SUB .x2 .x2 .x7) ;;               -- [63]
  single (.ADD .x10 .x10 .x5) ;;             -- [64]
  SD .x6 .x2 4072 ;;                          -- [65]

  -- SUBTRACT CARRY FROM u[j+4]: uBase-32 (4064)
  LD .x5 .x6 4064 ;;                          -- [66] u[j+4]
  single (.SLTU .x7 .x5 .x10) ;;             -- [67] borrow
  single (.SUB .x5 .x5 .x10) ;;              -- [68]
  SD .x6 .x5 4064 ;;                          -- [69]

  -- CORRECTION: if borrow (x7 != 0), add v back and qHat--
  -- BEQ x7 x0 skips 38 instructions → offset = 38*4+4 = 156
  single (.BEQ .x7 .x0 156) ;;               -- [70] skip correction → [109]

  -- Add-back: v[0..3] to u[j..j+3] with carry, then u[j+4]++, qHat--
  ADDI .x7 .x0 0 ;;                           -- [71] carry = 0
  -- Limb 0
  LD .x5 .x12 32 ;; LD .x2 .x6 0 ;;          -- [72,73]
  single (.ADD .x2 .x2 .x7) ;;               -- [74] u += carryIn
  single (.SLTU .x7 .x2 .x7) ;;              -- [75] carry1
  single (.ADD .x2 .x2 .x5) ;;               -- [76] u += v[i]
  single (.SLTU .x5 .x2 .x5) ;;              -- [77] carry2
  single (.OR .x7 .x7 .x5) ;;                -- [78] carryOut
  SD .x6 .x2 0 ;;                             -- [79]
  -- Limb 1
  LD .x5 .x12 40 ;; LD .x2 .x6 4088 ;;       -- [80,81]
  single (.ADD .x2 .x2 .x7) ;;               -- [82]
  single (.SLTU .x7 .x2 .x7) ;;              -- [83]
  single (.ADD .x2 .x2 .x5) ;;               -- [84]
  single (.SLTU .x5 .x2 .x5) ;;              -- [85]
  single (.OR .x7 .x7 .x5) ;;                -- [86]
  SD .x6 .x2 4088 ;;                          -- [87]
  -- Limb 2
  LD .x5 .x12 48 ;; LD .x2 .x6 4080 ;;       -- [88,89]
  single (.ADD .x2 .x2 .x7) ;;               -- [90]
  single (.SLTU .x7 .x2 .x7) ;;              -- [91]
  single (.ADD .x2 .x2 .x5) ;;               -- [92]
  single (.SLTU .x5 .x2 .x5) ;;              -- [93]
  single (.OR .x7 .x7 .x5) ;;                -- [94]
  SD .x6 .x2 4080 ;;                          -- [95]
  -- Limb 3
  LD .x5 .x12 56 ;; LD .x2 .x6 4072 ;;       -- [96,97]
  single (.ADD .x2 .x2 .x7) ;;               -- [98]
  single (.SLTU .x7 .x2 .x7) ;;              -- [99]
  single (.ADD .x2 .x2 .x5) ;;               -- [100]
  single (.SLTU .x5 .x2 .x5) ;;              -- [101]
  single (.OR .x7 .x7 .x5) ;;                -- [102]
  SD .x6 .x2 4072 ;;                          -- [103]
  -- u[j+4] += carry
  LD .x5 .x6 4064 ;;                          -- [104]
  single (.ADD .x5 .x5 .x7) ;;               -- [105]
  SD .x6 .x5 4064 ;;                          -- [106]
  -- qHat--
  ADDI .x11 .x11 4095 ;;                      -- [107]

  -- DOUBLE ADDBACK CHECK: if carry (x7) = 0, repeat addback
  -- Offset = -148 bytes (back to [71]): 13-bit encoding = 8044
  single (.BEQ .x7 .x0 8044) ;;              -- [108] if carry=0 → [71]

  -- STORE q[j]: q[j] at sp - 8 - j*8 = sp + (4088 - j*8)
  SLLI .x5 .x9 3 ;;                           -- [109] j*8
  ADDI .x7 .x12 4088 ;;                       -- [110] sp-8
  single (.SUB .x7 .x7 .x5) ;;               -- [111] &q[j]
  SD .x7 .x11 0 ;;                            -- [112] q[j] = qHat

  -- LOOP CONTROL
  ADDI .x9 .x9 4095 ;;                        -- [113] j--
  single (.BGE .x9 .x0 loop_back_off)         -- [114] if j >= 0 → loop

/-- Phase E: De-normalize remainder. Right-shift u[0..3] by shift amount.
    25 instructions. -/
def divK_denorm : Program :=
  LD .x6 .x12 3992 ;;                         -- [0] shift
  single (.BEQ .x6 .x0 96) ;;                -- [1] if shift=0, skip → [25]
  ADDI .x2 .x0 0 ;; single (.SUB .x2 .x2 .x6) ;; -- [2,3] antiShift
  -- u[0]
  LD .x5 .x12 4056 ;; LD .x7 .x12 4048 ;;    -- [4,5]
  single (.SRL .x5 .x5 .x6) ;;               -- [6]
  single (.SLL .x7 .x7 .x2) ;;               -- [7]
  single (.OR .x5 .x5 .x7) ;;                -- [8]
  SD .x12 .x5 4056 ;;                         -- [9]
  -- u[1]
  LD .x5 .x12 4048 ;; LD .x7 .x12 4040 ;;    -- [10,11]
  single (.SRL .x5 .x5 .x6) ;;               -- [12]
  single (.SLL .x7 .x7 .x2) ;;               -- [13]
  single (.OR .x5 .x5 .x7) ;;                -- [14]
  SD .x12 .x5 4048 ;;                         -- [15]
  -- u[2]
  LD .x5 .x12 4040 ;; LD .x7 .x12 4032 ;;    -- [16,17]
  single (.SRL .x5 .x5 .x6) ;;               -- [18]
  single (.SLL .x7 .x7 .x2) ;;               -- [19]
  single (.OR .x5 .x5 .x7) ;;                -- [20]
  SD .x12 .x5 4040 ;;                         -- [21]
  -- u[3]
  LD .x5 .x12 4032 ;;                         -- [22]
  single (.SRL .x5 .x5 .x6) ;;               -- [23]
  SD .x12 .x5 4032                            -- [24]

/-- Epilogue for DIV: copy q[0..3] to output. 10 instructions. -/
def divK_div_epilogue (jal_off : BitVec 21) : Program :=
  LD .x5  .x12 4088 ;; LD .x6  .x12 4080 ;;
  LD .x7  .x12 4072 ;; LD .x10 .x12 4064 ;;
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;; SD .x12 .x6 8 ;;
  SD .x12 .x7 16 ;; SD .x12 .x10 24 ;;
  JAL .x0 jal_off

/-- Epilogue for MOD: copy u[0..3] (de-normalized remainder) to output. 10 instructions. -/
def divK_mod_epilogue (jal_off : BitVec 21) : Program :=
  LD .x5  .x12 4056 ;; LD .x6  .x12 4048 ;;
  LD .x7  .x12 4040 ;; LD .x10 .x12 4032 ;;
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;; SD .x12 .x6 8 ;;
  SD .x12 .x7 16 ;; SD .x12 .x10 24 ;;
  JAL .x0 jal_off

/-- Zero path: b = 0, push 0. 5 instructions. -/
def divK_zeroPath : Program :=
  ADDI .x12 .x12 32 ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;; SD .x12 .x0 24

-- ============================================================================
-- Full program assembly with computed offsets
-- ============================================================================

-- Layout (instruction counts):
--   phaseA:      8   [0..7]      bytes 0..28
--   phaseB:      21  [8..28]     bytes 32..112
--   clz:         24  [29..52]    bytes 116..208
--   phaseC2:     4   [53..56]    bytes 212..224
--   normB:       21  [57..77]    bytes 228..308
--   normA:       21  [78..98]    bytes 312..392
--   copyAU:      9   [99..107]   bytes 396..428
--   loopSetup:   4   [108..111]  bytes 432..444
--   loopBody:    115 [112..226]  bytes 448..904
--   denorm:      25  [227..251]  bytes 908..1004
--   epilogue:    10  [252..261]  bytes 1008..1044
--   zeroPath:    5   [262..266]  bytes 1048..1064
--   NOP:         1   [267]       byte 1068 (exit PC)
--   subroutine:  75  [268..342]  bytes 1072..1368
-- Total: 343 instructions. Exit PC = 1068.
--
-- Branch offsets:
-- 1. phaseA BEQ [7] → zeroPath [262]: (262-7)*4 = 1020
-- 2. phaseC2 BEQ [56] → copyAU [99]: (99-56)*4 = 172
-- 3. normA JAL [98] → loopSetup [108]: (108-98)*4 = 40
-- 4. loopSetup BLT [111] → denorm [227]: (227-111)*4 = 464
-- 5. loopBody sub JAL [16 in body = 128 abs] → subr [268]: (268-128)*4 = 560
-- 6. loopBody BGE [114 in body = 226 abs] → loop [112]: (112-226)*4 = -456 = 7736
-- 7. epilogue JAL [261] → exit [267]: (267-261)*4 = 24
-- 8. denorm BEQ [1 in denorm = 228] → after denorm [252]: (252-228)*4 = 96

/-- 256-bit EVM DIV: Knuth Algorithm D. -/
def evm_div : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  ADDI .x0 .x0 0 ;;  -- NOP: separates exit PC from subroutine
  divK_div128_v4

/-- 256-bit EVM MOD: Knuth Algorithm D, outputs remainder. -/
def evm_mod : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  ADDI .x0 .x0 0 ;;  -- NOP: separates exit PC from subroutine
  divK_div128_v4

/-- 256-bit EVM DIV using the v5 128/64-bit division subroutine. This
    executable surface is intentionally separate from `evm_div` so existing
    v4 proof/codegen consumers remain stable. -/
def evm_div_v5 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  ADDI .x0 .x0 0 ;;  -- NOP: separates exit PC from subroutine
  divK_div128_v5

/-- 256-bit EVM MOD using the v5 128/64-bit division subroutine. -/
def evm_mod_v5 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  ADDI .x0 .x0 0 ;;  -- NOP: separates exit PC from subroutine
  divK_div128_v5

theorem evm_div_v5_length : evm_div_v5.length = 353 := by
  have h_phaseA : (divK_phaseA 1020).length = 8 := by rfl
  have h_phaseB : divK_phaseB.length = 21 := by rfl
  have h_clz : divK_clz.length = 24 := by rfl
  have h_phaseC2 : (divK_phaseC2 172).length = 4 := by rfl
  have h_normB : divK_normB.length = 21 := by rfl
  have h_normA : (divK_normA 40).length = 21 := by rfl
  have h_copyAU : divK_copyAU.length = 9 := by rfl
  have h_loopSetup : (divK_loopSetup 464).length = 4 := by rfl
  have h_loopBody : (divK_loopBody 560 7736).length = 115 := by rfl
  have h_denorm : divK_denorm.length = 25 := by rfl
  have h_epilogue : (divK_div_epilogue 24).length = 10 := by rfl
  have h_zeroPath : divK_zeroPath.length = 5 := by rfl
  have h_nop : (ADDI .x0 .x0 0).length = 1 := by rfl
  have h_div128 : divK_div128_v5.length = 85 := by
    unfold divK_div128_v5
    rfl
  unfold evm_div_v5
  simp only [seq, Program.length_append, h_phaseA, h_phaseB, h_clz, h_phaseC2,
    h_normB, h_normA, h_copyAU, h_loopSetup, h_loopBody, h_denorm, h_epilogue,
    h_zeroPath, h_nop, h_div128]

theorem evm_mod_v5_length : evm_mod_v5.length = 353 := by
  have h_phaseA : (divK_phaseA 1020).length = 8 := by rfl
  have h_phaseB : divK_phaseB.length = 21 := by rfl
  have h_clz : divK_clz.length = 24 := by rfl
  have h_phaseC2 : (divK_phaseC2 172).length = 4 := by rfl
  have h_normB : divK_normB.length = 21 := by rfl
  have h_normA : (divK_normA 40).length = 21 := by rfl
  have h_copyAU : divK_copyAU.length = 9 := by rfl
  have h_loopSetup : (divK_loopSetup 464).length = 4 := by rfl
  have h_loopBody : (divK_loopBody 560 7736).length = 115 := by rfl
  have h_denorm : divK_denorm.length = 25 := by rfl
  have h_epilogue : (divK_mod_epilogue 24).length = 10 := by rfl
  have h_zeroPath : divK_zeroPath.length = 5 := by rfl
  have h_nop : (ADDI .x0 .x0 0).length = 1 := by rfl
  have h_div128 : divK_div128_v5.length = 85 := by
    unfold divK_div128_v5
    rfl
  unfold evm_mod_v5
  simp only [seq, Program.length_append, h_phaseA, h_phaseB, h_clz, h_phaseC2,
    h_normB, h_normA, h_copyAU, h_loopSetup, h_loopBody, h_denorm, h_epilogue,
    h_zeroPath, h_nop, h_div128]

-- ============================================================================
-- Instruction count verification
-- ============================================================================

example : (divK_phaseA 0).length = 8 := by rfl
example : (divK_phaseC2 0).length = 4 := by rfl
example : (divK_normA 0).length = 21 := by rfl
example : (divK_loopSetup 0).length = 4 := by rfl
example : (divK_div_epilogue 0).length = 10 := by rfl

end EvmAsm.Evm64
