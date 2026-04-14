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
    3952(-144):            subroutine: saved d_lo
    3944(-152):            subroutine: saved un0
  After: result at sp+32..sp+56, x12 = sp + 32.

  Register allocation:
    x12 = EVM stack pointer (preserved)
    x1  = loop counter j / temp
    x2  = anti_shift / subroutine return addr
    x5  = general temp
    x6  = general temp / u_base in mul-sub
    x7  = general temp
    x10 = general temp / carry in mul-sub
    x11 = general temp / q_hat
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- 128/64-bit unsigned division subroutine
-- ============================================================================

/-- 128/64-bit unsigned division subroutine (Hacker's Delight divlu).
    Called via JAL x2, offset. Returns via JALR x0, x2, 0.
    Input: x7 = u_hi (< d), x5 = u_lo, x10 = d (normalized, >= 2^63)
    Output: x11 = floor((u_hi * 2^64 + u_lo) / d)
    Clobbers: x1, x5, x6, x7, x10, x11. Preserves: x2, x12.
    Uses scratch memory at 3992, 3984, 3976, 3968 (offsets from x12). -/
def divK_div128 : Program :=
  -- Save return addr and d
  SD .x12 .x2 3968 ;;                         -- [0]  save return addr
  SD .x12 .x10 3960 ;;                        -- [1]  save d
  -- Split d: d_hi = d >> 32, d_lo = (d << 32) >> 32
  SRLI .x6 .x10 32 ;;                         -- [2]  x6 = d_hi (>= 2^31)
  SLLI .x1 .x10 32 ;; SRLI .x1 .x1 32 ;;     -- [3,4] x1 = d_lo
  SD .x12 .x1 3952 ;;                         -- [5]  save d_lo
  -- Split u_lo: un1 = u_lo >> 32, un0 = (u_lo << 32) >> 32
  SRLI .x11 .x5 32 ;;                         -- [6]  x11 = un1
  SLLI .x5 .x5 32 ;; SRLI .x5 .x5 32 ;;      -- [7,8] x5 = un0
  SD .x12 .x5 3944 ;;                         -- [9]  save un0
  -- Step 1: q1 = DIVU(u_hi, d_hi), rhat = u_hi - q1*d_hi
  -- x7 = u_hi, x6 = d_hi
  single (.DIVU .x10 .x7 .x6) ;;             -- [10] x10 = q1 (use x10 since we saved d)
  single (.MUL .x5 .x10 .x6) ;;              -- [11] x5 = q1 * d_hi
  single (.SUB .x7 .x7 .x5) ;;               -- [12] x7 = rhat
  -- Refine q1: clamp to < 2^32
  SRLI .x5 .x10 32 ;;                         -- [13] test q1 >= 2^32
  single (.BEQ .x5 .x0 12) ;;                -- [14] skip if q1 < 2^32 → [17]
  ADDI .x10 .x10 4095 ;;                      -- [15] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [16] rhat += d_hi
  -- [17] Product check: q1*d_lo > rhat*2^32 + un1?
  LD .x1 .x12 3952 ;;                         -- [17] x1 = d_lo
  single (.MUL .x5 .x10 .x1) ;;              -- [18] x5 = q1 * d_lo
  SLLI .x1 .x7 32 ;;                          -- [19] x1 = rhat << 32
  single (.OR .x1 .x1 .x11) ;;               -- [20] x1 = rhat*2^32 + un1
  single (.BLTU .x1 .x5 8) ;;                -- [21] if rhs < lhs → correct [23]
  JAL .x0 12 ;;                                -- [22] skip → [25]
  ADDI .x10 .x10 4095 ;;                      -- [23] q1--
  single (.ADD .x7 .x7 .x6) ;;               -- [24] rhat += d_hi
  -- Compute un21 = rhat*2^32 + un1 - q1*d_lo
  LD .x1 .x12 3952 ;;                         -- [25] d_lo
  SLLI .x5 .x7 32 ;;                          -- [26] rhat << 32
  single (.OR .x5 .x5 .x11) ;;               -- [27] x5 = rhat*2^32 + un1
  single (.MUL .x1 .x10 .x1) ;;              -- [28] x1 = q1 * d_lo
  single (.SUB .x7 .x5 .x1) ;;               -- [29] x7 = un21
  -- Step 2: q0 = DIVU(un21, d_hi), rhat2 = un21 - q0*d_hi
  single (.DIVU .x5 .x7 .x6) ;;              -- [30] x5 = q0
  single (.MUL .x1 .x5 .x6) ;;               -- [31]
  single (.SUB .x11 .x7 .x1) ;;              -- [32] x11 = rhat2
  -- Refine q0: clamp
  SRLI .x1 .x5 32 ;;                          -- [33]
  single (.BEQ .x1 .x0 12) ;;                -- [34] skip if q0 < 2^32 → [37]
  ADDI .x5 .x5 4095 ;;                        -- [35] q0--
  single (.ADD .x11 .x11 .x6) ;;             -- [36] rhat2 += d_hi
  -- [37] Product check for q0
  LD .x1 .x12 3952 ;;                         -- [37] d_lo
  single (.MUL .x7 .x5 .x1) ;;               -- [38] x7 = q0 * d_lo
  SLLI .x1 .x11 32 ;;                         -- [39] rhat2 << 32
  LD .x11 .x12 3944 ;;                        -- [40] un0
  single (.OR .x1 .x1 .x11) ;;               -- [41] x1 = rhat2*2^32 + un0
  single (.BLTU .x1 .x7 8) ;;                -- [42] if rhs < lhs → correct [44]
  JAL .x0 8 ;;                                 -- [43] skip → [45]
  ADDI .x5 .x5 4095 ;;                        -- [44] q0--
  -- Combine: q = q1*2^32 + q0
  SLLI .x11 .x10 32 ;;                        -- [45] q1 << 32
  single (.OR .x11 .x11 .x5) ;;              -- [46] x11 = q
  -- Restore and return
  LD .x2 .x12 3968 ;;                         -- [47] restore return addr
  JALR .x0 .x2 0                              -- [48] return
  -- Total: 49 instructions

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

/-- Phase C2: Store shift, compute anti_shift, BEQ if shift=0.
    4 instructions. x6 = shift, x2 = anti_shift. -/
def divK_phaseC2 (shift0_off : BitVec 13) : Program :=
  SD .x12 .x6 3992 ;;
  ADDI .x2 .x0 0 ;; single (.SUB .x2 .x2 .x6) ;;
  single (.BEQ .x6 .x0 shift0_off)

/-- Phase C3a: Normalize b in-place (shift > 0).
    21 instructions. x6 = shift, x2 = anti_shift. -/
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
def divK_loopSetup (blt_off : BitVec 13) : Program :=
  LD .x5 .x12 3984 ;;
  ADDI .x1 .x0 4 ;; single (.SUB .x1 .x1 .x5) ;;
  single (.BLT .x1 .x0 blt_off)

/-- Loop body: trial quotient + multiply-subtract + correction + store q[j].
    Starts at loop_start. Includes save/restore of j.

    Layout within loop body (instruction indices relative to loop_start):
      [0]     SD save j
      [1..13] load u[j+n], u[j+n-1], v_top; check u_hi>=v_top; call 128/64
      [14]    LD restore j
      [15..17] mul-sub setup (u_base, carry=0)
      [18..61] mul-sub 4 limbs (4 × 11 instrs)
      [62..65] subtract carry from u[j+4]
      [66]    BEQ skip correction
      [67..103] add-back correction (37 instrs)
      [104..107] store q[j]
      [108..109] loop control

    110 instructions per loop body. -/
def divK_loopBody (subr_off : BitVec 21) (loop_back_off : BitVec 13) : Program :=
  -- Save j
  SD .x12 .x1 3976 ;;                         -- [0]

  -- Load u[j+n] and u[j+n-1]
  LD .x5 .x12 3984 ;;                         -- [1] n
  single (.ADD .x7 .x1 .x5) ;;               -- [2] x7 = j+n
  SLLI .x7 .x7 3 ;;                           -- [3] (j+n)*8
  ADDI .x5 .x12 4056 ;;                       -- [4] sp-40 = &u[0]
  single (.SUB .x5 .x5 .x7) ;;               -- [5] &u[j+n]
  LD .x7 .x5 0 ;;                             -- [6] x7 = u[j+n] (hi)
  LD .x5 .x5 8 ;;                             -- [7] x5 = u[j+n-1] (lo)

  -- Load v_top = b[n-1]
  LD .x6 .x12 3984 ;;                         -- [8] n
  ADDI .x6 .x6 4095 ;;                        -- [9] n-1
  SLLI .x6 .x6 3 ;;                           -- [10] (n-1)*8
  single (.ADD .x6 .x12 .x6) ;;              -- [11] &b[n-1]
  LD .x10 .x6 32 ;;                            -- [12] x10 = v_top = b[n-1]

  -- Trial quotient
  single (.BLTU .x7 .x10 12) ;;              -- [13] u_hi < v_top? → [16] call 128/64
  ADDI .x11 .x0 4095 ;;                       -- [14] q_hat = MAX64
  JAL .x0 8 ;;                                 -- [15] skip call → [17]
  JAL .x2 subr_off ;;                          -- [16] call 128/64 subroutine

  -- Restore j, compute u_base
  LD .x1 .x12 3976 ;;                         -- [17] restore j
  SLLI .x5 .x1 3 ;;                           -- [18] j*8
  ADDI .x6 .x12 4056 ;;                       -- [19] sp-40
  single (.SUB .x6 .x6 .x5) ;;               -- [20] x6 = u_base = &u[j]

  -- Init carry = 0
  ADDI .x10 .x0 0 ;;                          -- [21] carry = 0

  -- MUL-SUB LIMB 0: v[0] at sp+32, u[j+0] at u_base+0
  LD .x5 .x12 32 ;;                           -- [22]
  single (.MUL .x7 .x11 .x5) ;;              -- [23] prod_lo
  single (.MULHU .x5 .x11 .x5) ;;            -- [24] prod_hi
  single (.ADD .x7 .x7 .x10) ;;              -- [25] full_sub = prod_lo + carry
  single (.SLTU .x10 .x7 .x10) ;;            -- [26] borrow_add
  single (.ADD .x10 .x10 .x5) ;;             -- [27] partial_carry = borrow + prod_hi
  LD .x2 .x6 0 ;;                             -- [28] u[j+0]
  single (.SLTU .x5 .x2 .x7) ;;              -- [29] borrow_sub
  single (.SUB .x2 .x2 .x7) ;;               -- [30] u_new
  single (.ADD .x10 .x10 .x5) ;;             -- [31] carry_out
  SD .x6 .x2 0 ;;                             -- [32] store u[j+0]

  -- MUL-SUB LIMB 1: v[1] at sp+40, u[j+1] at u_base-8 (4088)
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

  -- MUL-SUB LIMB 2: v[2] at sp+48, u[j+2] at u_base-16 (4080)
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

  -- MUL-SUB LIMB 3: v[3] at sp+56, u[j+3] at u_base-24 (4072)
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

  -- SUBTRACT CARRY FROM u[j+4]: u_base-32 (4064)
  LD .x5 .x6 4064 ;;                          -- [66] u[j+4]
  single (.SLTU .x7 .x5 .x10) ;;             -- [67] borrow
  single (.SUB .x5 .x5 .x10) ;;              -- [68]
  SD .x6 .x5 4064 ;;                          -- [69]

  -- CORRECTION: if borrow (x7 != 0), add v back and q_hat--
  -- BEQ x7 x0 skips 38 instructions → offset = 38*4+4 = 156
  single (.BEQ .x7 .x0 156) ;;               -- [70] skip correction → [109]

  -- Add-back: v[0..3] to u[j..j+3] with carry, then u[j+4]++, q_hat--
  ADDI .x7 .x0 0 ;;                           -- [71] carry = 0
  -- Limb 0
  LD .x5 .x12 32 ;; LD .x2 .x6 0 ;;          -- [72,73]
  single (.ADD .x2 .x2 .x7) ;;               -- [74] u += carry_in
  single (.SLTU .x7 .x2 .x7) ;;              -- [75] carry1
  single (.ADD .x2 .x2 .x5) ;;               -- [76] u += v[i]
  single (.SLTU .x5 .x2 .x5) ;;              -- [77] carry2
  single (.OR .x7 .x7 .x5) ;;                -- [78] carry_out
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
  -- q_hat--
  ADDI .x11 .x11 4095 ;;                      -- [107]

  -- DOUBLE ADDBACK CHECK: if carry (x7) = 0, repeat addback
  -- Offset = -148 bytes (back to [71]): 13-bit encoding = 8044
  single (.BEQ .x7 .x0 8044) ;;              -- [108] if carry=0 → [71]

  -- STORE q[j]: q[j] at sp - 8 - j*8 = sp + (4088 - j*8)
  SLLI .x5 .x1 3 ;;                           -- [109] j*8
  ADDI .x7 .x12 4088 ;;                       -- [110] sp-8
  single (.SUB .x7 .x7 .x5) ;;               -- [111] &q[j]
  SD .x7 .x11 0 ;;                            -- [112] q[j] = q_hat

  -- LOOP CONTROL
  ADDI .x1 .x1 4095 ;;                        -- [113] j--
  single (.BGE .x1 .x0 loop_back_off)         -- [114] if j >= 0 → loop

/-- Phase E: De-normalize remainder. Right-shift u[0..3] by shift amount.
    25 instructions. -/
def divK_denorm : Program :=
  LD .x6 .x12 3992 ;;                         -- [0] shift
  single (.BEQ .x6 .x0 96) ;;                -- [1] if shift=0, skip → [25]
  ADDI .x2 .x0 0 ;; single (.SUB .x2 .x2 .x6) ;; -- [2,3] anti_shift
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
--   loopBody:    114 [112..225]  bytes 448..900
--   denorm:      25  [226..250]  bytes 904..1000
--   epilogue:    10  [251..260]  bytes 1004..1040
--   zeroPath:    5   [261..265]  bytes 1044..1060
--   NOP:         1   [266]       byte 1064 (exit PC)
--   subroutine:  49  [267..315]  bytes 1068..1260
-- Total: 316 instructions. Exit PC = 1064.
--
-- Branch offsets:
-- 1. phaseA BEQ [7] → zeroPath [261]: (261-7)*4 = 1016
-- 2. phaseC2 BEQ [56] → copyAU [99]: (99-56)*4 = 172
-- 3. normA JAL [98] → loopSetup [108]: (108-98)*4 = 40
-- 4. loopSetup BLT [111] → denorm [226]: (226-111)*4 = 460
-- 5. loopBody sub JAL [16 in body = 128 abs] → subr [267]: (267-128)*4 = 556
-- 6. loopBody BGE [113 in body = 225 abs] → loop [112]: (112-225)*4 = -452 = 7740
-- 7. epilogue JAL [260] → exit [266]: (266-260)*4 = 24
-- 8. denorm BEQ [1 in denorm = 227] → after denorm [251]: (251-227)*4 = 96

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
  divK_div128

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
  divK_div128

-- ============================================================================
-- Instruction count verification
-- ============================================================================

#eval evm_div.length
#eval evm_mod.length

#eval divK_phaseA 0 |>.length     -- expect 8
#eval divK_phaseB.length           -- expect 17
#eval divK_clz.length              -- expect 24
#eval divK_phaseC2 0 |>.length    -- expect 4
#eval divK_normB.length            -- expect 21
#eval (divK_normA 0).length        -- expect 22
#eval divK_copyAU.length           -- expect 9
#eval (divK_loopSetup 0).length   -- expect 4
#eval (divK_loopBody 0 0).length  -- expect 115
#eval divK_denorm.length           -- expect 25
#eval (divK_div_epilogue 0).length -- expect 10
#eval divK_zeroPath.length         -- expect 5
#eval divK_div128.length           -- expect 49

-- ============================================================================
-- Test infrastructure
-- ============================================================================

/-- Create a test state for DIV/MOD. -/
def mkDivTestState (prog : Program) (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp      then a0
    else if a == sp + 8  then a1
    else if a == sp + 16 then a2
    else if a == sp + 24 then a3
    else if a == sp + 32 then b0
    else if a == sp + 40 then b1
    else if a == sp + 48 then b2
    else if a == sp + 56 then b3
    else 0
  code := loadProgram 0 prog
  pc := 0

/-- Run program until PC reaches exitPC or fuel runs out. -/
def runToPC (exitPC : Word) (fuel : Nat) (s : MachineState) : Option MachineState :=
  match fuel with
  | 0 => if s.pc == exitPC then some s else none
  | fuel + 1 =>
    if s.pc == exitPC then some s
    else match step s with
    | none => none
    | some s' => runToPC exitPC fuel s'

-- Exit PC = 262 * 4 = 1048
def divExitPC : Word := 1064

/-- Run evm_div and extract 4 result limbs. -/
def runDivResult (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (fuel : Nat) : Option (List Word) :=
  let s := mkDivTestState evm_div sp a0 a1 a2 a3 b0 b1 b2 b3
  match runToPC divExitPC fuel s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

/-- Run evm_mod and extract 4 result limbs. -/
def runModResult (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (fuel : Nat) : Option (List Word) :=
  let s := mkDivTestState evm_mod sp a0 a1 a2 a3 b0 b1 b2 b3
  match runToPC divExitPC fuel s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

-- ============================================================================
-- Tests
-- ============================================================================

-- Basic single-limb
#eval runDivResult 1024 10 0 0 0  3 0 0 0  1000   -- expect [3, 0, 0, 0]
#eval runModResult 1024 10 0 0 0  3 0 0 0  1000   -- expect [1, 0, 0, 0]
#eval runDivResult 1024 100 0 0 0  7 0 0 0  1000  -- expect [14, 0, 0, 0]
#eval runModResult 1024 100 0 0 0  7 0 0 0  1000  -- expect [2, 0, 0, 0]

-- Edge cases
#eval runDivResult 1024 0 0 0 0  0 0 0 0  200     -- b=0: expect [0, 0, 0, 0]
#eval runDivResult 1024 0 0 0 0  5 0 0 0  1500     -- a=0: expect [0, 0, 0, 0]
#eval runDivResult 1024 42 0 0 0  42 0 0 0  1500  -- a=b: expect [1, 0, 0, 0]
#eval runModResult 1024 42 0 0 0  42 0 0 0  1500  -- a=b: expect [0, 0, 0, 0]
#eval runDivResult 1024 3 0 0 0  10 0 0 0  1500    -- a<b: expect [0, 0, 0, 0]
#eval runModResult 1024 3 0 0 0  10 0 0 0  1500    -- a<b: expect [3, 0, 0, 0]

-- Cross-limb: a = 2^64, b = 2 → q = 2^63
#eval runDivResult 1024 0 1 0 0  2 0 0 0  1000    -- expect [2^63, 0, 0, 0]

-- Large single limb: MAX64 / 1 = MAX64
#eval runDivResult 1024 0xFFFFFFFFFFFFFFFF 0 0 0  1 0 0 0  1000

-- Multi-limb dividend: (2^128 - 1) / 3
-- a = (MAX64, MAX64, 0, 0), b = 3
-- (2^128-1) / 3 = 113427455640312821154458202477256070485 = 0x55555555555555555555555555555555
-- = (0x5555555555555555, 0x5555555555555555, 0, 0)
#eval runDivResult 1024 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0 0  3 0 0 0  1500

-- Multi-limb divisor: 2^128 / 2^64 = 2^64 = (0, 1, 0, 0)
#eval runDivResult 1024 0 0 1 0  0 1 0 0  1500

-- Non-contiguous divisor (tests cascade n): b = (0, 0, 0, 1) = 2^192
-- a = (0, 0, 0, 2) = 2^193. DIV = 2, MOD = 0
#eval runDivResult 1024 0 0 0 2  0 0 0 1  1500    -- expect [2, 0, 0, 0]
#eval runModResult 1024 0 0 0 2  0 0 0 1  1500    -- expect [0, 0, 0, 0]

-- b = (1, 0, 0, 1) = 2^192+1, a = (0, 0, 0, 2) = 2^193
-- 2^193 / (2^192+1) = 1, remainder = 2^192-1 = (MAX64, MAX64, MAX64, 0)
#eval runDivResult 1024 0 0 0 2  1 0 0 1  2000    -- expect [1, 0, 0, 0]

-- MAX256 / 1 = MAX256
#eval runDivResult 1024 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF  1 0 0 0  2000

-- Verify q*b + r = a for DIV(100,7): q=14, r=2, 14*7+2 = 100 ✓
-- Verify q*b + r = a for DIV(2^128-1,3): q=(0x5555...,0x5555...,0,0), r=0
#eval runModResult 1024 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0 0  3 0 0 0  1500  -- expect [0, 0, 0, 0]

end EvmAsm.Evm64
