/-
  EvmAsm.Evm64.DivMod.FastN1Program

  Single-limb (n = 1) division fast path — issue #9303.

  When the divisor `b` fits in a single 64-bit limb (`b1 = b2 = b3 = 0`,
  `b0 ≠ 0`), the general Knuth Algorithm D in `evm_div_v5` is wasteful: it
  runs 4-limb normalization, a 4-limb multiply-subtract correction loop, and
  4 loop iterations. For a single-limb divisor each per-digit 2-by-1 division
  `(rem·2^64 + u[i]) / b0'` is *exact* (the running remainder `rem < b0'`
  guarantees the quotient `< 2^64`), so no trial-quotient correction or
  multi-limb mul-sub is needed — only a single-limb remainder recovery
  `rem ← u[i] -₆₄ q·b0'`.

  `evm_div_v6` / `evm_mod_v6` prepend a runtime dispatch:
    * `b1 | b2 | b3 ≠ 0`  (n ≥ 2)         → reuse the embedded `evm_div_v5`
    * `b0 = 0`            (divisor zero)  → reuse `evm_div_v5` (zeroPath)
    * else                (true n = 1)    → the fast path below

  The fast path carries its *own* copy of `divK_div128_v5` (proven via the
  existing base-relative `div128_v5_spec`), so it is self-contained and does
  not jump into the reused `evm_div_v5` body. Both dispatch arms converge on
  the embedded v5's NOP exit, so `evm_div_v6` has a single exit PC.

  Layout of `evm_div_v6` (instruction indices):
    [0..7]     divK_dispatchN1            (8)
    [8..31]    divK_clz                   (24)   — CLZ of b0 → x6 = s
    [32..38]   divK_fastSetup             (7)    — store s, b0' = b0<<s
    [39..60]   divK_normA                 (22)   — shift a → u[0..4] (s>0)
    [61..69]   divK_copyAU                (9)    — copy a → u[0..4] (s=0)
    [70..109]  4 × divK_fastDigit         (40)   — per-limb exact divide
    [110..119] divK_div_epilogue          (10)   — store quotient
    [120..204] divK_div128_v5             (85)   — fast path's own divide
    [205..557] evm_div_v5                 (353)  — reused n≥2 / zero path
  Exit PC = index 471 (the embedded v5's NOP), byte offset 1884.

  `evm_mod_v6` inserts `divK_fastDenorm` (7) before the MOD epilogue, shifting
  everything below it by 7.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.Execution

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Fast-path building blocks
-- ============================================================================

/-- Dispatch prologue. OR-reduce `b1|b2|b3`; `BNE` to v5 if n≥2; load `b0`,
    `BEQ` to v5 if `b0 = 0` (divisor zero). Otherwise fall through with
    `x5 = b0` into `divK_clz`. 8 instructions. -/
def divK_dispatchN1 (bneOff beqOff : BitVec 13) : Program :=
  LD .x5  .x12 40 ;;                          -- [0] b1
  LD .x10 .x12 48 ;;                          -- [1] b2
  single (.OR .x5 .x5 .x10) ;;               -- [2]
  LD .x10 .x12 56 ;;                          -- [3] b3
  single (.OR .x5 .x5 .x10) ;;               -- [4]
  single (.BNE .x5 .x0 bneOff) ;;            -- [5] n≥2 → v5
  LD .x5 .x12 32 ;;                           -- [6] b0
  single (.BEQ .x5 .x0 beqOff)               -- [7] b0=0 → v5 (zeroPath)

/-- Fast-path setup. Store `s` (CLZ of b0, in x6) at 3992; compute
    `antiShift = -s` in x2; compute `b0' = b0 << s` and store at 3984;
    `BEQ` to copyAU if `s = 0`. 7 instructions. -/
def divK_fastSetup (beqCopyOff : BitVec 13) : Program :=
  SD .x12 .x6 3992 ;;                         -- [0] store shift s
  ADDI .x2 .x0 0 ;;                           -- [1]
  single (.SUB .x2 .x2 .x6) ;;               -- [2] antiShift = -s
  LD .x5 .x12 32 ;;                           -- [3] b0
  single (.SLL .x5 .x5 .x6) ;;               -- [4] b0' = b0 << s
  SD .x12 .x5 3984 ;;                         -- [5] store b0'
  single (.BEQ .x6 .x0 beqCopyOff)           -- [6] s=0 → copyAU

/-- One single-limb division digit. Loads `uHi = u[j+1]`, `uLo = u[j]`,
    `d = b0'`; calls the fast path's own `divK_div128_v5` (`JAL x2 callOff`);
    stores the exact quotient digit `q[j] = x11`; recovers and stores the
    threaded remainder `u[j] ← u[j] -₆₄ q·b0'`. 10 instructions. -/
def divK_fastDigit (uHiOff uLoOff qOff : BitVec 12) (callOff : BitVec 21) : Program :=
  LD .x7  .x12 uHiOff ;;                       -- [0] uHi = u[j+1] = rem
  LD .x5  .x12 uLoOff ;;                       -- [1] uLo = u[j]
  LD .x10 .x12 3984 ;;                         -- [2] d = b0'
  JAL .x2 callOff ;;                           -- [3] x11 = qHat (exact)
  SD .x12 .x11 qOff ;;                         -- [4] q[j] = qHat
  LD .x5  .x12 uLoOff ;;                       -- [5] reload u[j]
  LD .x10 .x12 3984 ;;                         -- [6] reload b0'
  single (.MUL .x7 .x11 .x10) ;;             -- [7] qHat * b0' (low 64)
  single (.SUB .x5 .x5 .x7) ;;               -- [8] rem = u[j] - qHat*b0'
  SD .x12 .x5 uLoOff                          -- [9] u[j] = rem

/-- Single-limb remainder de-normalization for MOD: the final normalized
    remainder is in `u[0]` (= rem₀ = trueRem << s); `trueRem = rem₀ >> s`,
    with the upper limbs zero. 7 instructions. -/
def divK_fastDenorm : Program :=
  LD .x6 .x12 3992 ;;                          -- [0] s
  LD .x5 .x12 4056 ;;                          -- [1] u[0] = rem₀
  single (.SRL .x5 .x5 .x6) ;;               -- [2] trueRem = rem₀ >> s
  SD .x12 .x5 4056 ;;                          -- [3]
  SD .x12 .x0 4048 ;;                          -- [4] upper remainder limbs = 0
  SD .x12 .x0 4040 ;;                          -- [5]
  SD .x12 .x0 4032                             -- [6]

/-- Shared fast-path body: CLZ, setup, normalize dividend (`normA` for `s>0`,
    `copyAU` for `s=0`), then 4 single-limb division digits (`j = 3,2,1,0`).
    102 instructions. The digit `callOff`s point forward to the fast path's
    own `divK_div128_v5` copy. -/
def divK_fastBody (beqCopyOff : BitVec 13) (normaJalOff : BitVec 21)
    (call3 call2 call1 call0 : BitVec 21) : Program :=
  divK_clz ;;
  divK_fastSetup beqCopyOff ;;
  divK_normA normaJalOff ;;
  divK_copyAU ;;
  divK_fastDigit 4024 4032 4064 call3 ;;       -- j=3: uHi=u[4], uLo=u[3], q[3]
  divK_fastDigit 4032 4040 4072 call2 ;;       -- j=2
  divK_fastDigit 4040 4048 4080 call1 ;;       -- j=1
  divK_fastDigit 4048 4056 4088 call0          -- j=0: uHi=u[1], uLo=u[0], q[0]

-- ============================================================================
-- Top-level programs
-- ============================================================================

/-- 256-bit EVM DIV with the n=1 single-limb fast path (issue #9303).
    v5 entry at index 204; embedded v5 NOP exit at index 471 (byte 1884). -/
def evm_div_v6 : Program :=
  divK_dispatchN1 796 788 ;;
  divK_fastBody 88 40 188 148 108 68 ;;
  divK_div_epilogue 1412 ;;
  divK_div128_v5 ;;
  evm_div_v5

/-- 256-bit EVM MOD with the n=1 single-limb fast path (issue #9303).
    v5 entry at index 211; embedded v5 NOP exit at index 478 (byte 1912). -/
def evm_mod_v6 : Program :=
  divK_dispatchN1 824 816 ;;
  divK_fastBody 88 40 216 176 136 96 ;;
  divK_fastDenorm ;;
  divK_mod_epilogue 1412 ;;
  divK_div128_v5 ;;
  evm_mod_v5

-- ============================================================================
-- Length lemmas
-- ============================================================================

theorem divK_dispatchN1_length (a b : BitVec 13) :
    (divK_dispatchN1 a b).length = 8 := by rfl

theorem divK_fastSetup_length (a : BitVec 13) :
    (divK_fastSetup a).length = 7 := by rfl

theorem divK_fastDigit_length (u v q : BitVec 12) (c : BitVec 21) :
    (divK_fastDigit u v q c).length = 10 := by rfl

theorem divK_fastDenorm_length : divK_fastDenorm.length = 7 := by rfl

theorem divK_fastBody_length (a : BitVec 13) (n c3 c2 c1 c0 : BitVec 21) :
    (divK_fastBody a n c3 c2 c1 c0).length = 101 := by
  have h_clz : divK_clz.length = 24 := by rfl
  have h_setup : (divK_fastSetup a).length = 7 := by rfl
  have h_normA : (divK_normA n).length = 21 := by rfl
  have h_copyAU : divK_copyAU.length = 9 := by rfl
  have h_d3 : (divK_fastDigit 4024 4032 4064 c3).length = 10 := by rfl
  have h_d2 : (divK_fastDigit 4032 4040 4072 c2).length = 10 := by rfl
  have h_d1 : (divK_fastDigit 4040 4048 4080 c1).length = 10 := by rfl
  have h_d0 : (divK_fastDigit 4048 4056 4088 c0).length = 10 := by rfl
  unfold divK_fastBody
  simp only [seq, Program.length_append, h_clz, h_setup, h_normA, h_copyAU,
    h_d3, h_d2, h_d1, h_d0]

theorem evm_div_v6_length : evm_div_v6.length = 557 := by
  have h_disp : (divK_dispatchN1 796 788).length = 8 := by rfl
  have h_body : (divK_fastBody 88 40 188 148 108 68).length = 101 :=
    divK_fastBody_length _ _ _ _ _ _
  have h_epi : (divK_div_epilogue 1412).length = 10 := by rfl
  have h_div128 : divK_div128_v5.length = 85 := by unfold divK_div128_v5; rfl
  have h_v5 : evm_div_v5.length = 353 := evm_div_v5_length
  unfold evm_div_v6
  simp only [seq, Program.length_append, h_disp, h_body, h_epi, h_div128, h_v5]

theorem evm_mod_v6_length : evm_mod_v6.length = 564 := by
  have h_disp : (divK_dispatchN1 824 816).length = 8 := by rfl
  have h_body : (divK_fastBody 88 40 216 176 136 96).length = 101 :=
    divK_fastBody_length _ _ _ _ _ _
  have h_denorm : divK_fastDenorm.length = 7 := by rfl
  have h_epi : (divK_mod_epilogue 1412).length = 10 := by rfl
  have h_div128 : divK_div128_v5.length = 85 := by unfold divK_div128_v5; rfl
  have h_v5 : evm_mod_v5.length = 353 := evm_mod_v5_length
  unfold evm_mod_v6
  simp only [seq, Program.length_append, h_disp, h_body, h_denorm, h_epi,
    h_div128, h_v5]

end EvmAsm.Evm64
