# PLAN: Verified RISC-V EVM Implementation

> **Agent instruction**: Keep this file up to date as you work. When you finish
> implementing an opcode or task, move it to the "Done" list under
> "Current Status", update any counts or details that changed, and note any
> new sub-tasks you discovered. Check this file at the start of each session
> to pick up where the last agent left off.

Goal: implement and verify the EVM state transition function (STF) as RISC-V
macro assembly programs, for use as a zkEVM. Each EVM opcode becomes a verified
RISC-V subroutine operating on 256-bit stack words in memory. The STF is the
single most important piece in the execution layer — it processes blocks of
transactions against the world state.

**Target: RV64IM (64-bit)**, per the zkvm-standards spec
(`EvmAsm/Evm64/zkvm-standards/`). RV32IM was removed (not relevant).

Reference spec: `execution-specs/src/ethereum/forks/shanghai/vm/` (Python).
zkVM standards: `EvmAsm/Evm64/zkvm-standards/` (submodule).

---

## Architecture Overview

### RISC-V Backend

| | RV64IM (Evm64) |
|---|---|
| **Target** | `riscv64im_zicclsm-unknown-none-elf` |
| **Word size** | 64-bit (`BitVec 64`) |
| **Limbs per EvmWord** | 4 × 64-bit (LE) |
| **Memory ops** | LD/SD (8-byte aligned) |
| **Files** | `EvmAsm/Evm64/` |
| **Infrastructure** | `EvmAsm/Rv64/` |

### zkVM Standards (submodule: `EvmAsm/Evm64/zkvm-standards/`)

The standards define the target environment for Ethereum zkVMs:
- **RISC-V target**: RV64IM + Zicclsm (misaligned load/store support)
- **IO interface**: `read_input` / `write_output` for private input and public output
- **Cryptographic accelerators**: C interface for keccak256, ecrecover, SHA-256,
  RIPEMD-160, modexp, BN254, BLS12-381, BLAKE2f, KZG, secp256r1 (via
  `zkvm_accelerators.h`)
- These accelerators map directly to Ethereum precompiles and KECCAK256

### Machine State (Rv64)

```
MachineState:
  regs : Reg → BitVec 64       -- Registers: x0(zero), x1(ra), x2(sp),
                                --   x5-x7(t0-t2), x10-x12(a0-a2)
  mem  : Addr → BitVec 64      -- 64-bit addressable memory
  code : Addr → Option Instr   -- Instruction memory (immutable)
  pc   : BitVec 64             -- Program counter
  committed : List (Word × Word)  -- COMMIT syscall outputs
  publicValues : List (BitVec 8)  -- WRITE syscall outputs
  privateInput : List (BitVec 8)  -- HINT_READ input stream
```

EVM stack: x12 is EVM stack pointer, stack grows upward, 32 bytes per element.

### Proof Framework

- **Separation logic**: `r ↦ᵣ v` (register), `a ↦ₘ v` (memory), `**` (sep conj)
- **CPS Hoare triples**: `cpsTriple base end P Q` — from `base` to `end`, if P
  holds then Q holds, with automatic frame rule for untouched resources
- **Per-limb composition**: Each 256-bit op decomposes into 4 per-limb specs,
  then composed via `runBlock` tactic
- **Key tactics**: `xperm`, `xsimp`, `xcancel`, `seqFrame`, `runBlock`,
  `validMem`, `liftSpec`, `pcFree`

---

## Current Status

### Evm64 (PRIMARY) — 52 opcodes

| Category | Opcodes | Instructions (per op) | Status |
|----------|---------|----------------------|--------|
| Arithmetic | ADD, SUB, MUL, SIGNEXTEND | 30 / 30 / 63 / 48 | ✅ Fully proved |
| Bitwise | AND, OR, XOR, NOT | 17 / 17 / 17 / 12 | ✅ Fully proved |
| Shift | SHR, SHL, SAR | 90 / 90 / 95 | ✅ Fully proved |
| Comparison | ISZERO, LT, GT, EQ, SLT, SGT | 12 / 26 / 26 / 21 / 25 / 25 | ✅ Fully proved |
| Byte/SignExt | BYTE, SIGNEXTEND | 45 / 48 | ✅ Fully proved |
| Stack | POP, PUSH0, DUP1-16, SWAP1-16 | 1 / 5 / 9 / 16 | ✅ Fully proved |

**Deleted spec files** (incomplete CodeReq migration, easier to recreate):
- ~~`ShiftSpec.lean`~~ — ✅ Recreated as `LimbSpec.lean` (SHR) + `ShlSpec.lean` (SHL) + `Compose.lean` + `ShlCompose.lean` + `Semantic.lean` + `ShlSemantic.lean`
- ~~`ShlSpec.lean`~~ — ✅ Recreated (per-limb + body + composition + stack-level spec)
- ~~`SarSpec.lean`~~ — ✅ Recreated (per-limb + body + sign-fill + composition + stack-level spec)
- ~~`ByteSpec.lean`~~ — ✅ Recreated as `Byte/Spec.lean` (stack-level `evm_byte_stack_spec`) + `Byte/LimbSpec.lean` (per-body + cascade dispatch)
- ~~`StackOps.lean`~~ — ✅ Recreated as modular `Pop.lean`, `Push0.lean`, `Dup.lean`, `Swap.lean`

All deleted spec files have been recreated. See **Pending: Recreate Deleted Spec Files** below for details.

**Removed targets** (not relevant to primary goal):
- Evm32 (secondary RV32IM target) — removed entirely
- Rv32 infrastructure — removed entirely
- Examples (Swap, HelloWorld, Echo, etc.) — removed (all depended on Rv32)

### Infrastructure — RV64 only, no sorry

- RV64: Basic, Instructions, Program, Execution, CPSSpec,
  ControlFlow, SepLogic, GenericSpecs, InstructionSpecs, SyscallSpecs,
  HalfwordOps, WordOps
- Tactics: XPerm, XSimp, XCancel, SeqFrame, RunBlock, LiftSpec, ValidMem,
  PcFree, SpecDb
- **CodeReq infrastructure** (Issue #35): `CodeReq` type + `cpsTriple` 5-arg
  form + composition rules + tactic support in Rv64.
  CodeReq monotonicity helpers in SepLogic.lean
  (`union_singleton_apply`, `beq_base_offset`, `union_mono_tail`).
- **`CodeReq.ofProg`** (recent): Replaces chains of `singleton.union` with
  program-based CodeReq construction. Key infrastructure in SepLogic.lean:
  - `ofProg base prog` — builds CodeReq from a `List Instr`
  - `ofProg_append` — splits `ofProg base (p1 ++ p2)` into two `ofProg` unions
  - `ofProg_none_range` — proves out-of-range addresses return `none`
  - `unionAll` — structural subsumption for lists of CodeReqs
  - Range-based `ofProg` disjointness (O(1) vs O(n) singleton expansion)
  - MultiplySpec col0–col3 migrated to `ofProg` pattern
- **runTacticSilent**: Suppresses bv_omega diagnostic leaks from speculative
  tactic calls (Lean 4.29 regression fix in SeqFrame.lean/RunBlock.lean).
- **Execution Layer specs** (`EvmAsm/EL/`): Pure Lean specs for Ethereum
  data structures, independent of RISC-V. Currently:
  - `EL/RLP/` — RLP encoding/decoding with round-trip proofs (`native_decide`)
- **Byte-level infrastructure** (`ByteOps.lean`): `extractByte`/`replaceByte`
  algebra, `generic_lbu_spec` and `generic_sb_spec` CPS specs bridging
  byte-addressable operations to word-level separation logic assertions.
- **`divmod_addr` simp/grind set** (`Evm64/DivMod/AddrNorm.lean`, `AddrNormAttr.lean`,
  issue #263): Registers atomic `signExtend12`/`<<<`/`BitVec.toNat` evaluations
  on every concrete offset used in DivMod (33 signExtend12 offsets, 5 word
  shifts, 11 BitVec 6 toNat values) as `@[divmod_addr, grind =]` facts. The
  `divmod_addr` tactic macro closes address-arithmetic equalities grind-first,
  simp+bv_omega-fallback. First migration: 4 lemmas in `LoopComposeN3.lean`.
  Conventions, layout patterns, empirical justification, rules of thumb, and
  rollout roadmap are documented in `GRIND.md` (single source of truth for
  simp/grind-set conventions; `CLAUDE.md` and `AGENTS.md` link to it).
- **File-size guardrail** (`scripts/check-file-size.sh`, issue #314): CI step
  enforcing per-file line caps (1200 for `Compose/**`, 1500 elsewhere; `Program.lean`
  exempt). Files may opt out with a `-- file-size-exception: <reason>` comment in
  the first 20 lines. 6 oversize files grandfathered with exception comments
  pointing to their tracking issues (#312, #283, #266). Documented in `AGENTS.md`
  ("File-size guardrail") and `CONTRIBUTING.md`.
- **LP64 Calling Convention** (`Evm64/CallingConvention.lean`): LP64-aligned
  calling convention for the x0–x12 register subset, per zkvm-standards.
  - x1 (ra) = return address, x2 (sp) = call stack (grows down, callee-saved)
  - x10-x11 (a0-a1) = args/return values, x12 (a2) = EVM stack pointer
  - Program snippets: `cc_ret`, `cc_prologue` (16-byte frame), `cc_epilogue`
  - Proved specs: `callNear_spec`, `callFar_spec`, `ret_spec`, `ret_spec'`,
    `cc_prologue_spec`, `cc_epilogue_spec`,
    `callNear_function_spec` (call+return round-trip),
    `nonleaf_function_spec` (prologue+body+epilogue composition)
  - All new subroutines (handlers, RLP, interpreter) should use this convention.
    The older DivMod ad-hoc convention (x2 as return address) is legacy.

---

## Pending: Recreate Deleted Spec Files

Five Evm64 spec files were deleted because their CodeReq migration was
incomplete (manual `cpsTriple_seq_with_perm` calls lacked the `hd :
cr1.Disjoint cr2` argument added during the migration, and CR tree shapes
didn't match goals). The program definitions and tests remain in the
corresponding non-Spec files.

### Files to recreate (by priority)

#### ~~1. StackOps.lean — POP, PUSH0, DUP1-16, SWAP1-16~~ ✅ DONE

- **Files**: `Evm64/Pop.lean`, `Evm64/Push0.lean`, `Evm64/Dup.lean`, `Evm64/Swap.lean`
  (modular split; shared infra in `Stack.lean`)
- **Programs**: `evm_pop` (1 instr), `evm_push0` (5), `evm_dup(n)` (9), `evm_swap(n)` (16)
- **Specs**: All fully proved (0 sorry). Three-level hierarchy per opcode:
  low-level (explicit limbs) → EvmWord → stack (evmStackIs).
- **Pattern**: POP/PUSH0 use `CodeReq.ofProg` + `runBlock`. DUP/SWAP use
  explicit `CodeReq` union chains (symbolic `n` prevents `ofProg` whnf) with
  `runBlock` manual mode handling monotonicity via `buildMonoProof`'s
  union-split support. Per-limb helpers (`dup_pair_spec`, `swap_limb_spec`)
  use `runBlock` auto mode.
- **Shared infra** added to `Stack.lean`: `signExtend12_ofNat_small`,
  `evmStackIs_split_at`, `EvmWord.getLimb_zero`, `signExtend12_neg32`.

#### 2. ShiftSpec.lean — SHR per-limb, phase, body specs

- **File**: `Evm64/ShiftSpec.lean`
- **Programs**: `evm_shr` defined in `Shift.lean` (90 instructions, 3 phases)
- **What was in the old file**:
  - Per-limb helpers: `shr_merge_limb_spec` (7 instrs), `shr_last_limb_spec` (3),
    `shr_ld_or_acc_spec` (2), `shr_last_limb_inplace_spec` (4)
  - Phase specs: `shr_cascade_step_spec` (ADDI+BEQ cpsBranch),
    `shr_phase_c_spec` (cascade dispatch, cpsNBranch with 4 exits),
    `shr_phase_a_code_spec` (9 instrs, LD+OR+BNE+LD+SLTIU+BEQ)
  - Body specs: `shr_body_{0,1,2,3}_spec` (7-25 instrs each, `runBlock`)
  - Zero path: `shr_zero_path_spec` (5 instrs)
- **Approach**: Per-limb specs use `runBlock` auto mode (straightforward).
  Phase/body specs also use `runBlock`. The cascade and branch compositions
  previously used manual `cpsTriple_seq_cpsBranch_with_perm` — replace with
  `cpsTriple_seq_cpsBranch_with_perm_same_cr` after extending sub-specs to
  a common CR via `cpsTriple_extend_code`, or provide `(by crDisjoint)` for
  the `hd` argument.
- **Key pitfall**: `runBlock` for body specs involving `JAL .x0 jal_off`
  (symbolic offset) — the JAL's exit address `base + K + signExtend21 jal_off`
  needs `rw [hexit]` before `runBlock`. The `bv_omega` calls for addresses
  involving `signExtend21` may leak diagnostics; `runTacticSilent` suppresses
  these.

#### ~~3. ShlSpec.lean — SHL per-limb + body specs~~ ✅ DONE

- **Files**: `Evm64/Shift/ShlSpec.lean` (per-limb + body),
  `Evm64/Shift/ShlCompose.lean` (composition + bridge lemmas),
  `Evm64/Shift/ShlSemantic.lean` (stack-level `evm_shl_stack_spec`)
- **Bridge lemmas** in `Evm64/Basic.lean`: `getLimb_shiftLeft`,
  `getLimb_shiftLeft_eq_div`, `getLimb_shiftLeft_low` — connect per-limb body
  outputs to `getLimb (value <<< n)`, using `extractLsb'_split_64`
- **Composition**: mirrors SHR `Compose.lean` with `shlCode`, subsumption lemmas,
  zero-path specs (`evm_shl_zero_high_spec`, `evm_shl_zero_large_spec`),
  and body-path composition (`evm_shl_body_evmWord_spec`)
- **Stack-level spec**: `evm_shl_stack_spec` — zero axioms, zero sorry

#### ~~4. SarSpec.lean — SAR per-limb + body + sign-fill + composition + stack-level specs~~ ✅ DONE

- **Files**: `Evm64/Shift/SarSpec.lean` (per-limb + body + sign-fill),
  `Evm64/Shift/SarCompose.lean` (composition + bridge lemmas),
  `Evm64/Shift/SarSemantic.lean` (stack-level `evm_sar_stack_spec`)
- **Bridge lemmas** in `Evm64/Basic.lean`: `getLimb_sshiftRight_eq_ushiftRight`,
  `getLimb_sshiftRight_last`, `getLimb_sshiftRight_sign'`,
  `getLimb_sshiftRight_geq_256`, `getLimb_fromLimbs_const` — connect per-limb
  body outputs to `getLimb (sshiftRight value n)`
- **Composition**: mirrors SHR `Compose.lean` with `sarCode`, subsumption lemmas,
  sign-fill specs (`evm_sar_sign_fill_high_spec`, `evm_sar_sign_fill_large_spec`),
  SAR Phase C dispatch (`sar_phase_c_spec_pure`), and body-path composition
  (`evm_sar_body_evmWord_spec`)
- **Stack-level spec**: `evm_sar_stack_spec` — zero axioms, zero sorry
- **Key difference from SHR/SHL**: Sign-fill path (all limbs = `sshiftRight(v[3], 63)`)
  replaces zero-path; SRA instruction for MSB limb; sign extension for vacated limbs

#### ~~5. ByteSpec.lean — BYTE per-body + store + phase B specs~~ ✅ DONE

- **Files**: `Evm64/Byte/Spec.lean` (stack-level `evm_byte_stack_spec`, 3-way case split),
  `Evm64/Byte/LimbSpec.lean` (per-body + cascade dispatch specs),
  `Evm64/Byte/Program.lean` (45-instruction program + tests)
- **Specs**: `evm_byte_zero_high_spec`, `evm_byte_zero_geq32_spec`,
  `evm_byte_body_evmWord_spec`, `evm_byte_stack_spec` — all proved, 0 sorry
- **Pattern**: Uses `CodeReq.ofProg_mono_sub` for subsumption, cascade dispatch
  with frame and consequence rules, evmWordIs abstraction for stack-level spec

### General recreation guidelines

- Use `runBlock` auto mode wherever possible (handles CR extension, address
  normalization, and composition automatically).
- For manual compositions with different CRs, use `cpsTriple_seq_with_perm`
  with `(by crDisjoint)` for the `hd` argument, or extend to a common CR
  first and use `_same_cr` variants.
- All `_code` abbrevs should be `CodeReq` — prefer `CodeReq.ofProg base prog`
  over chains of `singleton.union`. See MultiplySpec.lean for the current pattern.
- Theorem statements use 5-arg `cpsTriple base exit cr P Q` with no
  `instrAt` atoms in P or Q.
- Reference the existing working specs (And.lean, Add.lean, MultiplySpec.lean,
  DivModSpec.lean) for the correct patterns.

---

## Roadmap: Phases 1-6 (Opcode Implementation)

All phases below target **Evm64** primarily. Files are under `EvmAsm/Evm64/`.

### ~~Phase 1: Complete Comparisons~~ — DONE

#### ~~1.1 SLT (Signed Less Than)~~ ✅
- **Files**: `Evm64/Comparison.lean` (helpers: `beq_eq_spec`, `beq_ne_spec`, `slt_msb_load_spec`) + `Evm64/Slt.lean`
- **Approach**: Compare MSB limbs (limb 3) with signed SLT instruction.
  If equal, fall through to unsigned borrow chain on lower 3 limbs.
  Uses `by_cases` on MSB equality for deterministic paths + `runBlock`.
- 25 instructions = 100 bytes. Also added `slt_spec_gen` to `SyscallSpecs.lean`.

#### ~~1.2 SGT (Signed Greater Than)~~ ✅
- **Files**: `Evm64/Comparison.lean` + `Evm64/Sgt.lean`
- **Approach**: SGT(a,b) = SLT(b,a). Swap operand load order (b-limbs into x7, a-limbs into x6).
- 25 instructions = 100 bytes. Mirrors SLT proof structure exactly.

### ~~Phase 2: Remaining Shifts & Bitwise~~ — DONE

> **Note**: Phases 2.1–2.3 were originally proved, then deleted in commit
> `1197924` due to incomplete CodeReq migration, then fully recreated.
> All specs are now proved with 0 sorry.

#### ~~2.1 SHL (Shift Left)~~ ✅
- **Files**: `Evm64/Shift/ShlSpec.lean` (per-limb + body), `Evm64/Shift/ShlCompose.lean`
  (composition + bridge lemmas), `Evm64/Shift/ShlSemantic.lean` (stack-level `evm_shl_stack_spec`)
- 90 instructions = 360 bytes. All specs proved, 0 sorry.

#### ~~2.2 SAR (Shift Right Arithmetic)~~ ✅
- **Files**: `Evm64/Shift/SarSpec.lean` (per-limb + body + sign-fill),
  `Evm64/Shift/SarCompose.lean` (composition + bridge lemmas),
  `Evm64/Shift/SarSemantic.lean` (stack-level `evm_sar_stack_spec`)
- 95 instructions = 380 bytes. All specs proved, 0 sorry.

#### ~~2.3 BYTE (Extract byte from word)~~ ✅
- **Files**: `Evm64/Byte/Spec.lean` (stack-level `evm_byte_stack_spec`),
  `Evm64/Byte/LimbSpec.lean` (per-body + cascade dispatch), `Evm64/Byte/Program.lean`
- 45 instructions = 180 bytes. All specs proved, 0 sorry.

### Phase 3: Stack Extensions

#### ~~3.1 DUP1-16 and SWAP1-16 (Generic)~~ ✅
- **Files**: `Evm64/Pop.lean`, `Evm64/Push0.lean`, `Evm64/Dup.lean`, `Evm64/Swap.lean`
- **Approach**: `evm_dup (n : Nat)` and `evm_swap (n : Nat)` as generic
  Lean functions producing `Program`. 9 instructions for DUP, 16 for SWAP.
  Full spec hierarchy: low-level (explicit limbs) → evmWordIs → evmStackIs.
  Added `signExtend12_ofNat_small` and `evmStackIs_split_at` to `Stack.lean`.
- Covers 34 opcodes (POP, PUSH0, DUP1-16, SWAP1-16) with one proof each. Fully proved.

#### 3.2 PUSH1-32
- **File**: `Evm64/StackOps.lean`
- **Approach**: Requires EVM bytecode parsing. Push immediate from EVM code
  region. Read 1-32 bytes from code[pc+1..pc+n], zero-extend to 256 bits,
  push onto stack.
- **Depends on**: EVM code region model (Phase 5.1)

### Phase 4: Remaining Arithmetic

#### ~~4.1 MUL (256-bit Multiply)~~ ✅
- **Files**: `Evm64/Multiply.lean` (program + 16 tests)
- **Approach**: Schoolbook 4×4 limb column-wise multiplication using RV64 MUL/MULHU.
  Column j processes b[j] × a[0..3-j]. After column j, result[j] is finalized.
  Carry detection via SLTU after ADD. Intermediate r[3] accumulator spilled to memory
  (reusing freed a-limb slots). Added `sltu_spec_gen_rd_eq_rs2` to SyscallSpecs.lean.
  Fixed operator precedence bug in rv64_mulhu/rv64_mulh/rv64_mulhsu (`>>>` binds tighter than `*`).
- 63 instructions = 252 bytes. All specs proved, 0 sorry.
  Manual-mode `runBlock` with column decomposition (col0: 21, col1: 23, col2: 13, col3: 5, epilogue: 1).
  Added `mul_spec_gen_rd_eq_rs1`, `mulhu_spec_gen_rd_eq_rs1`, `sltu_spec_gen_rd_eq_rs2` to SyscallSpecs.

#### 4.2 DIV and MOD — in progress (program + specs + composition in progress)
- **Files**: `Evm64/DivMod.lean` (program + tests), `Evm64/DivModSpec.lean` (CPS specs),
  `Evm64/DivModCompose.lean` (hierarchical composition)
- **Approach**: Knuth Algorithm D in base 2^64. 316 instructions total (21 phases
  + 49-instr div128 subroutine + NOP separator). DIV and MOD share 95% of code,
  differ only in epilogue (load quotient vs remainder).
- **Status**: 69 CPS specs proved in LimbSpec.lean (0 sorry). All building
  blocks for every phase. div128 subroutine fully specified in composable blocks
  including phase1, step1 (init+clamp_q1+prodcheck1), compute_un21, step2
  (init+clamp_q0+prodcheck2), end. Branch merge specs for BEQ/BLTU patterns.
  Composed per-limb specs: mulsub_limb (11 instrs), addback_limb (8 instrs),
  trial_load (12 instrs), store_qj (4 instrs).
  Hierarchical composition using progAt to avoid WHNF scaling limit:
  - `divCode`/`modCode` split `progAt base evm_div/evm_mod` into 14 per-phase progAt blocks
  - `divCode_mid` (12 blocks excl phaseA+zeroPath), `divCode_noAB` (12 blocks excl phaseA+phaseB)
  - `progAt_divK_phaseB_at32`: pre-normalized phaseB expansion (21 instrAt atoms at base+K offsets)

  **Completed compositions (0 sorry):**
  - `evm_div_bzero_spec` (b=0 path): phaseA → BEQ taken → zeroPath ✅
  - `evm_div_phaseA_ntaken_spec` (b≠0): phaseA body → BEQ ntaken → base+32 ✅
  - `evm_div_phaseB_n4_spec` (b[3]≠0): init1→init2→ADDI→BNE(taken)→tail, 16 instrs ✅
  - `evm_div_phaseAB_n4_spec` (b≠0, b[3]≠0): phaseA+phaseB composed, 24 instrs, base→base+116 ✅
  - `evm_mod_bzero_spec` (b=0 path): same as div but with modCode ✅
  - `evm_mod_phaseA_ntaken_spec` (b≠0): same as div but with modCode ✅

  - Phase B cascade variants ✅: n=3, n=2, n=1 all composed (0 sorry)
    - `evm_div_phaseB_n3_spec` (b[3]=0, b[2]≠0): 18 instrs, x5=b[2], n=3
    - `evm_div_phaseB_n2_spec` (b[3]=b[2]=0, b[1]≠0): 20 instrs, x5=b[1], n=2
    - `evm_div_phaseB_n1_spec` (b[3]=b[2]=b[1]=0): 21 instrs (full phaseB), x5=b[0], n=1
    - 5 singleton subsumption lemmas for cascade step instructions (indices 11-15 of phaseB)
  - CLZ (Count Leading Zeros) ✅: 24 instructions, 6-stage binary search
    - `divK_clz_spec` at base+116→base+212, `clzResult` function for postcondition
    - Combined stage specs avoid exponential branching via conditional postconditions

  - Phase C2 ✅: shift check cpsBranch (4 instrs, base+212)
    - `divK_phaseC2_ntaken_spec` (shift≠0 → normB), `divK_phaseC2_taken_spec` (shift=0 → copyAU)
  - NormB ✅: normalize divisor (21 instrs, base+228), `divK_normB_full_spec`
  - NormA ✅: normalize dividend (21 instrs + JAL, base+312→base+432), `divK_normA_full_spec`
  - CopyAU ✅: copy a[]→u[] (9 instrs, base+396), `divK_copyAU_full_spec`

  - LoopSetup ✅: cpsBranch (4 instrs, base+432)
    - `divK_loopSetup_ntaken_spec` (m≥0 → loop body), `divK_loopSetup_taken_spec` (m<0 → denorm)
  - DIV Epilogue ✅: load q[0..3] + store to output (10 instrs, base+1004), `divK_div_epilogue_spec`

  **Full path compositions:**
  - LoopBody (main Knuth D loop): 114 instructions at base+448
    - 20 sorry-free theorems in `LoopBody.lean` + N-specific variants in `LoopBodyN{1,2,3,4}.lean`
    - `intro_lets` tactic added for selective let-binding expansion (xperm scaling fix)
    - Per-case concrete specs were in `LoopBodyN{X}Concrete.lean` (removed, see semantic path below)
  - Per-n full specs: removed (existentially quantified computation results → not useful)
  - Stack-level b≠0 specs: TODO (needs semantic correctness bridge first)

  **Remaining work (semantic correctness):**
  - Multi-limb arithmetic foundations: `MultiLimb.lean` — half-word decomposition, rv64_divu/mulhu
    Nat-level correctness, val128/val256 representation, partial product decomposition (done)
  - Div128 mathematical foundations: `Div128Lemmas.lean` — half-word OR-combine, 128-bit Euclidean
    uniqueness, trial quotient bounds (q_true ≤ q̂ ≤ q_true + 2 when normalized) (done)
  - Multiply-subtract chain: `MulSubChain.lean` — carry/borrow propagation, 4-limb telescoping
    chain (`mulsub_chain_nat`), correction step (`mulsub_correction_eq`) (done)
  - Normalization: `Normalization.lean` — `norm_div_eq` (shifting preserves quotient),
    `norm_euclidean_bridge` (recover original q,r from normalized), `div_mod_no_overflow` (done)
  - Division bridge: `DivBridge.lean` — `bv_eq_of_nat_eq` (Nat eq → BitVec eq, auto no-overflow),
    `div_of_nat_euclidean` / `mod_of_nat_euclidean` (Nat Euclidean → EvmWord.div/mod), `div_from_mulsub` (done)
  - N=4 case lemmas: `DivN4Lemmas.lean` — quotient bound (≤1 when MSB set), q=0/q=1 subcases,
    MSB → hi32 normalization condition, val256 positivity (done)
  - CLZ correctness: `CLZLemmas.lean` — `clz_zero_imp_msb` (shift=0 → val ≥ 2^63),
    `msb_imp_clz_zero` (converse), `clzResult_fst_eq_zero_iff` (biconditional),
    algebraic proof via `clzStep` abstraction with stage bound chain (done)
  - Limb bridge: `DivLimbBridge.lean` — OR-reduce nonzero → val256 > 0 / fromLimbs ≠ 0,
    per-limb val256 lower bounds (n=1: ≥1, n=2: ≥2^64, n=3: ≥2^128, n=4: ≥2^192) (done)
  - Per-limb mulsub: `DivMulSubLimb.lean` — `mulhu_toNat_le` (MULHU ≤ 2^64-2),
    `mulsub_limb_nat_eq` (per-limb carry equation from register ops),
    `mulsub_carry_word_eq` (Word carry = Nat carry when < 2^64),
    `mulsub_4limb_euclidean_div` (4-limb chain → EvmWord.div/mod for single-digit quotient) (done)
  - Per-limb addback: `DivAddbackLimb.lean` — `addback_limb_nat_eq` (per-limb carry equation),
    `addback_4limb_val256` (4-limb addition chain), `addback_correction_euclidean`
    (mulsub underflow + addback → corrected Euclidean with q-1) (done)
  - Remainder bound: `DivRemainderBound.lean` — `remainder_lt_of_ge_floor` (key: Euclidean eq +
    overestimate → exact quotient + remainder < divisor), `mulsub_no_underflow_correct` (happy path),
    `mulsub_addback_correct` (addback path), `val256_euclidean_to_div_mod` (val256 → EvmWord bridge),
    `norm_euclidean_correct` (normalization round-trip) (done)
  - Quotient accumulation: `DivAccumulate.lean` — multi-iteration telescoping (`iter_accumulate_{2,3,4}`),
    val256 trailing-zero simplifications, per-n end-to-end `div_correct_n{1,2,3,4}_no_shift`,
    `div_quotient_of_normalized` / `mod_remainder_of_normalized` (shift bridge),
    `div_of_val256_eq_div` / `mod_of_val256_eq_mod` (val256 → EvmWord),
    `div_correct_normalized` / `mod_correct_normalized` (combined normalization bridge) (done)
  - Mulsub carry strict bound: `DivMulSubCarry.lean` — `mulsub_limb_carry_strict_lt` (per-limb carry
    always < 2^64, proven via case analysis on MULHU maximum), `mulsub_limb_word_carry_eq` (Word carry
    = Nat carry, unconditional), `mulsub_limb_nat_word_eq` (per-limb equation with Word carry_out),
    `mulsub_register_4limb_val256` (4-limb register ops → val256 Euclidean equation) (done)
  - Addback carry bridge: `DivAddbackCarry.lean` — `or_toNat_eq_add_of_le_one` (OR = ADD for {0,1}
    Words), `addback_carries_exclusive` (two overflow flags can't both fire), `addback_limb_nat_word_eq`
    (per-limb addback with OR carry), `addback_register_4limb_val256` (4-limb addback → val256) (done)
  - Stack spec bridge: `DivLimbBridge.lean` — `ne_zero_iff_getLimbN_or` (EvmWord nonzero ↔ limbs OR
    nonzero), `getLimbN_fromLimbs_match` / `getLimbN_fromLimbs_{0,1,2,3}` (fromLimbs round-trip for
    reconstructing evmWordIs from individual memory cells) (done)
  - **Semantic correctness path:**
    - Step 1: Make `loopBodyPostN{1,2,3,4}` parametric — move output values to definition
      parameters so per-case concrete specs can fill them in concretely.
      Status: ✅ Done (PRs #197 + #202)
    - Step 2: Per-n loop iteration cpsTriple specs using `divK_store_loop_j0_spec` (j=0)
      and `divK_store_loop_jgt0_spec` (j>0). Four raw specs per (n, j) pair
      (max_skip, max_addback, call_skip, call_addback), then unified skip/addback
      into `divK_loop_body_nX_{max,call}_unified_jY_spec`.
      Status:
        - ✅ n=4: j=0 all 4 paths done (`LoopIterN4.lean`)
        - ✅ n=3: j=0 all 4 paths + j=1 all 4 paths + unified specs (`LoopIterN3.lean`, `LoopComposeN3.lean`)
        - ✅ n=2: j=0,j=1,j=2 all 4 paths + unified specs (`LoopIterN2.lean`, `LoopComposeN2.lean`)
        - ✅ n=1: j=0,j=1,j=2,j=3 all 4 paths + unified specs (`LoopIterN1.lean`, `LoopComposeN1.lean`)
    - Step 2b: **Bool-parameterized loop composition** (Issue #262, PRs #267–#272).
      Unifies max/call branch paths via `(bltu : Bool)` parameter so that
      2^k path combinations collapse to 1 theorem.
      Status:
        - ✅ Unified defs: `iterN3`, `iterN2`, `loopIterPostN3`, `loopN3UnifiedPost`, `loopN2UnifiedPost` (`LoopDefs.lean`)
        - ✅ n=3 unified 2-iteration composition: `divK_loop_n3_unified_spec (bltu_1 bltu_0 : Bool)` (`LoopUnifiedN3.lean`)
        - ✅ n=3 unified preloop+loop: `evm_div_n3_preloop_loop_unified_spec` (`Compose/FullPathN3LoopUnified.lean`)
        - ✅ n=2 unified 3-iteration composition: `divK_loop_n2_unified_spec (bltu_2 bltu_1 bltu_0 : Bool)` (`LoopUnifiedN2.lean`)
          Layered: iter10 (4 cases) → max/call+iter10 (2 lemmas) → unified dispatch
        - ✅ n=1 unified 4-iteration composition: `divK_loop_n1_unified_spec (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)` (`LoopUnifiedN1.lean`)
          5-layer composition: iter10 → max/call_iter10 → iter210 → max/call_iter210 → unified
        - `iterN2Max`/`iterN2Call` marked `@[irreducible]` to prevent stuck if-reduction in projections
        - Unified condition predicates: `isTrialN3_j1/j0`, `isTrialN1_j3/j2/j1/j0`
      Issue #262 is **complete** — Bool unification achieved for all n-values (n=1,2,3; n=4 trivial).
    - Step 3: Per-n full-path composition theorems (base→base+1064) with bundled postconditions.
      Composes pre-loop (normalization) + loop body + post-loop (denorm/epilogue).
      Status:
        - ✅ n=4 shift≠0: `evm_div_n4_full_{max,call}_{skip,addback}_spec` (`FullPathN4.lean`)
        - ✅ n=4 shift=0: `evm_div_n4_full_shift0_call_{skip,addback}_spec` (`FullPathN4Shift0.lean`)
        - ✅ n=3 shift≠0: 4 full-path theorems (`FullPathN3Loop.lean`) — can be replaced by unified version
        - ✅ n=3 shift=0: 2 full-path theorems (`FullPathN3Shift0.lean`)
        - ✅ n=2 shift≠0: unified full-path `evm_div_n2_full_unified_spec` (`FullPathN2Full.lean`, `FullPathN2Cases.lean`)
          8 per-case lemmas + unified dispatch via `delta + rfl` postcondition bridge
        - ✅ n=2 shift=0: unified full-path `evm_div_n2_full_shift0_unified_spec` (`FullPathN2Shift0.lean`)
          j=2 always call (u4=0 < b1), unified over (bltu_1 bltu_0 : Bool) for 4 combinations
        - ✅ n=1 shift≠0: unified full-path `evm_div_n1_full_unified_spec` (`FullPathN1Full.lean`)
          16-case denorm_comp with parametric denorm' helper, all 16 Bool combinations
        - ✅ n=1 shift=0: unified full-path `evm_div_n1_full_shift0_unified_spec` (`FullPathN1Shift0.lean`)
          j=3 always call (u_top=0 < b0), unified over (bltu_2 bltu_1 bltu_0 : Bool) for 8 combinations
      All n-values complete. Next:
        - MOD variants: factor shared DIV/MOD loop to avoid duplication (Issue #266)
    - Step 4: Semantic correctness bridge — connect algorithm computations to `EvmWord.div`.
      Infrastructure exists: `div_correct_n4_no_shift`, `remainder_lt_of_ge_floor`,
      `mulsub_no_underflow_correct`, `mulsub_addback_correct`, `mulsubN4_val256_eq`.
      Partial progress:
        - ✅ Max trial overestimate: `val256_div_lt_pow64` — when b3≠0, val256(a)/val256(b) ≤ 2^64-1
        - ✅ Skip path correctness: `n4_max_skip_correct` — c3=0 + max trial → EvmWord.div correct
        - **Missing math theorem (Knuth's Theorem B)**: for the addback and call paths, need:
          1. **Mulsub borrow bound**: prove that `mulsubN4` borrow c3 has `c3.toNat ≤ 1`
             when the trial quotient overestimates by ≤ 1 (i.e., q_hat ≤ ⌊u/v⌋ + 1).
             This ensures the 2^256 terms cancel in the mulsub+addback combined equation.
          2. **Call path trial quotient overestimate**: prove that `div128Quot u_top u3 v3`
             produces a quotient q̂ satisfying `⌊u/v⌋ ≤ q̂ ≤ ⌊u/v⌋ + 1` when the divisor's
             leading limb has its MSB set (normalized). This is the formal version of
             Knuth TAOCP Vol 2 §4.3.1 Theorem B.
          3. **Addback combined equation**: given c3=1 (borrow) and carry=1 (addback carry),
             derive `val256(a) = (q_hat-1) * val256(b) + val256(aun)` from `mulsubN4_val256_eq`
             + `addbackN4_val256_eq`.
      Status: In progress (`DivN4Overestimate.lean`). This is independent of Steps 2-3 and can
      proceed in parallel. Once done for n=4, the bridge generalizes to n=1,2,3 via the same
      `div_correct_normalized` framework.
    - Step 5: Stack-level spec using `evmWordIs`. Case-split on b=0/≠0, then on n,
      apply full-path spec + semantic bridge to prove `evmWordIs (sp+32) (EvmWord.div a b)`.
      Status: Not started (blocked on Steps 3+4 for all n values)

  **Path to EVM-level DIV/MOD specs (summary):**
  1. ✅ Complete n=2 loop composition with Bool unification (PRs #270–#272)
  2. ✅ Complete n=2 full-path composition (PRs #274–#277)
  3. ✅ Complete n=1 loop iteration specs + Bool-unified composition (PRs #282–#286)
  4. ✅ Complete n=1 + n=2 shift=0 and shift≠0 full-path compositions (PRs #280, #288, #289)
  5. Complete Knuth's Theorem B (Step 4) — can proceed in parallel
  5. Per-n semantic bridge: connect full-path postconditions to `EvmWord.div`/`EvmWord.mod`
  6. Stack-level spec: case-split b=0/≠0, then on n, compose full-path + semantic bridge
  7. Factor shared DIV/MOD loop (Issue #266) to derive MOD specs from DIV proofs

#### 4.3 SDIV and SMOD (Signed)
- **Approach**: Check signs, compute unsigned div/mod, apply sign correction.

#### 4.4 ADDMOD and MULMOD
- **Approach**: ADDMOD needs 257-bit intermediate (carry). MULMOD needs
  512-bit intermediate. Both reuse DIV/MOD.

#### 4.5 EXP (Exponentiation)
- **Approach**: Square-and-multiply using MUL. Loop over exponent bits.

#### ~~4.6 SIGNEXTEND~~ ✅
- **Files**: `Evm64/SignExtend/` — `Program.lean` (program + 16 tests), `LimbSpec.lean` (per-body + phase A/B/C specs),
  `Compose.lean` (subsumption + no-change + body path composition), `Spec.lean` (stack-level `evm_signextend_stack_spec`)
- **Approach**: If b >= 31, result = x. Else compute limb_idx = b/8, shift_amount = 56 - (b%8)*8.
  Cascade dispatch to body_N: SLL+SRA sign-extends target limb in-place, SRAI fills higher limbs.
  Shares Phase B computation with BYTE opcode. `EvmWord.signextend` definition + per-limb bridge lemmas in `EvmWordArith.lean`.
- 48 instructions = 192 bytes. All specs proved, 0 sorry. Axiom-clean.

### Phase 5: Memory & Code Region

#### 5.1 EVM Code Region Model
- **File**: `Evm64/CodeRegion.lean` (new)
- **Approach**: Define EVM bytecode as a byte array in RISC-V memory.
  Use LBU for byte access. Define `evmCodeIs(base, bytes)` assertion.
  Needed for PUSH1-32, and for the interpreter loop (Phase 7).

#### 5.2 EVM Memory Model
- **File**: `Evm64/Memory.lean` (new)
- **Approach**: EVM memory as a byte-addressable region in RISC-V memory.
  Use LB/SB/LBU for byte access. Define `evmMemIs` assertion.
  Zero-initialized, auto-expanding (model fixed max size initially).

#### 5.3 MLOAD, MSTORE, MSTORE8, MSIZE
- **File**: `Evm64/Memory.lean`
- **Approach**: MLOAD pops offset, loads 32 bytes, pushes word.
  MSTORE pops offset+value, stores 32 bytes. MSTORE8 stores 1 byte.
  MSIZE pushes current memory size (track in register or memory).

### Phase 6: Environment & Block Context

#### 6.1 Environment Context Layout
- **File**: `Evm64/Environment.lean` (new)
- **Approach**: Memory layout for EVM execution context:
  - msg.caller, msg.value, msg.data (calldata)
  - block.number, block.timestamp, block.basefee, etc.
  - tx.origin, tx.gasprice, chainid
  Store at known base address. Define `envIs` separation logic assertion.

#### 6.2 Simple Environment Opcodes
- ADDRESS, CALLER, CALLVALUE, ORIGIN, GASPRICE, COINBASE, TIMESTAMP,
  NUMBER, CHAINID, BASEFEE, SELFBALANCE, CODESIZE, RETURNDATASIZE
- Each is LD × 4 from environment region + push to stack.

#### 6.3 CALLDATALOAD, CALLDATASIZE, CALLDATACOPY
- Load from calldata region in environment.

---

## Execution Layer Prerequisites

The STF (Phase 11) reads RLP-encoded blocks via `read_input`. These
prerequisites provide the pure spec and RISC-V infrastructure for that.

### EL.1 RLP Specification ✅
- **Files**: `EvmAsm/EL/RLP/Basic.lean`, `Decode.lean`, `Properties.lean`
- `RLPItem` type (bytes | list), `encode`, `decode` with canonical enforcement
- 17 kernel-verified properties via `native_decide` (round-trip, spec conformance)
- 0 sorry, 0 axioms

### EL.2 Byte-Level Infrastructure ✅
- **File**: `EvmAsm/Rv64/ByteOps.lean`
- `extractByte`/`replaceByte` algebra (round-trip, independence, overwrite)
- `generic_lbu_spec`: CPS spec for LBU in terms of `extractByte` on containing dword
- `generic_sb_spec`: CPS spec for SB in terms of `replaceByte` on containing dword

### EL.3 RLP RISC-V Decoder (in progress)
- **Files**: `EvmAsm/Rv64/RLP/`
- Phase 1: Prefix classifier (cascade BLTUs, 5 exits) — ✅ both variants landed
  - `rlp_phase1_step_spec` (per-step with pure ult fact),
    `rlp_phase1_step_spec_plain` (strips pure facts).
  - `rlp_phase1_classifier_spec` — plain 5-exit `cpsNBranch` at boundaries
    0x80, 0xB8, 0xC0, 0xF8 (no dispatch facts).
  - `rlp_phase1_classifier_spec_pure` — per-step dispatch facts at each
    exit (`⌜ult v5 k_i⌝` for taken exits, `⌜¬ ult v5 k4⌝` for fall-through).
  - Optional accumulated-chain variant (each exit carries *all* prior
    negations plus the current taken fact) not yet implemented; downstream
    phases that only need the current-step fact can use `_pure` as-is.
- Phase 2: Length extraction (short inline + long big-endian loop)
- Phase 3: Single-item flat decode (byte strings only)
- Phase 4: HINT_READ integration (load RLP input into memory buffer)
- Phase 5: Recursive list decode (iterative with explicit stack)
- Phase 6: Top-level pipeline (HINT_READ → decode → output)
- **Output format**: Pointer + length (zero-copy into input buffer)
- **Depends on**: EL.1 (spec to verify against), EL.2 (byte-level specs)

---

## Roadmap: Phases 7-11 (STF — State Transition Function)

The STF is the end goal. It takes a block (header + transactions) and the
pre-state, executes all transactions, and produces the post-state. The STF
is what gets proved inside the zkVM.

### STF Architecture

The STF decomposes into layers (from the execution-specs):

```
state_transition(block, pre_state) → post_state
  └── apply_body(block_header, transactions, ommers)
        └── for each tx: process_transaction(env, tx)
              └── process_message_call(message)
                    └── execute(env) — the interpreter loop
                          └── for each step: dispatch opcode → handler
```

In our RV64 implementation, this maps to:

```
main():  read_input → Block + pre_state
         call state_transition
         write_output → post_state_root
```

### Phase 7: Interpreter Loop (EVM execution core)

This is the heart of the STF — the inner loop that executes EVM bytecode.

#### 7.1 EVM Machine State
- **File**: `Evm64/EvmState.lean` (new)
- **Approach**: Define the EVM-level execution state in RISC-V memory:
  ```
  struct EvmState {
    pc      : u64       // EVM program counter (byte offset into code)
    gas     : u64       // Remaining gas
    sp      : u64       // Stack pointer (already x12)
    memory  : *u8       // EVM memory base pointer
    memsize : u64       // Current memory size
    code    : *u8       // EVM bytecode pointer
    codelen : u64       // Code length
    env     : *u8       // Environment context pointer
    status  : u64       // Running / Stopped / Reverted / Error
  }
  ```
  Define `evmStateIs` assertion combining all sub-assertions.

#### 7.2 Opcode Dispatch
- **File**: `Evm64/Dispatch.lean` (new)
- **Approach**: Read `code[evm_pc]` byte, dispatch to handler.
  **Option A**: Jump table — load handler address from table[opcode], JAL.
  **Option B**: Binary search tree of BEQ comparisons.
  Jump table is faster (O(1)) but needs 256-entry table in memory.
  Binary search is smaller but O(log n).
  **Recommendation**: Jump table. 256 × 8 = 2048 bytes, small for zkVM.
- **Spec**: `dispatch_spec` relates opcode byte to correct handler entry point.

#### 7.3 Opcode Handlers (subroutine wrappers)
- **File**: `Evm64/Handlers.lean` (new)
- **Calling convention**: Use LP64 convention from `CallingConvention.lean`.
  Each handler is a non-leaf function using `cc_prologue` / `cc_epilogue`.
  Compose with `callNear_function_spec` / `nonleaf_function_spec`.
- **Approach**: Each handler is a thin wrapper:
  1. Deduct gas cost
  2. Call the opcode subroutine (e.g., `evm_add`) via `JAL x1, offset`
  3. Advance EVM PC by appropriate amount (1 for most, 1+n for PUSHn)
  4. Return to dispatch loop via `cc_ret`
- **Spec**: Each handler spec composes gas deduction + opcode spec + PC advance.

#### 7.4 Interpreter Main Loop
- **File**: `Evm64/Interpreter.lean` (new)
- **Approach**: RISC-V loop:
  ```
  loop:
    LBU opcode, code_base[evm_pc]    // read current opcode
    // dispatch to handler via jump table
    LD  handler, table[opcode * 8]
    JALR ra, handler
    // handler returns here
    // check status: if still running, loop
    BEQ status, RUNNING, loop
    // else: halt (STOP/RETURN/REVERT/ERROR)
  ```
- **Spec**: Inductive spec relating N EVM steps to N iterations:
  `interpreter_step_spec`: one iteration preserves EVM state invariant.
  `interpreter_N_spec`: N iterations = N EVM instruction executions.
- **Key invariant**: At each loop entry, the RISC-V state correctly
  represents the EVM state (stack, memory, PC, gas, status).
- **Proof strategy**: Define simulation relation between EVM abstract state
  and RISC-V concrete state. Prove each opcode handler preserves the
  simulation. Then the loop preserves it inductively.

### Phase 8: Storage & System Calls

#### 8.1 Storage Model (via host syscalls)
- SLOAD/SSTORE use ECALL to communicate with the zkVM host.
- The host provides storage read/write as part of the witness.
- **Spec**: Abstract storage as `Map U256 U256`. SLOAD returns `storage[key]`,
  SSTORE updates `storage[key] := value`.

#### 8.2 Precompiles (via zkvm_accelerators)
- Map EVM precompile addresses (0x01-0x11) to `zkvm_accelerators.h` calls.
- ECRECOVER (0x01) → `zkvm_secp256k1_ecrecover`
- SHA256 (0x02) → `zkvm_sha256`
- RIPEMD160 (0x03) → `zkvm_ripemd160`
- MODEXP (0x05) → `zkvm_modexp`
- BN254 (0x06-0x08) → `zkvm_bn254_*`
- BLAKE2f (0x09) → `zkvm_blake2f`
- KZG (0x0a) → `zkvm_kzg_point_eval`
- BLS12-381 (0x0b-0x11) → `zkvm_bls12_*`
- secp256r1 (0x100) → `zkvm_secp256r1_verify`

#### 8.3 KECCAK256 (via accelerator)
- Pop offset+size, hash EVM memory region.
- Delegates to `zkvm_keccak256` accelerator.
- Spec: result = keccak256(memory[offset..offset+size]).

#### 8.4 LOG0-LOG4
- Pop offset+size (+topics), emit log event via ECALL.

#### 8.5 CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2
- Create child EVM frames. Model as recursive interpreter calls or
  host-delegated syscalls.
- RETURN and REVERT halt the current frame with output data.

### Phase 9: Gas Metering

#### 9.1 Static Gas
- Each opcode deducts a fixed gas cost before execution.
- Out-of-gas → halt with error, revert state.

#### 9.2 Dynamic Gas
- Memory expansion: quadratic cost based on memory high-water mark.
- Storage: cold/warm access costs (EIP-2929).
- CALL gas: 63/64 rule, stipend for value transfers.

### Phase 10: Transaction Processing

#### 10.1 Message Call
- **File**: `Evm64/MessageCall.lean` (new)
- **Approach**: Set up EVM execution frame:
  1. Initialize EVM state (code, calldata, gas, value, caller)
  2. Run interpreter loop to completion
  3. Handle output (RETURN data, REVERT, error)
  4. Apply state changes (storage writes, balance transfers)
- **Reference**: `execution-specs/.../vm/interpreter.py:process_message_call`

#### 10.2 Transaction Validation & Execution
- **File**: `Evm64/Transaction.lean` (new)
- **Approach**:
  1. Validate transaction (nonce, gas limit, balance)
  2. Deduct upfront cost
  3. Execute message call
  4. Refund remaining gas
  5. Pay priority fee to coinbase
- **Reference**: `execution-specs/.../fork.py:process_transaction`

### Phase 11: Block-Level STF

#### 11.1 Block State Transition
- **File**: `Evm64/StateTransition.lean` (new)
- **Approach**: The top-level STF function:
  1. Read block (header + transactions) from `read_input`
  2. Validate block header
  3. Process each transaction sequentially, updating world state
  4. Apply block rewards
  5. Compute post-state root
  6. Write post-state root via `write_output`
- **Reference**: `execution-specs/.../fork.py:state_transition`
- **Spec**: `state_transition_spec` proves that the RISC-V program computes
  the same post-state as the Python reference spec.

#### 11.2 World State Model
- Account state: nonce, balance, storage root, code hash
- State trie: delegated to host via ECALL (trie operations are zkVM-accelerated
  or proven separately)
- MPT proof verification: either inline or via host

#### 11.3 IO Integration
- `read_input`: Reads block data + pre-state witness (per zkvm IO standard)
- `write_output`: Writes post-state root (32 bytes) as public output
- The zkVM proves: "given this block and pre-state, the post-state root is X"

#### 11.4 Conformance Testing
- Run against Ethereum test vectors (ethereum/tests).
- Compare RISC-V execution results to reference Python execution.
- Use `native_decide` or extraction for executable tests.

---

## Priority Order

**Immediate (recreate deleted specs) — ✅ ALL DONE:**
1. ~~Recreate `StackOps.lean`~~ — ✅ Done (Pop.lean, Push0.lean, Dup.lean, Swap.lean)
2. ~~Recreate `ShiftSpec.lean`~~ — ✅ Done (SHR per-limb + phase + body specs, 961 lines, 0 sorry)
3. ~~Recreate `ShlSpec.lean`, `SarSpec.lean`~~ — ✅ Done (SHL/SAR full hierarchy: per-limb + compose + semantic)
4. ~~Recreate `ByteSpec.lean`~~ — ✅ Done (Byte/Spec.lean + Byte/LimbSpec.lean, stack-level spec)

**Short-term (enables simple contracts):**
5. Phase 4.2: DIV, MOD — near complete (full path compositions proved for all n-cases × shift variants × DIV/MOD, stack-level b=0 and b≠0 specs with evmWordIs; remaining: semantic correctness bridge + combined stack spec)
6. Phase 5: MLOAD, MSTORE, EVM memory model
7. Phase 5.1: EVM code region (needed for PUSHn and interpreter)

**Execution layer (RLP decoder — STF prerequisite):**
- ~~EL.1: RLP specification~~ — ✅ Done
- ~~EL.2: Byte-level infrastructure~~ — ✅ Done
- EL.3: RLP RISC-V decoder phases 1-6

**Medium-term (interpreter loop — STF core):**
8. Phase 7.1-7.2: EVM machine state + opcode dispatch
9. Phase 7.3: Opcode handler wrappers (gas + dispatch)
10. Phase 7.4: Interpreter main loop with simulation relation proof
11. Phase 6: Environment opcodes (CALLER, CALLVALUE, etc.)

**Towards STF (full EVM execution):**
12. Phase 8.1-8.3: SLOAD/SSTORE, KECCAK256 (via syscalls/accelerators)
13. Phase 8.4-8.5: LOG, CALL/CREATE, RETURN/REVERT
14. Phase 9: Gas metering (static then dynamic)
15. Phase 10: Transaction processing (message call + validation)
16. Phase 11: Block-level STF + IO integration + conformance testing

---

## Design Decisions

1. **RV64IM target**: Per zkvm-standards, `riscv64im_zicclsm` is
   the standardized target for Ethereum zkVMs. 64-bit words mean 4 limbs
   per 256-bit word.

2. **Stack-in-memory**: EVM stack elements are 256-bit words stored in
   RISC-V memory (4 consecutive 64-bit words in RV64). SP register (x12)
   points to top of stack. Stack grows upward, 32 bytes per element.

3. **Syscall bridge (ECALL)**: Complex operations (KECCAK, SLOAD/SSTORE, CALL,
   precompiles) use ECALL to delegate to the zkVM host. This aligns with the
   `zkvm_accelerators.h` C interface standard. The host provides:
   - Cryptographic accelerators (keccak, EC ops, pairings)
   - Storage read/write
   - State trie operations

4. **Per-limb modularity**: Each 256-bit operation decomposes into 4 per-limb
   operations (RV64) with individual specs, then composed via `runBlock`.

5. **Simulation relation for STF**: The interpreter loop proof uses a
   simulation relation between abstract EVM state and concrete RISC-V state.
   Each opcode handler preserves the simulation; the loop proof is inductive.

6. **Reference spec**: All opcodes must match the semantics in
   `execution-specs/src/ethereum/forks/shanghai/vm/`.

7. **Proof automation**: `xperm`/`xsimp` for assertion permutation,
   `runBlock` for multi-limb composition, `validMem`/`liftSpec`/`pcFree`
   for boilerplate elimination. Recent refactorings (let-code, runBlock)
   have eliminated thousands of lines of manual proof.

8. **IO standard**: The STF program uses `read_input`/`write_output` per
   the zkvm IO standard. Input = block + pre-state witness. Output =
   post-state root hash.
