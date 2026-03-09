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

**Primary target: RV64IM (64-bit)**. The 64-bit version is the priority, per
the zkvm-standards spec (`EvmAsm/Evm64/zkvm-standards/`). RV32IM is maintained
as a secondary target.

Reference spec: `execution-specs/src/ethereum/forks/shanghai/vm/` (Python).
zkVM standards: `EvmAsm/Evm64/zkvm-standards/` (submodule).

---

## Architecture Overview

### Two RISC-V Backends

| | RV64IM (Evm64) — **PRIMARY** | RV32IM (Evm32) — secondary |
|---|---|---|
| **Target** | `riscv64im_zicclsm-unknown-none-elf` | `riscv32im-unknown-none-elf` |
| **Word size** | 64-bit (`BitVec 64`) | 32-bit (`BitVec 32`) |
| **Limbs per EvmWord** | 4 × 64-bit (LE) | 8 × 32-bit (LE) |
| **Memory ops** | LD/SD (8-byte aligned) | LW/SW (4-byte aligned) |
| **ADD instructions** | 30 | 62 |
| **LT instructions** | 26 | 54 |
| **SHR instructions** | 90 | 288+ |
| **Efficiency** | ~2× fewer instructions | More limb processing |
| **Files** | `EvmAsm/Evm64/` (24 files) | `EvmAsm/Evm32/` (15 files) |
| **Infrastructure** | `EvmAsm/Rv64/` | `EvmAsm/Rv32/` |

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
- **Per-limb composition**: Each 256-bit op decomposes into 4 per-limb specs
  (Evm64) or 8 (Evm32), then composed via `runBlock` tactic
- **Key tactics**: `xperm`, `xsimp`, `xcancel`, `seqFrame`, `runBlock`,
  `validMem`, `liftSpec`, `pcFree`

---

## Current Status

### Evm64 (PRIMARY) — 52 opcodes, all proofs complete (0 sorry)

| Category | Opcodes | Instructions (per op) | Status |
|----------|---------|----------------------|--------|
| Arithmetic | ADD, SUB, MUL, SIGNEXTEND | 30 / 30 / 63 / 48 | ✅ Fully proved |
| Bitwise | AND, OR, XOR, NOT, BYTE | 17 / 17 / 17 / 12 / 45 | ✅ Fully proved |
| Shift | SHR, SHL, SAR | 90 / 90 / 95 | ✅ Fully proved |
| Comparison | ISZERO, LT, GT, EQ, SLT, SGT | 12 / 26 / 26 / 21 / 25 / 25 | ✅ Fully proved |
| Stack | POP, PUSH0, DUP1, SWAP1 | 1 / 5 / 9 / 16 | ✅ Fully proved |
| Stack (generic) | DUP1-16, SWAP1-16 | 9 / 16 each | ✅ Fully proved |

### Evm32 (secondary) — 15 opcodes, 1 sorry

| Category | Opcodes | Status |
|----------|---------|--------|
| Arithmetic | ADD, SUB | ✅ Fully proved |
| Bitwise | AND, OR, XOR, NOT | ✅ Fully proved |
| Shift | SHR | ⚠️ 1 sorry in ShiftComposition.lean (8-way case merge) |
| Comparison | ISZERO, LT, GT, EQ | ✅ Fully proved |
| Stack | POP, PUSH0, DUP1-16, SWAP1-16 | ✅ Fully proved |

### Infrastructure — complete, no sorry

- RV32 and RV64: Basic, Instructions, Program, Execution, CPSSpec,
  ControlFlow, SepLogic, GenericSpecs, InstructionSpecs, SyscallSpecs
- Tactics: XPerm, XSimp, XCancel, SeqFrame, RunBlock, LiftSpec, ValidMem,
  PcFree, SpecDb
- Examples: Swap, HelloWorld, Echo, Multiply, LoadModifyStore, Combining,
  Halting, Commit, Write, FullPipeline

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

#### ~~2.1 SHL (Shift Left)~~ ✅
- **Files**: `Evm64/Shift.lean` (program + 11 tests) + `Evm64/ShlSpec.lean` (per-limb + body specs)
- **Approach**: Mirror of SHR. Reuses SHR phases A/B/C/zero_path. 4 SHL bodies
  process top-down (SLL+SRL swapped vs SHR). Per-limb helpers: `shl_merge_limb_spec`,
  `shl_first_limb_spec`, in-place variants. Body specs: `shl_body_{0,1,2,3}_spec`.
- 90 instructions = 360 bytes. All specs proved, 0 sorry.

#### ~~2.2 SAR (Shift Right Arithmetic)~~ ✅
- **Files**: `Evm64/Shift.lean` (program + 12 tests) + `Evm64/SarSpec.lean` (per-limb + body + sign-fill specs)
- **Approach**: Like SHR but uses SRA for MSB limb and fills vacated limbs with
  sign extension (SRAI result, 63). Reuses SHR phase B and merge limb specs.
  Custom phase A/C (different offsets), sign-fill path (7 instrs) instead of zero_path.
- 95 instructions = 380 bytes. All specs proved, 0 sorry.

#### ~~2.3 BYTE (Extract byte from word)~~ ✅
- **Files**: `Evm64/Byte.lean` (program + 12 tests) + `Evm64/ByteSpec.lean` (per-body + store + phase B specs)
- **Approach**: If index >= 32, result = 0. Else compute which limb (index/8)
  and byte offset (56 - (index%8)*8), cascade dispatch to load correct limb,
  SRL + ANDI 0xFF. Shared store path writes result + 3 zero limbs.
- 45 instructions = 180 bytes. All specs proved, 0 sorry.
- Added `andi_spec_gen_same` and `slli_spec_gen_same` to SyscallSpecs.lean.

### Phase 3: Stack Extensions

#### ~~3.1 DUP1-16 and SWAP1-16 (Generic)~~ ✅
- **File**: `Evm64/StackOps.lean`
- **Approach**: `evm_dup (n : Nat)` and `evm_swap (n : Nat)` as generic
  Lean functions producing `Program`. 9 instructions for DUP, 16 for SWAP.
  Full spec hierarchy: low-level (explicit limbs) → evmWordIs → evmStackIs.
  Added `signExtend12_ofNat_small` and `evmStackIs_split_at` for Evm64.
- Covers 32 opcodes with one proof each. All proved, 0 sorry.

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

#### 4.2 DIV and MOD
- **File**: `Evm64/DivMod.lean` (new)
- **Approach**: 256-bit unsigned division. Shift-and-subtract or Knuth
  Algorithm D. Division by zero returns 0 (EVM convention, no trap).
  Implement DIV+MOD together since division produces both.

#### 4.3 SDIV and SMOD (Signed)
- **Approach**: Check signs, compute unsigned div/mod, apply sign correction.

#### 4.4 ADDMOD and MULMOD
- **Approach**: ADDMOD needs 257-bit intermediate (carry). MULMOD needs
  512-bit intermediate. Both reuse DIV/MOD.

#### 4.5 EXP (Exponentiation)
- **Approach**: Square-and-multiply using MUL. Loop over exponent bits.

#### ~~4.6 SIGNEXTEND~~ ✅
- **Files**: `Evm64/SignExtend.lean` (program + 16 tests) + `Evm64/SignExtendSpec.lean` (per-body + phase B specs)
- **Approach**: If b >= 31, result = x. Else compute limb_idx = b/8, shift_amount = 56 - (b%8)*8.
  Cascade dispatch to body_N: SLL+SRA sign-extends target limb in-place, SRAI fills higher limbs.
  Shares Phase B computation with BYTE opcode.
- 48 instructions = 192 bytes. All specs proved, 0 sorry.

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
- **Approach**: Each handler is a thin wrapper:
  1. Deduct gas cost
  2. Call the opcode subroutine (e.g., `evm_add`)
  3. Advance EVM PC by appropriate amount (1 for most, 1+n for PUSHn)
  4. Return to dispatch loop
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

**Immediate (complete basic opcode set):**
1. ~~Phase 1: GT, EQ (basic comparisons)~~ — **done**
2. ~~Phase 2: POP, PUSH0, DUP1, SWAP1~~ — **done**
3. ~~SHR~~ — **done** (Evm64 fully proved)
4. ~~Phase 1: SLT, SGT (signed comparisons)~~ — **done**
5. ~~Phase 2: SHL, SAR, BYTE (remaining shifts & bitwise)~~ — **done**
6. ~~Phase 3: DUPn/SWAPn generic~~ — **done**
7. ~~Phase 4.1: MUL~~ — **done**

**Short-term (enables simple contracts):**
8. Phase 4.2: DIV, MOD ← **next**
9. Phase 5: MLOAD, MSTORE, EVM memory model
10. Phase 5.1: EVM code region (needed for PUSHn and interpreter)

**Medium-term (interpreter loop — STF core):**
11. Phase 7.1-7.2: EVM machine state + opcode dispatch
12. Phase 7.3: Opcode handler wrappers (gas + dispatch)
13. Phase 7.4: Interpreter main loop with simulation relation proof
14. Phase 6: Environment opcodes (CALLER, CALLVALUE, etc.)

**Towards STF (full EVM execution):**
15. Phase 8.1-8.3: SLOAD/SSTORE, KECCAK256 (via syscalls/accelerators)
16. Phase 8.4-8.5: LOG, CALL/CREATE, RETURN/REVERT
17. Phase 9: Gas metering (static then dynamic)
18. Phase 10: Transaction processing (message call + validation)
19. Phase 11: Block-level STF + IO integration + conformance testing

---

## Design Decisions

1. **RV64IM is primary target**: Per zkvm-standards, `riscv64im_zicclsm` is
   the standardized target for Ethereum zkVMs. 64-bit words halve the limb
   count (4 vs 8), roughly halving instruction counts for 256-bit arithmetic.

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
