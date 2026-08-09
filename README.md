# evm.asm: A Verified Macro Assembler for building zkEVM in Lean 4 (early experiment)

A prototype implementation of a verified macro assembler targeting the zkEVM,
built on a RISC-V RV64IM backend, inspired by:

> Andrew Kennedy, Nick Benton, Jonas B. Jensen, Pierre-Evariste Dagand.
> **"Coq: The world's best macro assembler?"**
> *Proceedings of the 15th International Symposium on Principles and Practice
> of Declarative Programming (PPDP 2013)*, September 2013, ACM.
> https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/

## Warning: Experimental Prototype Only

**DO NOT USE THIS PROJECT FOR ANYTHING OF VALUE.**

This is an experimental research prototype with significant limitations:

- **No RISC-V spec compliance**: The instruction semantics are vibe-generated and
  have NOT been validated against the official RISC-V specification. There may
  be subtle (or not-so-subtle) deviations from actual RISC-V behavior.
- **No EVM spec compliance**: The specs for examples are also vibe-generated and
  have NOT been validated against the EVM specification.
- **No conformance testing**: No systematic testing has been performed to verify
  that this implementation matches real RISC-V processors or simulators. No testing has been performed against EVM either.
- **Prototype quality**: This code is for educational and research purposes to
  explore verified macro assembly techniques, not for production use.

## Motivation: Eliminating Compiler Trust in zkEVM

The usual way to use zkVMs is to compile high-level programs to RISC-V
assembly, then prove correctness of the execution trace using a zero-knowledge
proof system. The proof covers the *execution trace*, but it cannot cover the
*compiler*. If the compiler is buggy or malicious, the proof might not
match the developer's (or the receiver's) intent, even though the ZK proof is valid, and even if the
source code is correct.

**evm.asm** explores an alternative: write programs directly as RISC-V code,
and *prove* their correctness in Lean 4 before the ZK proof is ever
generated. The goal is that a developer (or a receiver of a ZK proof) never has to trust a compiler
for the guest program.

More specifically, evm.asm aims at building the guest part of the **zkEVM**. Reducing trusted computing base matters for this usage.

### Role in the L1-zkEVM stack

The target shape is a **stateless block validator** ELF that an L1 zkVM
prover can consume — the same slot occupied today by the Rust-compiled
`stateless-validator-{reth,ethrex}` binaries in
[`eth-act/ere-guests`](https://github.com/eth-act/ere-guests). evm.asm
targets the same wire (input: `(block, execution_witness)` per the
[`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)
IO interface; output: post-state root) but is built bottom-up from a
verified RV64 core instead of from a high-level EL client, so the
artifact carries a Lean-kernel-checked Hoare triple from RLP-bytes-in to
state-root-out — no compiler in the TCB. Benchmarks for such guests live
in
[`eth-act/zkevm-benchmark-workload`](https://github.com/eth-act/zkevm-benchmark-workload)
and [the L1 zkEVM benchmarking blog](https://zkevm.ethereum.foundation/blog/benchmarking-zkvms).

Integration with execution-layer clients is future work; see
[`PROGRESS.md`](PROGRESS.md) for the 9-item guest-program checklist and
the multidimensional status dashboard.

A second motivation is that our Hoare triples are *bounded* in steps
(`cpsTripleWithin N base ...`): every spec carries an explicit upper bound `N`
on the number of RISC-V steps the program executes. Two consequences:

1. **zkVM cycle limits.** `N` is a worst-case cycle budget, summable across
   composed macros, that fits a guest program inside a zkVM's per-proof cap
   without running it.
2. **Gas costs.** `N` is a verified per-opcode instruction count, the main
   input to a sound gas-pricing model.

## Key Idea

Lean 4 serves simultaneously as:

1. **An assembler**: Instructions are an inductive type; programs are lists of
   instructions with sequential composition (`;;`).
2. **A macro language**: Lean functions that produce programs act as macros,
   using all of Lean's facilities (recursion, pattern matching, conditionals).
3. **A specification language**: Hoare triples with separation logic assertions
   express correctness properties of EVM opcodes and macro compositions.
4. **A proof assistant**: Lean's kernel verifies that macros meet their
   specifications, with no external oracle required.

## Example: What a Verified EVM Opcode Looks Like

Each EVM opcode is implemented as a sequence of RISC-V instructions operating on
4×64-bit limbs. A **stack-level spec** ties the low-level implementation back to
the 256-bit EVM semantics using `evmWordIs` — an assertion that four consecutive
memory words encode a single `EvmWord` (a `BitVec 256`):

```lean
-- An EvmWord is stored as 4 limbs of 64 bits at consecutive addresses
def evmWordIs (addr : Addr) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimb 0) ** ((addr + 8) ↦ₘ v.getLimb 1) **
  ((addr + 16) ↦ₘ v.getLimb 2) ** ((addr + 24) ↦ₘ v.getLimb 3)
```

Here is the stack-level spec for the 256-bit AND opcode
(`EvmAsm/Evm64/And/Spec.lean`). It says: starting from two `EvmWord`s `a` and
`b` on the stack, the 17-instruction RISC-V program `evm_and_code` produces
`a &&& b` — with a machine-checked proof:

```lean
/-- Stack-level 256-bit EVM AND: operates on two EvmWords via evmWordIs. -/
theorem evm_and_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_and_code base
    cpsTripleWithin 17 base (base + 68) code
      (-- precondition: stack pointer, scratch registers, two 256-bit words
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- postcondition: sp advanced, result is a &&& b
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 3 &&& b.getLimb 3)) **
       (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b))
```

The statement is a bounded Hoare triple (`cpsTripleWithin`) with separation logic assertions.
The precondition describes the machine state before: register `x12` holds the
stack pointer, and two 256-bit words `a`, `b` sit at `sp` and `sp+32`. The
postcondition says that within 17 RISC-V steps, after running 68 bytes of code, the word at
`sp+32` now holds `a &&& b` — the bitwise AND defined by Lean's `BitVec 256`.

The proof composes four per-limb specs (one AND per 64-bit limb) using the
`runBlock` tactic, then lifts to the `evmWordIs` abstraction via
`cpsTripleWithin_weaken`:

```lean
  -- 1. Compose 4 per-limb ANDs + stack pointer adjustment (limb-level proof)
  have L0 := and_limb_spec 0 32 sp a0 b0 v7 v6 base ...
  have L1 := and_limb_spec 8 40 sp a1 b1 ...
  have L2 := and_limb_spec 16 48 sp a2 b2 ...
  have L3 := and_limb_spec 24 56 sp a3 b3 ...
  have LADDI := addi_spec_gen_same_within .x12 sp 32 ...
  runBlock L0 L1 L2 L3 LADDI

  -- 2. Lift to evmWordIs using EvmWord.getLimb_and semantic lemma
  exact cpsTripleWithin_weaken ...
    (fun h hp => by simp only [evmWordIs] at hp; ... ; xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_and]; ... ; xperm_hyp hq)
    h_main
```

Lean's kernel checks every step — from individual instruction semantics to the
final `a &&& b` result. No external solver or SMT oracle required.

## Project Structure

```
EvmAsm/
  Rv64/                       -- RV64IM backend
    Basic.lean                --   Machine state: registers (64-bit), memory, PC
    Instructions.lean         --   RV64IM instruction set and semantics
    Program.lean              --   Programs as instruction lists, sequential composition
    Execution.lean            --   Branch-aware execution, code memory, step/stepN
    SepLogic.lean             --   Separation logic assertions and combinators
    CPSSpec.lean              --   CPS-style Hoare triples, branch specs, structural rules
    ControlFlow.lean          --   if_eq macro, symbolic proofs, pcIndep
    GenericSpecs.lean         --   Generic specs parameterized over instructions
    InstructionSpecs.lean     --   Per-instruction CPS specs
    SyscallSpecs.lean         --   Syscall specs: HALT, WRITE, read_input
    Tactics/
      PerfTrace.lean          --   Performance tracing infrastructure
      XPerm.lean              --   xperm tactic: AC-permutation of sepConj chains
      XSimp.lean              --   xperm_hyp/xsimp tactics: assertion implication
      XCancel.lean            --   xcancel tactic: cancellation with frame extraction
      SeqFrame.lean           --   seqFrame tactic: auto frame+compose bounded CPS specs
      LiftSpec.lean           --   liftSpec tactic: lift instruction specs
      RunBlock.lean           --   runBlock tactic: block execution automation
      SpecDb.lean             --   @[spec_gen] attribute and spec database
  Evm64/                      -- EVM opcodes on RV64IM (4x64-bit limbs)
    Basic.lean                --   EvmWord (BitVec 256), getLimb64, fromLimbs64
    Stack.lean                --   evmWordIs, evmStackIs, pcFree lemmas
    EvmWordArith.lean         --   Math correctness lemmas (carry chains, etc.)
    Compare/
      LimbSpec.lean           --   Shared comparison per-limb specs (lt, beq, slt_msb)
    Add/                      --   256-bit ADD
      Program.lean            --     RV64 program definition
      LimbSpec.lean           --     Per-limb specs (add_limb0, add_limb_carry)
      Spec.lean               --     Full composition + stack-level spec
    Sub/                      --   256-bit SUB (same layout as Add/)
    And/                      --   256-bit AND (Program + LimbSpec + Spec)
    Or/                       --   256-bit OR
    Xor/                      --   256-bit XOR
    Not/                      --   256-bit NOT
    Lt/                       --   256-bit LT (Program + Spec, uses Compare/LimbSpec)
    Gt/                       --   256-bit GT
    Eq/                       --   256-bit EQ (Program + LimbSpec + Spec)
    IsZero/                   --   256-bit ISZERO (Program + LimbSpec + Spec)
    Slt/                      --   256-bit SLT signed (Program + Spec, uses Compare/LimbSpec)
    Sgt/                      --   256-bit SGT signed
    Pop/                      --   POP (Program + Spec)
    Push0/                    --   PUSH0 (Program + Spec)
    Dup/                      --   DUP1-16 (Program + Spec)
    Swap/                     --   SWAP1-16 (Program + Spec)
    Multiply/                 --   MUL (Program + LimbSpec, schoolbook 4x4 limb)
    DivMod/                   --   DIV/MOD (Program + LimbSpec + Compose, Knuth Algorithm D)
    SignExtend/               --   SIGNEXTEND (Program + LimbSpec + Compose + Spec)
    Shift/                    --   SHR/SHL/SAR (Program + LimbSpec + ShlSpec + SarSpec + Compose + ShlCompose + SarCompose + Semantic + ShlSemantic + SarSemantic)
    Byte/                     --   BYTE (Program + LimbSpec + Spec)
    zkvm-standards/           --   Submodule: zkVM RISC-V target standards
  Codegen/                    -- RV64 assembly emitter + program registry
    Programs.lean             --   Registry hub for `BuildUnit` probes
    Programs/                 --   Submodules: Evm.lean, HashBridge.lean,
                              --     Ssz.lean, RlpRead.lean, Mpt.lean —
                              --     RV64 macro-asm helpers implementing
                              --     pieces of run_stateless_guest
                              --     (UNPROVED scaffolding; see below)
EvmAsm.lean                  -- Top-level module hub
EvmAsm/Rv64.lean             -- Rv64 module hub
EvmAsm/Evm64.lean            -- Evm64 module hub
execution-specs/              -- Submodule: Ethereum execution specs
```

## Codegen & Execution

Verified `Program`s can be emitted as RV64 assembly, assembled, linked,
and run on the [Zisk](https://0xpolygonhermez.github.io/zisk/) emulator
(`ziskemu`). See [CODEGEN.md](CODEGEN.md) for the roadmap and status.
**M0–M10 are complete**: text emitter, total `Instr` coverage with
build-time `#guard` round-trip tests, `evm_add` 256-bit round-trip on
`ziskemu` from both a baked-in `.data` section and from prover input
via `ziskemu -i`, tiny EVM interpreter with runtime fetch/decode/
dispatch (M5a/M5b), 91 wired opcodes through `tinyInterpRegistry`
(PUSH0–32, DUP1–16, SWAP1–16, 17 fixed-shape singletons, MLOAD/MSTORE/
MSTORE8, DIV/MOD, SDIV/SMOD via trampoline, ADDMOD via inline-callable),
and a runtime-bytecode dispatcher (M8.5) that shaves the regression
suite from ~60 s to ~20 s. Codegen-proofs **Phase 1 (registry
invariants)** and the first 13/91 instances of **Phase 4 (handler-level
`cpsTripleWithin` specs)** have landed under `EvmAsm/Codegen/Proofs/`.

Quick start:

```bash
# Emit and run a verified evm_add on ziskemu:
lake exe codegen --program evm_add --halt linux93 -o gen-out/evm_add
ziskemu -e gen-out/evm_add.elf -o gen-out/evm_add.output

# End-to-end regression scripts:
scripts/codegen-smoke.sh                            # M0 toolchain validation
scripts/codegen-evm_add-check.sh                    # M2 verified ADD
scripts/codegen-evm_add-from-input-check.sh         # M4 ADD from ziskemu -i
scripts/codegen-opcodes-runtime-check.sh            # M8.5 31-case opcode regression
```

The EEST stateless-guest conformance harness is documented in
[docs/eest-stateless-testing.md](docs/eest-stateless-testing.md), including
large-batch, filtered, parallel, offset-resume, failure-capped, and quiet-output
runs.

Setup requirements: `riscv64-elf-binutils` (or `riscv-gnu-toolchain`)
and `ziskemu`. The Zisk emulator can be installed with
`bash <(curl -fsSL https://raw.githubusercontent.com/0xPolygonHermez/zisk/main/ziskup/install.sh)`
followed by `~/.zisk/bin/ziskup --nokey -y` to skip the proving-key
download (we only need the emulator). Codegen also has an `--asm-only`
mode for CI hosts without the cross toolchain.

### Wanted: an external Lean specification of the stateless guest

evm-asm currently uses an **internal, untrusted** Lean specification of the
stateless guest, under
[`EvmAsm/Stateless/SpecRef/`](EvmAsm/Stateless/SpecRef). Because it is our own
port, using it to justify spec alignment is circular — it can drift from
upstream, and a defect in the port would be invisible to any proof that cites
it.

**We are looking for an external Lean specification of the stateless guest.**
It should:

1. Specify the **Amsterdam** stateless guest, tracking the
   [`zkevm-tests` branch of `execution-specs`](https://github.com/ethereum/execution-specs/tree/zkevm-tests)
   and updated regularly as that branch moves.
2. For any input, specify a **set of allowed outputs** that a stateless guest
   may produce — not a single output, since the guest is permitted latitude the
   spec does not fix.
3. For every test case in
   [EEST](https://github.com/ethereum/execution-spec-tests), make that allowed
   set a **singleton**, coinciding with the output EEST expects.
4. For **any** byte string as input, make the allowed set contain the output of
   `run_stateless_guest` as implemented in
   [`execution-specs`](https://github.com/ethereum/execution-specs).

Conditions 3 and 4 pull in opposite directions on purpose: 3 pins the spec to
observed consensus behaviour where tests exist, while 4 keeps it honest on the
inputs no test covers — which is where a stateless guest is most likely to be
wrong.

If you are interested in producing such a specification, please open an issue.

### Stateless-guest scaffold (currently **unproved**)

`EvmAsm/Codegen/Programs.lean` (and the submodules under
`EvmAsm/Codegen/Programs/`) host a growing set of RV64IM macro-assembly
helpers that implement pieces of the Ethereum `run_stateless_guest`
entry point — RLP primitives (`rlp_list_nth_item`,
`rlp_encode_bytes`, `rlp_encode_list_prefix`, …), transaction
field accessors (legacy / EIP-1559 / EIP-2930 / EIP-4844 / EIP-7702
decoders, intrinsic-gas helpers, signature extraction, …), account
and MPT primitives (`account_decode`, `account_at_address`,
`account_extract_*`, `mpt_walk`, `mpt_branch_*`, `mpt_compact_*`,
`mpt_two_leaf_root_indexed`, `mpt_one_leaf_root_indexed`, …),
block-body helpers
(`block_body_decode`, `block_count_transactions`,
`block_validate_transactions_root_two_tx`,
`block_validate_transactions_root_one_tx`,
`block_validate_withdrawals_root_one_w`,
`block_validate_withdrawals_root_two_w`,
`block_validate_receipts_root_one_receipt`,
`block_validate_receipts_root_two_receipts`,
`block_hash_from_header`, `validate_parent_hash_link`,
`validate_header_pair`, `validate_header_chain`,
`block_validate_2tx_full`, `block_validate_1tx_full`,
`block_validate_1tx_full_with_body`,
`block_body_extract_2tx`, `block_body_extract_1tx`,
`block_body_extract_tx_count`,
`block_body_extract_withdrawal_count`,
`block_body_summary`,
`block_body_validate_empty`,
`chain_body_total_tx_count`,
`chain_body_total_withdrawal_count`,
`block_validate_2tx_full_with_body`,
`block_validate_empty_ommers_hash`,
`block_validate_no_withdrawals_pair`,
`block_validate_empty_receipts_root`,
`block_validate_empty_block`,
`validate_empty_block_with_parent`,
`validate_empty_block_chain`,
`block_hash_array_from_chain`,
`validate_block_hash_chain_match`,
`chain_compute_total_gas_used`,
`chain_extract_number_range`,
`header_extract_basefee`,
`chain_extract_basefee_range`,
`chain_block_hashes_commitment`,
`header_extract_state_root`,
`header_extract_parent_hash`,
`header_extract_receipts_root`,
`header_extract_transactions_root`,
`header_extract_withdrawals_root`,
`header_extract_ommers_hash`,
`header_extract_prev_randao`,
`header_extract_beneficiary`,
`block_hash_matches`,
`header_extract_gas_used`,
`header_extract_gas_limit`,
`block_validate_block_hash_pair`,
`block_hash_and_extract_number`,
`header_compute_summary_struct`,
`header_extract_difficulty`,
`header_extract_extra_data`,
`header_extract_nonce`,
`header_validate_nonce_zero`,
`header_validate_difficulty_zero`,
`validate_header_post_merge_zeros`,
`chain_validate_post_merge_zeros`,
`chain_validate_full`,
`chain_validate_increasing_timestamps`,
`chain_validate_consecutive_numbers`,
`chain_extract_basefee_range`,
`chain_validate_basefee_non_decreasing`,
`chain_validate_basefee_non_increasing`,
`chain_validate_gas_limit_constant`,
`chain_validate_gas_limit_non_decreasing`,
`chain_validate_gas_limit_non_increasing`,
`chain_extract_gas_limit_first_last`,
`chain_compute_total_gas_limit`,
`chain_extract_excess_blob_gas_first_last`,
`chain_compute_max_excess_blob_gas`,
`chain_compute_min_excess_blob_gas`,
`chain_compute_max_blob_count`,
`chain_compute_min_blob_count`,
`chain_extract_first_last_parent_beacon_block_root`,
`chain_extract_first_last_requests_hash`,
`header_extract_requests_hash`,
withdrawal RLP/hash, …), and address
derivation (`address_compute_create`, `address_compute_create2`,
`address_from_pubkey`). The catalogue is tracked under the
`PR-K*` series in [`PLAN.md`](PLAN.md).

**These programs carry no Lean Hoare-triple / CPS-spec proofs
yet.** The "0 `sorry`, 0 `axiom`" invariant in the Status section
below applies to the verified RV64 core, the per-opcode handlers
under `EvmAsm/Evm64/<Op>/`, and the tactic / separation-logic
infrastructure. The stateless-guest helpers are scaffolding: they
ship as `def *Function : String` raw-asm bodies emitted by
`lake exe codegen`, registered through `BuildUnit` probes, and
exercised end-to-end on ziskemu against the
[`execution-specs`](https://github.com/ethereum/execution-specs/) Python reference via the
`scripts/codegen-zisk-*-check.sh` fixtures (one script per PR).
What that gives us today:

- Each helper is built and executed on ziskemu against a Python
  reference fixture; CI re-runs the same fixtures on every PR.
- Function signatures, memory layouts, and side-effect contracts
  are documented in the doc-comment above each `*Function` def
  (`Calling convention`, `Composes`, `Status`) and serve as the
  prose precondition for the future CPS triple.
- Each `Spec.lean` slot in the eventual proof tree is reserved by
  a one-line stub placeholder so the import graph is stable from
  day one.

What it does **not** give us — and the gap to close before any of
these helpers is on the same footing as the opcode handlers:

- No `cpsTripleWithin N` Hoare triple — neither a step-bound `N`
  nor a verified pre/postcondition.
- No machine-checked link between the doc-comment contract and
  the assembled bytes; only the test fixtures pin behaviour.
- The RLP, MPT, signature, and address-derivation helpers
  currently have **no `@[spec_gen_rv64]` placeholders** wired in,
  so they aren't visible to the existing automation.

In short: today they are tested code with prose specs, not
proved code. Future PRs will add per-helper `Spec.lean` triples
and progressively reduce the unproved surface.

## Building

```bash
# Install elan (Lean version manager) if not already installed
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# download Mathlib cache (optional, recommended)
lake exec cache get

# Build the project
lake build
```

### Dependencies

Top-level Lake dependencies (declared in [`lakefile.toml`](lakefile.toml)):

- **[Mathlib4](https://github.com/leanprover-community/mathlib4)** — Lean 4
  mathematics library. Used pervasively for `BitVec`, `Nat` arithmetic, `Fin`,
  decidability instances, and tactic infrastructure.
- **Vendored Sail RISC-V model** (`vendor/sail-riscv-zkvm-lean/`) — a checked-in,
  release-pinned, *scoped* Lean export of the official
  [Sail RISC-V model](https://github.com/riscv/sail-riscv), covering exactly the
  RV64IM subset (`SAIL_MODULES = main I_insts M_insts`). Pulls in
  [`lean-sail`](https://github.com/sail-lean/lean-sail) (Sail's Lean monad
  runtime) via a git-pinned `require` in the vendored package's lakefile.

  Why vendored + scoped? The model is the project's trust anchor, so it is owned
  and reproducible rather than fetched from a moving fork: every input — the
  sail-riscv release tag, Sail compiler version, lean-sail rev, module scope,
  config, and a content `model_sha256` — is recorded in
  [`sail-import/PROVENANCE.toml`](sail-import/PROVENANCE.toml) and regenerable via
  [`scripts/regen-sail-model.sh`](scripts/regen-sail-model.sh). (This replaced an
  earlier dependency on the moving `dhsorens/sail-riscv-lean` fork.)

The vendored Sail model is the **trust anchor** for our RISC-V semantics:
hand-written specs in [`EvmAsm/Rv64/Instructions.lean`](EvmAsm/Rv64/Instructions.lean)
are tied to the Sail-generated decoder/executor via abstraction-relation
proofs in [`EvmAsm/Rv64/SailEquiv/`](EvmAsm/Rv64/SailEquiv/) (`StateRel.lean`
plus per-instruction-class `*Proofs.lean`). This is how we discharge the
"is your hand-written instruction semantics actually RISC-V?" obligation
against the official Sail model.

Tracking issues: [#84](https://github.com/Verified-zkEVM/evm-asm/issues/84)
(import sail-riscv-lean as Lake dep — landed),
[#93](https://github.com/Verified-zkEVM/evm-asm/issues/93) (map hand-written
`Instr` to SAIL-generated AST).

### Weekly build benchmark

A scheduled GitHub Actions workflow,
[`.github/workflows/benchmark.yml`](.github/workflows/benchmark.yml),
runs `lake build` every Monday at 06:00 UTC and records the wall-clock
time and peak resident set size in the run's job summary. Raw
`/usr/bin/time -v` outputs are uploaded as build artifacts
(`benchmark-<run-id>`) with a 90-day retention so regressions can be
diff'd against earlier runs.

The workflow is independent of PR CI and does not gate any pull
request. To trigger an off-schedule run manually, go to **Actions →
Benchmark → Run workflow** (or `gh workflow run benchmark.yml`).
Long-lived history (`benchmark-history` orphan branch) and
regression-hunting workflow are documented for contributors in
[`AGENTS.md`](AGENTS.md) and
[`docs/benchmark-workflow-design.md`](docs/benchmark-workflow-design.md).

The shape of this workflow was informed by a survey of
[`Beneficial-AI-Foundation/curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify)'s
benchmark CI, which was useful for figuring out what a Lean-project
build benchmark looks like in practice. Design rationale lives in
[`docs/benchmark-workflow-design.md`](docs/benchmark-workflow-design.md).

## Status

This is a **prototype** demonstrating the approach. The headline figures —
opcode coverage, per-opcode cycle bounds, codegen reach, and conformance
against [`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)
and the execution-specs reference — live in a single multidimensional
dashboard at **[`PROGRESS.md`](PROGRESS.md)**, regenerated from a
kernel-checked registry (`EvmAsm/Progress.lean`) by
[`scripts/progress-report.sh`](scripts/progress-report.sh) and gated in CI.

Top-line invariants:

- **0 `sorry`, 0 `axiom`** across the entire codebase (`lake build` clean,
  CI-enforced).
- **Verified RV64IM core** with separation logic, step-bounded CPS Hoare
  triples (`cpsTripleWithin N`), and automated tactics (`xperm`, `xcancel`,
  `seqFrame`, `liftSpec`, `runBlock`).
- **EVM opcode coverage**: see the [`PROGRESS.md`](PROGRESS.md) coverage
  table — currently proven, partial, executable-spec-only, and not-started
  tiers are tracked per opcode against the 149 byte-codes in
  `EvmAsm.Evm64.EvmOpcode` (PUSH/DUP/SWAP/LOG families expanded).
- **Codegen**: M0–M10 of [`CODEGEN.md`](CODEGEN.md) shipped (text emitter,
  tiny EVM interpreter with runtime dispatcher, 91 wired opcodes including
  DIV/MOD, SDIV/SMOD, ADDMOD); codegen-proofs Phase 1 (registry invariants)
  and initial Phase 4 handler specs (13/91) have landed.
- **Stateless-guest scaffold** (`PR-K*` series): unproved RV64
  macro-asm helpers for RLP, MPT, transaction decoding,
  account / block-body accessors, and address derivation. Each
  helper has end-to-end ziskemu fixtures against the Python
  reference but **no Hoare-triple specs yet**; see the
  ["Stateless-guest scaffold" subsection](#stateless-guest-scaffold-currently-unproved)
  above for the verification status and proof gap.
- **Roadmap**: the long-form opcode-by-opcode plan lives in
  [`PLAN.md`](PLAN.md); the L1-zkEVM context lives in
  [`PROGRESS.md`](PROGRESS.md)'s "Role in the L1-zkEVM stack" section.

## Documentation

- [Notable proven specifications](docs/notable-specs.md) — index of stack
  specs and `EvmWord` correctness theorems with commit-pinned permalinks.

## References

- Kennedy, A., Benton, N., Jensen, J.B., Dagand, P.-E. (2013).
  "Coq: The world's best macro assembler?" PPDP 2013.
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **SPlean** (Separation Logic Proofs in Lean), Verse Lab.
  https://github.com/verse-lab/splean
  The `xperm` / `xperm_hyp` / `xsimp` tactics in `Tactics/` are inspired by
  SPlean's `xsimpl` tactic.
- **YOLO** — Mikhalchuk, V., Gladshtein, V., Sergey, I. (2026).
  "Lazy Proof Automation for Separation Logic." ITP 2026 (to appear).
  Artifact: https://github.com/verse-lab/yolo
  The certificate-based permutation prover `buildPermProofCert` / `seps_permute`
  (in `Tactics/XPerm.lean` and `SepLogic.lean`, gated behind the `xperm.cert`
  option) **re-implements YOLO's core idea** — run the unverified atom-matching
  search once and discharge the whole entailment with a *single* cheap verified
  replay instead of an eager step-by-step proof. It is an **independent
  re-implementation of the idea, not a port of YOLO's code**: it shares none of
  YOLO's machinery (no `hprop` syntax tree, no left/right worklists, no
  extensible operation-tag typeclasses, no recorded-tactic-script replay).
  Instead it records the result as an index permutation `σ : List Nat` and
  discharges it with one `seps_permute` lemma whose `σ.Perm (List.range n)` side
  condition is closed by a single kernel-checked `decide`. Credit for the
  underlying idea (separating fast untrusted simplification from a single
  verified reconstruction) belongs to Mikhalchuk, Gladshtein, and Sergey.
- Charguéraud, A. (2020). "Separation Logic for Sequential Programs
  (Functional Pearl)." *Proc. ACM Program. Lang.* 4, ICFP, Article 116.
  https://doi.org/10.1145/3408998
- **bedrock2**: https://github.com/mit-plv/bedrock2
  The frame automation tactics (`xcancel`, `seqFrame`) in `Tactics/XCancel.lean`
  and `Tactics/SeqFrame.lean` are inspired by bedrock2's separation logic
  automation. Specifically:
  - The `wcancel` tactic in `bedrock2/src/bedrock2/SepLogAddrArith.v` (lines 127-134)
    inspired the cancellation approach: matching atoms by tag+address, computing
    the frame as the residual of unmatched hypothesis atoms.
  - The frame rule infrastructure in `bedrock2/src/bedrock2/FrameRule.v` (lines 75-175)
    inspired the automatic frame extraction pattern where specs include a universal
    frame parameter and tactics instantiate it during composition.
  - The instruction specs with explicit frame in `compiler/src/compiler/GoFlatToRiscv.v`
    (lines 439-546) informed the design of composing instruction specs with
    `cpsTriple_frameR` + `cpsTriple_seq_perm_same_cr`.
- Knuth, D.E. (1997). *The Art of Computer Programming, Volume 2:
  Seminumerical Algorithms* (3rd ed.), §4.3.1 "The Classical Algorithms."
  Addison-Wesley. Algorithm D is used for the DIV/MOD opcodes in `Evm64/DivMod.lean`.
- zkvm-standards: https://github.com/eth-act/zkvm-standards
  Standards for zkVM RISC-V target, I/O interface, and C-interface
  accelerators. The vendored header at
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`
  is the canonical accelerator C ABI targeted by the verified guest for
  cryptographic precompiles, KECCAK256, and secp256k1 verification; see
  [`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md)
  for the decision record, full design note, and per-precompile coverage /
  EVM-precompile → accelerator mapping table.
- Host I/O C ABI (source of truth):
  `EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`
  defines the canonical host-I/O surface (`read_input` / `write_output`).
  See [`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md)
  for the decision record, the SP1 `HINT_LEN` / `HINT_READ` / `COMMIT` →
  zkvm-standards mapping, and the migration plan tracked under beads
  parent `evm-asm-96ysd` (GH #114 / #116).
- SP1 zkVM: https://github.com/succinctlabs/sp1
  The RISC-V `ECALL` framing (instruction encoding, register
  convention, return-via-`a0`) follows the same mechanism SP1 uses;
  the *function set* and argument layout follow `zkvm_accelerators.h`,
  not SP1's syscall table. Concrete syscall IDs are a host detail
  remapped in the ECALL handler and tracked per-bridge in beads
  parent `evm-asm-nr2sk`.
- sail-riscv-lean: https://github.com/opencompl/sail-riscv-lean
- RISC-V ISA specification: https://riscv.org/technical/specifications/
