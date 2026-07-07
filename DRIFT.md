# DRIFT — trusted base & "what is NOT proven" ledger

> **Generated** by `lake exe progress-report drift` from the kernel-checked
> registry + obligation tracker in `EvmAsm/Progress.lean` and
> `EvmAsm/Progress/Obligations.lean`. `scripts/check-drift.sh` fails the build if
> this file drifts from the regenerated output — do **not** hand-edit. To
> refresh: `scripts/drift-report.sh --write`.

This is evm-asm's explicit assumptions / trusted-computing-base ledger, in the
spirit of the seL4 and CompCert assumptions lists. The Lean kernel makes every
*proven* statement unhackable; this file enumerates what the kernel does **not**
cover, so a green dashboard is never mistaken for a fully closed guest program.

## Guest-program obligations (kernel-checked)

The nine obligations a complete L1 stateless block-validation guest program must
satisfy, each with the opcodes/infrastructure blocking it. This is the
*direction* axis: opcode-tier counts cannot tell you which obligation is blocked
by what. Source of truth, per-status counts, and the opcode cross-check live in
[`EvmAsm/Progress/Obligations.lean`](EvmAsm/Progress/Obligations.lean)
(`doneCount_eq = 2`, `blockedCount_eq = 6`,
`notStartedCount_eq = 1`, and `blocker_opcodes_in_registry`,
which fails the build if any opcode blocker stops naming a real registry entry).

| Status | Count |
|---|---:|
| ✅ done | 2 |
| 🟡 blocked | 6 |
| ✗ not started | 1 |

| # | Obligation | Status | Blocked by |
|---|---|---|---|
| 1 | RV64 ELF for `riscv64im_zicclsm-unknown-none-elf` | 🟡 blocked | codegen emits `rv64imac` (one extension off `zicclsm`) |
| 2 | `read_input` / `write_output` per the IO interface | ✅ done | Rv64/SyscallSpecs.lean (codegen M4 wired) |
| 3 | RLP-decode the (block, witness) input | 🟡 blocked | RV64 RLP decoder phases 1–3 (in progress) |
| 4 | EVM interpreter loop on the decoded block | 🟡 blocked | codegen M5 (tiny EVM interpreter) not shipped |
| 5 | Full opcode coverage with verified handlers | 🟡 blocked | `MOD`, `SDIV`, `SMOD`, `ADDMOD`, `MULMOD`, `EXP`, `CALLDATACOPY`, `PUSH2..32`, execSpec-tier opcodes have no RV64 subroutine (axis A.2) |
| 6 | Accelerator ECALL bridges per `zkvm_accelerators.h` | 🟡 blocked | per-precompile EL bridges not yet codegen-wired |
| 7 | MPT verification of pre-state witness proofs | ✗ not started | — |
| 8 | Verified post-state root → public output | 🟡 blocked | obligation #4 (interpreter loop), obligation #5 (opcode coverage), obligation #6 (accelerator bridges), obligation #7 (MPT verification) |
| 9 | Halt convention per `standard-termination-semantics` | ✅ done | `--halt linux93` default; docs/host-io-halt-convention.md |


## What is NOT proven

### 🔶 `conditional` opcodes — proven only on a restricted input domain

A complete top-level Hoare triple exists, but gated by a non-vacuous
precondition; the excluded domain is **unverified**.

| Opcode | Why not (yet) fully proven |
|---|---|


### 🟡 `partly` opcodes — no complete top-level triple yet

Pure-spec / `<op>_correct` lemma proven, but no end-to-end stack-spec wrap.

| Opcode | Why not (yet) fully proven |
|---|---|


### ⏳ `execSpec` opcodes — handler/bridge semantics only, no RV64 subroutine

These 25 opcodes have executable-spec / handler / host-bridge
semantics only; **no RV64 subroutine is proven to produce the EVM result**:

STOP, KECCAK256, BALANCE, EXTCODESIZE, EXTCODECOPY, RETURNDATACOPY, EXTCODEHASH, SLOAD, SSTORE, JUMP, JUMPI, TLOAD, TSTORE, MCOPY, LOG0..4, CREATE, CALL, CALLCODE, RETURN, DELEGATECALL, CREATE2, STATICCALL, REVERT, INVALID, SELFDESTRUCT.

### ✗ `notStarted` opcodes — not represented in `EvmOpcode`

| Opcode | Why not (yet) fully proven |
|---|---|


## Trust boundaries (unverified by design)

- **Codegen is unverified by design.** The RISC-V lowering, the ziskemu
  emulator, and the deferred codegen milestones (M5 EVM-interpreter loop and
  beyond) are explicitly outside the kernel-checked core. Drift is *fenced* by
  build-time `#guard` round-trip tests (`Codegen/RoundTripTests.lean`) and the
  conformance floor (`check-conformance-floor.sh`), not *proven*.
- **Handler glue is proven per-opcode, not universally.** Each opcode is
  `.proven` on its verified *body* spec, but the subroutine the codegen emits,
  `h_<OP>`, wraps that body in glue — a stack-underflow guard prologue, any
  `preBody` clobber-saves / `la` address loads, and the advance-`x10`/`ret`
  tail — that the body spec does not cover. This handler glue is separately
  kernel-proven (guard + body + tail, both underflow and no-underflow paths)
  for `ADD` (`Codegen.Proofs.evmAddGuardedHandlerSpec`) and `CALLDATALOAD`
  (`Codegen.Proofs.evm_calldataload_staged_guarded_handler_spec`); for the other
  `.proven` opcodes (`MOD`, `EXP`, `ADDMOD`, …) the preBody glue is **not yet
  proven**. The final tie from the proven Program to the emitted ELF bytes is
  machine-checked for `h_ADD` only (`scripts/check_guarded_handler_bytes.py`);
  for `CALLDATALOAD` the `la` targets are proven relative to reconstruction
  hypotheses, with the byte-tie deferred.
- **RV64 instruction-model fidelity.** The Lean RV64 semantics are tied to the
  official Sail RISC-V model via `Rv64/SailEquiv/` (the `dhsorens/sail-riscv-lean`
  fork pinned in `lakefile.toml`); the tie itself is a trusted reference, not a
  kernel theorem about real silicon.
- **EVM reference semantics.** Conformance is measured against
  `ethereum/execution-specs` (pinned submodule); that the pinned spec faithfully
  encodes consensus rules is assumed, not proven here.
- **Gas / memory cost modeling.** Per-opcode `cpsTripleWithin N` bounds are a
  verified *step-count surrogate*; the EVM gas schedule mapping is modeled, not
  proven equivalent to the yellow-paper schedule.
- **Per-opcode handler glue.** Even for `.proven` opcodes, the handler
  `preBody`/tail glue around the verified subroutine — gas accounting
  (`copyWordGasAsm`), MSIZE / memory-expansion bookkeeping
  (`updateActiveMemorySizeAsm`), OOG guards, and offset normalization — is
  unverified `.custom` asm (the CALLDATACOPY #9880 convention). A dedicated
  gas-glue verification track is deferred work; until it lands, the `.proven`
  tier certifies the opcode's data effect, not its gas/expansion glue.
- **Trusted axiom base.** Only the three classical axioms
  (`propext`, `Classical.choice`, `Quot.sound`); `native_decide`/`bv_decide`
  trust axioms are forbidden (CI-gated by `check-axioms.sh` /
  `check-forbidden-tactics.sh`).

