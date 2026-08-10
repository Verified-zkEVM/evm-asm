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

The ten obligations a complete L1 stateless block-validation guest program must
satisfy, each with the opcodes/infrastructure blocking it. This is the
*direction* axis: opcode-tier counts cannot tell you which obligation is blocked
by what. Source of truth, per-status counts, and the opcode cross-checks live in
[`EvmAsm/Progress/Obligations.lean`](EvmAsm/Progress/Obligations.lean)
(`doneCount_eq = 2`, `blockedCount_eq = 8`,
`notStartedCount_eq = 0`, plus two cross-checks that
fail the build: `blocker_opcodes_in_registry` if an opcode blocker stops naming a
real registry entry, and `no_proven_opcode_blockers` if one names an entry that
has already reached `.proven`).

**Reading the `Audited` column.** A blocker list is a claim about the present.
The date + commit records when the row was last checked against the live
registries; `—` means not since the field was introduced (#11803), so treat that
row's blockers as unverified rather than current.

| Status | Count |
|---|---:|
| ✅ done | 2 |
| 🟡 blocked | 8 |
| ✗ not started | 0 |

| # | Obligation | Status | Blocked by | Audited |
|---|---|---|---|---|
| 1 | RV64 ELF for `riscv64im_zicclsm-unknown-none-elf` | 🟡 blocked | codegen emits `rv64imac` (one extension off `zicclsm`) | 2026-08-10 @372162cc2 |
| 2 | `read_input` / `write_output` per the IO interface | ✅ done | Rv64/SyscallSpecs.lean (codegen M4 wired) | — |
| 3 | RLP-decode the (block, witness) input | 🟡 blocked | `rlp_item_span` is `.conditional` short-list+WalkedSpanForm only (#11577 closed the zero-triple gap; long-list outer and non-SpanForm walked items still uncovered), `rlp_item_size` covers short forms only — long string `0xb8`–`0xbf` and long list `0xf8`–`0xff` uncovered (`Correspondence.lean` `rlp_item_size`), nested-list decode bridges: `rlpItemDecode`'s list arms check a span fit and say nothing about the payload, while `decodeAux` rejects a malformed interior — a strength mismatch, tracked at #11795 with the relation-side decision scoped at #11898 | 2026-08-10 @11577 |
| 4 | EVM interpreter loop on the decoded block | 🟡 blocked | no simulation bridge from dispatched handlers to the SpecRef interpreter — #11801 is the one-opcode `h_ADD` pilot for that bridge, `stage_system_call` has no machine post yet; #11578 proves only the pure 0x01/0x02 request framing, with the tail-called dispatcher contract still outstanding | 2026-08-10 @76889ef97 |
| 5 | Full opcode coverage with verified handlers | 🟡 blocked | `RETURN`, `REVERT`, `SELFDESTRUCT`, 14 `.execSpec` entries have no RV64 subroutine (axis A.2): KECCAK256, BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH, SLOAD, SSTORE, LOG0..4, CREATE, CALL, CALLCODE, DELEGATECALL, CREATE2, STATICCALL | 2026-08-10 @372162cc2 |
| 6 | Accelerator ECALL bridges per `zkvm_accelerators.h` | 🟡 blocked | per-precompile EL bridges not yet codegen-wired | — |
| 7 | MPT verification of pre-state witness proofs | 🟡 blocked | trie-walk loop spec for `mpt_walk` over `mptNodeIs`/`nodeDbIs` against `trieLookup` (#11799), witness-ingest DB builder triples against `build_node_db`/`build_code_db` (#11800), three-tier resolve coherence (appended DB / resolve cache / witness section) vs SpecRef's single node source — where `resolveCacheValidIs` (`Evm64/MptAssertions.lean`) earns its keep | 2026-08-10 @372162cc2 |
| 8 | Verified post-state root → public output | 🟡 blocked | obligation #4 (interpreter loop), obligation #5 (opcode coverage), obligation #6 (accelerator bridges), obligation #7 (MPT verification) | — |
| 9 | Halt convention per `standard-termination-semantics` | ✅ done | `--halt linux93` default; docs/host-io-halt-convention.md | — |
| 10 | Witness reads are sound (get_account_optional composition) | 🟡 blocked | account_decode ↔ decode_account_from_leaf (#11345), bal_canonical_sort ordering + permutation (#10817), trie-walk loop spec for `mpt_walk` over mptNodeIs/nodeDbIs against trieLookup (#11799) — carries the three-tier resolve (appended DB / resolve cache / witness section) vs SpecRef's single node source; divergence stated in docs/4ch8f-slstate-specref-correspondence.md:164, witness-ingest DB builder triples against build_node_db/build_code_db (#11800), no `cpsTripleWithin` for `witness_codes_index_build` / `witness_codes_lookup_by_hash` — the code-DB *routines* (the predicate side is done; see #11573 / PR #11902) | 2026-08-10 @04de93895 |


## What is NOT proven

### 🔶 `conditional` opcodes — proven only on a restricted input domain

A complete top-level Hoare triple exists, but gated by a non-vacuous
precondition; the excluded domain is **unverified**.

| Opcode | Why not (yet) fully proven |
|---|---|
| `RETURN` | full standalone (depthAware=false) return-data window + halt core, from the post-gas handler entry through the RETURN-only system_call_mode capture block and the 0xa0010000 descriptor (header/22-dword-body zeroing, size@+64, clamped=min(size,176)@+248, evm_memory[offset..offset+clamped] copied to +72, first min(size,32) bytes to +0, kind=1@+32) to the shared dispatchHaltRet 2 core (evm_halt_flag:=2, x1:=resume, ret to resume&&&~~~1). The front now covers all system_call_mode cases: zero skips capture; nonzero with size>4096 skips conservatively; nonzero with size<=4096 stores system_call_returndata_len:=size and copies the full returndata window to system_call_returndata. `.conditional` remains because the memory-gas `preBody` (its .exit_outofgas branch) is framed OUT as a decision-1 TCB boundary, so the theorem still carries the post-gas memory-domain hyps (hOff/hOff32 and branch-conditional hOffCapture/hRdCapture). The seven `la` immediates stay as reconstruction hyps (shared deferred byte-check, as in the halt core). |
| `REVERT` | full standalone (depthAware=false) return-data window + rollback + halt core, from the post-gas handler entry through the 0xa0010000 descriptor (header/22-dword-body zeroing, size@+64, clamped=min(size,176)@+248, evm_memory[offset..offset+clamped] copied to +72, first min(size,32) bytes to +0, kind=2@+32), the five straight-line rollback env-cell stores on x20 (env+448:=env+456, env+464:=0, env+472:=env+480), to the shared dispatchHaltRet 2 core (evm_halt_flag:=2, x1:=resume, ret to resume&&&~~~1). Near-clone of RETURN reusing its window loop closures + halt core verbatim (only the code layout shifts down 80 bytes with no capture block, the kind-store value is 2, and the rollback is appended). `.conditional` NOT because of a system_call_mode gate (REVERT has no capture block — that is kind==1/RETURN-only — so it is strictly more general than RETURN) but because (1) the memory-gas `preBody` (its .exit_outofgas branch) is framed OUT as a decision-1 TCB boundary and (2) the evm_memory well-formedness domain hyps (hOff/hOff32 etc.) restrict the input domain, exactly as in RETURN. The four `la` immediates stay as reconstruction hyps (shared deferred byte-check, as in the halt core). |
| `SELFDESTRUCT` | halt/routing tail only — the shared dispatchHaltRet 4 core (evm_halt_flag:=4, x1:=.Ldispatch_resume, ret to resume&&&~~~1) over the verified `evm_selfdestruct` program; direct STOP/INVALID clone with routing code 4 (`.exit_selfdestruct`). The two `la`s (`evm_halt_flag`, `.Ldispatch_resume`) are RESOLVED via `la_resolve` (#10059), leaving only decidable `laInRange` per `la`. `.conditional` — NOT `.proven` unlike STOP/INVALID (whose dispatched handler IS just the halt tail, body:=[]) — because SELFDESTRUCT's dispatched handler (`selfdestructTailAsm`) runs a substantial effects body BEFORE this tail that is framed OUT as the residual: cold-access gas (with its own .exit_outofgas branch), new-account surcharge, EIP-6780 created-in-tx detection, balance transfer to the beneficiary, EIP-7708 log, beneficiary nonstorage record, and the CREATE-child frame_return path. A larger residual than RETURN/REVERT's gas-only preBody; a future phase proves it against `EL/SelfdestructEffects` to earn `.proven`. |

### 🟡 `partly` opcodes — no complete top-level triple yet

Pure-spec / `<op>_correct` lemma proven, but no end-to-end stack-spec wrap.

| Opcode | Why not (yet) fully proven |
|---|---|


### ⏳ `execSpec` opcodes — handler/bridge semantics only, no RV64 subroutine

These 14 opcodes have executable-spec / handler / host-bridge
semantics only; **no RV64 subroutine is proven to produce the EVM result**:

KECCAK256, BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH, SLOAD, SSTORE, LOG0..4, CREATE, CALL, CALLCODE, DELEGATECALL, CREATE2, STATICCALL.

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
- **`RETURNDATACOPY`'s image omits the framed-out high-limb operand guards.**
  The `.proven` witness `evm_returndatacopy_body_stack_spec_within` covers the
  body (`base → base+80`: bounds guards, operand pop / pointer setup, copy loop),
  but the emitted handler additionally runs, *between* the operand loads and the
  frame materialization, two blocks the modeled image excises along with the
  dynamic-gas / MSIZE glue: (i) `memDynamicU256RangeOogGuardAsm`, which sends a
  high-limb `size` — and, when `size ≠ 0`, a high-limb `destOffset` — to
  `.exit_outofgas`; and (ii) an `ld`/`or`/`or`/`bnez` check sending a high-limb
  *source offset* (`dataOffset` limbs 1–3) to `.exit_invalid`. The triple is a
  statement about that excised image, so it describes only the path on which
  those guards fall through; on operands with nonzero high limbs the emitted
  handler exits before this body's postcondition is reached. Note the three
  bridging hypotheses `h_destOff`/`h_srcOff`/`h_sizeV`
  (`operand.getLimbN 0 = BitVec.ofNat 64 n`) are **naming** bridges from the
  stack limbs to the `Nat` offsets — they place no constraint on the high limbs
  and are not where this residual lives. Closing it means modeling those blocks
  in the guard image (shifting every guard branch offset) or proving the
  framed-out region. CALLDATACOPY carries the same class of residual — its
  source-offset normalization block is likewise `preBody` glue.

  *Why each excised guard is safe to excise — three different arguments, none of
  them in the proof.* Read this before treating a `RETURNDATACOPY: proven` row as
  covering wide operands; the justifications do not share a shape:

  | assumed by | justified by | holds at `size = 0`? | reasoning lives in |
  |---|---|---|---|
  | high-limb `size` | **gas** — `copy_gas_cost` and memory expansion both explode ⇒ `OutOfGasError` | yes | `EvmMemoryGas.lean` `memDynamicU256RangeOogGuardAsm` docstring |
  | high-limb `destOffset` | **gas, but conditional on `size ≠ 0`** — quadratic expansion ⇒ `OutOfGasError`; at `size = 0` `calculate_gas_extend_memory` `continue`s and charges nothing, so the spec *accepts* it | **no — spec accepts** | same docstring; the guard's `beqz <size>` ordering mirrors `gas.py`'s `if size == 0: continue` |
  | high-limb source offset (`dataOffset`) | **not gas** — the spec's explicit `Uint(start) + Uint(size) > ulen(return_data)` ⇒ `OutOfBoundsRead` | yes — rejecting is *required*, not over-strict | the `h_RETURNDATACOPY` comment in `Codegen/Programs/NoopReturnData.lean` |

  So each excised guard matches a real execution-specs outcome (Amsterdam
  `vm/instructions/environment.py`, `vm/gas.py`): excising them costs coverage
  but hides no divergence, and in particular the guest does **not** over-reject
  the `size = 0` / high-limb-`destOffset` case the spec accepts.
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

