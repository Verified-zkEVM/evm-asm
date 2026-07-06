# Dual-path differential (D3 / R-E2) — design + deferral note

> **Status: DEFERRED from Phase 3** (agent-progress-steering rollout), with
> this design note as the actionable hand-off. Phase 3 landed D1 (the
> boundary-biased arithmetic fuzzer, validated against the execution-specs
> oracle over 20k+ cases), D2 (EEST budget-vs-wrong distinction), and D4
> (round-trip coverage fence). D3's defining feature — asserting equality
> between the in-Lean execution model and the **ziskemu** round-trip — could
> not be validated in the Phase 3 environment because **ziskemu was not
> available locally**. Shipping an unrunnable/unvalidated dual-path harness
> would manufacture false confidence (report §1, §6), so it is deferred to a
> session with a working ziskemu rather than committed blind.

## What D3 is (report R-E2, rescoped)

Contrast the **two surfaces that already exist in the repo** on shared
inputs and assert byte-equal outputs — **no new native interpreter** (report
§6 non-goal):

* **Path A — in-Lean RISC-V execution model.** `EvmAsm/Rv64/Execution.lean`
  defines `step : MachineState → Option MachineState` (PC-driven fetch +
  execute; `none` on the SP1 HALT convention `ECALL` with `t0 = 0`, on
  `EBREAK`, and on memory traps). This is the model the `cpsTriple` proofs
  reason about. (`execProgram` in `Rv64/Program.lean` is only a *straight-line*
  executor — it does **not** follow branches — so it cannot run the
  arithmetic programs' Knuth-D loops; D3 must iterate `step` with fuel.)
* **Path B — codegen → RISC-V → ziskemu round-trip.** Already exercised by
  the per-opcode scripts, e.g. `scripts/codegen-evm_div-check.sh` emits
  `EvmAsm.Codegen.Programs.evm_div` to an ELF and runs it on ziskemu,
  diffing the public output against the expected 256-bit result.

A divergence between A and B pinpoints a codegen / lowering bug a single
path hides (the Hive engine-vs-RLP analog).

## Why it catches the DIV-class bug

The v4 DIV bug lived in the lowered Knuth-D code, on the domain the proof
EXCLUDED (`b.getLimbN 3 ≠ 0`). Running the *same lowered program* through
both the in-Lean `step` model and ziskemu, on boundary-biased inputs that
include the unproven domain, surfaces a lowering/model-fidelity divergence
that the (domain-restricted) proof and common-case tests both miss.

## Concrete build plan (for the next session, with ziskemu present)

1. **Fuel-bounded in-Lean runner.** Add (to a `Tests/` module, never the
   trusted base) `runToHalt : Nat → MachineState → Option (MachineState ×
   Nat)` iterating `step` until it returns `none` (HALT) or fuel runs out.
   Distinguish HALT-with-output from fuel-exhaustion (mirror D2's
   budget-vs-wrong distinction).
2. **Shared input.** The existing `Programs.*` arithmetic programs bake the
   operands in as constants (e.g. `evm_div` is dividend=2^64, divisor=2), so
   each program is a single shared input. Either (a) run each existing
   per-opcode program through both paths as point-checks, or (b)
   parameterize the codegen programs by operands (read from `INPUT_ADDR`) so
   the D1 corpus operands can drive both paths — the higher-value option.
3. **I/O ABI matching.** Load the program into `CodeMem` at the codegen base;
   seed `MachineState` memory with the operands at the input region; after
   HALT, read the result from the output region. The memory-region constants
   are in `EvmAsm/Rv64/Basic.lean` (`INPUT_MEM_START = 0x40000000`,
   `RAM_MEM_START = 0xa0000000` incl. `OUTPUT_ADDR`). The in-Lean read MUST
   use the same offsets ziskemu's `-o` output dumps.
4. **Differential script** `scripts/dual-path-diff.sh`: for each shared
   input, (A) `lake exe` the in-Lean runner → output bytes; (B) run the
   existing codegen→ziskemu script → output bytes; assert equal. Wire
   **nightly + on `merge_group`** (heavy; build-budget non-goal §6), not as a
   serial per-PR gate. Seed/extend the same permanent corpus shape as D1.
5. **Localization.** Reuse D2's per-region decomposition; on divergence,
   report the failing opcode/step, not just "differs".

## Guardrails (unchanged)

No new trusted components (both surfaces already exist). No
`native_decide`/`bv_decide`, no `maxHeartbeats`. The in-Lean runner lives
under `EvmAsm/Tests/` and is never imported into a proof. ziskemu stays the
unverified-by-design boundary this *measures*, not verifies.
