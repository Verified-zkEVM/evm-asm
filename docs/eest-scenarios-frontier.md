# EEST Scenario Frontier

The Amsterdam blockchain-test fixture reported by the user is generated at:

```text
gen-out/eest-fixtures/zkevm@v0.4.0/fixtures/fixtures/blockchain_tests/for_amsterdam/frontier/scenarios/scenarios/scenarios.json
```

It comes from `execution-specs/tests/frontier/scenarios/test_scenarios.py` and
the generators under `execution-specs/tests/frontier/scenarios/scenarios/`.
The current cached fixture contains 34 test-program entries and 1,258 stateless
blocks.

This is a broad feature-completeness frontier, not a narrow opcode fixture. The
scenario generator combines CALL, CREATE, revert, double-call, and static-context
execution shapes, then runs many operation programs through those shapes. A
failure here can point at several existing surfaces at once: call/create frame
execution, revert propagation, environment opcodes, storage/log/selfdestruct
effects, returndata, gas, receipts, and post-state root computation.

The owning bead is `evm-asm-fhsxz.2.4.2.54.2`. Use this fixture filter when
probing it through the stateless harness:

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter frontier/scenarios/scenarios/scenarios \
  --limit 1 \
  --jobs 1 \
  --quiet-passes \
  --max-failures 1 \
  --steps 1000000000
```

When triaging failures, first identify the test-program id in the fixture name
(for example `program_SSTORE_SLOAD`, `program_LOGS`, or
`program_ALL_FRONTIER_OPCODES`), then categorize the failing scenario by the
missing implementation surface before creating a narrower implementation bead.
