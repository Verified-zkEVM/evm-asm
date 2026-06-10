# evm-asm live-chain conformance harness

Run **real Ethereum data** — live block environment, real transaction calldata,
real contract bytecode — through the **actual verified evm-asm RISC-V guest** on
the Zisk emulator, and check the result against the **live chain**.

This is a demo today and a **living equivalence checker** over time: it is
capability-driven (reads `capabilities.json`), reports coverage against real
blocks, and is structured so that as evm-asm matures it grows — without a
rewrite — into a systematic whole-block-vs-mainnet conformance run. See
[Roadmap](#roadmap).

```
  ./run.sh                 narrated demo (default), live RPC
  ./run.sh --deep          + proof deep-dives (kernel theorem + cycle bound)
  ./run.sh --no-net        offline: vendored canned chain data (no RPC)
  ./run.sh --report        opcode-coverage scorecard over a live block
  ./run.sh --check-manifest verify capabilities.json matches PROGRESS.md
  ./run.sh --auto          no pauses (PACE=0 for instant output)

  env: RPC_URL=…  GUEST_ELF=…  ZISKEMU=…  PACE=<sec>  NO_COLOR=1
```

For a screen recording, run plain `./run.sh` (typewriter narration, pauses
between acts). For CI / quick check, `./run.sh --no-net --auto`.

## What the demo shows

1. **Act 1 — a live mainnet block, read by a verified EVM.** Pulls the latest
   block and feeds `NUMBER / TIMESTAMP / BASEFEE / COINBASE / CHAINID` into the
   guest's environment opcodes; each output equals the chain value. Every one is
   a kernel-checked Hoare triple (see `--deep`).
2. **Act 2 — real transaction calldata, through verified arithmetic.** Takes a
   real ERC-20 transfer, extracts its `amount` word with `CALLDATALOAD`, and runs
   verified 256-bit `MUL` on it — matching the value decoded from the chain.
3. **Act 3 — real on-chain contract bytecode, and the verified frontier.** Runs
   WETH9's real deployed bytecode through the guest and scores its opcode
   coverage: ~75% backed by a kernel-checked triple, ~98% spec-faithfully
   runnable; the remainder (`SLOAD`, `CALL`, `STATICCALL`) is exactly the
   roadmap below.

The closing panel states the trust base (0 `sorry`, 0 `axiom`, no compiler-trust
tactics; only the three classical axioms — audited by `scripts/check-axioms.sh`).

## What this does NOT claim (yet)

- It does **not** replay a whole block to a verified post-state root. `CALL` /
  `CREATE` are no-ops in the standalone guest, there is no MPT / state-trie
  verification, and many opcodes run without a complete proof (tier `execSpec`).
- Act 3 runs real bytecode but does **not** assert equivalence with `cast call`
  for a full contract: real Solidity dispatchers reach `SLOAD` / `CALL` (state
  and inter-contract calls) that the standalone guest doesn't yet model. Act 3
  is therefore framed as *execution + coverage*, not equivalence. The
  "matches mainnet" headline is carried by Acts 1 and 2, which genuinely match.

Honesty is the point: the coverage scorecard makes the gap explicit and
quantitative every run.

## How it works

```
  real data (cast)  →  pack-bytecode.py  →  ziskemu -e runtime_dispatcher.elf  →  result word
       │                                                                              │
       └──────────────────────────  compared to  ──────────────────────────────── live chain
```

- `lib.sh` — helpers (RPC with retry/fallback, `hex_to_csv`, `run_guest`,
  decoding, `deep_dive`, presentation).
- `capabilities.json` — the capability manifest: per-opcode proof tier, witness
  theorem, cycle bound, and runtime status, mirroring the kernel-checked registry
  in `PROGRESS.md`. `--check-manifest` fails on tier drift.
- `opcode_coverage.py` — disassembles bytecode (skipping PUSH data) and scores it
  against the manifest. Powers Act 3 and `--report`.
- `candidates.env` — pinned, pre-validated real tx hash + contract address.
- `canned/` — vendored chain data for `--no-net` (network-free runs).
- `guest/runtime_dispatcher.elf` — the verified guest ELF (see below).

## The guest ELF (pinned)

`guest/runtime_dispatcher.elf` is the verified evm-asm runtime-bytecode
dispatcher. It is **not committed** (it's a binary that breaks text-based CI
tooling) — build it once with `conformance/build-guest.sh`, which pins it to
commit `78bb73314`. `run.sh` prints a clear message if it's missing.

Why pinned: on `main` HEAD the *standalone* `runtime_dispatcher` does not link —
`h_CREATE` / `h_CREATE2` emit `jal create_frame_descend`, a symbol defined only
in the embedded `stateless_guest` path (the in-flight CREATE-frame-descent work,
WIP commit `1258d67e5`). Main CI link-checks the *guest*, not the standalone
dispatcher, so it's green despite this. We pin to the parent of that commit,
which links cleanly and supports every opcode this harness uses (env / arithmetic
/ stack / memory / calldata — not `CREATE`).

**When main's standalone dispatcher links again**, set `GUEST_REF=HEAD` in
`build-guest.sh` (and drop its file-size-guard bump), rebuild, and the harness is
otherwise unchanged. At that point this can run on HEAD continuously.

Rebuild: `conformance/build-guest.sh` (creates a throwaway git worktree, reuses
the main checkout's built deps, emits and vendors the ELF).

## Roadmap

The harness grows with evm-asm by editing `capabilities.json` and adding an act
— not by rewriting the driver. Stages track
`EvmAsm/Progress/Obligations.lean`:

- **Stage 0 (now):** supported-opcode subset over real data; `--report` scores
  coverage. ← you are here.
- **Stage 1 — full opcode coverage:** flip `MOD/SDIV/SMOD/ADDMOD/MULMOD/EXP/
  PUSH2..32` as their top-level specs land (Obligation 5); coverage climbs.
- **Stage 2 — storage:** replay real `view` calls with `--storage` preload
  (real `SLOAD`), assert vs `cast call`.
- **Stage 3 — inter-contract / creation:** when `CALL`/`CREATE` stop being no-ops
  (Obligation 6), promote `--report` from *classify* to *replay one tx and diff*.
- **Stage 4 — state trie + tx executor:** with MPT (Obligation 7) and the
  message-call executor (Obligation 4), replay whole transactions and assert
  receipts.
- **Stage 5 — full block → post-state root:** with the stateless guest complete
  (Obligation 8), replay a whole live block and assert the verified post-state
  root equals the chain's. A schedulable nightly mainnet conformance job.
