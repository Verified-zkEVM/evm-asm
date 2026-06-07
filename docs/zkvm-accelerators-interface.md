# ADR: zkvm_accelerators.h as the canonical accelerator C ABI

Status: Accepted (2026-05-06)
Authors: @pirapira (decision); Hermes-bot (drafting)
Refs: beads `evm-asm-y4o09`, `evm-asm-nr2sk`; GH #114, #116

## Decision

The canonical C interface that the verified RISC-V guest targets for
cryptographic accelerators is the header

  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`

(vendored from <https://github.com/eth-act/zkvm-standards>). All EVM
precompile dispatch (`0x01`–`0x11`, `0x100`) and the non-precompile
accelerators `KECCAK256` and `secp256k1_verify` lower onto a function
declared in that header. The header — not a particular zkVM — is the
source of truth for argument layout, return-value framing
(`zkvm_status` / `ZKVM_EOK`), and per-function preconditions.

## Why this is non-obvious from the code today

`README.md` historically said "the ECALL-based syscall mechanism follows
SP1's conventions." That is a statement about the *mechanism* (RISC-V
`ECALL` with syscall ID in `a7`/`t0`, args in `a0`–`a2`, etc.), not
about the *function set or signatures*. SP1 ships its own list of
syscall IDs and accelerator argument shapes; the EVM-asm proofs
target the eth-act zkvm-standards function set described in
`zkvm_accelerators.h`. The two coexist:

- The dispatch *mechanism* (instruction encoding, register convention,
  return-via-`a0`) reuses SP1's RISC-V `ECALL` framing because it is
  the same mechanism every RISC-V zkVM uses; nothing in
  `zkvm_accelerators.h` constrains it.
- The *syscall ID table* — which integer in `a7`/`t0` selects which
  accelerator — is an implementation detail of the host zkVM, not of
  the C ABI. We track concrete IDs in the per-precompile bridge beads
  (parent `evm-asm-nr2sk`); a host that ships a different ID table
  remaps in its ECALL handler without affecting the verified guest.

In short: function set + argument layout + status framing come from
`zkvm_accelerators.h`; ECALL framing follows the RISC-V convention SP1
also uses; concrete syscall IDs are handler-side and tracked
separately.

## Coverage table

The header declares 19 entry points. Each one is (or will be) bridged by
a Lean payload type, a syscall-ID constant tying the ECALL handler to
the function, and a Hoare triple linking the RISC-V state transition to
the pure result. Per-function status is tracked in the children of
`evm-asm-nr2sk`.

Selector constants live in
`EvmAsm/Evm64/Accelerators/SyscallIds.lean` as both `Nat` IDs under
`EvmAsm.Accelerators.SyscallId` and RV64 words under
`EvmAsm.Rv64.SyscallIdWord`; the `allSelectors_pairwiseDistinct` and
`accelerator_ids_in_range` theorems pin the table mechanically.

| Surface | C symbol | Selector | Lean payload bridge | ECALL / execution bridge status |
|---------|----------|----------|---------------------|---------------------------------|
| KECCAK256 opcode | `zkvm_keccak256` | `keccak256` / `0x100` | `EvmAsm/EL/KeccakInputBridge.lean`, `EvmAsm/EL/KeccakResultBridge.lean` | `EvmAsm/EL/KeccakEcallBridge.lean`, `EvmAsm/EL/KeccakExecutionBridge.lean`, `EvmAsm/EL/KeccakStackBridge.lean`, `EvmAsm/EL/KeccakStackExecutionBridge.lean` |
| secp256k1 signature verify | `zkvm_secp256k1_verify` | `secp256k1_verify` / `0x101` | `EvmAsm/EL/Secp256k1VerifyInputBridge.lean`, `EvmAsm/EL/Secp256k1VerifyResultBridge.lean` | `EvmAsm/EL/Secp256k1VerifyEcallBridge.lean` |
| ECRECOVER `0x01` | `zkvm_secp256k1_ecrecover` | `secp256k1_ecrecover` / `0x102` | `EvmAsm/EL/Secp256k1EcrecoverInputBridge.lean`, `EvmAsm/EL/Secp256k1EcrecoverResultBridge.lean` | `EvmAsm/EL/Secp256k1EcrecoverEcallBridge.lean` |
| SHA256 `0x02` | `zkvm_sha256` | `sha256` / `0x103` | `EvmAsm/EL/Sha256InputBridge.lean`, `EvmAsm/EL/Sha256ResultBridge.lean` | `EvmAsm/EL/Sha256EcallBridge.lean` |
| RIPEMD160 `0x03` | `zkvm_ripemd160` | `ripemd160` / `0x104` | `EvmAsm/EL/Ripemd160InputBridge.lean`, `EvmAsm/EL/Ripemd160ResultBridge.lean` | `EvmAsm/EL/Ripemd160EcallBridge.lean` |
| IDENTITY `0x04` | none | none | pure memory copy path, no accelerator payload | not applicable |
| MODEXP `0x05` | `zkvm_modexp` | `modexp` / `0x105` | `EvmAsm/EL/ModexpInputBridge.lean`, `EvmAsm/EL/ModexpResultBridge.lean` | `EvmAsm/EL/ModexpEcallBridge.lean` |
| BN254 G1 ADD `0x06` | `zkvm_bn254_g1_add` | `bn254_g1_add` / `0x106` | `EvmAsm/EL/Bn254G1AddInputBridge.lean`, `EvmAsm/EL/Bn254G1AddResultBridge.lean` | `EvmAsm/EL/Bn254G1AddEcallBridge.lean` |
| BN254 G1 MUL `0x07` | `zkvm_bn254_g1_mul` | `bn254_g1_mul` / `0x107` | `EvmAsm/EL/Bn254G1MulInputBridge.lean`, `EvmAsm/EL/Bn254G1MulResultBridge.lean` | `EvmAsm/EL/Bn254G1MulEcallBridge.lean` |
| BN254 PAIRING `0x08` | `zkvm_bn254_pairing` | `bn254_pairing` / `0x108` | `EvmAsm/EL/Bn254PairingInputBridge.lean`, `EvmAsm/EL/Bn254PairingResultBridge.lean` | `EvmAsm/EL/Bn254PairingEcallBridge.lean` |
| BLAKE2F `0x09` | `zkvm_blake2f` | `blake2f` / `0x109` | `EvmAsm/EL/Blake2fInputBridge.lean`, `EvmAsm/EL/Blake2fResultBridge.lean` | `EvmAsm/EL/Blake2fEcallBridge.lean` |
| KZG POINT EVAL `0x0a` | `zkvm_kzg_point_eval` | `kzg_point_eval` / `0x10a` | `EvmAsm/EL/KzgPointEvalInputBridge.lean`, `EvmAsm/EL/KzgPointEvalResultBridge.lean` | `EvmAsm/EL/KzgPointEvalEcallBridge.lean` |
| BLS12 G1 ADD `0x0b` | `zkvm_bls12_g1_add` | `bls12_g1_add` / `0x10b` | `EvmAsm/EL/Bls12G1AddInputBridge.lean`, `EvmAsm/EL/Bls12G1AddResultBridge.lean` | `EvmAsm/EL/Bls12G1AddEcallBridge.lean` |
| BLS12 G1 MSM `0x0c` | `zkvm_bls12_g1_msm` | `bls12_g1_msm` / `0x10c` | `EvmAsm/EL/Bls12G1MsmInputBridge.lean`, `EvmAsm/EL/Bls12G1MsmResultBridge.lean` | `EvmAsm/EL/Bls12G1MsmEcallBridge.lean` |
| BLS12 G2 ADD `0x0d` | `zkvm_bls12_g2_add` | `bls12_g2_add` / `0x10d` | `EvmAsm/EL/Bls12G2AddInputBridge.lean`, `EvmAsm/EL/Bls12G2AddResultBridge.lean` | `EvmAsm/EL/Bls12G2AddEcallBridge.lean` |
| BLS12 G2 MSM `0x0e` | `zkvm_bls12_g2_msm` | `bls12_g2_msm` / `0x10e` | `EvmAsm/EL/Bls12G2MsmInputBridge.lean`, `EvmAsm/EL/Bls12G2MsmResultBridge.lean` | `EvmAsm/EL/Bls12G2MsmEcallBridge.lean` |
| BLS12 PAIRING `0x0f` | `zkvm_bls12_pairing` | `bls12_pairing` / `0x10f` | `EvmAsm/EL/Bls12PairingInputBridge.lean`, `EvmAsm/EL/Bls12PairingResultBridge.lean` | `EvmAsm/EL/Bls12PairingEcallBridge.lean` |
| BLS12 MAP FP TO G1 `0x10` | `zkvm_bls12_map_fp_to_g1` | `bls12_map_fp_to_g1` / `0x110` | `EvmAsm/EL/Bls12MapFpToG1InputBridge.lean`, `EvmAsm/EL/Bls12MapFpToG1ResultBridge.lean` | `EvmAsm/EL/Bls12MapFpToG1EcallBridge.lean` |
| BLS12 MAP FP2 TO G2 `0x11` | `zkvm_bls12_map_fp2_to_g2` | `bls12_map_fp2_to_g2` / `0x111` | `EvmAsm/EL/Bls12MapFp2ToG2InputBridge.lean`, `EvmAsm/EL/Bls12MapFp2ToG2ResultBridge.lean` | `EvmAsm/EL/Bls12MapFp2ToG2EcallBridge.lean` |
| secp256r1 verify `0x100` | `zkvm_secp256r1_verify` | `secp256r1_verify` / `0x112` | `EvmAsm/EL/Secp256r1VerifyInputBridge.lean`, `EvmAsm/EL/Secp256r1VerifyResultBridge.lean` | `EvmAsm/EL/Secp256r1VerifyEcallBridge.lean` |

The table is intentionally path-based: if a bridge module is renamed or split,
this table should be updated in the same PR so downstream readers can trace
from the C symbol to the Lean payload and ECALL surface.

## Installed ziskemu backend notes

The zkvm-standards rows above describe the desired ABI surface, not proof that
the locally installed `ziskemu` has a concrete backend for every symbol. As of
the 2026-06-02 local installation used for EEST work:

- `zkvm_sha256` is implemented in this repo as a guest wrapper around
  ziskemu's SHA-256 compression intrinsic at CSR `0x805`; see
  `EvmAsm/Codegen/Programs/HashBridge.lean` and
  `scripts/codegen-zisk-zkvm-sha256-check.sh`.
- `zkvm_keccak256` is similarly implemented as a guest sponge wrapper around
  ziskemu's Keccak-f[1600] primitive.
- No named RIPEMD160 backend is present in the local zisk sources. Searches for
  `ripemd`, `RIPEMD`, `zkvm_ripemd`, and `ripemd160` under
  `/home/zksecurity/.zisk/zisk` and `/home/zksecurity/zisk` find no callable
  symbol or implementation file.
- ziskemu's `emulator-asm` tree does contain a "precompile results" stream/cache
  facility, but that path replays externally supplied result words. It is not a
  RIPEMD160 computation backend and is not exposed by the `ziskemu` CLI used by
  the current codegen/EEST scripts.

Therefore, RIPEMD160 dispatch should not be wired as if a backend already
exists. The next implementation slice must either add/prove a concrete zisk
RIPEMD160 backend path, or explicitly implement RIPEMD160 in the guest and test
it against Ethereum's `hashlib.new("ripemd160", data)` behavior.

RIPEMD160 has two byte-level boundaries. The computation boundary produces the
raw 20-byte digest. The EVM precompile output boundary is 32 bytes: 12 leading
zero bytes followed by that digest, matching execution-specs
`left_pad_zero_bytes(hash_bytes, 32)`. The Lean bridge records this as
`Ripemd160ResultBridge.evmOutputBytesFromHash`; dispatch code should copy those
32 bytes as returndata, while stack-word views may decode the raw 20-byte
digest as a big-endian word because the high 12 bytes are then zero.

ECRECOVER is only partially supported at the zisk layer:

- ziskemu has secp256k1 point-add and point-double primitives
  (`_opcode_secp256k1_add`, `_opcode_secp256k1_dbl`) in
  `/home/zksecurity/.zisk/zisk/emulator-asm/src/emu.c`. However, the
  reproducible backend probe
  `scripts/codegen-zisk-secp256k1-add-dbl-backend-probe-check.sh` classifies
  both the documented `syscall_secp256k1_add`/`syscall_secp256k1_dbl` and the
  emulator-private `_opcode_secp256k1_add`/`_opcode_secp256k1_dbl` symbol
  families as NOT READY: neither links from a bare codegen ELF on the installed
  ziskemu 0.16.0 (undefined reference at link time, since the normal codegen
  path links with `riscv64-elf-ld -nostdlib` and does not pull in zisk's host C
  library — same limitation as the BLS12 family below). The affine point
  helpers in `EvmAsm/Codegen/Programs/Secp256k1Curve.lean`
  (`secp256k1_point_add`, `secp256k1_point_double`) therefore use the
  **software route** built on the verified `secf_*` field arithmetic, with no
  accelerator-backed fallback wired. The software route is exercised by
  `scripts/codegen-zisk-secp256k1-curve-check.sh`, which verifies `double(G)`
  and `add(G,G)` against the precomputed `2G` constant. Until the backend probe
  reports ready, keep the software route active rather than calling the
  undefined `_opcode_secp256k1_*`/`syscall_secp256k1_*` symbols.
- zisk's C library has `secp256k1_ecdsa_verify` in
  `/home/zksecurity/.zisk/zisk/lib-c/c/src/ec/ec.cpp`. This computes the
  ECDSA verification point from a known public key. It is not public-key
  recovery from `(msg_hash, v, r, s)`.
- The precompile-results hint parser in
  `/home/zksecurity/.zisk/zisk/emulator-asm/src/client.c` defines
  `HINTS_TYPE_ECRECOVER`, but its switch case is commented out and explicitly
  says it is not implemented.

Therefore, EVM precompile address `0x01` should not be wired as if
`zkvm_secp256k1_ecrecover` is already available. The next backend slice must
either add/prove a concrete ziskos hint-backed ECRECOVER path, or implement the
missing recovery wrapper on top of lower-level secp256k1 operations and then
probe it with valid and invalid vectors from
`execution-specs/tests/frontier/precompiles/test_ecrecover.py`.

BLS12-381 is in a similar "ABI exists, backend path not yet exposed" state for
the runtime opcode harness:

- The zkvm-standards C ABI declares the BLS12 entry points
  `zkvm_bls12_g1_add`, `zkvm_bls12_g1_msm`, `zkvm_bls12_g2_add`,
  `zkvm_bls12_g2_msm`, `zkvm_bls12_pairing`,
  `zkvm_bls12_map_fp_to_g1`, and `zkvm_bls12_map_fp2_to_g2`.
- The normal codegen path emits one bare assembly file and links it with
  `riscv64-elf-ld -nostdlib`; see
  `EvmAsm/Codegen/Driver.lean`. It does not link zisk's host C library, so a
  direct call to `zkvm_bls12_g1_add` from `runtime_dispatcher.elf` currently
  fails as an undefined symbol.
- The checked zisk source tree has BLS12 field/curve routines under
  `lib-c/c/src/bls12_381` and has precompile-result stream/cache plumbing in
  `emulator-asm/src/client.c`, `server.c`, and `emu.c`. The relevant CLI hooks
  are gated by `ASM_PRECOMPILE_CACHE` in
  `emulator-asm/src/configuration.c`.
- The installed `ziskemu` used by the current codegen scripts does not expose
  the precompile-result replay flags needed by that path.

Run the reproducible readiness probe with:

```bash
scripts/codegen-zisk-bls12-precompile-replay-probe.sh
```

The bare-RV64 wrapper family probe links every BLS12 accelerator selector used
by EIP-2537 runtime bodies and classifies the installed backend route:

```bash
scripts/codegen-zisk-bls12-backend-probes-check.sh
```

Use `--require-ready` when a downstream BLS runtime-body test genuinely needs
the replay path and should fail if the installed `ziskemu` cannot provide it.
Until this probe reports ready, BLS12 CALL/STATICCALL runtime bodies should
preserve explicit unsupported/backend-blocked behavior rather than calling
undefined `zkvm_bls12_*` symbols.

## Calling convention

The guest follows LP64 as documented in
[`EvmAsm/Evm64/CallingConvention.lean`](../EvmAsm/Evm64/CallingConvention.lean):
arguments in `a0`–`a2` (`x10`–`x12`), return value in `a0`, `sp` saved
by the callee, `ra` saved by the caller of non-leaf routines. Each
accelerator wrapper marshals its `zkvm_accelerators.h` arguments into
that register layout, issues an `ECALL`, and reads back the
`zkvm_status` from `a0`. Concrete bridges live (or will live) under
`EvmAsm/EL/` next to the existing keccak bridges.

## Sibling: host-I/O C ABI

zkvm-standards also defines a *host I/O* surface — the channel by which
the guest receives its private input and emits its public output — in a
separate interface file:

  `EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`

That surface (`read_input` / `write_output`) is shape-only, just like
`zkvm_accelerators.h`: it specifies argument layout and semantics but
leaves concrete syscall IDs to each host zkVM's dispatch layer.  The
decision record for adopting this interface is in
[`docs/zkvm-host-io-interface.md`](zkvm-host-io-interface.md).

The two zkvm-standards interfaces are fully independent:
- `zkvm_accelerators.h` — cryptographic precompiles and KECCAK256.
- `io-interface/README.md` (`read_input`/`write_output`) — guest I/O.

Both follow the same philosophy: function set + argument layout come
from zkvm-standards; ECALL framing follows the RISC-V convention SP1
also uses; concrete syscall IDs are handler-side.

## Maintenance

Update this ADR when:

- The vendored `zkvm_accelerators.h` is bumped (record the source
  commit).
- A bridge child of `evm-asm-nr2sk` lands and the coverage table above
  needs ticking.
- The decision itself is revisited (e.g. eth-act zkvm-standards is
  superseded).

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
