# EEST Precompile Frontier

The stateless guest has reusable accelerator payload and ECALL bridge surfaces
for the cryptographic precompiles, but `EvmAsm/Stateless/VM/Precompiles.lean`
still routes EVM precompile dispatch to the unimplemented frontier. The matrix
below keeps the EEST fixture classes explicit so precompile tests are not
silently postponed as new generated fixtures appear.

Generate the current matrix with:

```bash
scripts/eest-precompile-frontier-report.py --markdown
```

After a stateless harness run, the report also consumes the latest
`gen-out/eest-run/manifest.tsv` or `gen-out/eest-run/run-*/manifest.tsv` and
matching `*.result.tsv` files, then adds selected-case guest outcomes by family.
`fixture files` counts cached generated JSON files; `selected` and the match
columns describe only the latest harness selection.

| Family | Address | Backend / missing piece | Bead |
|--------|---------|-------------------------|------|
| Precompile account warming | active precompiles | VM call gas/account-access path before dispatch | `evm-asm-fhsxz.2.4.2.62.1` |
| Precompile absence | `0x01..0x101` excluding active precompiles | absent-account CALL semantics before dispatch | `evm-asm-fhsxz.2.4.2.62.2.6` |
| ECRECOVER | `0x01` | recovery output implemented in-guest via `secp256k1_recover_pubkey_staged` (accelerator-backed, armed through `ecrecover_backend_ptr`); gas + v/r/s gates were already wired | `evm-asm-fhsxz.2.4.2.62.2.5` |
| SHA256 | `0x02` | `zkvm_sha256` bridge exists; stateless dispatch missing | `evm-asm-fhsxz.2.4.2.62.2` |
| RIPEMD160 | `0x03` | `zkvm_ripemd160` bridge exists at the desired ABI level, but the local ziskemu installation has no named RIPEMD160 backend; backend/probe required before dispatch | `evm-asm-fhsxz.2.4.2.62.2` |
| IDENTITY | `0x04` | in-guest memory copy; no accelerator | `evm-asm-fhsxz.2.4.2.62.2` |
| MODEXP | `0x05` | `zkvm_modexp` bridge exists; gas/return-data framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| BN254 add/mul/pairing | `0x06..0x08` | `zkvm_bn254_*` bridges exist; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| BLAKE2F | `0x09` | `zkvm_blake2f` bridge exists; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| KZG point evaluation | `0x0a` | `zkvm_kzg_point_eval` bridge exists; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| BLS12-381 | `0x0b..0x11` | `zkvm_bls12_*` bridges and runtime dispatch are wired for the BLS12 family; focused fixture coverage uses `scripts/codegen-eest-bls12-g1-frontier-check.sh`, `scripts/codegen-eest-bls12-g2-frontier-check.sh`, and `scripts/codegen-eest-bls12-pairing-map-frontier-check.sh` | `evm-asm-fhsxz.2.4.2.62.3` |
| P256VERIFY | `0x100` | `zkvm_secp256r1_verify` bridge exists; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| CALL/STATICCALL/revert/create interactions with precompiles | mixed | VM call/create/revert semantics plus dispatch | `evm-asm-fhsxz.2.4.2.62.1` |

## Precompile absence frontier

`execution-specs/tests/frontier/precompiles/test_precompile_absence.py`
generates the Amsterdam fixture at:

```text
gen-out/eest-fixtures/zkevm@v0.4.0/fixtures/fixtures/blockchain_tests/for_amsterdam/frontier/precompiles/precompile_absence/precompile_absence.json
```

The cached fixture has three stateless blocks, one each for empty, 31-byte, and
32-byte calldata. For every address from `0x01` through `0x101`, the generator
skips active fork precompiles and emits:

- `SSTORE(address, CALL(gas=0, address=address, args_size=calldata_size))`
  with expected value `1`.
- `SSTORE(address + 2^64, RETURNDATASIZE)` with expected value `0` when
  `RETURNDATASIZE` is valid for the fork.

This means the blocker is not a cryptographic backend. The guest must classify
inactive near-zero addresses as ordinary absent accounts before precompile
dispatch: a zero-value `CALL` to an absent account succeeds, has empty return
data, and leaves `RETURNDATASIZE = 0`. Only active fork precompile addresses
should route to precompile dispatch/gas/output handling.

## ECRECOVER framing contract

ECRECOVER dispatch must mirror
`execution-specs/src/ethereum/forks/frontier/vm/precompiled_contracts/ecrecover.py`
before calling any `zkvm_secp256k1_ecrecover` backend:

- Charge fixed precompile gas `3000`.
- Read exactly four 32-byte words from call data with `buffer_read`
  semantics, so short input is right-padded with zero bytes:
  `message_hash = data[0:32]`, `v = data[32:64]`,
  `r = data[64:96]`, `s = data[96:128]`.
- Interpret `v`, `r`, and `s` as big-endian `U256` values.
- Accept only `v = 27` or `v = 28`; the backend recovery id is
  `v - 27`.
- Reject `r = 0`, `s = 0`, `r >= SECP256K1N`, and
  `s >= SECP256K1N`.
- Rejection and backend recovery failure are successful precompile calls with
  empty return data. The caller's output memory is therefore unchanged except
  for any generic return-data-copy handling done elsewhere.
- Successful backend recovery returns a 64-byte uncompressed public key
  payload. The EVM precompile output is
  `left_pad_zero_bytes(keccak256(pubkey)[12:32], 32)`: twelve leading zero
  bytes plus the 20-byte Ethereum address.

Fixture vectors to carry into runtime opcode tests are in
`execution-specs/tests/frontier/precompiles/test_ecrecover.py`. At minimum,
use `valid_signature_1`:

```text
msg_hash = 18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c
v        = 000000000000000000000000000000000000000000000000000000000000001c
r        = 73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f
s        = eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549
output   = 000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b
```

Also include invalid vectors where `v` is outside `{27, 28}`, `r = 0`,
`s = 0`, `r = SECP256K1N`, and `s = SECP256K1N`; those expected outputs are
empty (`b""`) in the execution-spec fixture and must not synthesize a 32-byte
zero word.

The accelerator bridge source of truth is
[`docs/zkvm-accelerators-interface.md`](zkvm-accelerators-interface.md). The
report's path filters intentionally cover benchmark, fork-specific, and ported
static EEST fixture trees so the matrix stays complete when future fixtures are
added under the existing precompile test naming conventions.
