# Stateless Guest Input Contract

This note is for changes to `stateless_guest`, the EEST converter, and any
RISC-V code that reads the stateless payload. The invariant is simple: the zkVM
guest must consume the same stateless input content as execution-specs
`run_stateless_guest`.

## Source Of Truth

Execution-specs Amsterdam consumes a schema-prefixed SSZ byte string:

- `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`
  `run_stateless_guest(input_bytes)` calls `deserialize_stateless_input`, then
  `verify_stateless_new_payload`.
- `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`
  `deserialize_stateless_input` requires the two-byte big-endian schema id
  `0x0001`, decodes the remaining bytes as `SszStatelessInput`, and converts it
  with `ssz_to_stateless_input`.
- `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py` defines
  `SszStatelessInput` as:
  `new_payload_request`, `witness`, `chain_config`, and `public_keys`.

The zkVM input may have a host-transport wrapper, but the payload behind that
wrapper must be those same schema-prefixed SSZ bytes. Today ziskemu input files
use the host layout from `scripts/stateless-gen-input.py` and
`scripts/eest-stateless-to-input.py`:

```text
u64_le payload_len || schema_prefixed_stateless_input || zero padding to 8 bytes
```

The leading `u64_le payload_len` and trailing alignment padding are ziskemu host
transport, not execution-specs input content. The guest-visible stateless
payload starts at the bytes counted by that length.

## EEST Fixture Conversion

EEST zkevm fixtures already carry execution-specs-compatible fields in each
block:

- `statelessInputBytes`: schema-prefixed SSZ `StatelessInput`.
- `statelessOutputBytes`: canonical SSZ `StatelessValidationResult`.

`scripts/eest-stateless-to-input.py` must preserve `statelessInputBytes`
byte-for-byte when packing ziskemu inputs. It may derive manifest metadata such
as `input_len`, `succ_bit`, `block_gas_limit`, labels, and fixture paths for
scheduling/reporting, but those derived manifest columns are not extra guest
runtime content.

Do not rebuild the stateless input from JSON fixture side channels when the
fixture already provides `statelessInputBytes`. Rebuilding can silently diverge
from the execution-specs path, especially for fields that affect payload RLP,
requests, withdrawals, block access lists, witness code/state/header lists,
public keys, or future SSZ schema extensions.

## RISC-V Guest Rule

RISC-V programs should decode from the schema-prefixed SSZ payload, not from a
parallel hand-built format. When a validation step needs a value that
execution-specs derives from `StatelessInput`, derive it from the same payload
bytes in the guest. Examples:

- Header checks read `new_payload_request.execution_payload` from the SSZ
  payload.
- Witness-backed state/code/header reads use `witness.state`, `witness.codes`,
  and `witness.headers` from the SSZ payload.
- BAL replay and gas-derived BAL limits use
  `new_payload_request.execution_payload.block_access_list` and the block gas
  limit from that same payload.
- EIP-7934 block RLP size checks must reconstruct or measure the block from the
  guest's SSZ payload, matching the execution-specs validation path, rather than
  trusting a JSON-side RLP length or fixture label.

A new derived field is acceptable only if it is an internal cache of data that
is already present in the schema-prefixed SSZ payload. The PR adding it should
state the source SSZ path and keep the original payload available to the guest.

## Quick Audit Checklist

Before changing `stateless_guest` input construction or decoding, check:

1. Does execution-specs `run_stateless_guest` receive the same
   schema-prefixed SSZ bytes?
2. Is any additional ziskemu input data only transport or a cache derivable from
   those bytes?
3. If a manifest column influences launch decisions, is it derived from
   `statelessInputBytes` and never treated as authoritative guest data?
4. If a guest check rebuilds RLP, roots, BAL limits, or request data, is it
   reading the source fields from the SSZ payload?
5. If the SSZ schema changes, have the offsets and caps been rechecked against
   `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`?
