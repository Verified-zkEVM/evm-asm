# SSZ — spec correspondence

**Status: live authority.** Method: [`docs/agents/spec-correspondence.md`](agents/spec-correspondence.md).
Sibling instance: [`docs/rlp-spec-correspondence.md`](rlp-spec-correspondence.md).

Read this before claiming an SSZ routine is "done".

## Headline

**SSZ has no executable differential, and most of it has no spec at all.** Of 17
`ssz_*` guest symbols, **6 have specs and all six are leaves**. The entire
merkleization tower — `ssz_merkleize*` → `ssz_hash_tree_root_*` →
`ssz_htr_*` — is emitted, `Program`-converted, drift-guarded, and **completely
unspecified**. `EvmAsm/Stateless/SSZ/HashTreeRoot/` is 8 files / 1791 lines
containing **zero theorems**.

That is the deliverable for this family: a coverage fact, not a divergence.

## Pins

| Artifact | Pin | Where recorded |
|---|---|---|
| `execution-specs` | `e5a8caf1b8055e4d805c7fb169edfa710914b7da` (`tests-zkevm@v0.6.2`) | this repo's gitlink |
| `eth-remerkleable` | **0.1.29** | `execution-specs/uv.lock` |

SSZ is **split** across the taxonomy in method §6, which is part of why it is
hard: the *schemas* (`forks/amsterdam/stateless_ssz.py`) are **vendored** and
therefore citation-checked by `scripts/check-spec-refs.sh`, but the *generic
codec* (serialize / deserialize / merkleize) is the **external** package
`remerkleable`.

## Boundary chosen

None — see below. No boundary has been selected because the precondition for
choosing one is absent.

## Why there is no differential

Unlike RLP, SSZ has **no shared model** to differential against:

- The guest side (`EvmAsm/Stateless/SSZ/{Decode,Encode,HashTreeRoot}/`) was
  written **independently** of `SpecRef/SszCodec.lean` — the port doc calls the
  guest-side files "SAsm emitters and doc-only contracts"
  (`docs/4ch8f-specref-port.md:46`).
- `SpecRef/SszCodec.lean` was itself ported from the consensus-specs
  `simple-serialize.md` **prose**, standing in for `remerkleable` rather than
  being checked against it.

So the RLP shortcut — one definition shared by both towers, so a model-level
differential transfers to the routines — **does not exist here**. Every verdict
below is `inspection`, and the family is deliberately **not** enumerated in
`EvmAsm/Progress/Correspondence.lean`: registering verdicts that cannot carry a
basis better than `inspection` would be the exact unaudited-measurement failure
the method exists to prevent.

**A cheap first step is available.** `SpecRef/SszCodec.lean` has closure 7 with
zero Mathlib roots, so a *model-only* oracle (SpecRef vs `remerkleable`,
ignoring the guest entirely) is inexpensive even though the full three-column
table is not. That would establish the shared-model leg the guest side could
later bridge to.

## Routine table

| Guest routine | Spec | Verdict | Basis | Reference |
|---|---|---|---|---|
| `ssz_pack_bytes` | `sszPackBytesFn_spec` — `Codegen/Programs/SszPackBytesSAsm.lean:535` | agrees | inspection | `remerkleable` chunk packing |
| `eph_u32le` | `ephU32leFn_spec` — `Codegen/Programs/EphU32leSAsm.lean:34` | agrees | inspection | SSZ offset (`uint32` LE) |
| `spw_u32le` | `spwU32leFn_spec` — `Codegen/Programs/SszPayloadWithdrawalsSAsm.lean:32` | agrees | inspection | as above |
| `sws_u32le` | `swsU32leFn_spec` — `Codegen/Programs/SszWitnessStateSAsm.lean:32` | agrees | inspection | as above |
| `read_chain_id` | `readChainIdFn_spec` — `Stateless/SSZ/Decode/ChainIdSAsm.lean:149` | agrees | inspection | `stateless_ssz.py` `SszChainConfig` |
| `read_active_fork` | `readActiveForkFn_spec` — `Stateless/SSZ/Decode/ActiveForkSAsm.lean:73` | agrees | inspection | `stateless_ssz.py` `SszForkConfig` |
| `ssz_merkleize` | — | n/a — unproven | — | `SszCodec.merkleize:306` / consensus-specs |
| `ssz_merkleize_pow2` | — | n/a — unproven | — | `SszCodec.merkleizeReduce:287` |
| `ssz_merkleize_padded` / `_partial` / `_scratch` | — | n/a — unproven | — | `SszCodec.liftToDepth:296` |
| `ssz_hash_tree_root_bytes` | — | n/a — unproven | — | `SszValue.hashTreeRoot:341` |
| `ssz_hash_tree_root_list_bytelist` | — | n/a — unproven | — | as above + `mixInLength:317` |
| `ssz_hb_chunks` / `_mix` / `_partial` | — | n/a — unproven | — | `packBytes` / `mixInLength` |
| `ssz_ltb_child_roots` / `_mix` / `_partial` | — | n/a — unproven | — | as above |
| `ssz_htr_withdrawals` | — (also UNCONVERTED) | n/a — unproven | — | `_withdrawal_to_ssz:242` |
| `ssz_htr_execution_requests` | — (also UNCONVERTED) | n/a — unproven | — | `_execution_requests_to_ssz:392` |
| `ssz_ew_field_roots` | — | n/a — unproven | — | `_witness_to_ssz:452` |
| `ssz_zero_hashes` | — | n/a — unproven | — | `SszCodec.zeroHash:269` |
| `ssz_tx_list_versioned_hashes_match` | — | n/a — unproven | — | blob versioned-hash check |
| `ssz_withdrawal_to_rlp` | helper `swrRevLeBeFn_spec` only | n/a — unproven | — | `_withdrawal_to_ssz` + RLP |

**Counts:** 6 proven leaves · 12 unproven (+ `ssz_withdrawal_to_rlp` partly).

## Gaps and follow-ups

1. **The merkleization tower** — 11 unspecified routines. This is the single
   largest unproven surface covered by any correspondence instance.
2. **A shared SSZ model.** Until the guest side and `SpecRef/SszCodec.lean` meet,
   no SSZ row can rise above `inspection`. The model-only oracle above is the
   cheapest way to start.
3. `ssz_htr_withdrawals` and `ssz_htr_execution_requests` are not even converted
   to `Program`s (`docs/4ch8f-guest-image-coverage.md` lists them UNCONVERTED),
   so they have no drift guard either.

## Reproduce

Nothing to replay — there is no corpus for this family. The table was built by
enumerating `ssz_*` from the linker facts and grepping each symbol tree-wide for
a spec (method §8 steps 1–2). To re-verify a row:

```bash
grep -rn --include='*.lean' -E '^\s*theorem .*<routine-camelCase>' EvmAsm
```
