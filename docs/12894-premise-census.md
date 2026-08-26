# 12894 premise-first census

This is the theorem-statement follow-up to the reachability pilot.  The
question is which `.proven` whole-routine contracts carry a stateful entry
premise that a notes-only survey can miss.  The census is anchored at
`origin/main` `d9c90f0e3` (the branch base); no Lean or guest source was changed.

## Method and denominator

`scripts/proven_premise_scan.py` starts from the `.proven` rows in
`EvmAsm/Progress/Routines.lean`, locates each referenced theorem declaration,
and scans its statement.  It also expands assertion definitions named by the
statement, rather than treating the theorem's notes as a proxy for its
premises.  The run produced 202 registry row instances and 201 unique theorem
names.  Its required positive control is the known
`addressFromPubkey_spec_within` row; the scan fails if it cannot expand
`afpCallerPre` and find the fixed zero scratch premise.

The raw detector reports six zero-filled regions.  Four are not stateful entry
gates: `rlp_content_to_u64_strict_at_guest_spec_within`,
`rlp_content_to_u256_be_strict_at_guest_spec_within`,
`secfZero32FlatEntry_spec`, and `pointDouble_spec` mention zero output bytes in
their postcondition (or an output branch), not a required pre-state.  Fixed
global rows for frame depth, read/write discard, dispatcher gas, MPT cache reset
and BN254 allotment permit arbitrary incoming cell values; they are therefore
not zero/content gates.  `blsgLtP` and `bnfLtP` use immutable `globalConst`
moduli.  These are exclusions, not unexamined rows.

After that semantic classification, two `.proven` theorem statements carry a
stateful bytes-region premise:

| routine / theorem | expanded premise | source and use | status |
| --- | --- | --- | --- |
| `address_from_pubkey` / `addressFromPubkey_spec_within` | `bytesRegion afpDigestPtr (List.replicate 32 0)` | `AddressFromPubkeySpec.lean:1352-1363`, consumed by the theorem at `:1418-1448`; `afpDigestPtr = 0xaa8453a0` | measured inverse violation: first call only |
| `zkvm_keccak256_segments` / `zkvm_keccak256_segments_spec_within` | `bytesRegion outputBase (List.replicate 32 0)` | `HashBridgeKeccakSegTop.lean:208-217`, consumed at `:808-828` (the pre appears at `:825`) | measured covered on the valid split |

The first row is the positive control: its fixed scratch is written by the
keccak callee and the routine does not clear it.  The second row is deliberately
not called a defect merely because it has the same syntactic shape: `outputBase`
is a caller-supplied buffer, so its callsite must be measured.

## KSS callsite and multiplicity census

In the linked ELF SHA-256
`8618ff3dbc0183563a1f00dbc2bed277e8376baef77150182db564a2e0084739`, `nm`
resolves `zkvm_keccak256_segments` at `0x80003574`.  There are exactly two
production direct calls:

* `tx_signing_hash + 316`: call at `0x8002be64`, return PC `0x8002be68`;
* `tx_signing_hash_legacy_eip155 + 424`: call at `0x8002c044`, return PC
  `0x8002c048`.

The transitive production callers are `eip7702_authorization_signing_hash`
through `tx_signing_hash`, and `tx_pubkey_signature_material`, which invokes
both the current and legacy signing-hash paths.  The two direct KSS callsites
are therefore not two independent routines; they are two arms of the signing
hash family.

## KSS inverse measurement

The valid half of the deterministic seed-12894 sample contains 100 rows.  The
entry pilot reached KSS at `0x80003574` on 94/100 rows and matched the first
return PC on all 94.  The inverse probe records `a2/x12` at the entry (the
`outputBase` argument), then reads all four 8-byte words at that dynamic address
at the entry.  It is therefore a measurement of the exact 32-byte pre-state,
not a read after KSS has written its digest.

| population | rows | KSS reached | first output zero | second KSS entry | second output zero |
| --- | ---: | ---: | ---: | ---: | ---: |
| valid | 100 | 94 | 94 | 5 | 5 |

All five repeated entries also had all four dwords zero.  The first output
pointer was `0xa3a4bfe0` on all 94 reached rows; on the five repeated rows the
second pointer was the same in three cases and was re-pointed to `0xb8a1e518`
in two.  Thus both reuse and re-pointing cases were observed, and neither
violated the premise.  The 6 valid rows with no KSS entry are not evidence
against the contract; they simply do not reach this path in the sample.

The register-address inverse instrument is
`scripts/reachability_inverse_regmem.py`; the raw valid-split TSV is
`/tmp/12894-pilot-artifacts/kss-inverse-valid.tsv`.  To check whether the five
repeated entries were merely a thin sample, the same instrument was rerun on
the complete 200-row sample (100 valid and 100 invalid), with the same linked
ELF and runner.  It reached KSS on 115/200 rows; all 115 first entries had a
zero output region, and all 11 second entries had a zero output region.  Of
those 11 repeats, nine reused `0xa3a4bfe0` and two were re-pointed to
`0xb8a1e518`; all 11 still satisfied the premise.  The raw widened TSV is
`/tmp/12894-pilot-artifacts/kss-inverse-all.tsv`.  The positive-control address
inverse remains in `docs/12894-address-from-pubkey-inverse.md`.

The zeroing writer is upstream, not KSS itself.  `tx_signing_hash` copies its
caller-supplied `a4` to `s4` and passes it as `a2/x12` at the KSS call; the
legacy routine similarly copies `a3` to `s3` and passes it as `a2/x12`.  Neither
body writes the output region before KSS.  In the linked image,
`tx_pubkey_signature_material` at `0x8002c07c` clears all sixteen dwords of its
material block (`0x8002c0b8`--`0x8002c0f4`) before passing `s3+80` to either
signing-hash arm.  The EIP-7702 route is likewise cleared by
`eip7702_authorization_recover_address` at `0x80029540`: its loop at
`0x8002957c`--`0x80029590` clears all sixteen scratch dwords before passing
`s3+80` at `0x800295c0` through `eip7702_authorization_signing_hash`.
Thus the observed coverage is a caller obligation that is currently met on
all production paths, rather than a self-clearing invariant of KSS.

## Conclusion

The theorem-text census finds two stateful zero-region candidates, not one.  The
`address_from_pubkey` candidate is a real first-call-only coverage defect, as
shown by its 114/114 repeated-entry inverse measurement.  The KSS candidate is
covered on every measured invocation: 115/115 first entries and 11/11 second
entries in the widened sample, including nine repeated pointers and two
re-pointed pointers.  It is therefore a confirmed-covered result, not a second
defect.  The selection heuristic is now explicit: screen for the **absence of a
re-zeroing writer between invocations**, not for the syntactic shape of the
premise or for storage class (fixed global versus parameter).  KSS is covered
because its callers perform that write; the obligation is still fragile if a
new caller omits it.  There is no measured basis here to retier or rewrite the
KSS theorem, though an explicit caller proof would make the currently implicit
obligation durable.
