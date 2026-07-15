# sd13v bounded builder coverage ledger

This is the pre-wiring evidence ledger for the bounded, fixed-allocation
post-state MPT builder.  The builder is temporarily routed only on the
unmerged validation branch; no production wiring claim exists until every row
marked `required` has a clean-build result and the routed full-guest evidence
below exists.

## Route guard

The working branch temporarily routes `BlockVerdictStateRoot.lean` through
`mpt_bounded_state_root` solely to validate the full guest.  It is neither
merged nor a wiring claim: the route remains gated on the complete evidence
below and must be removed or retained only in the reviewed wiring increment.

## Structural KATs

| Shape | Evidence | Status |
|---|---|---|
| Node classification | `codegen-zisk-mpt-bounded-classify-node-check.sh` | clean-green |
| Branch raw-reference capture | `codegen-zisk-mpt-bounded-capture-branch-refs-check.sh` | clean-green |
| Extension decode bound/path | `codegen-zisk-mpt-bounded-decode-extension-check.sh` | clean-green |
| Leaf decode bound/path | `codegen-zisk-mpt-bounded-decode-leaf-check.sh` | clean-green |
| Canonical branch encoding | `codegen-zisk-mpt-bounded-encode-branch-check.sh` | clean-green |
| Witness-only hashed reference resolution | wired full-guest fixture below | routed green |
| Hashed-child frame opening | wired full-guest fixture below | routed green |

The following state-root KATs record the current coverage and blockers:

| Shape | Current result |
|---|---|
| Extension merge | EEST-unreachable (0 of 48,111 fixtures); correctness is a tracked proof obligation |
| Leaf group | clean-green after reloading the clobbered post-call path length |
| Extension split | clean-green |
| Leaf split | clean-green after fixing the branch-prefix scratch stack alias |
| Terminal leaf split | clean-green |
| Sort probe | BuildUnit link failure: missing builder/extension dependencies |

The two deferred probe scripts exercise the same Keccak body successfully
covered by `zisk_witness_lookup_by_hash`, but their standalone ELF fails in
ziskemu despite matching the oracle probe's scratch-region mapping and
Keccak PCs.  They are not counted as green or as builder failures.

## Static handler audit

Every concrete `mptBounded*Function` handler was scanned for writes to
callee-saved registers `s0` through `s11`; each written register has both an
SP-relative prologue save and matching epilogue restore.  This includes the
two repaired `s6` cases (`mpt_bounded_encode_branch` and
`mpt_bounded_collapse_branch_leaf`).  `mptBoundedBuilderFrontEndFunction` is a
textual concatenation, not a callable ABI frame, and is deliberately excluded
from that check.

## Required routed coverage before wiring

The wiring increment must add a full-guest fixture named
`sd13v-routed-hashed-child-update`: an existing state trie whose modified
account lies below a hashed child reference.  Its A/B run must demonstrate
that the routed `mpt_bounded_state_root` invokes both
`mpt_bounded_resolve_witness` and `mpt_bounded_open_child_frame`, and matches
the reference guest verdict/root.  A generic randomized corpus does not by
itself discharge this row; the fixture name and trace/counter evidence must be
recorded with the routed A/B result.

### Routed hashed-child result

On unmerged `test/sd13v-routed-builder`, the full `stateless_guest` emitted
with the bounded route was run under ziskemu against manifest row `00000` of
`gen-out/eest-run/run-20260715T141913Z-431051/manifest.tsv`
(`account_write_authority_is_recipient`, non-zero value).  Its 69-byte public
output matched the EEST oracle byte-for-byte.  Non-perturbing execution-count
disassembly recorded `mpt_bounded_state_root=1`, `mpt_bounded_rebuild_subtree=7`,
`mpt_bounded_resolve_witness=7`, `mpt_bounded_open_root_frame=1`, and
`mpt_bounded_open_child_frame=6`.  This satisfies the named fixture's
hashed-child resolver/open-child requirement; it does not discharge the
separate split/merge rows below.

The emitted builder also carries zero-byte ELF function metadata for
`mpt_bounded_rebuild_subtree` and the internal
`mpt_bounded_extension_merge_probe` arm.  With
`ziskemu -S -X --roi-filter 'mpt_bounded_(rebuild_subtree|extension_merge_probe)'`
the latter gives a compact, direct in-situ merge-coverage signal.  The current
hashed-child fixture and the screened clear-delegation fixtures execute the
rebuild handler but not this merge arm.

## Condition-1 mutation-shape inventory

This inventory is the completeness gate for the replacement semantics of the
spec `mpt_set`/patch path. A green primitive does **not** make a mutation shape
covered. `blocker` means the shape is listed but cannot yet support a wiring
claim; it is not an early-bail allowance.

| Spec mutation shape | Evidence | State |
|---|---|---|
| Insert into an empty branch slot | `branch-insert`, `missing-group` | green |
| Insert that splits an existing leaf into a branch | `leaf-multidigit`, `leaf-split`, `leaf-group`, and `terminal-leaf-split` clean-green | green |
| Insert that splits an extension | `extension-multidigit`, `extension-group`, and `extension-split` clean-green | green |
| Add or replace a child of an existing branch | `branch-insert` covers add; no dedicated replace-child KAT yet | missing dedicated KAT |
| Update an existing leaf value at the same key | `state-root` exact-leaf replacement | green |
| Delete a sole leaf | `root-delete` | green |
| Delete from a multi-child branch without collapse | `branch-delete` | green |
| Delete and collapse a branch to a leaf | `branch-collapse-leaf` | green |
| Delete and collapse a branch to an extension | `branch-collapse-extension` | green |
| Delete and collapse a branch around a surviving branch | `branch-collapse-branch` | green |
| Merge/collapse adjacent extensions | EEST-unreachable (0 of 48,111 fixtures); handler is implemented and correctness is a proof obligation | proof obligation |
| Resolve a hashed pre-state child during any shape | named `sd13v-routed-hashed-child-update` full-guest fixture | deferred to routed A/B |

The extension-merge handler is present and non-conservative: after decoding a
rebuilt extension child, `.Lmbrs_ext_merge` checks the combined bounded path
length, appends the child path, transfers its raw child reference, and invokes
`mpt_bounded_encode_extension`.  Its failure exits are only malformed/bounds
checks, not a shape-specific early bail.  Its correctness is therefore a
tracked proof obligation rather than an EEST test blocker.

Condition 1 still requires the dedicated replace-child KAT, final routed A/B
evidence, and retirement of the legacy NodeDb route before any merge or
verdict-routing claim.

### NodeDb route audit

The routed outer account-root call is `mpt_bounded_state_root`; there is no
remaining `mpt_state_root_ins` call in `BlockVerdictStateRoot.lean`. Its
resolver uses only the immutable witness and its rebuilding helpers retain raw
child references without appending to the mutable NodeDb.

This does **not** retire the legacy NodeDb from the full verdict path. Two live
callers remain and make the P0 arena-overflow issue `qgecl` open:

* `BalAccountApplyPostFields` replays one account's storage descriptors with
  `mpt_state_root_ins`, then its deletes with `mpt_delete_acc`. One account
  plus 14,564 distinct storage slots fits in 29.13M of the 200M BAL gas limit.
  A valid 532-byte all-hashed root branch is re-appended for each update at a
  576-byte NodeDb stride, so those updates alone require 8,388,864 bytes,
  exceeding the 8 MiB arena.
* `mpt_indexed_trie_root_small` falls back to `mpt_state_root_ins` for a
  transaction root with at least 129 values. The fallback accepts large
  transaction values; 1,024 approximately-8,150-byte values fit below the
  8 MiB RLP block-size limit, while their encoded leaf NodeDb records alone
  exceed 8 MiB. Its `mset_node` caller buffer is only 2,048 bytes although the
  leaf encoder accepts values up to 16,000 bytes, an earlier overflow risk.

Withdrawals are SSZ-bounded to 16 entries and beacon changes to at most two
descriptors, so those two callers remain below the arena bound. The sd13v
account-root builder is therefore a validated partial improvement, not a
complete qgecl closure. A maintainer scope decision is required before adding
a bounded storage/indexed-root replacement or merging verdict routing.
