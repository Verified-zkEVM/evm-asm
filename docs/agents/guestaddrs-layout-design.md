# GuestAddrs layout-application design

## Problem and success criterion

`GuestAddrs.lean` is generated and high-churn: every linked layout change can
rewrite it.  Its import graph is deliberately wide (186 direct importers in
the #12068 measurement), but importer count is not the defect and is not the
success metric.  `Codegen.Layout` is the useful contrast: it has more importers
(332) but only five historical commits.  The defect is a high-fanout,
high-churn concrete-address node.

The success criterion is lower CI wall-clock time for a layout-only change.
The importer count is expected to remain approximately constant because the
same layout concepts still have the same users.

## The seam

The existing `GuestLayout`/`GuestLayoutInstance` split is the right seam, but it
must be completed at the concrete-application boundary.

### Abstract layer

Define small layout records by domain rather than one flat record:

- text/PC and relocation targets;
- data arenas and tables;
- call-frame layout;
- MPT/RLP and witness arenas;
- any other group whose fields have a coherent owner.

Each group lives in its own schema module.  A converted leaf exposes
`*_prog_of (L : GroupLayout)` for only the group(s) it uses.  Its `la`/`jal`
values go through `AsmReloc` and the abstract fields; its symbolic emission and
`GuestLayout.zero` guards remain layout-independent.  This extends the proven
shape already used by `HashBridgeProg`, `BloomAddValueProg`, `U256Prog`, and
the other current leaves.

Do not create a single 1125-field `GuestLayout`: the 24-field pilot already
shows that the mega-flat form fails elaboration.  Grouping is a measured
elaboration constraint, not a stylistic preference.

### Concrete application layer

One generated `GuestLayoutInstance`/`GuestConcrete` module imports
`GuestAddrs.lean`, binds the grouped records, and applies the abstract leaves
to the concrete layout.  It is the only ordinary source module that consumes
the generated address table.  It re-exports concrete Programs for the final
guest/link boundary and for deliberately concrete PC/address proofs.

Do **not** keep a per-routine bridge that imports the concrete instance on a
high-fanout path.  That merely moves the dependency: every bridge importer
would still rebuild when the instance changes.  High-fanout specs and proofs
consume the abstract `*_prog_of` declarations (or `GuestLayout.zero` for
symbolic rendering).  Existing concrete names can be retained as aliases in
the final concrete module while callers migrate.

Dispatch, `GuestImageEntries`, progress/registry files, and linker/check
drivers are intentional concrete roots.  They need linked addresses and are
not accidental exceptions.  Everything else must cross the abstract seam.

## Migration and breakage

For each direct concrete user:

1. split the layout-independent declaration/proof from its concrete
   application;
2. replace `GuestAddrs.foo` with the appropriate domain field;
3. parameterise address-valued statements where the proof is genuinely
   layout-generic, and move linked-PC assertions to the concrete root where it
   is not;
4. preserve the existing public name through a concrete alias until all
   callers use the abstract declaration.

The migration is expected to touch many files once.  That cost is distinct
from the recurring layout cost.  The generated address table remains the
artifact consumed by the linker and its existing drift/byte-identity gates;
the reshape changes the dependency graph, not emitted bytes or address facts.

Add a blocking import-graph gate: outside the generator, concrete application,
Dispatch, artifact/registry roots, and named link drivers, a source file may not
import or reference `GuestAddrs`.  The gate is what keeps the seam from eroding
after this PR; a prose convention is not enough.

## Operational schema freeze

After the migration, the grouped layout schemas are frozen for ordinary
relayouts.  A normal layout change regenerates only `symbol-addresses.tsv`,
`GuestAddrs.lean`, and the concrete application module, followed by the normal
link and drift gates.

If a routine needs a new address field, the owner of the layout schema must
make an explicit schema-change PR.  That PR must:

- add the field to the smallest domain record;
- update the generator and concrete instance together;
- migrate all users to that group;
- update the import-graph allowlist only for the concrete roots; and
- include the paired CI-time measurement below.

The schema owner/maintainer enforces this through review, while the import gate
enforces the no-new-concrete-edge part in CI.  A field is never added ad hoc to
silence a build error, and a new field is batched with the next schema-change
PR rather than turning every relayout into an interface rebuild.

## Predicted CI effect and measurement

Prediction, stated before implementation: after the migration, a layout-only
relink should leave abstract leaves and proofs' oleans untouched and rebuild
only `GuestAddrs`, the concrete application, and final link/check modules.
Therefore the compile critical path and CI wall-clock should fall materially,
even though the 186-importer count does not move.  If high-fanout concrete
bridges remain and the measured time is unchanged, the reshape has only moved
churn and must be rejected.

Measure with paired commits on the same runner, ref, workflow, and cache
policy.  Each pair carries exactly one generated-layout change and no source
change: one commit uses the current architecture and one uses the reshaped
architecture.  Record both workflow wall-clock and the compile job's critical
path, plus the rebuilt-module list and cache mode.  Repeat three times and
compare medians.  A non-positive or statistically indistinguishable wall-time
change rejects the design; importer count is only explanatory data, never the
acceptance metric.
