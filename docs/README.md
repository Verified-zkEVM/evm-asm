# docs/ — what lives here and how it's kept

Three kinds of documents, with different retention rules:

1. **Live authority** — pages that answer current questions and are kept
   correct: the `4ch8f-*` strategy/coverage/audit/correspondence set,
   `sasm-design.md`/`sasm-howto.md`, `notable-specs.md`,
   the `*-spec-correspondence.md` instance set, `zkvm-*-interface.md`, the `eest-*`
   testing/frontier set, and everything under [`docs/agents/`](agents/)
   (routed from `AGENTS.md` "Deep references"). If one of these is wrong,
   fix it — agents act on them.
2. **Design records** — the `*-design.md` / `*-survey.md` / `*-plan.md` /
   `*-audit.md` one-shots that shaped a landed feature. They are kept when
   (a) code or a live doc links to them as provenance, or (b) they record a
   decision/measurement you'd otherwise re-derive (capacity tables, perf
   measurements, deferral hand-offs). They describe the state of the world
   *at their date* — trust the Lean sources and drift-guard scripts over any
   number found here. When one is **superseded**, it gets a status banner
   pointing at the live authority (see `call-frame-memory-layout.md`) or is
   deleted.
3. **Nothing else.** Scratch analysis belongs in beads (`bd comment`), PR
   descriptions, or the session scratchpad — not here.

Retention rule of thumb: a doc earns deletion (git history preserves it) when
its named work has landed, nothing links to it, and its content is either
recorded elsewhere or describes a surface that no longer exists. Periodic
sweeps are welcome — check inbound references (`grep -rl <name>.md`) and the
landed status of the named deliverable before removing, and never leave a
dangling link behind.

Naming: keep the established patterns — `4ch8f-<topic>.md` for the
verify-guest epic, `<issue-or-bead>-<topic>.md` for issue-scoped work,
`agents/<topic>.md` for agent-routed reference pages.
