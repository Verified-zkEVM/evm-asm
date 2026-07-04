# Top-theorem ledger — `run_stateless_guest_spec`

The single page that says **what remains to prove** for the north-star theorem
and **where each piece plugs in**. Keep it updated whenever an obligation
changes status (same discipline as PLAN.md).

## The statement

`EvmAsm/Stateless/EntrySpec.lean` defines the shape (bead `evm-asm-4ch8f.8`);
the full decision record — trust boundary, one-sided direction, rejected
alternatives, review synthesis of PRs #9733/#9734 — is
**docs/4ch8f-top-spec.md**.

```
runStatelessGuestSound cr fuel fr execute :
  ∀ input, input.length ≤ MAX_INPUT_BYTES →
    cpsHaltTripleWithin fuel GUEST_ENTRY cr
      (guestInputAssertion input ** fr.scratch)
      (guestOutputSound execute input ** fr.residue)
```

- **One-sided, pinned observation window**: `guestOutputSound` = "the 40-byte
  window at `OUTPUT_ADDR` (`out.length = OUTPUT_CLAIM_BYTES` pinned inside the
  post) is a sound claim: if the validation byte `OUTPUT[32]` is 1, then
  `SpecAccepts` — the input deserializes, `verify_stateless_new_payload`
  succeeds under the seam, and `OUTPUT[0..32)` is the spec's NPR root".
  False-rejects are allowed; false-accepts are not. The pinned length exists
  because an existential output judged by a self-delimiting decode is
  vacuously dischargeable (#9734 review).
- **Fidelity**: `runStatelessGuestFaithful` (full output = the spec's
  serialized result, byte-for-byte) is stated but a declared NON-goal for
  `.64` v1 (decision record §1).
- **Non-vacuity**: kernel `#guard`s pin the flag/root offsets to the SpecRef
  encoder and witness `SpecAccepts` end-to-end on the sanity pipeline; the
  `GuestFraming.scratch_sat` witness rules out an unsatisfiable-precondition
  discharge, and `fr.residue` gives the entry-owned resources a home at halt
  (without it the triple is unprovable — #9733 review defect, fixed).
- **Seam**: parameter `execute : ExecutionSeam` — the `.10` interpreter model
  closes it.

The final theorem (bead `evm-asm-4ch8f.64`) instantiates the
`(cr, fuel, fr, execute)` quadruple: the COMPOSED guest image `CodeReq`
(bead .63, from the wave-.9 conversions — today's `Entry.run_stateless_guest`
is still the PR6 stub), the gas-derived step cap, the `.6` work-region
bundle, and the real seam.

## How a leaf proof plugs in

1. **Port a routine** with the SAsm DSL (docs/sasm-howto.md §7; playbook:
   docs/agents/port-playbook.md). Deliverable: `<routine>Fn_spec : (<routine>Fn …).Spec …`
   plus `<routine>_verified : Program` with `#guard` pins.
2. **Package as callee**: `Fn.toHandle` / `Fn.toHandleR` (ra-spill), widened via
   `FnHandle.widenRw`/`widenRo` to the caller's regions.
3. **Compose**: callers verify against handles (`Stmt.call`/`callReg`), the
   spine composes with `cpsTripleWithin_seq`/`cpsCallWithin`, and the top wraps
   with `cpsTripleWithin_as_cpsHaltTripleWithin` (CPSSpec.lean:897) once the
   halt stub is in the CodeReq.
4. **Deploy**: swap the routine into `Entry.run_stateless_guest` (or the
   Codegen program) via `emitProgram` + string-equality correspondence
   (`scripts/asm_to_program.py`, bead 4ch8f.9), then EEST A/B
   (sasm-howto §7.6).

## Obligation table

Status: `todo` / `in-progress (bead)` / `done (file:theorem)`.

| # | Obligation | Pipeline stage | Bead(s) | Status | Exemplar to copy |
|---|---|---|---|---|---|
| 0 | Statement shape (`runStatelessGuestSound`) | — | 4ch8f.8 | **done** (`EvmAsm/Stateless/EntrySpec.lean`; decision record docs/4ch8f-top-spec.md) | — |
| 1 | Canonical `work` bundle (working-RAM anyBytes tiling per RegionMap + phase model) + a satisfiability witness for `guestInputAssertion input ** work` | entry | 4ch8f.63 | **done** (`Codegen/Proofs/GuestImage.lean:guestFraming`, witness `guestScratch_sat` via `Rv64/MemSat.lean`; NOTE `MAX_INPUT_BYTES` repaired to `0x37FFFFF8` — decision record §2a) | — |
| 2 | Input decode: SSZ offset chase over the schema-prefixed payload | `deserialize_stateless_input` | 4ch8f.27 | in-progress — `read_chain_id`/`read_active_fork` **done** (`SSZ/Decode/ChainIdSAsm.lean:readChainIdFn_spec`, `ActiveForkSAsm.lean:readActiveForkFn_spec`); `decode_validation_bit`, `decode_header_count`, extractors todo | ChainIdSAsm.lean |
| 3 | Header validation family | `validate_headers` | 4ch8f.26/.33/.34 | todo | ChainIdSAsm (byte-wise reads), ClzSAsm (branchy leaf) |
| 4 | Witness DBs (node_db/code_db build + lookups) | `Witness.{NodeDb,CodeDb}` | 4ch8f.21/.28 | todo (unblocked by RegionMap) | TreeInsert.lean (slot predicates over arenas) |
| 5 | MPT read/walk/mutation + trie roots | state access | 4ch8f.22/.29/.31/.32 | todo | TreeDemo.lean `treeMinFn` (zipper-ghost walk) |
| 6 | Byte/copy + u256 + RLP + SSZ-HTR + bloom leaf families | shared leaves | 4ch8f.12–.20 | in-progress — `u256_is_zero` **done** (`Codegen/Proofs/U256IsZeroSpec.lean:u256_is_zero_deployed_spec`, the playbook acceptance test); `swd_read_u64le` (`Programs/SwdReadU64leSAsm.lean:swdReadU64leFn_spec`) + `sg_load_u32le` (`Programs/SgLoadU32leSAsm.lean:sgLoadU32leFn_spec`) **done** (4ch8f.12.6/.12.3); rest is the remaining `port: verify …` beads — **start here** | U256IsZeroSpec.lean (straight-line leaf over a converted Program); ChainIdSAsm / howto §6 |
| 7 | Tx decode + signing hashes + secp256k1 recovery | `Transaction` | 4ch8f.25/.38/.39/.40 | todo | accelerator bridges: `Rv64/ZiskAccel.lean` KATs |
| 8 | Interpreter loop + opcode handlers + frames (the seam's guest side) | `ExecutionEngine` → `Block`/`VM` | 4ch8f.10 (strategy), .49–.59 | strategy in-progress | `Codegen/Proofs/HandlerSpecs.lean` (13/91 handler specs) |
| 9 | Verdict orchestration + validators (BAL, receipts, gas) | `Block` verdict | 4ch8f.36/.37/.41–.47/.61 | todo | `Codegen/Proofs/CreateDeployedCodeValidSpec.lean` (deployed-spec template) |
| 10 | Real seam instantiation: `execute` = Lean model of `execute_new_payload_request`, tied to obligation 8 | seam | 4ch8f.10 → .64 | todo | docs/4ch8f-specref-port.md §seam |
| 11 | Guest shell: epilogue pipeline, NPR hash-tree-root block, schema gate, verdict stamp, `Entry.run_stateless_guest` body composition | shell | 4ch8f.63 | in-progress — structural half **done**: image `CodeReq` (`Codegen/Proofs/GuestImage.lean:guestImageCodeReq` + generated `GuestImageEntries.lean`, lift via `Rv64/CodeReqExtents.lean`; coverage 23.76%, gaps = beads .63.2–.63.12, docs/4ch8f-guest-image-coverage.md) + stamp audit (decision record §6a; P1 finding .63.1). Pipeline triples todo | `Entry.lean` PR6 stub structure |
| 12 | Top composition: seq the stages, halt-wrap, discharge `run_stateless_guest_spec` | top | 4ch8f.64 | todo (blocked on 1–11) | `cpsTripleWithin_as_cpsHaltTripleWithin` |
| 13 | Deployment correspondence: emitted ELF ↔ Lean Program (string equality at scale) | emit | 4ch8f.9 (.9.3 wave live), tj9ts | in-progress | `Codegen/Programs/RlpWalk.lean:rlpWalkInitFunction_eq_verified_prog` |

## Vacuity guards (read before closing any obligation)

- A `.Spec`/triple with an unsatisfiable precondition proves nothing — provide
  or reuse a satisfiability witness (a `guestInputAssertion ** work` satisfiability witness at the top;
  per-routine, an `inputRegion_wf`-style lemma).
- `#print axioms` on every closed obligation: `propext`, `Classical.choice`,
  `Quot.sound` only.
- The bead-closure rubric in AGENTS.md applies: an obligation is `done` only
  when the named theorem exists on `main` and is wired into this ledger.
