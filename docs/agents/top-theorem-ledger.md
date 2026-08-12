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
| 4 | Witness DBs (node_db/code_db build + lookups) | `Witness.{NodeDb,CodeDb}` | 4ch8f.21/.28 | todo — assertion vocabulary + lookup models landed (`Evm64/MptAssertions.lean:nodeDbIs`/`nodeDbLookupSpec_eq_build_node_db`, `Evm64/WitnessAssertions.lean:codeDbIs`/`witnessLookupSpec_correct`); routine triples remain | frame against `nodeDbIs`/`codeDbIs`; TreeInsert.lean (slot predicates over arenas) |
| 5 | MPT read/walk/mutation + trie roots | state access | 4ch8f.22/.29/.31/.32 | todo — node vocabulary landed (`Evm64/MptAssertions.lean:mptNodeIs`, `mptNodeKindSpec_rlp`, `hpDecode_hpEncode`); abstract walk semantics needs `rlpToMutableNode` (bead 4ch8f.75.3, blocks .29) | TreeDemo.lean `treeMinFn` (zipper-ghost walk) |
| 6 | Byte/copy + u256 + RLP + SSZ-HTR + bloom leaf families | shared leaves | 4ch8f.12–.20 | in-progress — `u256_is_zero` **done** (`Codegen/Proofs/U256IsZeroSpec.lean:u256_is_zero_deployed_spec`, the playbook acceptance test); `swd_read_u64le` (`Programs/SwdReadU64leSAsm.lean:swdReadU64leFn_spec`) + `sg_load_u32le` (`Programs/SgLoadU32leSAsm.lean:sgLoadU32leFn_spec`) **done** (4ch8f.12.6/.12.3); `swd_write_be8` (`Programs/SwdWriteBe8SAsm.lean:swdWriteBe8Fn_spec`) + `swd_write_be32_u64` (`Programs/SwdWriteBe32U64SAsm.lean:swdWriteBe32U64Fn_spec`) **done** (4ch8f.12.8/.12.7, whileS big-endian writers); `swr_rev_le_be` (`Programs/SwrRevLeBeSAsm.lean:swrRevLeBeFn_spec`) + `bhr_rev_le_be` (`Programs/BhrRevLeBeSAsm.lean:bhrRevLeBeFn_spec`, reuses swr's generic core) **done** (4ch8f.12.4/.12.5, runtime-length reverse-copy, byte-identity pinned); rest is the 3 copy-loop beads (.12.9/.12.1/.12.2) — **start here** | U256IsZeroSpec.lean (straight-line leaf over a converted Program); ChainIdSAsm / howto §6 |
| 7 | Tx decode + signing hashes + secp256k1 recovery | `Transaction` | 4ch8f.25/.38/.39/.40 | todo | accelerator bridges: `Rv64/ZiskAccel.lean` KATs |
| 8 | Interpreter loop + opcode handlers + frames (the seam's guest side) | `ExecutionEngine` → `Block`/`VM` | 4ch8f.10 (strategy), .49–.59 | strategy in-progress — frame layout re-pinned to emitted geometry (#9852) + phase/Own-not-Is audits done (`docs/4ch8f-callframe-audit.md`); open bug beads .72 (blocks .52/.56) and .73; the **generic** `evm_mload_stack_spec_within` over `evmMemoryIs base capacity` is the memory-handler template (`Evm64/MLoad/MemoryRegionStackSpec.lean`; the former concrete `_evmMemoryArea` instantiation was retired in #10526 — the assertion is base-parametrized and must be instantiated per frame) | `Codegen/Proofs/HandlerSpecs.lean` (13/91 handler specs) |
| 9 | Verdict orchestration + validators (BAL, receipts, gas) | `Block` verdict | 4ch8f.36/.37/.41–.47/.61 | todo — the storage/tuple validators read `bv_system_storage_log` post-dispatch while frames clobber it: P0 bug bead .73 blocks .43/.47 | `Codegen/Proofs/CreateDeployedCodeValidSpec.lean` (deployed-spec template) |
| 10 | Real seam instantiation: `execute` = Lean model of `execute_new_payload_request`, tied to obligation 8 | seam | evm-asm-zizr0.2 → 4ch8f.75.10 → .64 | todo — the concrete↔abstract map is drawn in `docs/4ch8f-slstate-specref-correspondence.md` (two-tier; `guestStateCorresponds` waits on the seam types) | docs/4ch8f-specref-port.md §seam |
| 11 | Guest shell: epilogue pipeline, NPR hash-tree-root block, schema gate, verdict stamp, `Entry.run_stateless_guest` body composition | shell | 4ch8f.63 | in-progress — structural half **done**: image `CodeReq` (`Codegen/Proofs/GuestImage.lean:guestImageCodeReq` + generated `GuestImageEntries.lean`, lift via `Rv64/CodeReqExtents.lean`; coverage 24.65% / 84444 B floor ratchet #12057 (was 24.73%/84340 #12021), gaps = beads .63.2–.63.12, docs/4ch8f-guest-image-coverage.md) + stamp audit (decision record §6a; P1 finding .63.1). Pipeline triples todo | `Entry.lean` PR6 stub structure |
| 12 | Top composition: seq the stages, halt-wrap, discharge `run_stateless_guest_spec` | top | 4ch8f.64 | in-progress — the composition is **stated and proved under named phase hypotheses** (#12130): `Codegen/Proofs/TopComposition.lean:runStatelessGuestSound_of_phases` takes six named `Prop`s (`InputDecodePhaseShape`, `WitnessDbPhaseShape`, `HeaderChainPhaseShape`, `ExecPhaseShape`, `StateRootPhaseShape`, `VerdictPublishShape`) over one shared `cr` and yields `runStatelessGuestSound cr L.fuel fr execute`, with `fuel` DERIVED as the sum of six per-phase budgets (#10552 gets its additive shape; `k` is still undefined and is NOT invented). The family is jointly satisfiable (`runStatelessGuestSound_demo`, a trap-at-entry guest over a host-zeroed window), so this is not a vacuous implication. Remaining: discharge the six, plus two defects the audit surfaced (see below) | `cpsTripleWithin_as_cpsHaltTripleWithin`; anti-vacuity checklist = `TopComposition.lean` §1/§2 forcing lemmas |
| 13 | Deployment correspondence: emitted ELF ↔ Lean Program (string equality at scale) | emit | 4ch8f.9 (.9.3 wave live), tj9ts | in-progress | `Codegen/Programs/RlpWalk.lean:rlpWalkInitFunction_eq_verified_prog` |

## Two defects the row-12 audit surfaced (#12130) — both block `.64`, neither is 1–11

1. **The `.63` framing bundle owns no register.** `guestScratch` and
   `guestResidue` are `**`-chains of `anyBytes` memory atoms, so no heap
   satisfying them owns a register (`TopComposition.lean:guestScratch_regFree`,
   kernel-checked by induction). The frame `R` in `cpsHaltTripleWithin` is
   universally quantified, so `r ↦ᵣ v` is an admissible frame for every `r` —
   and therefore `runStatelessGuestSound cr fuel guestFraming execute`
   **entails that the guest leaves every register at its entry value at halt**
   (`guestFraming_forces_regPreserved`), in particular that it can never reach
   its own clean ECALL halt stub from an entry state with `t0 ≠ 0`
   (`guestFraming_clean_halt_forces_entry_t0_zero`). Fix: `scratch` AND
   `residue` must name the guest's register clobber set. Until then the summit
   is not instantiable at `guestFraming` — the statement would be *false*, not
   weak, which is the same failure mode as `wlCallWithinShape` (#12141).
2. **Image-`CodeReq` coverage is a soundness-of-statement issue, not a
   completeness one.** `guestImageCodeReq` pins ~24.65% of `.text`. A `cr` that
   leaves an executed address unpinned admits the state whose code memory is
   exactly `cr`, where the machine is already halted — so the phase hypothesis
   is FALSE (`TopComposition.lean:cpsTripleWithin_needs_entry_code` proves the
   entry-address case). Full-image coverage (beads .63.2–.63.12) is therefore a
   prerequisite for stating the phases at the image, not a nicety.

## Vacuity guards (read before closing any obligation)

- A `.Spec`/triple with an unsatisfiable precondition proves nothing — provide
  or reuse a satisfiability witness (a `guestInputAssertion ** work` satisfiability witness at the top;
  per-routine, an `inputRegion_wf`-style lemma).
- `#print axioms` on every closed obligation: `propext`, `Classical.choice`,
  `Quot.sound` only.
- The bead-closure rubric in AGENTS.md applies: an obligation is `done` only
  when the named theorem exists on `main` and is wired into this ledger.
