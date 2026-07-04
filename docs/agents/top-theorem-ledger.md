# Top-theorem ledger — `run_stateless_guest_spec`

The single page that says **what remains to prove** for the north-star theorem
and **where each piece plugs in**. Keep it updated whenever an obligation
changes status (same discipline as PLAN.md).

## The statement

`EvmAsm/Stateless/EntrySpec.lean` defines the shape (bead `evm-asm-4ch8f.8`,
decisions recorded in the file header):

```
RunStatelessGuestSound execute guest nSteps entry fr :
  ∀ payload,
    cpsHaltTripleWithin nSteps entry (CodeReq.ofProg entry guest)
      (inputRecordAt payload ** fr.scratch)
      (∃ obs, outputBytesAt obs ** ⌜obs.length = 40⌝ **
              ⌜GuestOutputSound execute payload obs⌝ ** fr.residue)
```

- **One-sided, pinned observation window**: `GuestOutputSound` = "if the flag
  byte at fixed offset 32 of the 40-byte window is 1, then
  `SpecRef.run_stateless_guest payload execute` succeeds and agrees on the
  observed root+flag bytes". False-rejects are allowed; false-accepts are not.
  The window length is pinned inside the postcondition — an existential output
  judged by a self-delimiting decode is vacuously dischargeable (PR #9734
  review). Full-serialization equality is the separate `GuestOutputFaithful`
  clause (guest-shell bead); completeness is `GuestOutputComplete` (not
  required).
- **Non-vacuity**: `GuestFraming.scratch_sat` forces a satisfiability witness
  for the precondition — an obligation cannot be closed with an unsatisfiable
  scratch assertion.
- **Seam**: `execute : SpecRef.ExecutionSeam` is the EVM re-execution cut
  (docs/4ch8f-specref-port.md). The final theorem instantiates it with the
  Block/VM model.

The final theorem (bead `evm-asm-4ch8f.64`):

```
theorem run_stateless_guest_spec :
  RunStatelessGuestSound <real seam> <composed guest image> <fuel> <entry> <framing>
```

The `guest` instantiation is the COMPOSED guest image the codegen emits
(beads 4ch8f.63/.64) — today's `Entry.run_stateless_guest` is still the PR6
stub; the statement is parameterized so leaf work is instantiation-agnostic.

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
| 0 | Statement shape (`RunStatelessGuestSound`) | — | 4ch8f.8 | **done** (`EvmAsm/Stateless/EntrySpec.lean`) | — |
| 1 | Canonical `GuestFraming` (scratch = working-RAM anyBytes tiling per RegionMap + phase model; `scratch_sat` witness) | entry | 4ch8f.63 | todo | `SAsm/PhaseSplit.lean` (`anyBytes`), `Codegen/RegionMap.lean` |
| 2 | Input decode: SSZ offset chase over the schema-prefixed payload | `deserialize_stateless_input` | 4ch8f.27 | in-progress — `read_chain_id`/`read_active_fork` **done** (`SSZ/Decode/ChainIdSAsm.lean:readChainIdFn_spec`, `ActiveForkSAsm.lean:readActiveForkFn_spec`); `decode_validation_bit`, `decode_header_count`, extractors todo | ChainIdSAsm.lean |
| 3 | Header validation family | `validate_headers` | 4ch8f.26/.33/.34 | todo | ChainIdSAsm (byte-wise reads), ClzSAsm (branchy leaf) |
| 4 | Witness DBs (node_db/code_db build + lookups) | `Witness.{NodeDb,CodeDb}` | 4ch8f.21/.28 | todo (unblocked by RegionMap) | TreeInsert.lean (slot predicates over arenas) |
| 5 | MPT read/walk/mutation + trie roots | state access | 4ch8f.22/.29/.31/.32 | todo | TreeDemo.lean `treeMinFn` (zipper-ghost walk) |
| 6 | Byte/copy + u256 + RLP + SSZ-HTR + bloom leaf families | shared leaves | 4ch8f.12–.20 | in-progress — `u256_is_zero` **done** (`Codegen/Proofs/U256IsZeroSpec.lean:u256_is_zero_deployed_spec`, the playbook acceptance test); rest is the 24 `port: verify …` beads — **start here** | U256IsZeroSpec.lean (straight-line leaf over a converted Program); ChainIdSAsm / howto §6 |
| 7 | Tx decode + signing hashes + secp256k1 recovery | `Transaction` | 4ch8f.25/.38/.39/.40 | todo | accelerator bridges: `Rv64/ZiskAccel.lean` KATs |
| 8 | Interpreter loop + opcode handlers + frames (the seam's guest side) | `ExecutionEngine` → `Block`/`VM` | 4ch8f.10 (strategy), .49–.59 | strategy in-progress | `Codegen/Proofs/HandlerSpecs.lean` (13/91 handler specs) |
| 9 | Verdict orchestration + validators (BAL, receipts, gas) | `Block` verdict | 4ch8f.36/.37/.41–.47/.61 | todo | `Codegen/Proofs/CreateDeployedCodeValidSpec.lean` (deployed-spec template) |
| 10 | Real seam instantiation: `execute` = Lean model of `execute_new_payload_request`, tied to obligation 8 | seam | 4ch8f.10 → .64 | todo | docs/4ch8f-specref-port.md §seam |
| 11 | Guest shell: epilogue pipeline, NPR hash-tree-root block, schema gate, verdict stamp, `Entry.run_stateless_guest` body composition | shell | 4ch8f.63 | todo | `Entry.lean` PR6 stub structure |
| 12 | Top composition: seq the stages, halt-wrap, discharge `run_stateless_guest_spec` | top | 4ch8f.64 | todo (blocked on 1–11) | `cpsTripleWithin_as_cpsHaltTripleWithin` |
| 13 | Deployment correspondence: emitted ELF ↔ Lean Program (string equality at scale) | emit | 4ch8f.9 (.9.3 wave live), tj9ts | in-progress | `Codegen/Programs/RlpWalk.lean:rlpWalkInitFunction_eq_verified_prog` |

## Vacuity guards (read before closing any obligation)

- A `.Spec`/triple with an unsatisfiable precondition proves nothing — provide
  or reuse a satisfiability witness (`GuestFraming.scratch_sat` at the top;
  per-routine, an `inputRegion_wf`-style lemma).
- `#print axioms` on every closed obligation: `propext`, `Classical.choice`,
  `Quot.sound` only.
- The bead-closure rubric in AGENTS.md applies: an obligation is `done` only
  when the named theorem exists on `main` and is wired into this ledger.
