# 4ch8f.8 — the top-level spec statement (decision record)

Bead `evm-asm-4ch8f.8`. Deliverable: `EvmAsm/Stateless/EntrySpec.lean`
(`runStatelessGuestSound` / `runStatelessGuestFaithful`) + this record.
Feeder: the merged SpecRef port (`EvmAsm/Stateless/SpecRef/`, bead `.8.1`,
`docs/4ch8f-specref-port.md`). Consumers: `.63` (guest shell), `.64`
(end-to-end theorem), `.10` (execution seam).

## 0. The statement, in words

> For every host-supplied input of at most `MAX_INPUT_BYTES` (~896 MiB,
> §2a), the `stateless_guest`
> image — started at its ELF entry with the input framed at `INPUT_ADDR`
> and owning its work regions — **halts within a static step budget**, and
> the 40-byte window a verifier reads at `OUTPUT_ADDR` is a **sound
> claim**: if the validation byte (`OUTPUT[32]`) is 1, then the input
> deserializes per the spec, `SpecRef.verify_stateless_new_payload`
> validates it, and the 32-byte root at `OUTPUT[0..32)` is the spec's
> `compute_new_payload_request_root` — binding the claim to the payload.

Formally: `runStatelessGuestSound cr fuel work execute`, a
`cpsHaltTripleWithin` at whole-guest granularity (EntrySpec.lean).

## 1. Direction: iff under envelope (decision; supersedes soundness-only)

**Decided (maintainer 2026-08-15, project-wide): machine accepts if and
only if spec accepts**, under the project envelope (small block number,
small timestamp, small enough gas costs — parameters outside that envelope
may reject in the impl where the spec does not, and that is okay when the
envelope is an **explicit precondition** of the theorem, not a silent
excuse). In-envelope, a false reject is a **bug**, not a liveness/quality
problem.

- The catastrophic protocol failure remains a false *accept* (ZisK proof of
  `valid = 1` when the spec rejects). The accepting direction is now an
  equal proof obligation: every check needs its accepting arm, not only
  its rejecting one. Reject-implies-reject alone is not correspondence
  done.
- `runStatelessGuestSound` (guest says valid ⇒ `SpecAccepts`) is still the
  landed `.64` v1 *statement shape* in `EntrySpec.lean`, but it is **not**
  the project target bar. Vacuous reject paths that satisfy soundness
  without proving bails unreachable on in-envelope spec-valid inputs are
  **known incompleteness**, not an accepted endpoint.
- The two-sided form is `runStatelessGuestFaithful` (output bytes =
  `serialize_stateless_output (verify_stateless_new_payload si)`
  byte-for-byte on deserializable inputs — this subsumes completeness).
  That is the **iff target** for `.64`: extra obligations are (a) proving
  every conservative bail unreachable on in-envelope spec-valid inputs
  (or fixing the impl so it does not bail), and (b) the exact chain-config
  echo of `SSZ.Encode.serialize_stateless_output` matching the SpecRef
  serializer. Envelope hypotheses must appear in the theorem statement
  (same honesty rule as `docs/agents/spec-correspondence.md`).

## 2. Trust boundary (decision)

What the theorem assumes (everything else is proven or quantified):

| element | status |
|---|---|
| input bytes | **universally quantified** (`∀ input, length ≤ MAX_INPUT_BYTES = 0x37FFFFF8` — revised from `2^30`, see §2a); host framing at `INPUT_ADDR = 0x40000000`: `[+8..16)` u64-LE length, `[+16..)` payload (= the Python `run_stateless_guest` argument: 2-byte schema id ++ SSZ). `[+0..8)` ZisK meta unread. Host zero-pads the final dword (`bytesRegion` tail convention; matches the ziskemu 8-byte-pad rule). |
| initial machine state | pc = `GUEST_ENTRY = 0x80000000` (ELF `e_entry`), code = the image `CodeReq` (parameter `cr`, composed by `.63` from the wave-`.9` conversions), work-region ownership (parameter `work`, the `.6` phase views; contents unconstrained — havoc). Registers unconstrained (`_start` initializes `sp` itself). |
| step semantics | `Rv64.Execution.step` — deterministic; accelerators are the **concrete** bead-`.1` semantics (`ZiskAccel`), *no accelerator axioms*; invalid/unmodeled CSR traps. |
| observation | the 40-byte window at `OUTPUT_ADDR = 0xa0010000`: root `[0..32)`, validation byte `[32]`. Kernel-checked layout pins in EntrySpec tie these offsets to the SpecRef SSZ encoder. |
| halt | `isHalted` (= `step = none`): the clean `--halt linux93` ECALL-t0=0 stub, but traps also qualify. Determinism makes the triple's ∃-run *the* run, so the postcondition constrains the actual outcome; a trap after a stale `valid = 1` write is a real (and intended) proof obligation, not a statement gap. |
| spec side | `SpecRef.*` (Lean port of `tests-zkevm@v0.4.0` `stateless_guest.py`/`stateless.py`) **is the spec** — trusted by definition; its fidelity to Python is evidenced by the port doc + `#guard` pipelines, not by proof. |
| execution seam | parameter `execute : ExecutionSeam` — see §4. |

Notably *inside* the boundary (proven, not assumed): SSZ decode, header
chain validation, witness DBs, all crypto kernels, the EVM interpreter,
the verdict — the entire guest body.

## 2a. `MAX_INPUT_BYTES` revision (bead .63 — statement repair)

The original constant was `2^30` ("the project's 1 GiB bound"). Bead
`.63`, building the first `GuestFraming.scratch_sat` witness, found the
statement **unprovable at that bound** — a framing-fights-statement
signal, resolved by repairing the constant rather than working around:

- `↦ₘ` (and hence `bytesRegion`/`guestInputAssertion`) bakes in
  `isValidDwordAccess`, whose valid map is `[0x20, 0x78000000] ∪
  [0x40000000, 0x40002000] ∪ [0xa0000000, 0xc0000000]`
  (`Rv64/Basic.lean`). A `2^30`-byte payload at `INPUT_ADDR+16` has
  dwords up to `0x80000008` — outside every zone — so
  `guestInputAssertion` is **unsatisfiable** for lengths above the model
  boundary and `scratch_sat` (∀-quantified over admissible inputs) is
  unprovable. (`2^30` also overhung its own stated window: `0x40000010 +
  2^30 = 0x80000010 > 0x80000000`.)
- **New value `0x37FFFFF8`** (~896 MiB) — the *sharp* bound: the largest
  length whose zero-padded dword window `[0x40000010, 0x40000010 +
  8·⌈len/8⌉)` stays within `MEM_END = 0x78000000` (inclusive). A
  kernel `#guard` in EntrySpec pins `INPUT_ADDR + INPUT_BODY_OFFSET +
  MAX_INPUT_BYTES = MEM_END + 8`, so a future `MEM_END` change
  re-derives the constant.
- Rejected alternative: growing `Rv64.MEM_END` past `.text`
  (`0x80000000`) — that widens the machine model's writable window for
  *every* proof in the repo to buy input sizes no host exercises
  (ziskemu inputs are far below 896 MiB; the emitted-reality
  `inputRegion` is 8 KiB).

## 3. Statement shape (decision)

`cpsHaltTripleWithin fuel GUEST_ENTRY cr (input ** work) (sound-output)`,
wrapped as a plain `Prop` parameterized over `(cr, fuel, fr, execute)`
(`fr : GuestFraming` — the scratch/residue bundle, see §3a).

- **Why `cpsHaltTripleWithin`** (not `cpsTripleWithin` to an exit pc):
  the guest ends in a halt ecall, not a return; the halt triple
  (CPSSpec.lean:892) is the existing machine-side notion and composes
  from a `cpsTripleWithin` to the halt stub via
  `cpsTripleWithin_as_cpsHaltTripleWithin`.
- **Why parameterized**: the four parameters are exactly the artifacts
  later beads produce (`.63` the image `CodeReq` + work bundle, `.5`-style
  gas-derived fuel, `.10` the seam). Pinning placeholder values here
  would either block on those beads or bake in wrong constants. The
  *shape* — quantifiers, framing, observation, soundness clause — is the
  `.8` decision; `.64`'s headline theorem instantiates it.
- **Termination included** (axis 4): the triple asserts `∃ k ≤ fuel`
  reaching a halted state on *every* input ≤ `MAX_INPUT_BYTES` — malformed inputs
  must reach a reject halt, not diverge. Fuel is a static cap in the
  `.5` `whileS` idiom: a wrong cap makes the proof unprovable, never
  unsound.
- **Soundness clause** (`guestOutputSound`): conditions on the *verifier's
  read* (`out.getD 32 0 = 1`), not on the guest's intent. Any halted
  outcome whose byte 32 reads 1 — including hypothetical bail markers or
  trap leftovers that happen to write 1 there — must be spec-justified.
  `SpecAccepts` requires deserialization to succeed (`.ok si`), matching
  Python where a deserialization exception propagates (never caught into
  a result), so garbage input can never be validly claimed.

Rejected alternatives:
- *Full-output equation as the only statement* — couples `.64` v1 to the
  chain-config echo fidelity and to bail-unreachability (§1).
- *Quantifying soundness over every decodable output prefix* — a
  truncated chain-config tail could decode to a different config, making
  the claim false for reasons the verifier never observes; the fixed
  40-byte window is what the verdict consumer actually reads.
- *Axiomatizing the seam behavior* (`execute` correct-by-axiom) — would
  put the EVM inside the trusted base; instead the seam stays a
  parameter until `.10` supplies the model (§4).

## 3a. The framing bundle (post-review revision, PRs #9733/#9734)

Bead `.8` was executed twice in parallel (#9733 and #9734); the
cross-review found one defect in each statement, and the landed form is
the synthesis:

- **#9733 defect (this record's original form): no residue slot.** The
  postcondition owned only the 40-byte observation window, but the
  precondition owned all scratch — a `cpsHaltTripleWithin` must account
  for every entry-owned resource in its post, so the triple was
  *unprovable*. Fix: `GuestFraming.residue` joins the post
  (`guestOutputSound … ** fr.residue`).
- **#9734 defect: ∃-out vacuity.** Its post was `∃ out,
  outputBytesAt out ** ⌜sound⌝ ** residue` with the claim judged by a
  self-delimiting SSZ decode and no length pin. The prover chooses
  `out`: `out = []` lets the residue absorb the OUTPUT window, and any
  over-long `out` fails the exact-length decode — both make the claim
  vacuous even on accept runs. Fix kept from #9733: `out.length =
  OUTPUT_CLAIM_BYTES` is pinned *inside* the post, so the
  `bytesRegion OUTPUT_ADDR out` conjunct must own the window dwords and
  `out` is uniquely the memory the verifier reads.
- **Kept from #9734**: `GuestFraming.scratch_sat` — the satisfiability
  witness that rules out discharging the triple with an unsatisfiable
  scratch assertion; and the framing of the input meta dwords stays
  *unconstrained* (asserting them zero, as #9734 did, would make the
  theorem inapplicable to hosts that write nonzero ZisK meta).

## 4. Closing the execution seam (interface to `.10`)

`SpecRef.verify_stateless_new_payload` takes
`execute : ExecutionSeamInput → Except SpecError Unit` — the cut at
Python's `execute_new_payload_request` (`stateless.py:378`). The top-level
Props inherit this parameter.

**Decision**: the seam is closed by *definition on the spec side*, not by
axiom and not by the guest. Bead `.10`'s interpreter strategy delivers a
Lean functional model of `execute_new_payload_request` (the EL: blocks,
txs, EVM) — call it `elExecute`. Then:

- `.64` v1 headline: `runStatelessGuestSound guestCR gasFuel guestWork elExecute`.
- `elExecute` joins `SpecRef` inside the spec (trusted-by-definition,
  Python-fidelity by review/`#guard`s, same status as the rest of the
  port). The guest's interpreter loop is *proven* to simulate it
  (the `.10` pilot's simulation-theorem pattern, scaled by `.49`–`.61`).
- Until `elExecute` exists, every intermediate composition theorem is
  stated `∀ execute` or against the explicit parameter — nothing in the
  `.63` shell work depends on the seam's content.

## 5. File placement (decision)

- `EvmAsm/Stateless/EntrySpec.lean` — constants, framing assertion,
  `SpecAccepts`, `guestOutputSound`, the two Props, kernel-checked layout
  pins. (Kept importing `Stateless.Entry` for the existing import chain;
  the legacy PR6 `Entry` Program body is `.63`'s to reconcile.)
- No separate `SpecRef/Verdict.lean`: the observation is field-level
  (root bytes + flag byte), so no output SSZ *decoder* is needed for
  soundness; `runStatelessGuestFaithful` reuses the SpecRef *serializer*.

## 6. Obligations this creates downstream

- **`.63` (shell)**: compose the image `CodeReq`; fix the `GuestFraming`
  bundle (RegionMap-derived, `.6` phase views + the `scratch_sat` witness); prove the verdict stamp writes
  `OUTPUT[32] = 1` only on the all-pass path and that no bail marker or
  reason code writes 1 there (reason codes land at `OUTPUT[32..40)` —
  audit the encoding); reconcile/retire the legacy `Stateless.Entry`
  stub. *Structural half DONE*: `Codegen/Proofs/GuestImage.lean`
  (`guestImageCodeReq` + `guestFraming` + `guestScratch_sat`; coverage
  accounting `docs/4ch8f-guest-image-coverage.md`), stamp audit §6a.
  Remaining: the shell pipeline triples + the `Stateless.Entry`
  reconciliation.
- **`.64` (top theorem)**: instantiate the quadruple; derive the halt
  triple from the body `cpsTripleWithin` via
  `cpsTripleWithin_as_cpsHaltTripleWithin`; prove the trap-freedom of the
  post-stamp tail (or that the stamp is the last OUTPUT-window write) —
  extended by §6a to trap-freedom of the whole verdict window.
- **`.10`**: deliver `elExecute` with the simulation obligations shaped
  as `∀ execute`-free statements against it.
- **Fidelity follow-up** (post-v1): `runStatelessGuestFaithful` — needs
  the serializer-echo equality and bail-unreachability on valid inputs.

## 6a. Verdict-stamp soundness audit (bead .63, structural half)

Exhaustive enumeration of every writer of the OUTPUT window's first 40
bytes (`OUTPUT_ADDR = 0xa0010000`) in the linked `stateless_guest`
image, against the `.8` claim's conditioning byte `OUTPUT[32]`. Scope
note: most `0xa0010000` grep hits under `EvmAsm/Codegen/Programs/` are
standalone probe BuildUnits that build their own ELFs; the writers below
are the ones reachable in `statelessGuestUnit`
(`Codegen/Programs/StatelessGuest.lean:59`).

**Execution order and the writer set** (all `file:line` as of this audit):

1. **Encoder** (`Stateless/SSZ/Encode/Program.lean:132-141`, body):
   zeroes `OUTPUT[0..32)` (4×`SD x0`), then one `SD` at `+32` whose low
   byte is `x11 & 1` and whose tail `[33..40)` is the SSZ
   chain-config offset (`0x25`) + `chain_id` low bytes. **`x11` is 0
   unconditionally**: `decode_validation_bit`'s first instruction is
   `ADDI x11 x0 0` (`SSZ/Decode/Program.lean:167`) and nothing between
   it and the encoder writes `x11` (the `read_chain_id_verified` x11
   use at `ChainIdSAsm.lean:91` runs *before* it). So byte 32 holds 0
   from here to the final stamp. (The Entry.lean:56 PR6 comment
   claiming "`x11 = 1` iff `witness.headers` empty" is STALE —
   superseded by `Decode/Program.lean:152`.)
2. **Validator pipeline** (`StatelessGuestEpilogue.lean:49-`): no
   OUTPUT stores. The `.Lsg_fail_*` labels only load reason codes into
   `a0` and fall through to `.Lsg_hash` (`:133-153`) — the old
   `0xFE…`-marker/reason writes were REMOVED (comment `:144-153`);
   `unimplemented_exit` (`Stateless/Unimplemented.lean:93-99`, which
   writes marker/reason at `OUTPUT[0..16)`, never byte 32) is **not
   linked into the guest** (its only occurrence in the codegen path is
   a doc comment, `StatelessGuestEpilogue.lean:31`).
3. **NPR block `.Lsg_hash`**: its ONLY OUTPUT store is the final
   `zkvm_sha256` call writing the 32-byte root to `OUTPUT[0..32)`
   (`StatelessGuestEpilogue.lean:772-773`); every other store in the
   block targets `npr_*` scratch. Cannot touch `[32..40)`.
4. **Verdict window** (`:785-793`): save loop copies `OUTPUT[0..112)`
   to `npr_saved_output`, `jal stateless_verdict_v2`, restore loop
   copies it back (the `fhsxz` firewall). *Inside* the window the
   dispatcher freely uses the OUTPUT prefix, including byte 32 as the
   `halt_kind` slot — see the finding below.
5. **Schema-ID + SSZ outer-offset gates** (`:805-837`): loads only;
   any failure forces `a0 = 0` (`.Lsg_bad_input`, `:839-840`).
6. **THE STAMP** (`StatelessGuestEpilogue.lean:842`):
   `li t0, 0xa0010000; sb a0, 32(t0)` — a BYTE store, the single
   authoritative and FINAL byte-32 write. `a0 = 1` requires
   `stateless_verdict_v2 = 1` ∧ schema id `0x0001` ∧ canonical outer
   offsets. There is no separate `.Lsg_all_pass` stamp (`:123-132`
   deliberately writes nothing).
7. **Post-stamp**: MTVEC restore to `0xa0009828` (`zisk_system`, not
   OUTPUT), `j .Lsg_done`, halt. The function bodies appended after the
   epilogue are jumped over (`j .Lstateless_guest_halt_…`,
   `StatelessGuest.lean:62`). **No OUTPUT write follows the stamp.**

**Reason codes** (`Unimplemented.lean:53-77` + epilogue-local `0x18`,
`0x19`): `REASON_PRECOMPILE = 0x01` is the only code with low byte
`0x01`, but reason codes are only ever stored at `OUTPUT+8` (by the
unlinked `unimplemented_exit`), never at `+32`; in the guest they are
never stored at all. **No reason code can place `0x01` at byte 32.**

**FINDING (P1, filed as a `.63` child): the verdict-window transient-1
trap channel.** During step 4, ordinary contract execution writes
`OUTPUT[0..32) := RETURN data` and `OUTPUT+32 := halt_kind` (u64) — and
`halt_kind = 1` means RETURN (`Dispatch.lean:1121-1125` scheme;
`returnRevertTail 1`, `Programs/NoopHalt.lean:254-255`; also LOG
overflow `= 4` at `EvmLogHandlers.lean:166-168`, exceptional kinds
2-8, STOP `= 0` at `EvmBasic.lean:129`, and the reset
`Dispatch.lean:2180`). So **byte 32 routinely holds `0x01` with
attacker-influenced bytes at `[0..32)` between the RETURN tail and the
restore loop**. The save/restore firewall discards this on every
completed run; but `isHalted` includes traps, so a trap inside that
window would halt the machine with a verifier-visible false accept.
The `.64` halt triple therefore cannot close without **trap-freedom of
the verdict window** (or moving the `halt_kind` side channel off
OUTPUT+32, e.g. into the existing `rdg_halt_kind` `.data` slot —
`Dispatch.lean:3410-3416` already mirrors it there — which would
eliminate the transient entirely). This is a proof obligation /
hardening item, not a currently-demonstrated exploit: no trap in that
window has been observed on the EEST corpus.

