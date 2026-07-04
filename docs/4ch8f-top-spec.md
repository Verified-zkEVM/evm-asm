# 4ch8f.8 — the top-level spec statement (decision record)

Bead `evm-asm-4ch8f.8`. Deliverable: `EvmAsm/Stateless/EntrySpec.lean`
(`runStatelessGuestSound` / `runStatelessGuestFaithful`) + this record.
Feeder: the merged SpecRef port (`EvmAsm/Stateless/SpecRef/`, bead `.8.1`,
`docs/4ch8f-specref-port.md`). Consumers: `.63` (guest shell), `.64`
(end-to-end theorem), `.10` (execution seam).

## 0. The statement, in words

> For every host-supplied input of at most 1 GiB, the `stateless_guest`
> image — started at its ELF entry with the input framed at `INPUT_ADDR`
> and owning its work regions — **halts within a static step budget**, and
> the 40-byte window a verifier reads at `OUTPUT_ADDR` is a **sound
> claim**: if the validation byte (`OUTPUT[32]`) is 1, then the input
> deserializes per the spec, `SpecRef.verify_stateless_new_payload`
> validates it, and the 32-byte root at `OUTPUT[0..32)` is the spec's
> `compute_new_payload_request_root` — binding the claim to the payload.

Formally: `runStatelessGuestSound cr fuel work execute`, a
`cpsHaltTripleWithin` at whole-guest granularity (EntrySpec.lean).

## 1. Direction: soundness-only first (decision)

**Decided: one-sided (soundness) for the `.64` v1 theorem; fidelity
stated but deferred.**

- Soundness ("guest says valid ⇒ spec validates") is the *protocol*
  claim: a ZisK proof of a false `valid = 1` is the catastrophic failure.
  False *rejects* are a liveness/quality problem, already hunted
  empirically by the EEST conformance harness (~full pass) and squeezed
  by the standing "no conservative skips" policy.
- The reject paths (`unimplemented_exit` `0xFE…` markers, validator-
  pipeline bails) satisfy the soundness postcondition vacuously, which is
  exactly what lets `.64` v1 land without first proving every bail
  unreachable.
- The two-sided form is stated as `runStatelessGuestFaithful` (output
  bytes = `serialize_stateless_output (verify_stateless_new_payload si)`
  byte-for-byte on deserializable inputs — this subsumes completeness).
  It is a **non-goal for `.64` v1**; its extra obligations over soundness
  are (a) proving every conservative bail unreachable on spec-valid
  inputs, and (b) the exact chain-config echo of
  `SSZ.Encode.serialize_stateless_output` (header rebuild + bounded
  tail-copy from the *input* bytes) matching the SpecRef serializer
  (re-serialization of the *parsed* config; equal iff SSZ round-trips
  canonically — expected, unverified).

## 2. Trust boundary (decision)

What the theorem assumes (everything else is proven or quantified):

| element | status |
|---|---|
| input bytes | **universally quantified** (`∀ input, length ≤ 2^30`); host framing at `INPUT_ADDR = 0x40000000`: `[+8..16)` u64-LE length, `[+16..)` payload (= the Python `run_stateless_guest` argument: 2-byte schema id ++ SSZ). `[+0..8)` ZisK meta unread. Host zero-pads the final dword (`bytesRegion` tail convention; matches the ziskemu 8-byte-pad rule). |
| initial machine state | pc = `GUEST_ENTRY = 0x80000000` (ELF `e_entry`), code = the image `CodeReq` (parameter `cr`, composed by `.63` from the wave-`.9` conversions), work-region ownership (parameter `work`, the `.6` phase views; contents unconstrained — havoc). Registers unconstrained (`_start` initializes `sp` itself). |
| step semantics | `Rv64.Execution.step` — deterministic; accelerators are the **concrete** bead-`.1` semantics (`ZiskAccel`), *no accelerator axioms*; invalid/unmodeled CSR traps. |
| observation | the 40-byte window at `OUTPUT_ADDR = 0xa0010000`: root `[0..32)`, validation byte `[32]`. Kernel-checked layout pins in EntrySpec tie these offsets to the SpecRef SSZ encoder. |
| halt | `isHalted` (= `step = none`): the clean `--halt linux93` ECALL-t0=0 stub, but traps also qualify. Determinism makes the triple's ∃-run *the* run, so the postcondition constrains the actual outcome; a trap after a stale `valid = 1` write is a real (and intended) proof obligation, not a statement gap. |
| spec side | `SpecRef.*` (Lean port of `tests-zkevm@v0.4.0` `stateless_guest.py`/`stateless.py`) **is the spec** — trusted by definition; its fidelity to Python is evidenced by the port doc + `#guard` pipelines, not by proof. |
| execution seam | parameter `execute : ExecutionSeam` — see §4. |

Notably *inside* the boundary (proven, not assumed): SSZ decode, header
chain validation, witness DBs, all crypto kernels, the EVM interpreter,
the verdict — the entire guest body.

## 3. Statement shape (decision)

`cpsHaltTripleWithin fuel GUEST_ENTRY cr (input ** work) (sound-output)`,
wrapped as a plain `Prop` parameterized over `(cr, fuel, work, execute)`.

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
  reaching a halted state on *every* input ≤ 1 GiB — malformed inputs
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

- **`.63` (shell)**: compose the image `CodeReq`; fix the `work` bundle
  (RegionMap-derived, `.6` phase views); prove the verdict stamp writes
  `OUTPUT[32] = 1` only on the all-pass path and that no bail marker or
  reason code writes 1 there (reason codes land at `OUTPUT[32..40)` —
  audit the encoding); reconcile/retire the legacy `Stateless.Entry`
  stub.
- **`.64` (top theorem)**: instantiate the quadruple; derive the halt
  triple from the body `cpsTripleWithin` via
  `cpsTripleWithin_as_cpsHaltTripleWithin`; prove the trap-freedom of the
  post-stamp tail (or that the stamp is the last OUTPUT-window write).
- **`.10`**: deliver `elExecute` with the simulation obligations shaped
  as `∀ execute`-free statements against it.
- **Fidelity follow-up** (post-v1): `runStatelessGuestFaithful` — needs
  the serializer-echo equality and bail-unreachability on valid inputs.
