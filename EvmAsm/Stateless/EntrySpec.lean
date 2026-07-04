/-
  EvmAsm.Stateless.EntrySpec

  The top-level specification STATEMENT for
  `Stateless.Entry.run_stateless_guest` (bead evm-asm-4ch8f.8; the
  end-to-end theorem itself is bead evm-asm-4ch8f.64).

  ## What the top theorem says (decisions, 4ch8f.8)

  1. **Soundness direction only (one-sided), over a PINNED
     observation window.** The guest may false-reject (flag byte 0)
     for any reason — unsupported feature, fuel, witness shape —
     without violating the spec. What it may never do is
     false-accept: if the flag byte at the fixed offset 32 of the
     40-byte OUTPUT observation window is 1, then the Python
     reference (`SpecRef.run_stateless_guest`, the Lean port of
     `execution-specs/.../stateless_guest.py`) run on the same input
     succeeds and agrees on the observed root+flag bytes
     (`GuestOutputSound`). The window length is pinned INSIDE the
     postcondition — review of the first draft found that an
     existential output with a self-delimiting decode is vacuously
     dischargeable (empty or over-extended `out` decodes to no claim);
     see the §per-run-contracts comment. Full-serialization byte
     equality (which also pins the chain-config echo) is the separate
     `GuestOutputFaithful` clause, the guest-shell bead's target; the
     completeness direction is documented as `GuestOutputComplete`.
     Neither is part of the headline statement.

  2. **Trust boundary.**
     - Host input bytes: the ZisK transport record at `INPUT_ADDR + 8`
       (`ziskInputRecord` = length word + payload;
       docs/agents/stateless-input-contract.md). The statement
       quantifies over ALL payloads — nothing about the host is
       trusted beyond placement; the 8 ZisK meta bytes at `+0` are
       deliberately unconstrained.
     - Machine model: `EvmAsm.Rv64` step semantics including the
       concrete ZisK accelerator semantics (`Rv64/ZiskAccel.lean`,
       kernel-checked KATs) — part of the model, not an axiom.
     - The execution seam: `SpecRef.verify_stateless_new_payload` cuts
       EVM re-execution at `execute : ExecutionSeam`
       (docs/4ch8f-specref-port.md §"The execution seam"). The
       statement is parameterized by the seam; instantiating it with
       the real STF model is the Block/VM subtree's obligation
       (beads 4ch8f.10/.49–.62).

  3. **Vehicle.** `cpsHaltTripleWithin` over
     `CodeReq.ofProg entry guest`: from any state where the code is
     placed, the input record sits at `INPUT_ADDR`, and the guest's
     working-state framing `fr.scratch` holds, execution HALTS within
     `nSteps` and the OUTPUT region holds sound bytes. The framing is
     bundled in `GuestFraming` with a SATISFIABILITY witness
     (`scratch_sat`) so the statement cannot be discharged vacuously
     by an unsatisfiable scratch assertion. Pinning the canonical
     scratch (working-RAM anyBytes tiling per `Codegen/RegionMap.lean`
     + the phase-ownership model) is part of bead 4ch8f.63.

  4. **Deployment gap.** This statement is about the Lean `Program`
     value `Stateless.Entry.run_stateless_guest`. The emitted-ELF
     correspondence (`emitProgram` string equality, bead evm-asm-tj9ts
     / 4ch8f.9) is a separate, mechanical layer.

  The obligation ledger that decomposes this statement into leaf work
  lives at `docs/agents/top-theorem-ledger.md`.
-/

import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.SpecRef.Guest

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Guest I/O region constants

    Numeric mirrors of `EvmAsm.Codegen.Programs.EvmBasic.INPUT_ADDR` /
    `OUTPUT_ADDR` / `INPUT_DATA_OFFSET`. Layering rule L1
    (`scripts/check-layering.sh`) forbids the verified core from
    importing `Codegen`, so the values are restated here; drift is
    caught by the `#guard`s in `EvmAsm/Codegen/RegionMap.lean` pinning
    the same addresses. -/

/-- Base of the host-supplied input region (mirrors
    `Codegen.Programs.EvmBasic.INPUT_ADDR`). -/
def STATELESS_INPUT_ADDR : Word := 0x40000000

/-- Base of the public output region (mirrors
    `Codegen.Programs.EvmBasic.OUTPUT_ADDR`; same value as
    `UNIMPL_OUTPUT_ADDR` in `Stateless/Unimplemented.lean`). -/
def STATELESS_OUTPUT_ADDR : Word := 0xa0010000

/-- Offset of the SSZ payload inside the input region (mirrors
    `Codegen.Programs.EvmBasic.INPUT_DATA_OFFSET`): 8 bytes of ZisK
    metadata then the LE u64 payload length. -/
def STATELESS_INPUT_DATA_OFFSET : Nat := 16

/-- The guest-relevant transport record: the LE u64 payload length at
    `INPUT_ADDR + 8`, then the schema-prefixed SSZ `SszStatelessInput`
    bytes at `INPUT_ADDR + 16` (see `Stateless/MemoryLayout.lean` and
    docs/agents/stateless-input-contract.md). The 8 ZisK metadata bytes
    at `INPUT_ADDR + 0` are intentionally NOT part of the record — the
    statement must not constrain host transport bytes the guest never
    relies on (they stay in `fr.scratch`). Note `bytesRegion`'s
    trailing-dword convention pins the pad bytes of a
    non-multiple-of-8 payload to zero — matching the ziskemu host
    packing rule (zero padding to 8 bytes). -/
def ziskInputRecord (payload : SpecRef.Bytes) : SpecRef.Bytes :=
  SpecRef.natToBytesLE 8 payload.length ++ payload

/-- Assertion: the input region holds the transport record for
    `payload` (length word + payload; ZisK meta dwords excluded). -/
def inputRecordAt (payload : SpecRef.Bytes) : Assertion :=
  bytesRegion (STATELESS_INPUT_ADDR + 8) (ziskInputRecord payload)

/-- Assertion: the output region starts with exactly `out`. Bytes of
    the 64 KiB output window past `out.length` are intentionally
    unconstrained (they stay inside the guest's scratch framing). -/
def outputBytesAt (out : SpecRef.Bytes) : Assertion :=
  bytesRegion STATELESS_OUTPUT_ADDR out

/-! ## Decoding the guest's verdict -/

/-- Decode OUTPUT-region bytes as an SSZ `StatelessValidationResult`
    (exactly the reference codec — no parallel decoder). -/
def decodeGuestOutput (out : SpecRef.Bytes) :
    Option SpecRef.StatelessValidationResult :=
  (do
    let sv ← SpecRef.deserialize SpecRef.sszStatelessValidationResultType out
    SpecRef.sszToValidationResult sv).toOption

/-- Does the guest's output claim `successful_validation = 1`?
    Undecodable output claims nothing (counts as a reject). -/
def guestOutputClaimsValid (out : SpecRef.Bytes) : Bool :=
  match decodeGuestOutput out with
  | some r => r.successfulValidation
  | none => false

/-! ## The per-run contracts

    The headline soundness claim is stated over a FIXED-length
    observation window, not a self-delimiting decode of an
    existentially chosen byte list. Review of the first draft
    (PR #9734, Fable) found two vacuity escapes in the decode-based
    form: choose `out = []` (nothing owns the OUTPUT dwords — the
    residue can hide them) or extend `out` past the true serialization
    (exact-length SSZ decode fails ⇒ claims nothing). Pinning
    `out.length` to the observation window and reading the flag byte
    at its fixed offset closes both. -/

/-- SSZ layout of `StatelessValidationResult`: 32-byte NPR root, then
    the `successful_validation` flag byte, then the (variable-length)
    chain-config offset+body. The external verifier observes the first
    33 bytes; the window is padded to the containing dword boundary so
    `outputBytesAt` owns whole dwords. -/
def STATELESS_OUTPUT_FLAG_OFFSET : Nat := 32
def STATELESS_OUTPUT_OBS_BYTES : Nat := 40

/-- **Soundness** (the headline obligation), over the pinned
    40-byte observation window `obs`: if the flag byte at offset 32
    claims validity, the Lean reference run on the same payload
    succeeds and agrees on the observed bytes (NPR root + flag).
    Reference *errors* (including input-deserialization failures,
    which Python propagates) make the right-hand side unsatisfiable,
    so the guest must not stamp the flag on any input the reference
    rejects. -/
def GuestOutputSound (execute : SpecRef.ExecutionSeam)
    (payload obs : SpecRef.Bytes) : Prop :=
  obs.getD STATELESS_OUTPUT_FLAG_OFFSET 0 = 1 →
    ∃ specOut, SpecRef.run_stateless_guest payload execute = .ok specOut ∧
      specOut.take (STATELESS_OUTPUT_FLAG_OFFSET + 1)
        = obs.take (STATELESS_OUTPUT_FLAG_OFFSET + 1)

/-- **Fidelity** (the stronger accept-path clause, target of the guest
    shell bead): the FULL serialized output — chain-config echo
    included — is byte-identical to the reference output whenever it
    decodes to a claim of validity. Implies the observed-window
    agreement of `GuestOutputSound`; kept separate because the
    headline statement must not depend on a prover-chosen
    self-delimiting decode. -/
def GuestOutputFaithful (execute : SpecRef.ExecutionSeam)
    (payload out : SpecRef.Bytes) : Prop :=
  guestOutputClaimsValid out = true →
    SpecRef.run_stateless_guest payload execute = .ok out

/-- **Completeness** (documented, NOT required by the headline
    statement): whenever the reference validates, the guest does too.
    False-rejects are explicitly allowed in the deployed guest
    (fuel, unsupported precompiles, witness-shape limits). -/
def GuestOutputComplete (execute : SpecRef.ExecutionSeam)
    (payload out : SpecRef.Bytes) : Prop :=
  ∀ specOut, SpecRef.run_stateless_guest payload execute = .ok specOut →
    guestOutputClaimsValid specOut = true →
    out = specOut

/-! ## The machine-level statement -/

/-- The guest's working-state framing: the scratch resources the guest
    owns before the run (working RAM, output window, stack, …) and the
    residue it leaves behind. `scratch_sat` is the non-vacuity
    witness: an unsatisfiable `scratch` would make any
    `cpsHaltTripleWithin` with this precondition hold trivially, so a
    framing must come with evidence that the precondition is
    inhabited for every payload. -/
structure GuestFraming where
  /-- Resources owned at entry, beyond the input record. -/
  scratch : Assertion
  /-- Residue at halt, beyond the output bytes. -/
  residue : Assertion
  /-- Non-vacuity: the precondition is satisfiable for every payload. -/
  scratch_sat : ∀ payload : SpecRef.Bytes,
    ∃ h, (inputRecordAt payload ** scratch) h

/-- The top-level soundness statement SHAPE (bead 4ch8f.8): placed at
    `entry` with framing `fr`, for EVERY host payload the guest halts
    within `nSteps` and the output region holds bytes that are sound
    w.r.t. the reference under the seam `execute`.

    The final theorem (bead 4ch8f.64) provides concrete
    `execute`/`nSteps`/`fr` and proves
    `RunStatelessGuestSound execute Entry.run_stateless_guest nSteps entry fr`. -/
def RunStatelessGuestSound (execute : SpecRef.ExecutionSeam)
    (guest : Program) (nSteps : Nat) (entry : Word)
    (fr : GuestFraming) : Prop :=
  ∀ payload : SpecRef.Bytes,
    cpsHaltTripleWithin nSteps entry (CodeReq.ofProg entry guest)
      (inputRecordAt payload ** fr.scratch)
      (fun h => ∃ obs : SpecRef.Bytes,
        (outputBytesAt obs **
         ⌜obs.length = STATELESS_OUTPUT_OBS_BYTES⌝ **
         ⌜GuestOutputSound execute payload obs⌝ **
         fr.residue) h)
  -- `obs.length` is pinned, so `outputBytesAt obs` necessarily owns
  -- OUTPUT[0..40) — the residue cannot absorb the observed window and
  -- the flag byte the claim reads is uniquely the memory content.

/-! ## Sanity pins (kernel-evaluated)

    Tie the verdict decoder to the reference codec on the SpecRef
    sanity vectors, so `guestOutputClaimsValid` cannot silently drift
    from `serialize_stateless_output`. -/

-- The reference's own sanity result decodes and claims validity.
#guard guestOutputClaimsValid
  (SpecRef.serialize_stateless_output SpecRef.sanityResult) == true

-- Flipping the bit is visible to the decoder.
#guard guestOutputClaimsValid
  (SpecRef.serialize_stateless_output
    { SpecRef.sanityResult with successfulValidation := false }) == false

-- Garbage output claims nothing.
#guard guestOutputClaimsValid [0xff, 0xff] == false

-- The flag byte sits at the documented fixed offset of the serialized
-- output (32-byte root, then successful_validation) — the offset the
-- headline observation window reads.
#guard (SpecRef.serialize_stateless_output SpecRef.sanityResult).getD
  STATELESS_OUTPUT_FLAG_OFFSET 0 == 1
#guard (SpecRef.serialize_stateless_output
  { SpecRef.sanityResult with successfulValidation := false }).getD
  STATELESS_OUTPUT_FLAG_OFFSET 0 == 0
#guard (SpecRef.serialize_stateless_output SpecRef.sanityResult).take 32 ==
  SpecRef.sanityResult.newPayloadRequestRoot

-- The observation window covers the root + flag and is dword-aligned.
#guard STATELESS_OUTPUT_FLAG_OFFSET + 1 ≤ STATELESS_OUTPUT_OBS_BYTES
#guard STATELESS_OUTPUT_OBS_BYTES % 8 == 0

-- The transport record (length word at +8, payload at +16, ZisK meta
-- excluded) places the payload at the documented offset.
#guard 8 + (ziskInputRecord [0xab]).length == STATELESS_INPUT_DATA_OFFSET + 1
#guard (ziskInputRecord (List.replicate 300 (0 : BitVec 8))).take 8 ==
  ([0x2c, 0x01] ++ List.replicate 6 (0 : BitVec 8))

end EvmAsm.Stateless
