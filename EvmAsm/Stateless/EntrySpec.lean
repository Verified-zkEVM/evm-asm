/-
  EvmAsm.Stateless.EntrySpec

  The top-level specification SHAPE for the verified stateless guest
  (bead evm-asm-4ch8f.8). Decision record: docs/4ch8f-top-spec.md.

  The headline Prop is `runStatelessGuestSound cr fuel fr execute`:

    for every host-supplied input (≤ `MAX_INPUT_BYTES`), starting at the
    guest ELF entry with the input framed at `INPUT_ADDR` and owning the
    work regions, the guest HALTS within `fuel` steps, and whatever the
    verifier then reads at `OUTPUT_ADDR` is a SOUND claim: if the
    `successful_validation` byte (OUTPUT[32]) is 1, then the input
    deserializes per the spec, the spec's `verify_stateless_new_payload`
    (with execution seam `execute`) also validates, and the 32-byte root
    at OUTPUT[0..32) is the spec's `compute_new_payload_request_root`.

  Parameters deliberately left open (supplied by later beads, see the
  decision record §4):
    * `cr : CodeReq`   — the guest image's code requirement (bead .63
      composes it from the wave-.9 `Program` conversions).
    * `fuel : Nat`     — the step budget (a gas-derived static cap in the
      `.5` `whileS` style; wrong cap ⇒ unprovable, never unsound).
    * `fr : GuestFraming` — ownership of the guest's scratch/work regions
      at entry (`fr.scratch`, bead .6 phase views over `RegionMap`; bead
      .63 fixes the bundle) and the residue left at halt (`fr.residue`).
      `fr.scratch_sat` is the non-vacuity witness: an unsatisfiable
      scratch would make the halt triple hold trivially.
    * `execute : SpecRef.ExecutionSeam` — the Lean model of
      `execute_new_payload_request` (bead .10's interpreter model closes
      this seam; until then the Prop is stated against the seam
      parameter, exactly as `SpecRef.verify_stateless_new_payload` is).

  Direction: soundness-only (one-sided). `runStatelessGuestFaithful` is
  the stronger two-sided fidelity Prop (output bytes = the spec's
  serialized result on deserializable inputs); it is a stated NON-goal
  for the first end-to-end theorem (bead .64) — see the decision record.

  The machine-side notions come from `Rv64.CPSSpec`:
  `cpsHaltTripleWithin` (halt = `step = none`; the clean guest halt is
  the ECALL-t0=0 stub emitted by `--halt linux93`, and traps also
  satisfy `isHalted` — since `step` is deterministic, the ∃-run in the
  triple is THE run, so the postcondition constrains the actual outcome).
-/

import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.SpecRef.Guest
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Stateless

open EvmAsm.Rv64
open EvmAsm.Stateless.SpecRef

/-! ## Trust-boundary constants (decision record §2)

    Framing follows the emitted reality recorded in
    `Codegen.RegionMap.inputRegion` / `outputRegion` and the ELF:
    * `INPUT_ADDR = 0x40000000`: `[+0..8)` ZisK meta, `[+8..16)` u64-LE
      payload length, `[+16..)` payload (= the `input_bytes` the Python
      `run_stateless_guest` receives: 2-byte schema id ++ SSZ body).
    * `OUTPUT_ADDR = 0xa0010000` (= `SSZ.Encode.OUTPUT_BASE`): the SSZ
      `StatelessValidationResult` — root `[0..32)`, validation byte
      `[32]`, chain-config echo after.
    * `GUEST_ENTRY = 0x80000000`: the `stateless_guest.elf` entry point
      (`e_entry`, `-Ttext=0x80000000`, `_start` first).
    * `MAX_INPUT_BYTES = 0x37FFFFF8` (~896 MiB): the largest length whose
      zero-padded payload dwords `[0x40000010, 0x40000010 + 8·⌈len/8⌉)`
      all stay inside the machine model's valid memory map — the legacy
      zone ends at `Rv64.MEM_END = 0x78000000` (inclusive; see
      `Rv64.isValidDwordAccess`, whose validity `↦ₘ` bakes in). Any
      larger bound makes `guestInputAssertion` unsatisfiable and the
      `GuestFraming.scratch_sat` witness unprovable. REVISED by bead
      `.63` from the original `2^30` (which also overhung `.text` by 16
      bytes: `0x40000010 + 2^30 = 0x80000010`); the `#guard` below pins
      the constant to the model boundary so a `MEM_END` change re-derives
      it. Decision record: docs/4ch8f-top-spec.md §2a. -/

def INPUT_ADDR : Word := 0x40000000
def INPUT_LEN_OFFSET : Word := 8
def INPUT_BODY_OFFSET : Word := 16
def OUTPUT_ADDR : Word := 0xa0010000
def GUEST_ENTRY : Word := 0x80000000
def MAX_INPUT_BYTES : Nat := 0x37FFFFF8

-- The bound is exactly "last payload dword sits at `MEM_END`":
-- `INPUT_ADDR + INPUT_BODY_OFFSET + MAX_INPUT_BYTES - 8 = MEM_END`.
#guard INPUT_ADDR.toNat + INPUT_BODY_OFFSET.toNat + MAX_INPUT_BYTES == MEM_END + 8
#guard MAX_INPUT_BYTES % 8 == 0

/-- The observation window at `OUTPUT_ADDR` the soundness claim is stated
    over: root (32) + validation byte (1), padded to the 40-byte dword
    boundary. The verifier's accept signal is byte 32; bytes beyond the
    window (the chain-config echo) are outside the soundness claim (they
    belong to `runStatelessGuestFaithful`). -/
def OUTPUT_CLAIM_BYTES : Nat := 40

/-- The u64 little-endian byte encoding of `n` (the input length field at
    `INPUT_ADDR + 8`). -/
def u64LEBytes (n : Nat) : List (BitVec 8) :=
  (List.range 8).map (fun i => BitVec.ofNat 8 (n >>> (8 * i)))

@[simp] theorem u64LEBytes_length (n : Nat) : (u64LEBytes n).length = 8 := by
  simp [u64LEBytes]

/-! ## Precondition: host input framing -/

/-- Ownership + contents of the host input framing: the length dword at
    `INPUT_ADDR+8` and the payload bytes at `INPUT_ADDR+16`. The ZisK
    meta dword `[+0..8)` is not read by the guest and stays in the frame.

    NOTE (`bytesRegion` tail convention): the payload region asserts whole
    trailing dwords, so a payload whose length is not a multiple of 8 has
    its final-dword tail bytes pinned to 0 — i.e. the statement assumes
    the host zero-pads the input buffer to the next dword, which matches
    the ziskemu input convention (8-byte-padded inputs; see the
    `reference` memory note and the probe harness). -/
def guestInputAssertion (input : Bytes) : Assertion :=
  bytesRegion (INPUT_ADDR + INPUT_LEN_OFFSET) (u64LEBytes input.length) **
  bytesRegion (INPUT_ADDR + INPUT_BODY_OFFSET) input

/-! ## Postcondition: the verifier-facing claim -/

/-- The spec-side acceptance condition the guest's `valid = 1` claim must
    imply: the payload deserializes (a Python deserialization exception
    would propagate out of `run_stateless_guest`, so an undeserializable
    input can never be validly claimed), the spec's stateless validation
    succeeds under the execution seam `execute`, and the claimed root is
    the spec's NPR root (binding the claim to the actual payload). -/
def SpecAccepts (execute : ExecutionSeam) (input root : Bytes) : Prop :=
  ∃ si, deserialize_stateless_input input = .ok si ∧
    (verify_stateless_new_payload si execute).successfulValidation = true ∧
    root = compute_new_payload_request_root si

/-- Soundness of the output window: whatever 40 bytes sit at
    `OUTPUT_ADDR` when the guest halts, IF the validation byte
    (OUTPUT[32]) is 1 THEN the spec accepts the input with the claimed
    root (OUTPUT[0..32)). Reject paths (validation byte ≠ 1, including
    the `0xFE…` unimplemented-exit marker) satisfy this vacuously —
    soundness never constrains rejections. -/
def guestOutputSound (execute : ExecutionSeam) (input : Bytes) : Assertion :=
  fun h => ∃ out : Bytes, out.length = OUTPUT_CLAIM_BYTES ∧
    bytesRegion OUTPUT_ADDR out h ∧
    (out.getD 32 0 = 1 → SpecAccepts execute input (out.take 32))

/-! ## The framing bundle -/

/-- The guest's working-state framing (decision record §3, revised after
    the #9733/#9734 cross-review):

    * `scratch` — the resources the guest owns at entry beyond the input
      record (working RAM, the OUTPUT window, the stack, …; bead .63
      instantiates it from the RegionMap phase views).
    * `residue` — whatever those resources have become at halt. Without
      this slot the halt triple is UNPROVABLE: the postcondition heap
      must account for every resource owned at entry, and the soundness
      claim alone owns only the 40-byte observation window.
    * `scratch_sat` — the non-vacuity witness (from #9734): a
      `cpsHaltTripleWithin` with an unsatisfiable precondition holds
      trivially, so a framing must come with evidence that the
      precondition is inhabited for every admissible input.

    Note the OUTPUT observation window is deliberately NOT allowed to
    hide in `residue`: `guestOutputSound` pins `out.length` to the fixed
    window size, so its `bytesRegion OUTPUT_ADDR out` conjunct must own
    the window dwords in the postcondition split, and `out` is therefore
    uniquely the memory content the verifier reads (this closes the
    ∃-out vacuity hole found in #9734's decode-based variant). -/
structure GuestFraming where
  scratch : Assertion
  residue : Assertion
  scratch_sat : ∀ input : Bytes, input.length ≤ MAX_INPUT_BYTES →
    ∃ h, (guestInputAssertion input ** scratch) h

/-! ## The top-level Props -/

/-- **The headline statement shape** (soundness + termination): for every
    host input within the size bound, the guest — running from the ELF
    entry with the input framed and `fr.scratch` owned — halts within
    `fuel` steps in a state that splits into the sound 40-byte
    observation window and `fr.residue`.

    Bead `.64` proves this for the concrete `(cr, fuel, fr, execute)`
    quadruple: the guest-image `CodeReq` (bead .63), the gas-derived step
    cap, the `.6`-style framing bundle (with its satisfiability witness),
    and the `.10` interpreter model closing the execution seam. -/
def runStatelessGuestSound (cr : CodeReq) (fuel : Nat) (fr : GuestFraming)
    (execute : ExecutionSeam) : Prop :=
  ∀ input : Bytes, input.length ≤ MAX_INPUT_BYTES →
    cpsHaltTripleWithin fuel GUEST_ENTRY cr
      (guestInputAssertion input ** fr.scratch)
      (guestOutputSound execute input ** fr.residue)

/-- The two-sided fidelity Prop (stated, NOT a `.64` v1 goal): on every
    deserializable input the guest's full output equals the spec's
    serialized result byte-for-byte. This subsumes completeness
    (no false rejects) for deserializable inputs; proving it additionally
    requires the exact chain-config echo produced by
    `SSZ.Encode.serialize_stateless_output` to match the SpecRef
    serializer — tracked as a `.64` follow-up. -/
def runStatelessGuestFaithful (cr : CodeReq) (fuel : Nat) (fr : GuestFraming)
    (execute : ExecutionSeam) : Prop :=
  ∀ input si, input.length ≤ MAX_INPUT_BYTES →
    deserialize_stateless_input input = .ok si →
    cpsHaltTripleWithin fuel GUEST_ENTRY cr
      (guestInputAssertion input ** fr.scratch)
      (bytesRegion OUTPUT_ADDR
        (serialize_stateless_output (verify_stateless_new_payload si execute))
        ** fr.residue)

/- Fidelity refines soundness pointwise on the halt heap: a byte-exact
   output window satisfies the sound-claim window (the serialized
   result's first 40 bytes are the observation, and its claim clause
   holds because the spec result IS the source of the bytes) — recorded
   here as the reason `.64` v1 can target `runStatelessGuestSound`
   without losing the upgrade path. Proving the implication between the
   two Props needs `serialize` length facts and belongs to the `.64`
   follow-up, not the statement layer. -/

/-! ## Kernel-checked layout pins

    These tie the observation window's offsets to the SpecRef SSZ
    encoder, so `guestOutputSound`'s byte-32 / first-32-bytes reads are
    justified from the spec side (not just the guest's layout comments):
    on the sanity pipeline the serialized result carries the NPR root at
    `[0..32)` and the validation flag at `[32]`. -/

private def sanityResult : StatelessValidationResult :=
  verify_stateless_new_payload sanityInput executeAlwaysOk

-- Byte 32 of the serialized result is the successful_validation flag.
#guard (serialize_stateless_output sanityResult).getD 32 0
        == (if sanityResult.successfulValidation then 1 else 0)

-- Bytes [0..32) of the serialized result are the NPR root.
#guard (serialize_stateless_output sanityResult).take 32
        == compute_new_payload_request_root sanityInput

-- `SpecAccepts` is inhabited end-to-end on the sanity pipeline: the
-- schema-prefixed sanity bytes deserialize, validate (placeholder seam),
-- and yield the matching root — i.e. the soundness target is satisfiable.
#guard match sanityInputBytes with
  | .ok bytes =>
      (match deserialize_stateless_input bytes with
       | .ok si =>
           (verify_stateless_new_payload si executeAlwaysOk).successfulValidation
             && (compute_new_payload_request_root si
                   == compute_new_payload_request_root sanityInput)
       | .error _ => false)
  | .error _ => false

/- A Prop-level `SpecAccepts` witness theorem is deliberately NOT stated
   here: the SpecRef decoders (`decodeFully`, the SSZ deserializer) are
   well-founded-recursive, so concrete runs do not kernel-reduce under
   `decide` (the `#guard`s above are interpreter-evaluated, which is the
   project-standard sanity artifact for such pipelines). Prop-level
   witnesses on concrete inputs arrive with `.64`'s simulation machinery,
   which never needs to reduce the spec on concrete bytes. -/

end EvmAsm.Stateless
