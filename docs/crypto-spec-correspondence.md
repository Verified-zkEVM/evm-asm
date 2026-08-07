# Crypto — spec correspondence

**Status: live authority.** Method: [`docs/agents/spec-correspondence.md`](agents/spec-correspondence.md).
Sibling instances: [`docs/rlp-spec-correspondence.md`](rlp-spec-correspondence.md),
[`docs/bal-spec-correspondence.md`](bal-spec-correspondence.md),
[`docs/ssz-spec-correspondence.md`](ssz-spec-correspondence.md).

Read this before claiming a crypto routine agrees with anything.

## Headline

⚠️ **This family's characteristic failure is naming the wrong prime, and it has
already happened twice in the tree.** BLS12-381 has two constants that both get
called "the modulus":

| name | value | bits | who checks it | reference |
|---|---|---|---|---|
| **base field** `blsP` | `0x1a0111ea…aaab` | 381 | `blsg_lt_p` (against `blsg_p_be`) | `Bls12.bytes_to_fq` |
| **scalar order** `BLS_MODULUS` | `0x73eda753…0001` | 255 | `blsk_lt_be` | `Kzg.bytes_to_bls_field` |

#11574 as filed, and `docs/leaf-routine-targets.md` before #11676, both paired
`blsg_lt_p` with `bytes_to_bls_field` / `BLS_MODULUS`. That is a **different
prime checked by a different routine**. `Stateless.Crypto.blsP_ne_blsModulus`
(`EvmAsm/Stateless/Crypto/FieldAssertions.lean`) pins the two as distinct so the
confusion is a build failure rather than a review miss.

The second recurring hazard is quieter: **the two sides of a BLS bridge read
byte lists of different lengths**, and juxtaposing them typechecks. See
*Boundary chosen*.

## Pins

- Reference: `execution-specs` submodule at the tree's pinned gitlink, fork
  `amsterdam`.
  - `vm/precompiled_contracts/bls12_381/__init__.py:426-454` — `bytes_to_fq`
  - `vm/precompiled_contracts/alt_bn128.py:39-82` — `bytes_to_g1`
- ⚠️ **Both reference functions bottom out in packages the repo does not
  vendor**, so two clause kinds in the tables below are *read*, not
  machine-checked (method doc §6a):
  - `py_ecc` — `FQ.field_modulus` / `field_modulus`
    (`py_ecc/fields/field_properties.py:29` and `:24`). Both verified equal to
    the port's constants at the pinned version.
  - CPython's `int.from_bytes(·, "big")` and `U256.from_be_bytes`, against the
    port's `Nat.fromBytesBE`.
  `scripts/check-spec-refs.sh` can machine-check a `forks/.../x.py:NNN` citation;
  it cannot check these.

## Boundary chosen

**Guest routine ↔ `SpecRef` port function, at the field-element decode step.**

⚠️ **The BLS boundary needs an explicit relation to be statable at all, and this
is the part worth reading twice.** `bytes_to_fq` consumes a **64-byte** EIP-2537
wire felt; `blsg_lt_p` scans **48** compact bytes. Both sides have type
`List Byte → Nat`, so a bridge that simply juxtaposed them would *elaborate* —
and be about two different lists.

The wire felt is `16 zero bytes ++ 48 big-endian bytes`, and the pad is a real
guest artifact rather than a modelling convenience. Two independent sightings:

- **Written** by `blsk_g1_wire` (`scripts/asm-fixtures/bls12KzgG1WireFunction.s`,
  `Programs/Bls12Kzg.lean:496`): 16 × `sb zero`, then 48 × `lbu`/`sb`, per
  coordinate at a 64-byte stride.
- **Checked** on every calldata read — see the table in *Gaps* below. This is
  the load-bearing sighting; the writer never sees calldata.

`Stateless.Crypto.eip2537_wire_pad_value` states the relation
(`fromBytesBE w = beBytesToNat (w.drop 16)` under the pad hypothesis), resting on
`Nat.fromBytesBE_zero_prefix` and on `beBytesToNat_eq_fromBytesBE` (#11677) —
which is itself needed because the tree has **two** big-endian decoders and
nothing had said they agree.

⭐ **BN254 needs no such step, and the asymmetry is recorded rather than
mirrored.** `bytes_to_g1` reads `buffer_read(data, 0, 32)` against a guest
routine scanning the same 32 bytes. Writing a vacuous BN254 pad lemma to make the
families look symmetric would assert a relation with no content.

## Why there is no differential

No executable differential exists for this family, and none is cheap. A
`Subject` must stay out of the Mathlib import closure (method doc §9); the
reference behaviour here is `py_ecc` field arithmetic, which is neither vendored
nor portable into the harness. So every row's value is bounded by the port's
fidelity to the Python, which is what the clause tables in
`EvmAsm/Progress/Correspondence.lean` establish — hence `.ported`, never
`.bridged` or `.diff`.

## Routine table

Verdicts and bases match `EvmAsm/Progress/Correspondence.lean`; the clause tables
live there.

| routine | spec | verdict | basis | reference |
|---|---|---|---|---|
| `blsg_lt_p` | `blsgLtP_spec_specref` | `domainRestricted` | `ported` | `Bls12.bytes_to_fq` |
| `bnf_lt_p` | `bnfLtP_spec_specref` | `agrees` | `ported` | the `x >= field_modulus` guard of `Bn128.bytes_to_g1` |

Machine triples behind them, both registered in `EvmAsm/Progress/Routines.lean`:
`Bls12G1LtPSAsm.blsgLtP_spec` (`Programs/Bls12G1LtPSAsm.lean:734`) and
`Bn254FieldLtPSAsm.bnfLtP_spec` (`Programs/Bn254FieldLtPSAsm.lean:732`).

⚠️ **Both machine triples predate their rows by months.** They were missed
because a name search for the *routine* finds the emitting module, and specs live
in sibling `*SAsm` modules — the #10779 lesson. `docs/leaf-routine-targets.md:98`
records the same correction. What #11574 asked for that genuinely did not exist
was the vocabulary and the rows, not the proofs.

⚠️ **Predicate agreement is the ceiling for both rows.** `lt_p` returns a boolean
in `a0`, never the field element, so **value** agreement is not available from
these routines and must not be claimed of them.

⚠️ **`bnf_lt_p`'s `agrees` is graded against a CLAUSE**, named in the row's
`reference`. `bytes_to_g1` also bounds `y` and tests `y² = x³ + 3`; this routine
looks at neither. Grading it as whole-function agreement would be an overclaim.

## Gaps and follow-ups

**1. The BLS pad composition is unproved — and that, not a behavioural
divergence, is why the row is `domainRestricted`.**

The guest *does* check the pad. Every calldata reader calls
`blsg_is_zero_n(ptr, 16)` and rejects on nonzero before the 48-byte scan:

| reader | pad check | reachable via |
|---|---|---|
| `blsg_decode_g1` | `Programs/Bls12G1.lean:692-700` (both coordinates) | 0x0b, 0x0c, 0x0f |
| `blsg2_decode_g2` | `Programs/Bls12G2.lean:774-784` (all four felts) | 0x0d, 0x0e, 0x0f |
| `zkvm_bls12_map_fp_to_g1` | `Programs/Bls12MapG1Real.lean:23-29` | 0x10 |
| `zkvm_bls12_map_fp2_to_g2` | `Programs/Bls12MapG2Real.lean:23-38` | 0x11 |

All are live: the dispatch table wires 0x0b..0x11 at
`Programs/PrecompileSharedExecute.lean:136-142`.

⚠️ **What is not proved is that `blsg_is_zero_n(16) ∧ blsg_lt_p(48)` implies
`bytes_to_fq`'s verdict on the 64-byte felt**, and it cannot be yet: those
decoders exist only as assembly **strings** — no `Program`, no `_eq_prog` drift
guard, no fixture — so no triple is statable over them. **Converting
`blsg_decode_g1` is the prerequisite for regrading this row to `agrees`**, and it
is the single highest-value next step in this family.

Note the resulting shape: the range check underneath is a *proved* routine while
the pad guard above it is *unverified assembly text*. That inversion is worth
fixing on its own terms.

**2. The BN254 port omits a length guard.** `alt_bn128.py:59` raises on
`len(data) != 64`; `Bn128.bytes_to_g1` has no such check. **Not recorded as a
`portDefect`**, because it is unreachable — every port call site passes
`buffer_read data k 64` (`SpecRef/PrecompilesCurve.lean:113/115/124`) and
`buffer_read` pads to exactly `size` (`SpecRef/Vm.lean:299-301`). An unreachable
defensive check is not a behavioural divergence. It is named here rather than
dropped because a future caller handing `bytes_to_g1` a short list **would**
diverge: the port would read a short prefix, the Python a zero-padded 32 bytes,
and those are different numbers.

**3. The rest of the family is unregistered.** These two rows cover the field
*bound* checks only. Point decode, the curve-equation tests, the MSM/pairing
kernels, and the whole KZG tower have no correspondence rows. The
`g1AffineIs` / `bnPointIs` vocabulary landed in #11679 with the on-curve
condition **stated, not proven** — that is deliberate, and it is what a future
point-decode row would be written against.

**4. `docs/4ch8f-crypto-kernel-inventory.md:53`** claimed no `cpsTripleWithin`
connects any crypto asm body to its spec. Corrected in this change — roughly 40
`*SAsm.lean` triples falsify it, including the two here.

## Reproduce

```
lake build EvmAsm.Progress.Correspondence EvmAsm.Progress.Routines
bash scripts/check-registry-crosscheck.sh
bash scripts/check-registry-crosscheck.sh --self-test
python3 scripts/gen-axiom-witnesses.py --write && bash scripts/check-axioms.sh
```

There is no `lake exe correspondence-check crypto` subject — see *Why there is no
differential*. Do not add one without a reference that can live outside the
Mathlib closure.
