# The software-crypto-kernel verification strategy (bead evm-asm-4ch8f.11)

How the software crypto kernels (MODEXP, secp256k1 recovery, P256VERIFY,
BN254 add/mul/pairing, the BLS12-381 family + KZG, BLAKE2F, RIPEMD160,
hash bridges) will be verified, and what the pilot
(`EvmAsm/Rv64/SAsm/PowLadderDemo.lean`, fully proved) establishes.

Evidence base: `docs/4ch8f-crypto-kernel-inventory.md` (bead .11.1 — the
per-kernel measurements this document turns into decisions).  Companion:
`docs/4ch8f-interp-strategy.md` (bead .10 — the `Fn.SpecS`/`whileS`
machinery this strategy builds on), `docs/sasm-design.md`.

## 0. The two structural facts, and what they buy

1. **The accelerator seam is typed and closed.**  Every field multiply,
   curve add/double, permutation, and Blake2b round in the guest is one
   of 17 CSRS ids with concrete, kernel-checked semantics
   (`MachineState.csrsWrite`/`csrsValid`, `Accel.*`, bead .1), reached
   through a handful of `jal`-reused wrapper routines that wave B
   converted to typed `Instr.CSRS` `Program`s (`p256_op_with`,
   `secf_mul_mod_p/n`, `bnf_*`, `blsf_*`, …).  A proof of ONE wrapper
   covers thousands of dynamic call sites.

2. **The SAsm block engine does not (and should not) execute `CSRS`.**
   `instrOk` rejects it; there was, before this bead, no machine-level
   CPS triple for any accelerator step.  The sanctioned crossing is the
   handle mechanism: `FnHandle`/`FnHandleS.sound` is an arbitrary
   hand-proven `cpsTripleWithin`, so an accelerator wrapper can be
   verified once directly against `step_csrs` + the `.1` semantics and
   then consumed by ordinary SAsm proofs via `Stmt.call`/`callRegS`.
   The pilot establishes this crossing end-to-end (§5).

Everything below is sequenced around those two facts.

## 1. Per-kernel tier assignment

Three tiers were on the table:

- **F — full functional verification**: a `cpsTripleWithin`/SAsm triple
  connecting the kernel body to a Lean functional spec of the
  precompile's input→output behavior.
- **G — verified glue over concrete accelerators**: same machinery, but
  the headline spec is stated at the field/group level (the accelerator
  postconditions composed), not at the precompile level.
- **T — trusted kernel with a differential obligation**: no body proof;
  correctness rests on the `codegen-zisk-*-check.sh` probes, with the
  obligation stated precisely and a removal bead filed (no-conservative-
  skips policy).

**Decision: every kernel gets tier F as its end state; no kernel is
permanently T.**  Tier G is rejected as a *terminal* tier because the
`.8` headline (soundness against execution-specs) composes only through
precompile-level specs — a field-level-only proof leaves exactly the
protocol-level layer (Miller loops, SSWU, KZG plumbing) unverified, and
the inventory shows that layer is where the hand-baked constants and
hoisting rewrites live (P1-D6/D7): the riskiest code would stay outside
the proof.  Tier G survives only as the *intermediate milestone* inside
each kernel bead (field/group layer first, protocol layer on top).

Tier T is rejected as a resting place on the strength of bead .11.5:
the MODEXP `exp == 0 ∧ modulus == 1` divergence sat undetected under
months of differential probing — bignum- and protocol-class kernels
have corner cases that vector suites do not reach.  Kernels *waiting*
for their proof remain de-facto trusted with the existing differential
probes as the interim obligation; that state is tracked by the open
consumer beads themselves (.38/.57/.58 children), which double as the
policy-required removal beads.  One kernel-shaped caveat: the two BLS
maps' RFC 9380 sqrt-candidate guarantee and the KZG "unreachable"
assertion are *completeness* (false-reject) risks, not soundness risks,
under the `.8` statement; their proofs may land last (sequencing below)
without weakening the headline.

**Sequencing (by consumer value and shared-infrastructure reuse):**

| wave | kernels | tier path | why now |
|---|---|---|---|
| 1 | shared field-arith library (§2) + secp256k1 field/scalar stack | F | unblocks .38 → tx-sender verification (.39/.40), the highest-value consumer; every routine is a ladder/wrapper instance of the pilot shapes |
| 2 | secp256k1 curve + recovery (`secp256k1_recover_r`, `…_pubkey_staged`) | F | completes .38; group-law layer over 0x803/0x804 accelerators |
| 3 | hash bridges (`zkvm_sha256`, `zkvm_keccak256`, `…_segments`), BLAKE2F | F | byte-plumbing over one accelerator each; pattern-setters for .17/.18; BLAKE2F needs the `whileS` rounds loop (attacker-controlled count) |
| 4 | MODEXP backend + dispatcher | F | pure bignum (no seam); the .11.5 class of bugs makes this the strongest proof-over-tests case; needs the schoolbook-mul + binmod invariants (§2, the only genuinely new bignum layer) |
| 5 | P256VERIFY | F | whole group law through ONE wrapper (`p256_op_with`); direct pilot replay at linked addresses; spec = execution-specs `secp256r1_verify` |
| 6 | BN254 G1 add/mul; BLS12 G1/G2 add/msm; RIPEMD160 | F | group-law case-splits over curve accelerators + the scalar-mul skeleton; RIPEMD160 is self-contained hash-schedule |
| 7 | Fp2/FQ12 towers (BN254 + BLS12), Fermat/sqrt ladders per family | F | tower-field layer; all ladders are `powFn_spec` instantiations |
| 8 | pairings (0x08, 0x0F), BLS maps (0x10, 0x11), KZG (0x0A) | F (G milestone first) | protocol level; consumes everything above; the two hoisting rewrites and the RFC 9380 branch search get dedicated lemma beads |

## 2. The field-arithmetic library plan

The inventory's §4 identified the shared layer; the decision is its
Lean shape.

**Spec vocabulary: `Nat`-modular arithmetic.  Not `ZMod`, not limb
`BitVec`s.**  Grounds:

- The trusted seam is already `Nat`: `Accel.arith256Mod a b c m =
  (a*b+c) % m`, `Accel.curveAdd`, `Accel.powMod` — all `Nat` functions
  (ZiskAccel.lean).  A `Nat` spec layer composes with the seam by
  `rfl`-level algebra (`Nat.mul_mod`, `Nat.pow_mod`, `omega`).
- The repo has **zero** `ZMod` usage today; the whole SpecRef corpus
  (`Stateless/SpecRef/Crypto.lean`) is `Nat` over `List (BitVec 8)`.
- Kernel-reducibility: `decide`-KATs (the adversarial guard that the
  spec is not vacuously shaped) work out of the box on `Nat`.

*Rejected — `ZMod p`*: buys mathlib's field/group instances (inverses,
`ZMod.pow_card_sub_one_eq_one` for Fermat), but every seam crossing
would pay a `ZMod.val`/`Nat` coercion tax in exactly the proofs that are
already the volume cost, and the group-law facts we actually need
arrive cheaper as targeted lemmas (below).  `ZMod` remains available
*inside* pure side-lemmas (state over `Nat`, prove via `ZMod` if
convenient); the *interfaces* stay `Nat`.  *Rejected — bare limb
vectors*: pushes carry reasoning into every consumer; the decode
functions (`wsNat256`, `Accel.leLimbsToNat`) centralize it once.

**Where mathlib enters.**  Only through ordinary `Nat`/`List` lemmas so
far (`Nat.pow_mod`, `Nat.testBit_*`, `List.drop_take`).  Fermat's little
theorem is needed once per prime family to justify `inv = x^(p-2)` and
`sqrt = x^((p+1)/4)` *against a spec that demands a true inverse/root* —
plan: state as project lemmas over `Nat` (`x * powMod x (p-2) p % p = 1`
for the five concrete primes), prove via `ZMod.pow_card_sub_one_eq_one`
+ `ZMod.natCast` transport in one dedicated file.  This is the single
place heavyweight mathlib number theory is imported; record its
dependency weight there and nowhere else.  (For inversions the *kernel
algorithm and the EL spec both* compute via `pow`, equivalence needs no
Fermat at all — Fermat is needed only where the spec-side semantics is
"the inverse", e.g. chord-slope divisions inside `Accel.curveAdd`'s own
correctness story and ECDSA's `s⁻¹`.)

**Library layout** (new files; nothing under `Programs/` or
`GuestAddrs`-coupled):

| file | contents | status |
|---|---|---|
| `EvmAsm/Crypto/PowLadder.lean` | `beBytesToNat`, `beBit`, `ladderStep`, `ladder`, `ladder_correct : ladder m x bs (8·len) = x ^ beBytesToNat bs % m` (1 < m), `beBytesToNat_testBit`, LE-limb round-trips (`leLimbsToNat_natToLeLimbs`) + kernel KATs | **landed (this bead)** |
| `EvmAsm/Rv64/SAsm/AccelStep.lean` | window decode/encode (`wsDword`, `wsNat256`, `leBytes32`), `readWords`/`writeWords` ↔ `bytesRegion` bridges, `csrs_arith256Mod_spec_within` (the CSRS step triple), `csrs_arith256Mod_ret_spec`, `arith256ModPre/Post`, **`arith256ModHandle : FnHandleS`** | **landed (this bead)** |
| `EvmAsm/Rv64/SAsm/PowLadderDemo.lean` | window-locality lemmas (`wsDword_setBytes_low`, `wsNat256_setBytes_leBytes32`, `flatMap_dwordBytes_slice`), the ladder pilot | **landed** (locality lemmas to be promoted into AccelStep when first reused) |
| `EvmAsm/Crypto/BeLe.lean` (planned) | BE↔LE marshalling spec: `beBytesToNat bs = leLimbsToNat (reverse-marshal bs)`; contract for the ~6 duplicated `*_be_to_le`/`_le_to_be` routines (32 B and 48 B) | wave 1 |
| `EvmAsm/Crypto/Bignum.lean` (planned) | schoolbook multiply and binary long-division loop invariants over LE limb lists (MODEXP backend's `modexp_mul`/`modexp_binmod`) | wave 4 |
| `EvmAsm/Crypto/ScalarMul.lean` (planned) | double-and-add fold over an abstract `(add, dbl, ∞-flag)` triple + `scalarMul_correct`; instantiated per curve with the accelerator group ops | wave 2/6 |
| `EvmAsm/Crypto/Fp2.lean` (planned) | pairs-of-`Nat` arithmetic matching `Accel.complexAddL/SubL/MulL` (u² = −1), norm/inverse | wave 7 |
| `EvmAsm/Crypto/Fermat.lean` (planned) | the per-prime Fermat/QR facts (the one mathlib-heavy file) | wave 2 (secp sqrt) |

The 384-bit (`0x80B`) clients reuse everything: `csrsWrite` routes both
ids through the same `Accel.arith256Mod`, so the step triple and handle
generalize by a `nLimbs` parameter (a mechanical follow-up bead — the
pilot pinned 4 limbs to keep the round-trip lemmas concrete).

## 3. The canonical glue-contract shape

**Decision — one shape, used by every accelerator wrapper:**

> A wrapper routine (`p256_op_with`, `secf_mul_mod_p`, `bnf_mul_mod_p`,
> `blsf_fp_mul`, curve/complex-op wrappers, …) is packaged as a
> **snapshot-parameterized handle** (`FnHandleS`) whose
> - `pre` names the parameter-block pointer register and pins the
>   block's five pointers to dword-aligned, 32-byte-fitting offsets
>   *inside the caller's rw window*, plus the accelerator's validity
>   side conditions (modulus ≠ 0; for curve ids: reduced coordinates,
>   x₁ ≠ x₂ / y ≠ 0);
> - `post rf₀ ws₀ A₀` is a *function of the entry snapshot*: the output
>   buffer becomes the `Accel.*` value of the entry window's decoded
>   operands (`ws = setBytes ws₀ dOff (leBytes32 (Accel.arith256Mod
>   a₀ b₀ c₀ m₀))`), registers and ambient assertion untouched;
> - `sound` is proven **at machine level** — `step_csrs` + the
>   `csrsWrite`/`csrsValid` `0x802`-arm lemmas + the
>   `bytesRegion`-vs-`readWords`/`writeWords` bridges — packaged through
>   the `Fn.retSpec`-style composition with `jalr_ret_spec`.  The SAsm
>   block engine is never extended.
>
> Kernel bodies are SAsm `Fn`s; each accelerator use is
> `Stmt.callRegS "…" rs [handle]` (singleton table).  Loops are
> `Stmt.while` for constant-trip ladders (fuel = the exact bit/limb
> count, symbolic in the length parameters) and `Stmt.whileS` where a
> per-execution runtime value must cross the loop (MODEXP's
> data-dependent `nb/ne/nm` bounds, pointer-parameterized buffers).

Concretely landed as `arith256ModHandle` + `arith256ModHandle_sound`
(AccelStep.lean), consumed by the pilot at two aliasing param blocks.
Two load-bearing details the pilot surfaced:

- **Aliasing is free under decode-valued posts.**  The square step has
  `a = b = d = acc`; because the post speaks only of *entry-decoded*
  values and one output splice, no alias side conditions are needed —
  this is what makes the per-kernel beads mechanical.
- **Keep handle `sound` proofs out of the structure literal.**  A
  `where sound := by …` literal makes every `.post`/`.pre` projection
  in consumer proofs re-elaborate the proof term (heartbeat blow-ups);
  the standalone-theorem + field-reference pattern is mandatory.

**Rejected alternatives.**
- *(A) Extend the SAsm block engine with a `CSRS` case*: touches the
  trusted `execInstrRF`/`instrOk`/`BlockSound` core; `execInstrRF`'s
  pure `(rf, ws)` state would need the full 5-pointer indirection and
  validity semantics inlined, and every existing block proof re-checked.
  The handle route reuses the soundness theory unchanged and produced a
  ~1-step triple instead.
- *(B) Monomorphic `FnHandle` per wrapper*: cannot state "output =
  function of entry operands" — the same fatal weakness the `.10`
  strategy identified for opcode handlers; the ladder invariant could
  not be re-established after the second call.
- *(C) A `Stmt.callS` (direct-call snapshot handle) primitive*: would
  read slightly better than the singleton `callRegS` + `LI` idiom, but
  adds a trusted soundness case for pure sugar.  Recorded as a
  nice-to-have (Opus-grade) if the per-kernel beads find the idiom
  noisy; not needed now.

## 4. The spec side

**Targets.**  Per kernel, the functional spec is a Lean port of the
execution-specs (`tests-zkevm@v0.4.0`) precompile function **where one
exists in pure Python** (MODEXP/EIP-198 arithmetic, `is_on_curve_*`,
the BN254/BLS py_ecc algorithms, `verify_kzg_proof`, BLAKE2F/RIPEMD160
compression).  Where execution-specs delegates to native libraries —
**ECDSA is the notable case**: `secp256k1_recover` calls `coincurve`,
`secp256r1_verify` calls `cryptography` — the Lean reference is defined
project-side over the `Nat` vocabulary (affine curve ops as in
`Accel.curveAdd`, ECDSA recover/verify as deterministic functions),
with kernel-checked KATs against the library-generated vectors already
in `scripts/codegen-zisk-*-check.sh`.  These references live in
`EvmAsm/Stateless/SpecRef/Crypto.lean`-adjacent files and connect to the
EL ABI through the existing `EvmAsm/EL/*Bridge.lean` surfaces.

**Algorithm-faithful porting is the cost-control decision**: since the
spec is (a Lean image of) the same *algorithm* the kernel implements,
kernel≡spec proofs are algorithm-to-algorithm and heavy abstract math
(group associativity, pairing bilinearity, hash security) is **out of
scope** — soundness is against execution-specs, not against textbook
definitions.  Number theory enters only at genuine kernel↔spec
divergences, each of which gets a named lemma bead:

1. Fermat inversion / sqrt exponents vs "the inverse/root" (§2,
   `Crypto/Fermat.lean`);
2. the two pairing hoisting rewrites (single denominator inverse,
   single final exponentiation across pairs) — `(∏ tᵢ/dᵢ)^k =
   (∏ tᵢ · (∏ dᵢ)⁻¹)^k` over the FQ12 quotient ring;
3. the secp sqrt skip-bit ladder vs `(p+1)/4` (the .11.2 fix's
   correctness, now provable rather than grep-audited);
4. RFC 9380's "exactly one of the 8 candidates is the root" for
   map-fp2-to-g2 (completeness-only; may be assumed as a documented
   completeness gap until wave 8);
5. MODEXP dispatcher-vs-backend agreement (.11.3) and the cap
   mismatch (.11.4) — the proof is keyed to the dispatcher's 1024-byte
   EIP-7823 domain, per .11.4's finding.

**Rejected**: mathlib's elliptic-curve machinery
(`Mathlib.AlgebraicGeometry.EllipticCurve.*`) as the group-law source —
it would import the heaviest corners of mathlib to prove facts
(associativity) that the algorithm-faithful strategy never needs; and a
`BitVec 256`-valued spec layer — every seam crossing would re-prove
`toNat` transport that `Nat` gets for free.

## 5. What the pilot proves (for the adversarial reviewer)

`EvmAsm/Rv64/SAsm/PowLadderDemo.powFn_spec` — zero sorries, axioms
`[propext, Classical.choice, Quot.sound]`:

> The MSB-first square-and-multiply ladder — exponent bits fetched from
> a read-only big-endian constant, every multiplication a
> `csrs 0x802` accelerator step through the `{a,b,c,module,d}`
> param-block wrapper, squaring under full aliasing
> (`a = b = d = acc`) — terminates with the accumulator decoding to
> **`x ^ (beBytesToNat ebytes) % m`** (`Nat.pow`, not a ladder-shaped
> restatement), for any modulus `1 < m < 2²⁵⁶`, any base, any exponent
> width up to 4096 bytes.

- **Is the spec really `x^e mod m`?**  The post is
  `wsNat256 ws 176 = x ^ Crypto.beBytesToNat ebytes % m`; the bridge
  from the fold is `Crypto.ladder_correct`, whose own shape is guarded
  by kernel-checked positive KATs (`ladder 1009 7 [0x01,0x23] 16 =
  7 ^ 0x123 % 1009` and a 3-byte case, `by decide`) — a wrong ladder
  (LSB-first, skipped squarings, off-by-one bit index) fails them.
- **Does the cap-VC close at 4569-bit widths?**  Fuel is
  `8 * ebytes.length`, *symbolic*; the `exhausted` VC closes by counter
  arithmetic for every length ≤ 4096 bytes (32768 bits) — no per-width
  re-proof, no gas coupling needed for constant-trip ladders.
- **First CSRS triple**: `csrs_arith256Mod_spec_within` is the first
  machine-level `cpsTripleWithin` over an accelerator instruction; its
  `csrsValid` obligations (six `validDwordRange`s + modulus ≠ 0) are
  discharged from window well-formedness, not assumed.
- **The `1 < m` precondition is load-bearing**: at `m = 1` the staged
  `acc₀ = 1` is unreduced and the invariant fails at entry — the exact
  .11.5 MODEXP corner; the strategy requires every ladder consumer to
  either gate `m > 1` upstream (P256/secp/BN254/BLS primes: trivially)
  or special-case it (MODEXP dispatcher — the .11.5 fix).
- **Composition risks exercised**: `callRegS` from inside a `while`
  loop body; two param blocks selected by a pointer register; staging
  (param pointers, modulus, base, zero addend) proven invariant under
  accumulator splices via the locality lemmas; the exponent fetched
  through the ro-region path with the `SLL`/mask bit test proven
  equivalent to `Nat.testBit` of the BE value.

Deliberate pilot simplifications, each mapped to follow-up work:
demo-local addresses (per-kernel beads re-instantiate at linked
addresses once .9.5's layout lands); 4-limb (`0x802`) only (§2 —
`nLimbs`-generic bead); BE→LE marshalling elided by staging LE operands
directly (the real wrappers convert; `Crypto/BeLe.lean` bead); the
exponent as a Lean-level ro constant (right for Fermat/final-exp
ladders; MODEXP's runtime exponent needs the `whileS` variant).

## 6. Decomposition (re-scopes .38/.57/.58; Opus/Fable split)

Fable = touches the trusted seam contract or new spec vocabulary;
Opus = instantiates an existing shape with a template.

1. **`.11.6` — generalize the accelerator handle** (Fable, one
   session): `nLimbs`-parametric `arith256ModHandle` (0x802 + 0x80B),
   curve/complex-op handles (`0x803/4/6/7/8/9/A/C/D/E/F/810`) with
   `ptValid` preconditions; promote the pilot's locality lemmas into
   AccelStep.
2. **`.11.7` — BE↔LE marshalling** (Opus): `Crypto/BeLe.lean` + verified
   generic converter triple; retires the 6 duplicated converters'
   proofs at once.
3. **`.11.8` — Fermat/QR facts** (Fable for the statement, Opus for
   per-prime instances): `Crypto/Fermat.lean` (the one mathlib-heavy
   file).
4. **`.11.9` — scalar-mul skeleton** (Fable): `Crypto/ScalarMul.lean` +
   the double-and-add SAsm shape with the software infinity flag, over
   abstract add/dbl handles.
5. **`.38a/b/c` — secp256k1** (Opus once .11.6/7/8 land): field stack
   ladders (= `powFn_spec` replays at linked addresses), curve ops over
   0x803/0x804 handles, recovery orchestration (Fable for the recovery
   spec statement).
6. **`.57a` — hash bridges + BLAKE2F** (Opus with the .17/.18 pattern;
   BLAKE2F's runtime-`rounds` loop is the first `whileS` consumer —
   Fable reviews the invariant).
7. **`.58a` — MODEXP** (Fable: `Crypto/Bignum.lean` invariants + the
   dispatcher/backend agreement per .11.3/.11.4; consumes the .11.5
   fix).
8. **`.58b` — P256VERIFY** (Opus for the arithmetic stack, Fable for
   the ECDSA-verify spec + the D4 512-bit-reduction lemma).
9. **`.58c` — BN254/BLS group + tower layers** (Opus).
10. **`.58d` — pairings/maps/KZG** (Fable for the hoisting lemmas and
    the RFC 9380 / KZG-unreachable completeness decisions; Opus for the
    Miller-loop body once the line-function spec exists).

The exec-log/dispatch interfaces are untouched — precompile kernels
compose with .57's router through the existing `EL/*Bridge` surfaces.
