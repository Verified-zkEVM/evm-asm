# SLH-DSA (FIPS 205) verifier — formally verified RV64 structure

A RISC-V (RV64) routine, written in the SAsm structured-assembly DSL, that
implements the **algorithmic structure** of SLH-DSA (FIPS 205) signature
verification, with an end-to-end proof that its emitted machine code computes
the ported FIPS 205 verification result — at a deliberately non-cryptographic
demonstration instance.

## Scope (read first)

The demonstration instance `demoPrims` makes **every hash an additive mixer**,
so the instantiated scheme has **no cryptographic security whatsoever**. What is
proved is that the RV64 code correctly implements FIPS 205's algorithmic
structure — `H_msg` digest split, FORS leaf recovery + auth-path climb, the
WOTS+ digit vector and per-chain completion, `T_len` compression, the XMSS
climb, and the root compare. SLH-DSA *correctness* (`verify ∘ sign = accept`)
holds for any choice of the opaque primitives, so the one-instruction mixer
keeps the verified code small while exercising every algorithmic component.
This is **not** a verified SLH-DSA verifier in the security sense.

## Where the program is

- **`slhVerifyFn`** — the verifier as a SAsm `Fn` (four blocks: `load`,
  `wsetup`, `wots`, `final`), in [`VerifySAsm.lean`](VerifySAsm.lean).
- **`slhVerify_program`** — the emitted flat RV64 `Program` (the actual machine
  code), same file. `slhVerify_position_independent` and `slhVerify_region_wf`
  (same file) prove the code is position-independent and the input region is
  well-formed.

Input format: 21 little-endian 64-bit words at the input arena base
`0x40000000` (PK seed/root, randomizer, packed message, the two FORS
leaf/auth words, the twelve WOTS+ chain words, the XMSS auth node). Output:
`a0 = 1` iff the signature verifies, else `0`.

## Where the topmost theorem is

Both in [`VerifyProof.lean`](VerifyProof.lean):

- **`slhVerifyFn_spec`** — the headline result: the full bounded CPS triple
  `(slhVerifyFn …).Spec base`, i.e. from any state satisfying the precondition
  (`a0 = inputBase`) the flattened program runs within `body.steps` steps to a
  state satisfying the postcondition. Discharged by `vcgen` (region
  well-formedness, the three load blocks' memory VCs, and the
  strongest-postcondition VC).
- **`slhVerifyFn_post_fips`** — the spec-level capstone: the postcondition, at
  the packed message word, is `a0 = 1` **iff** `SLHDSA.slhVerifyInternal`
  (the ported FIPS 205 algorithm) accepts the signature. Combined with
  `slhVerifyFn_spec`, this is end-to-end correctness of the machine code against
  the specification.

## Supporting pieces

| File | Contents |
| --- | --- |
| [`Scheme.lean`](Scheme.lean) (+ `Params`, `Address`, `Encoding`, `WotsChecksum`, `Wots`, `Xmss`, `Fors`, `Hypertree`, `Primitives`) | Ported FIPS 205 spec. `slhVerifyInternal` is the verification algorithm; `slhVerifyInternal_slhSignInternal` is the deterministic correctness core. Ported from VCVio; see [`LICENSE`](LICENSE). |
| [`DemoInstance.lean`](DemoInstance.lean) | The demo parameter set `demoParams`/primitive bundle `demoPrims`, and `demoVerifyWords` — the word-level reference verifier the RV64 code computes register-for-register. |
| [`DemoCorrect.lean`](DemoCorrect.lean) | `demoVerifyWords_correct` — `demoVerifyWords` equals `slhVerifyInternal demoPrims`. |
| [`VerifyProof.lean`](VerifyProof.lean) | The block-effect lemmas, the memory VCs, `slhVerifyFn_spec`, `slhVerifyFn_post_fips`, and the non-vacuity witnesses (`slhVerify_pre_inhabited`, `accept_witness`, `reject_witness`). |

## Building

```
lake build EvmAsm.SLHDSA
```

builds the whole development via the [`EvmAsm/SLHDSA.lean`](../SLHDSA.lean)
umbrella. Every theorem is kernel-checked and depends only on the three
classical axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no
`native_decide`/`bv_decide`.
