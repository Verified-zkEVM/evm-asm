# Never-emitted String defs under `Programs/` (Task 2)

Measured on working tree `perf/guest-layout-param-prototype` (Programs surface
matches `origin/main` aff464653 for this question; BloomAddValue param does not
change String reachability). Analyzer: Lean-level identifier reachability
(`/tmp/opencode/never_emitted2.py` — not committed). **Not** symbol-addresses.tsv
(void: mixes function entries with branch labels).

## Method

1. Collect every top-level `def`/`abbrev` with type `String` under
   `EvmAsm/Codegen/Programs/**/*.lean` → **2555** defs.
2. Build a String→String reference graph (identifier mention in body).
3. **Emission roots** (deliberately exclude `theorem`/`lemma` — those are
   guards/`_eq_prog` and must not count as emission):
   - any non-String `def`/`abbrev`/`opaque`/`instance` body in Programs that
     names a String def (BuildUnit fields, helpers, concatenations);
   - any mention of a Programs String def from Lean under `EvmAsm/Codegen/`
     **outside** `Programs/` (Dispatch, Driver, …).
4. Reachability from roots through the String→String graph.
5. **Never-emitted** = String defs not reachable.

Spot-audit: dead names have only their `def` line and (when present) their own
`_eq_prog` / `#guard` — no concatenation consumer.

## Headline

| Quantity | Count |
|---|---|
| String defs | 2555 |
| Emission roots | 1664 |
| Reachable from emission | 2519 |
| **Never-emitted** | **36** |
| Files with ≥1 never-emitted | 18 |
| Never-emitted inside modules that `import GuestAddrs` | **2** (2 files) |
| Modules whose *every* String def is never-emitted | 7 |

Coord’s “seven in one file” reproduces exactly:

`PrecompileBackendProbes.lean` — 7× `zkvm*SafeFailWrapper` (only the `def`
line; nothing concatenates them).

## Per-module breakdown (all 36)

```
  7  PrecompileBackendProbes.lean
       zkvmBlake2fSafeFailWrapper
       zkvmBls12G1MsmSafeFailWrapper
       zkvmBn254G1AddSafeFailWrapper
       zkvmBn254G1MulSafeFailWrapper
       zkvmBn254PairingSafeFailWrapper
       zkvmKzgPointEvalSafeFailWrapper
       zkvmSecp256r1VerifySafeFailWrapper
  4  CreateCodeEffectLog.lean
       codeStateCommitPendingFunction
       codeStateFindFunction
       codeStatePendingContainsFunction
       codeStateUpsertFunction
  3  AmsterdamSystemTx.lean
       liAmsterdamAuthStateGas
       liAmsterdamStorageSetStateGas
       liAmsterdamSystemStateGasReservoir
  3  PrecompileRuntime.lean
       chargeBls12G1MsmGasAsm
       chargeBls12G2MsmGasAsm
       chargeBls12PairingGasAsm
  3  Selfdestruct.lean
       selfdestructBeneficiaryNonstorageAsm
       selfdestructNewAccountSurchargeAsm
       selfdestructRecordSeenOriginAsm
  2  Bls12Field.lean
       bls12FpAddFunction
       bls12FpMulFunction
  2  CallFrameDescend.lean
       ziskCallDescendDataSection
       ziskCallDescendPrologue
  2  CreateRuntime.lean
       createCopyChildReturndataToFrameAsm
       createExecuteInitcodeFrameCallAsm
  1  BlockVerdictReceiptGate.lean   bvRuntimeCompletenessClear
  1  Bls12G1Eq48SAsm.lean           blsgEq48Function
  1  Bls12G1IsZeroNSAsm.lean        blsgIsZeroNFunction
  1  Bls12G2EqNSAsm.lean [GuestAddrs] blsg2EqNFunction
  1  Bn254CurveIsInfSAsm.lean       bncIsInf64Function
  1  Eip7702Authority.lean [GuestAddrs] eip7702WarmRecoveredAuthoritiesDataSection
  1  RegistryMain.lean              lookupProgramMain
  1  RlpWalk.lean                   rlpField0ToU64Function
  1  Secp256k1FieldEq32SAsm.lean    secfEq32Function
  1  Secp256k1FieldIsZeroSAsm.lean  secfIsZero32Function
```

## GuestAddrs / build-cost reading

- Only **2** never-emitted Strings sit in modules that import `GuestAddrs`
  (`blsg2EqNFunction`, `eip7702WarmRecoveredAuthoritiesDataSection`).
- Those modules also host other live code; this is **not** “pure GuestAddrs
  import solely for dead Strings” at module granularity.
- Several never-emitted names are verified SAsm re-emit `*Function` wrappers
  whose `_prog` may still be image-linked via the Program/GuestImage path.
  This measurement is **String-emission** only; Program-linked presence was
  **not** folded in (would require GuestImageEntries / MANIFEST join — separate
  question). So some of the 7 “modules_all_strings_never_emitted” SAsm leaves
  may still contribute Program objects to the image while their String def is
  dead weight for the asm-string pipeline.

## What this is / is not

| Claim | Status |
|---|---|
| Lean-level String reachability from emission consumers | **Measured** |
| Guard-only references do not count as emission | **Yes** (theorem/lemma excluded from roots) |
| symbol-addresses.tsv missing-label count | **Not used** (void, as coord warned) |
| Whether dead Strings’ modules could drop GuestAddrs | **Only 2 dead in GA importers; not module-pure** |
| Program/`_prog` image linkage for the same symbols | **Not measured** |
| Byte size / elab-time cost of the 36 | **Not measured** |

## Reproduction

```bash
python3 /tmp/opencode/never_emitted2.py
# or restore the script body from this session’s analyzer
```
