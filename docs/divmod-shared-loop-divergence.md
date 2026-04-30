# DIV/MOD shared-loop divergence survey (issue #266 slice 1)

Goal: identify exactly where the DIV and MOD full-path proofs diverge, so we can
factor a shared preloop+loop spec and stop duplicating ~5 KLOC of `ModFullPath*`
files.

Source files surveyed (totals via `wc -l`, 2026-04-30):

  Compose/FullPathN3.lean            346
  Compose/FullPathN3Loop.lean         89
  Compose/FullPathN3LoopUnified.lean 819
  Compose/FullPathN4.lean           1025
  Compose/PhaseAB.lean               976
  Compose/Epilogue.lean             (DIV preamble + denorm + epilogue)
  Compose/ModEpilogue.lean           146
  Compose/ModFullPathN3.lean         355
  Compose/ModFullPathN3LoopUnified.lean 291
  Compose/ModFullPathN4.lean         696
  Compose/ModPhaseBn3.lean           156
  Compose/ModPhaseBn21.lean          378

Total Mod* files in Compose/: 5,579 lines (17 files).

## (a) Exact PC at which DIV and MOD diverge

The two programs `divCode` and `modCode` (defined in `Compose/Base.lean`,
lines 63 and 83) are identical except for **block 10**: `divCode` uses
`divK_div_epilogue 24`, `modCode` uses `divK_mod_epilogue 24`. Both
epilogues are 40 bytes and start at:

    epilogueOff = 1008          (named in Compose/Offsets.lean)

Everything before `epilogueOff` (PCs `base + 0` through `base + 1008`) is
**byte-identical instructions** between DIV and MOD. The denorm block lives at
`denormOff = 908` and runs `base+908 → base+1008`; it is shared. The epilogue
itself runs `base+1008 → base+1048` and is the only point of true code
difference.

**Note on the issue text.** Issue #266's body says "the divergence is at
~base+904, start of Phase B". This is off by two counts:

  - The actual end-of-shared / start-of-divergent-epilogue PC is
    `base + epilogueOff = base + 1008`, not `base + 904`.
  - "Start of Phase B" is a different block entirely (`base + phaseBOff =
    base + 32`, the b=0 / leading-limb analysis), not the post-loop epilogue.

What sits at `base + 904`? Nothing — it falls inside the loop body; the loop
body ends at `base + loopBodyOff + 460 = base + 908 = base + denormOff`.
The "904" number in the issue body looks like a typo for either 908 or 1008.

So the *useful* divergence point for slice 2 is:

    PC = base + epilogueOff (= base + 1008)

with the entire preamble+denorm at `base+908 → base+1008` ALSO being shared
(both `divK_denorm_body_spec_within` and `mod_denorm_body_spec_within` already
exist and are byte-identical apart from `divCode` vs `modCode` in their
`cpsTripleWithin` argument).

## (b) Precise intermediate assertion at the divergence PC

At `base + epilogueOff`, after the denorm body runs, the heap looks like
(quoting `evm_div_preamble_denorm_epilogue_spec` and
`evm_mod_preamble_denorm_epilogue_spec_within`):

For DIV-path callers, the standing precondition fed into `divK_div_epilogue 24`
(the actual "Q[]→output" loads) is the post-state of `divK_denorm_body`:

    (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u3') ** (.x7 ↦ᵣ u3 <<< antiShift) **
    (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ 0) **
    (sp + signExtend12 4056) ↦ₘ u0' ** ... ** (sp + signExtend12 4032) ↦ₘ u3' **
    -- plus q[] memory and output-buffer memory:
    (sp + signExtend12 4088) ↦ₘ q0 ** ... ** (sp + signExtend12 4064) ↦ₘ q3 **
    (sp + 32) ↦ₘ m0 ** (sp + 40) ↦ₘ m8 **
    (sp + 48) ↦ₘ m16 ** (sp + 56) ↦ₘ m24

DIV's epilogue then loads q[] into the output (`m0..m24` ← `q0..q3`).
MOD's epilogue loads u'[] (the denormalized remainder, `u0'..u3'`) into
the output instead. The pre-state at `base + epilogueOff` is identical
in both cases — no register, no memory cell, no PC differs.

Suggested name for slice 2: `denormDonePost sp shift u0 u1 u2 u3 q0 q1 q2 q3
m0 m8 m16 m24` (or similar). It is exactly the post-state of
`divK_denorm_body_spec_within` augmented with the unchanged q[] and m[]
chunks, and lives entirely on `sharedDivModCode`.

## (c) Helpers/theorems that already line up with this split point

These specs already terminate at `base + epilogueOff` (= 1008) or at the
denorm boundary `base + denormOff` (= 908), and so are immediately reusable:

  - `divK_denorm_body_spec_within`           Epilogue.lean:85
  - `mod_denorm_body_spec_within`            ModEpilogue.lean:34
  - `divK_denorm_preamble_spec_within`       (private) Epilogue.lean
  - `mod_denorm_preamble_spec_within`        (private) ModEpilogue.lean (and a re-proved private copy
                                              `fullPath_mod_denorm_preamble_spec_within` in FullPath.lean)
  - `evm_div_preamble_denorm_epilogue_spec`  FullPath.lean:504
                                             `base+908 → base+1068`, on `divCode`
  - `evm_mod_preamble_denorm_epilogue_spec_within`  ModFullPathN4.lean:121
                                             `base+908 → base+1068`, on `modCode`

The cleanest reusable shared post-loop sub-spec would be on `sharedDivModCode`
and end at `base + epilogueOff`; both the DIV and MOD epilogues are 10
instructions and would compose in via `cpsTripleWithin_extend_code` against
their respective code-membership monos.

`sharedDivModCode_sub_modCode` (and the implicit DIV mirror) already exist —
they are imported by `ModFullPathN1LoopUnified.lean`,
`ModFullPathN2LoopUnified.lean`, `ModFullPathN3LoopUnified.lean` to lift loop
specs from `sharedDivModCode` to `modCode`. So **the sharing infrastructure
through end-of-loop is already in place**; the missing piece is sharing the
denorm preamble+body too (i.e. extending the shared region from
`base + denormOff` to `base + epilogueOff`).

## (d) Theorems that are entangled and need to be re-split

Currently each `evm_{div,mod}_n{1,2,3,4}*_full_unified_spec` (and its `_call`,
`_max`, `_shift0`, `_beq` variants) does:

    preloop+loop  →[seq_perm_same_cr]→  preamble_denorm_epilogue

in one `cpsTripleWithin_seq_perm_same_cr` call. Examples:

  - FullPathN3LoopUnified.lean:801  `evm_div_n3_full_unified_spec`
        `hA = evm_div_n3_preloop_loop_unified_spec`     (base → base+908)
        `hB = evm_div_n3_denorm_epilogue_bundled_spec`  (base+908 → base+1068)
        composed via `cpsTripleWithin_seq_perm_same_cr`
  - ModFullPathN3LoopUnified.lean:272  `evm_mod_n3_full_unified_spec`
        symmetric
  - FullPathN2LoopUnified.lean:233 / ModFullPathN2LoopUnified.lean:299
  - FullPathN1LoopUnified.lean / ModFullPathN1LoopUnified.lean
  - FullPathN4.lean:449 / ModFullPathN4.lean (n=4 max+skip and call+skip)
  - FullPathN4Beq.lean:611 / FullPathN4Beq.lean:806  (beq-path variants)
  - FullPathN2Full.lean:131, FullPathN2Cases.lean:124,257,390,...
  - FullPathN4Shift0.lean / ModFullPathN4Shift0.lean

Good news: the `*_denorm_epilogue_bundled_spec` already isolates the
post-loop chunk into a single named `have`, so the preloop+loop side is
ALREADY independently provable; the duplication is really at the level of
the bundled-epilogue specs (`evm_div_n3_denorm_epilogue_bundled_spec`,
`evm_mod_n3_denorm_epilogue_bundled_spec`, etc.).

### Recommended slice ordering for #266

Slice 2 (next): pick the n=3 max×max path. Define a single
`denormDoneDivPost` / `denormDoneModPost` (post-state at
`base + epilogueOff`). Prove both by strengthening the existing
preloop+loop specs to also run the shared denorm body (i.e., extend the
shared post-loop boundary from `denormOff` to `epilogueOff`).

Slice 3: prove a single `evm_divMod_preloop_loop_denorm_unified_spec` on
`sharedDivModCode` (n=3 max×max), exit PC `base + epilogueOff`. Lift to
`divCode` and `modCode` via the existing `sharedDivModCode_sub_*` infra.

Slice 4: build MOD `evm_mod_n3_full_unified_spec` by composing the shared
preloop+loop+denorm with just the 10-instruction `divK_mod_epilogue 24`.

Slice 5: replicate slices 3/4 for n=2, n=1, n=4 paths and the call/beq/shift0
variants (~12 extra full-path theorems).

Slice 6: delete `ModFullPathN{1,2,3,4}*.lean` whose theorems are now obtained
by composition rather than re-proof. Note: ModEpilogue.lean's
`mod_denorm_body_spec_within` and `mod_denorm_preamble_spec_within` would
also shrink (or be deleted entirely if the shared `divK_denorm_body_spec_within`
on `sharedDivModCode` is wired up via `sharedDivModCode_sub_modCode`).

Estimated savings if executed: removing ~3,500 lines from 9 `ModFullPath*`
files, replaced by ~600 lines of shared specs + thin per-mode wrappers.
That's net ~2,900 LOC, in line with issue #266's "4-6 KLOC" estimate.

## Caveat / not-in-scope notes

  - The *preloop* (PhaseA, PhaseB-by-n, CLZ, Norm, copyAU, loopSetup) is
    already fully shared — every `evm_div_n*_to_loopSetup_spec_within` has a
    one-to-one `evm_mod_n*_to_loopSetup_spec_within` mirror with byte-identical
    proofs but `modCode` instead of `divCode`. Those mirrors (in
    `Mod{PhaseBn3,PhaseBn21,CLZ,NormA,Norm,FullPathN{1,2,3}}.lean`) are
    candidates for the same lift-via-`sharedDivModCode_sub_modCode` treatment.
    But they predate the shared-code abstraction; switching them is a separate
    cleanup orthogonal to the loop-pipeline factoring tracked here.
  - Issue #266 mentions 4-6 KLOC; the bulk is in the LoopUnified paths
    (n=3: 2×290 LOC = 580; n=2: 2×311 = 620; n=1: 2×354 = 708; n=4 base:
    1025+696 = 1721). Even halving those four pairs yields 2.6 KLOC net.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
