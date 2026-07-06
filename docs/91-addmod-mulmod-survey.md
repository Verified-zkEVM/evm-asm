# ADDMOD / MULMOD reuse strategy on top of DivMod (#91 slice 1)

This is the design-survey output for GH issue
[#91 — ADDMOD and MULMOD opcodes](https://github.com/Verified-zkEVM/evm-asm/issues/91).
Its job is to map out, before any Lean code lands, what already exists in the
DivMod / Multiply / EvmWordArith surfaces, and to pick concrete answers for
the four open design questions in beads `evm-asm-evgr`. Subsequent slices
(`evm-asm-f453` / `evm-asm-sord` / `evm-asm-lxq4` / `evm-asm-m4wu` /
`evm-asm-vxun`) implement the choices made here.

EVM semantics (Yellow Paper / `execution-specs`):

- `ADDMOD(a, b, N)` = `(a + b) mod N` if `N ≠ 0`, else `0`.
  The intermediate `a + b` is a **257-bit** value (carry out of bit 255).
- `MULMOD(a, b, N)` = `(a * b) mod N` if `N ≠ 0`, else `0`.
  The intermediate `a * b` is a **512-bit** value (8 × 64-bit limbs).

The output is a 256-bit value in both cases.

## 1. Inventory of what already exists

### 1.1 DivMod stack-level surface (closed via #61 / #1737)

`EvmAsm/Evm64/DivMod/` provides verified 256-bit unsigned division and
modulus. The user-facing entry points (notable specs index in
`docs/notable-specs.md`):

- `evm_div_stack_spec` / `evm_mod_stack_spec` — top-level stack triples
  for `evm_div` / `evm_mod` at the EVM dispatcher boundary.
- `EvmWord.div_correct` / `EvmWord.mod_correct`
  (`EvmAsm/Evm64/EvmWordArith/DivCorrect.lean`):
  ```lean
  theorem div_correct (a b : EvmWord) :
      (EvmWord.div a b).toNat =
        if b = 0 then 0 else a.toNat / b.toNat
  theorem mod_correct (a b : EvmWord) :
      (EvmWord.mod a b).toNat =
        if b = 0 then 0 else a.toNat % b.toNat
  ```
  Both already give the EVM-style zero-divisor convention (`b = 0 ⇒ 0`).

The DivMod implementation is **256/256** by construction: it is a 4-limb
Knuth Algorithm D specialized to a 4-limb numerator. ADDMOD's
257/256 and MULMOD's 512/256 do **not** fit this signature directly —
see §3 for the strategies considered.

### 1.2 Multiply surface

`EvmAsm/Evm64/Multiply/` already does a **column-organized 4×4
schoolbook multiply** (`Multiply/Program.lean` + `Multiply/LimbSpec.lean`)
that internally produces the full 512-bit product across 8 column
intermediates (`r0..r7`), but only the **low 256 bits** are exposed at
the stack level.

Concretely, `Multiply/Spec.lean` defines:

```lean
@[irreducible]
def evmMulStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** … **
  evmWordIs (sp + 32) (a * b)        -- truncated to 256 bits
```

The high 4 limbs (`r4..r7`) are stored to scratch cells / discarded so
the consumer sees a clean `regOwn`/`memOwn` interface; this is exactly
the data MULMOD needs to recover.

`EvmWord.mul_correct` (`EvmAsm/Evm64/EvmWordArith/MulCorrect.lean`)
proves each output limb of the schoolbook agrees with `(a * b).getLimb i`
for `i ∈ {0,1,2,3}`. The 512-bit version (`limb i` for `i = 4..7`) is
**not** currently named.

### 1.3 Add / Sub / EvmWordArith helpers

- `EvmAsm/Evm64/Add/` provides `evm_add_stack_spec` returning `a + b` mod 2^256.
- `Sub`, `Mul` (low 256), `Div`, `Mod`, `Lt`/`Gt`/`Eq`/etc. all live as
  proven stack specs.
- `EvmAsm/Evm64/EvmWordArith/Arithmetic.lean` and
  `EvmWordArith/Common.lean` carry the limb-level Nat algebra used
  by every higher-level theorem (`toNat_eq_limb_sum`,
  `BitVec.toNat_add`-style bridges, …).
- `EvmWord.addmod_correct` and `EvmWord.mulmod_correct` now live in
  `EvmAsm/Evm64/EvmWordArith/AddMod.lean` and
  `EvmAsm/Evm64/EvmWordArith/MulMod.lean`; later slices should reuse
  these semantic targets rather than restating opcode semantics.

## 2. Question (a) — can DivMod 4-limb modulo be reused by zero-padding?

For ADDMOD: the intermediate is 257 bits. The "carry bit" can be
described as a Nat `c ∈ {0,1}` with the invariant
`a.toNat + b.toNat = c * 2^256 + (a + b).toNat` (where `a + b` is the
truncated 256-bit BitVec sum). This is **not** representable as a 4-limb
EvmWord, so the DivMod 4-limb dividend signature does not fit directly.

Two strategies considered:

1. **Re-prove a 5-limb / 8-limb Knuth Algorithm D** specialized to one
   wider numerator each. This duplicates the entire DivMod loop
   (LoopBody, LoopIterN*, Compose, Spec) for every new width and is
   prohibitively expensive — the existing 256/256 surface required ~50
   sub-slices to close.

2. **Pre-reduce the wider numerator to a 4-limb residue, then call
   `EvmWord.mod` once.** This is mathematically valid because
   `(x mod N) = ((x mod (N · k)) mod N)` for any positive `k`, so any
   reduction step that preserves congruence mod N can run before the
   final `EvmWord.mod`.

   For ADDMOD: the 257-bit sum `s = a + b` decomposes as
   `s = c · 2^256 + r`, where `c ∈ {0,1}` and `r = (a + b) (mod 2^256)`.
   Then `(a + b) mod N = (c · 2^256 + r) mod N
                       = ((c · (2^256 mod N) + r) mod N)`.
   Both `2^256 mod N` and `r` are ≤ N-1 < 2^256, so a single
   `EvmWord.add` followed by one `EvmWord.mod` reduces the 257-bit
   problem to two 256/256 modulo calls. To stay within `EvmWord.mod`
   signatures, compute `m = (2^256) mod N` first (one `EvmWord.mod`
   on the constant `2^256` represented as a pair of EvmWords — see
   below), then `acc = (c · m + r) mod N` (another `EvmWord.mod`,
   using a single 256-bit `+` since `c · m + r < 2 · N ≤ 2^257`,
   which still does not fit, so this sub-step likewise needs a
   conditional final subtract — see §4).

   For MULMOD: the 512-bit product `p = a · b` has high half `pH` and
   low half `pL` (`p = pH · 2^256 + pL`), each a 4-limb EvmWord that
   can be obtained from the existing schoolbook (§1.2). Then
   `p mod N = (pH · (2^256 mod N) + pL) mod N
            = ((pH mod N) · (2^256 mod N) + (pL mod N)) mod N`.
   This decomposes into one `EvmWord.mul` (lower 256 of the product
   `pH_mod * m` — which is itself ≤ (N-1)^2 / N < N, …) plus
   modular adds. Total cost: 2× `EvmWord.mod`, 1× `EvmWord.mul`,
   1× modular add.

**Decision (a):** strategy 2 (pre-reduction via congruence). It reuses
the existing 256/256 DivMod surface unchanged; no wider Knuth D variant
is added. The price is one extra `EvmWord.mod` per opcode (to compute
`m = 2^256 mod N`) and a small modular-add helper.

## 3. Question (b) — which existing helpers cover the wider intermediate?

ADDMOD needs:

- A **257-bit add carry-out**. Provided by `BitVec.toNat_add` chained
  with `EvmWord.add`. Concretely, define
  `EvmWord.addCarry (a b : EvmWord) : Bool × EvmWord :=
       (decide (a.toNat + b.toNat ≥ 2^256), a + b)`.
  Slice 2 (`evm-asm-f453`) introduces this and proves
  `addCarry_spec : (addCarry a b).snd.toNat + (if (addCarry a b).fst then 2^256 else 0)
       = a.toNat + b.toNat`.
- The constant `pow256_mod_n : EvmWord → EvmWord` defined as
  `(EvmWord.fromLimbs (fun _ => 0))` shifted — at the runtime level we
  do not need a literal `2^256` register, since the carry bit `c`
  selects either `0` or `m = 2^256 mod N`. Pre-computing `m` is one
  `EvmWord.mod` call where the dividend is the synthetic 257-bit value
  `(1 :: 0 :: 0 :: 0 :: 0)`. To keep the DivMod surface 4-limb, slice 2
  uses the algebraic identity `2^256 mod N = ((2^256 - 1) mod N) + 1
  (mod N) = ((-1) mod N) + 1 (mod N)`, which is computable inside
  `EvmWord` as `(EvmWord.add (EvmWord.mod ⟨-1⟩ N) 1) mod N`. (`-1`
  in `EvmWord` is `BitVec.allOnes 256`, which is already used in
  several places in the codebase.)

MULMOD needs:

- The **full 512-bit (8-limb) product**. The schoolbook in
  `Multiply/Program.lean` already computes all 8 column accumulators;
  slice 4 (`evm-asm-lxq4`) lifts the unused high 4 limbs into a public
  `EvmWord.mulHigh (a b : EvmWord) : EvmWord` plus the bridge
  `mulHigh_correct : (mulHigh a b).toNat = (a.toNat * b.toNat) / 2^256`.
  The proof reuses `mul_correct_limb{0..3}`'s machinery applied to
  limb indices 4–7. No new arithmetic primitive is needed; it is a
  re-export of work that is already in `MulCorrect.lean` for the low
  limbs.
- A **modular add** `EvmWord.modAdd (a b N : EvmWord) : EvmWord`
  computing `(a + b) mod N` assuming `a, b < N` (so the 257-bit sum
  has at most one final subtraction). Implementable as `addCarry a b`
  followed by a conditional `EvmWord.sub` of N, with proof bridging
  to `Nat.add_mod`. Used twice in MULMOD, once in ADDMOD.

## 4. Question (c) — where does the algebraic correctness theorem live?

`EvmAsm/Evm64/EvmWordArith/AddMod.lean` and
`EvmAsm/Evm64/EvmWordArith/MulMod.lean`, imported by the future total
`AddMod/Spec.lean` / `MulMod/Spec.lean` surfaces. The theorem statements:

```lean
namespace EvmAsm.Evm64.EvmWord
theorem addmod_correct (a b N : EvmWord) :
    (EvmWord.addmod a b N).toNat =
      if N = 0 then 0 else (a.toNat + b.toNat) % N.toNat
theorem mulmod_correct (a b N : EvmWord) :
    (EvmWord.mulmod a b N).toNat =
      if N = 0 then 0 else (a.toNat * b.toNat) % N.toNat
end EvmAsm.Evm64.EvmWord
```

Algebraic shape: `Nat.add_mod`, `Nat.mul_mod`, `Nat.add_mul_mod_self_left`
on the `toNat` side, threaded through `BitVec.toNat_add` /
`BitVec.toNat_mul` and `EvmWord.div_correct` / `mod_correct` for the
runtime side. The N=0 branch reduces by `simp` since both
`EvmWord.mod _ 0` and the EVM convention return zero.

## 5. Question (d) — Program / block layout sketches

### 5.1 `evm_addmod` Program (slice 3, `evm-asm-sord`)


> 2026-06 runtime update: ADDMOD is total in execution-specs, including
> 257-bit carry-out cases. The runtime must compute the carry contribution
> instead of routing `x7 != 0` to invalid-op. See
> [`addmod-total-runtime-plan.md`](addmod-total-runtime-plan.md) for the
> concrete helper-block plan and current dispatcher offsets.

Stack input top-to-bottom: `[a, b, N, …]` (32 bytes each); output: `[r, …]`
where `r = (a+b) mod N` or 0 if N=0.

```
prologue:
  -- Pop nothing yet; reuse evm_add to fold a + b in place
  -- (consumes 64 bytes, leaves (a+b) at sp+32, N at sp+64).

phase 1 — record carry:
  -- Re-do the high-limb add with carry detection (cheap because
  -- limbs already in registers from evm_add); store carry bit
  -- in scratch register x7.

phase 2 — pre-reduce by N:
  -- Test N=0 → if so jump to "store 0".
  -- Compute m = 2^256 mod N via (-1) mod N then +1 then mod.
  -- Compute c·m + (a+b mod 2^256) using modAdd helper.
  -- Final EvmWord.mod by N produces the result.

epilogue:
  -- Overwrite top stack cell with result; advance x12 by 64.
```

Rough block count: prologue ≤ 4 instr; phase 1 ≤ 6 instr; phase 2 is
dominated by two `evm_mod` calls + two `evm_add` calls (each is a
multi-hundred-instruction program already verified), plus ≤ 20 glue
instructions. Total Program size dominated by inlined `evm_mod` /
`evm_add`; prefer **calling** them via the LP64 calling convention
(`callNear`/`cc_prologue` per AGENTS.md §"Calling Convention") rather
than inlining, to keep the spec composable. A near-call dispatch loop
already exists in DivMod's caller, so this slice borrows the same
shape.

### 5.2 `evm_mulmod` Program (slice 5, `evm-asm-m4wu`)

Stack input top-to-bottom: `[a, b, N, …]`; output: `[r, …]` with
`r = (a*b) mod N`.

```
prologue:
  -- Use evm_mul (full schoolbook) but **don't truncate** the high
  -- limbs — store them at sp + 32..sp + 56 (currently scratch).

phase 1 — read high half:
  -- The 8 column accumulators include the high 4 limbs at known
  -- column indices. Slice 4 exposes a Multiply variant that leaves
  -- pH at the same scratch offsets used today, so this is a memory
  -- relabel rather than recomputation.

phase 2 — pre-reduce:
  -- Test N=0 → jump to "store 0".
  -- Compute m = 2^256 mod N.
  -- pH_mod = pH mod N      (1× evm_mod call)
  -- t      = pH_mod ·_N m  (1× evm_mul + 1× evm_mod, all 256-bit)
  -- acc    = (t +_N pL) mod N  (1× modAdd + 1× evm_mod, with
  --          (t + pL) ≤ 2N−2 ≤ 2^257-2 so one conditional subtract suffices)

epilogue:
  -- Overwrite top stack cell with acc; advance x12 by 64.
```

Cost dominated by 2× `evm_mod`, 1× `evm_mul` (low-256 of an already-mod-N
product), 2× modular `add`/`sub`. All of these are proven stack-spec
artifacts today, so the new content is the bridge proof
`mulmod_correct` plus the dispatch glue.

## 6. Slice plan recap (no scope changes)

The existing beads slices match this design:

- `evm-asm-f453` (slice 2): introduce `addCarry`, `addmod`, prove
  `addmod_correct`. Adds `EvmAsm/Evm64/EvmWordArith/AddModMulMod.lean`
  and lifts the 257-bit add helper.
- `evm-asm-sord` (slice 3): `evm_addmod` Program.lean and stack spec.
- `evm-asm-lxq4` (slice 4): `mulHigh` re-export of schoolbook 8-limb
  + `mulmod_correct`.
- `evm-asm-m4wu` (slice 5): `evm_mulmod` Program.lean and stack spec.
- `evm-asm-vxun` (slice 6): wire ADDMOD/MULMOD into the dispatcher and
  post the GH #91 close-proposal status comment.

## 7. Open risks

1. **Calling-convention spill cost.** Each `evm_mod` call has a non-trivial
   prologue/epilogue; doing 2× `evm_mod` per opcode may push the per-opcode
   instruction budget past comfortable single-file limits. Mitigation:
   share scratchpad layout between the two calls (per #334), so the second
   call reuses the first's frame.
2. **`m = 2^256 mod N` precomputation.** The `(-1) mod N + 1 mod N` trick
   adds two `EvmWord.add`/`mod` operations per opcode invocation. If profiling
   shows this dominates, an alternative is to special-case `N` powers of two
   (where `m = 0`) — but that is a future optimization, not part of the
   correctness story.
3. **Schoolbook high-limb relabel.** Slice 4 assumes today's
   `Multiply/Program.lean` retains all 8 column accumulators in
   addressable scratch cells through to the epilogue. If a future
   refactor narrows the schoolbook to compute only the low 4 limbs,
   MULMOD must regrow that surface — file a P2 beads task at slice-4
   start to add a regression test pinning the high-limb scratch
   layout.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
