# MODEXP dual-path analysis (bead evm-asm-4ch8f.11.3)

Investigation of the two independent MODEXP implementations flagged by the
crypto-kernel inventory (P1-D2): the dispatcher's single-register small-op path
vs. the multi-limb bignum backend. Ground truth is the amsterdam spec,
`tests-zkevm@v0.4.0:src/ethereum/forks/amsterdam/vm/precompiled_contracts/modexp.py`
(EIP-198 semantics, EIP-7823 length cap).

## The two paths and their routing

Both live behind one dispatcher (`EvmAsm/Codegen/Programs/Modexp.lean`,
`modexpPrecompileGasAsm`). After gas is charged and the length caps are applied
(each of base/exp/modulus length rejected if `> 1024`, matching EIP-7823), the
dispatcher branches:

```
li x31, 4
bltu x31, x5 (base_len)  -> backend
bltu x31, x22 (exp_len)  -> backend
bltu x31, x23 (mod_len)  -> backend
otherwise                -> small-op path
```

- **Small-op path** (`Modexp.lean:203-259`): taken iff **all three** of
  base_len, exp_len, mod_len are `<= 4`. Reads each operand into one 64-bit
  register and runs an LSB-first square-and-multiply with `mul`/`remu`.
- **Bignum backend** (`ModexpBackend.lean`, `zkvm_modexp`): taken iff **any**
  length is `> 4`. Little-endian limb arrays, schoolbook `modexp_mul`, binary
  long-division `modexp_binmod`, MSB-first square-and-multiply.

The dispatcher also short-circuits before either path: `mod_len == 0`
(equivalently base==0 && mod==0) returns empty output, matching the spec's
`modulus == 0 -> output = b"\x00" * modulus_length` (zero-length here).

**Routing is disjoint.** Small-op requires all three lengths `<= 4`; the backend
requires at least one length `> 4`. No input reaches both. Therefore the two
paths **can never disagree on a shared input** — the D2 "two code paths compute
the same result" risk cannot manifest as a live divergence between them.

## Small-op path: spec-correct on its whole domain (all lengths <= 4)

Operands are `< 2^32`, so every intermediate product is `< 2^64` (no register
overflow). Checked against spec:

- `modulus == 0` -> result register stays 0, output = mod_len zero bytes. OK.
- `exp == 0` -> result initialised as `1 mod modulus` via `li x27,1; remu
  x27,x27,x26`, loop exits immediately. For `modulus == 1` this yields 0. OK.
- `modulus == 1` -> base reduced to 0, result reduced to 0, stays 0. OK.
- general -> standard LSB-first square-and-multiply, each step `remu` mod m. OK.

The small-op path is EIP-198-correct across its entire domain, including the
`modulus == 1` corner.

## Backend: one spec divergence found — `exp == 0 && modulus == 1`

`zkvm_modexp` sets `result = 1` (`ModexpBackend.lean:235-242`) and then, if
`exp == 0`, jumps straight to output formatting **without reducing `result`
modulo the modulus** (`bnez a0, .Lmexp_format`, line 246). For every modulus it
therefore emits `1`, but the spec computes `pow(base, 0, modulus) = 1 % modulus`,
which is **0 when `modulus == 1`**. (For `exp != 0` the first squaring runs
`binmod`, so `modulus == 1` reduces correctly; only the `exp == 0` shortcut is
affected. The `modulus == 0` case has its own correct `.Lmexp_modzero` path.)

This is reachable: routing to the backend only needs one length `> 4`, e.g.
`base = 0x0000000002` (len 5), `exp` len 1 value 0, `modulus` len 5 value 1.
Spec output = 5 zero bytes; backend output = `0x0000000001`.

Faithful control-flow model (`pow` vs. the backend's branch structure):

```
base=2 exp=0 mod=1 Mlen=1: backend=01          spec=00          **DIVERGE**
base=2 exp=0 mod=1 Mlen=5: backend=0000000001  spec=0000000000  **DIVERGE**
base=7 exp=3 mod=1 Mlen=1: backend=00          spec=00          OK
base=2 exp=5 mod=13 Mlen=1: backend=06         spec=06          OK
base=2 exp=0 mod=7 Mlen=1: backend=01          spec=01          OK
base=0 exp=0 mod=5 Mlen=3: backend=000001      spec=000001      OK
```

This is a genuine consensus divergence in the backend (not a small-op/backend
disagreement, since that input routes to the backend only). Note the current
`zisk_modexp_backend_probe` harness links a safe-fail shim, not the real
`zkvm_modexp`, so no existing probe exercises this success path — an empirical
ziskemu repro needs a probe unit that links `zkvmModexpBackendImpl`.

Filed as a child bead (P1). Not fixed here: the minimal fix (reduce `result`
mod modulus before the `exp == 0` format, e.g. an extra `binmod`) inserts
instructions into `zkvm_modexp` and shifts downstream image addresses, so it is
neither byte-identical nor cheaply probe-verifiable and is out of scope for this
investigation-only bead.

## Conclusions

- D2 as stated ("two paths, same input, must agree") is **not** a live risk:
  routing is disjoint.
- The small-op path is fully spec-correct on `<= 4`-byte operands.
- The backend has an independent EIP-198 divergence for `exp == 0 && modulus ==
  1`; tracked in the child bead.
