# 4ch8f.11 — software crypto kernel inventory (feeder for the strategy decision)

> **Purpose.** This is the *evidence* for bead `evm-asm-4ch8f.11` (the per-kernel
> verification-strategy decision: full functional verification vs
> verified-glue-over-concrete-accelerators vs trusted-kernel-with-differential-tests,
> plus the field-arithmetic library plan). **No strategy verdicts here** — only
> measurements, structure, and cross-references. The `.11` session (Fable) turns
> these numbers into decisions.
>
> **Scope fences.** This doc is the only deliverable that touches the repo tree
> (plus bead updates). It does not modify any `Programs/`, `SAsm/`, or
> `docs/sasm-design.md` (owned by parallel sessions).
>
> **How to read the numbers.**
> - Instruction counts are **exact** for `emitProgram`-based leaf helpers (from
>   `scripts/asm-fixtures/*.s` + kernel-checked `#guard prog.length = N`), and
>   **estimated (≈)** for the assembly-string kernels (the `.4byte` accelerator
>   callers and the large software routines), counted from the emitted Lean string
>   literals — these run ~15–20 % below post-link `Instr` counts because
>   `la`/large-`li`/`call` pseudo-ops expand. Estimates are marked `≈`.
> - Accelerator `.4byte` call-site counts are **exact** (`grep 0x80XNNNNN`).
> - `UNKNOWN` marks anything not determinable from the source — never guessed.

---

## 0. Executive shape (the two ratios the decision hinges on)

Two facts dominate every per-kernel row below:

1. **The accelerator seam is narrow and already fully modeled.** There are
   **64 static `.4byte` accelerator call-sites** in the whole guest (§2), each
   mapping to a **concrete, kernel-checked** `Accel.*` function in
   `EvmAsm/Rv64/ZiskAccel.lean` (bead `.1`, done). Every field multiply, curve
   add/double, hash permutation, and Blake2b round bottoms out at one of these.
   The seam is reused via a handful of helper wrappers `jal`'d thousands of times
   — e.g. **P256VERIFY funnels its entire group law through ONE `.4byte`
   (`p256_op_with`, P256Verify.lean:346)**; secp256k1 through two
   (`secf_mul_mod_p`/`_mod_n`). So "how much math is glue over a modeled
   accelerator" is answerable precisely.

2. **There are no kernel-level functional proofs today — for any crypto kernel.**
   The only Lean assets touching these routines are (a) the concrete accelerator
   semantics + **9 kernel-checked KATs** in `ZiskAccel.lean`, (b) `*_eq_prog :=
   rfl` **string-drift guards** on the ~40 converted leaf helpers (these prove
   "string == rendered `Program`", *not* that the math is correct), and (c)
   **spec-side EL ecall-ABI bridges** under `EvmAsm/EL/*Bridge.lean` (model the
   precompile ABI, *not* the RV64 body). **No `cpsTripleWithin` / SAsm port
   connects any crypto asm body to its spec.** Correctness rests entirely on the
   differential `scripts/codegen-zisk-*-check.sh` probes against py_ecc /
   execution-specs / the `cryptography` lib.

The spec-gap ladder used throughout (increasing difficulty):

| class | meaning | example kernels |
|---|---|---|
| **byte-plumbing** | copy / pad / endianness only; proof = memcpy + accelerator postcondition | SHA/KECCAK/BLAKE2F bridges, all `be_to_le`/`eq32`/`lt_p` leaves |
| **bignum** | multi-limb schoolbook mul + long division + exponent ladder | MODEXP |
| **group-law** | affine chord/tangent completeness + infinity handling over the accelerator | BN254/secp256k1/P256 add·dbl·scalar-mul, BLS G1 |
| **tower-field** | Fp2 / FQ12 extension arithmetic, Fermat inversion, quotient-ring reduction | BN254 Fq12, BLS G2/Fq12, P256 (mod-n leg) |
| **protocol-level** | pairing (Miller + final exp), map-to-curve (SSWU + isogeny), KZG verify, ECDSA verify | BN254/BLS pairings, BLS maps, KZG, P256VERIFY |

---

## 1. The kernels at a glance (ranked-difficulty table)

Rows ordered hardest→easiest by spec-gap class then software-math volume. "sw-math"
= instructions doing arithmetic in RV64 code (not the accelerator glue around a
`.4byte`). "accel sites" = static `.4byte` call-sites in the kernel's own file(s)
(dynamic invocations are far higher — noted per kernel).

| # | kernel (precompile) | ≈instrs | #routines | accel sites (ids) | ≈sw-math instrs | loop nest | spec-gap | converted? | tests |
|---|---|---:|---:|---|---:|---:|---|---|---|
| 1 | **BLS12 KZG** (0x0A) | ~272 +pairing stack | 7 (+pairing) | 1 (0x80B) | ~250 +pairing | 4 (→pairing) | protocol + compressed-G1 | kernel NO; 4 helpers YES | zisk-bls12-kzg |
| 2 | **BLS12 pairing** (0x0F) | ~560 (Fq12+Pairing) | 16 | 7 (0x80B) | ~540 | 3 | protocol (ate+final-exp) | 5 progs YES; kernels NO | zisk-bls12-pairing, eest |
| 3 | **BN254 pairing** (0x08) | ~1275 (5 files) | 13 | 0x802 + 0x808/9/A (transitive) +2 direct 0x802 | ~1015 | 5 | protocol (Miller+final-exp+hoist) | pt_copy YES; rest COMPOSITE | zisk-bn254-pairing; EL bridges |
| 4 | **BLS12 map-fp2-to-g2** (0x11) | ~760 | 1 (+pow) | 0 direct | ~760 | 4 | protocol (SSWU+3-iso+cofactor) | NO | zisk-bls12-map, eest |
| 5 | **BLS12 map-fp-to-g1** (0x10) | ~907 | 1 (+pow) | 0 direct | ~900 | 3 | protocol (SSWU+11-iso+cofactor) | NO | zisk-bls12-map, eest |
| 6 | **P256VERIFY** (0x100) | ~487 | 13 | 1 (0x802) | ~460 | 2 (ladder-in-ladder ≈4) | protocol (ECDSA) / group-law | 6 leaves YES; op_with DOTWORD | zisk-p256verify |
| 7 | **BLS12 G2 add/msm** (0x0D/0x0E) | ~490 | 20 | 4 (0x80E/F, 0x80B×2; 0x810 via helper) | ~470 | 5–6 | tower-field + group-law | 2 progs YES; kernels NO | zisk-bls12-g2, eest |
| 8 | **secp256k1 recovery** (0x01) | ~815 (3 files) | 28 | 4 (0x802×2, 0x803, 0x804) | ~750 | 2 | group-law + field-tower | leaves YES; math WAVE3; 4 DOTWORD | 10 shell probes |
| 9 | **BN254 Fq12** (0x08 core) | ~250 | 10 | 5 (0x802) | ~200 | 3 | tower-field (quotient-ring mul) | 4 leaves YES; rest DOTWORD | zisk-bn254-pairing (Fq12 probe) |
| 10 | **MODEXP** (0x05) | ~365 backend (+~231 dispatcher) | 8 + dispatcher | 0 (no accelerator) | ~365 (≈100 %) | 3 | bignum modexp | NO (monolithic string) | zisk-modexp-backend-probe |
| 11 | **RIPEMD160** (0x03) | ~233 | 3 | 0 (no accelerator) | ~233 (≈100 %) | 3 | byte-plumbing + hash-schedule | NO (cross-jal + large-li) | zisk-ripemd160 |
| 12 | **BN254 G1 add/mul** (0x06/0x07) | ~330 | 12 | 2 (0x806, 0x807; 0x802 via on-curve) | ~200 | 5 | group-law | 5 leaves YES; rest DOTWORD | zisk-bn254-g1; EL bridges |
| 13 | **BLS12 G1 add/msm** (0x0B/0x0C) | ~460 | 20 | 6 (0x80C×2, 0x80D×2, 0x80B×2) | ~250–300 | 2–4 | group-law (+subgroup for MSM) | 7 leaves YES; kernels NO | zisk-bls12-g1, eest |
| 14 | **BN254 Fp2** (0x08 core) | ~200 | 11 | 5 (0x808/9/A, 0x802×2) | ~115 | 3 | tower-field (Fermat) | 4 leaves YES; 2 WAVE3; 5 DOTWORD | zisk-bn254-pairing (Fp2 probe) |
| 15 | **BLAKE2F** (0x09) | ~108 | 3 | 1 (0x819, ×rounds at runtime) | ~30 (rest accel-driven) | 1 | protocol-glue / byte-plumbing | leaves YES; kernel DOTWORD | zisk-blake2f (EIP-152 v4-7) |
| 16 | **SHA-256 bridge** (`zkvm_sha256`) | ~119 | 1 | 3 (0x805) | ~114 (glue) | 1 | byte-plumbing | NO (DOTWORD) | zisk-sha256-* |
| 17 | **KECCAK bridge** (`zkvm_keccak256`) | ~68 | 1 | 2 (0x800) | ~64 (glue) | 2 | byte-plumbing | NO (DOTWORD) | zisk-keccak256-* |
| 18 | **KECCAK segments** (`…_segments`) | ~69 | 1 | 2 (0x800) | ~65 (glue) | 2 | byte-plumbing | NO (DOTWORD) | via tx-signing-hash |

**Reading the ranking.** The genuine *software-math* cost centers are the two
pairings (0x08, 0x0F) and the two BLS maps (0x10, 0x11) at protocol level;
MODEXP and RIPEMD160 are the only kernels with **zero** accelerator use (pure
bignum / pure hash-schedule). At the other extreme, the hash bridges, BLAKE2F,
BN254 G1, and BLS G1 are thin **glue** over already-modeled accelerators —
byte-plumbing plus a group-law case-split.

---

## 2. The accelerator seam (foundation — bead `.1` concrete semantics)

Every ZisK accelerator is invoked as a raw pre-encoded `csrs <id>, <reg>` word
(`.4byte 0xNNNNNNNN`). Each id has concrete, kernel-checked semantics in
`EvmAsm/Rv64/ZiskAccel.lean` — dispatch in `MachineState.csrsWrite`
(ZiskAccel.lean:498-576), validity in `csrsValid` (:590-668), math in
`namespace Accel`. Register operand: Keccakf/Sha256f and all BLS ids
(0x80B–0x810, 0x819) use **a0** (enc `…52073`); Arith256Mod and all
secp256k1/BN254 curve+complex ids (0x802–0x80A) use **t0** (enc `…2a073`).

`arith256Mod(a,b,c,m) = (a·b + c) mod m` (ZiskAccel.lean:215) is the workhorse
for *all* software field arithmetic — mulmod (c=0), addmod (b=1, addend in c),
submod (b=p−1, addend in a). `curveAddL`/`curveDblL` (:329/334) are affine and
**exclude** the special cases (x1=x2, y=0, point at infinity) — those stay in
software. `complexAddL/SubL/MulL` (:377/383/391) are Fp2 with u²=−1.

### 2a. CSRS id → concrete semantics → callers (whole-guest census)

64 static executable call-sites total (comment/prose `.4byte` mentions excluded).

| CSRS id | accelerator | `Accel.*` fn | files calling it (per-file sites) | total |
|---|---|---|---|---:|
| **0x800** | Keccakf | `keccakF` (25-lane, in place) | HashBridge (4), MptIndexedTrieRoot (4), HashProbes (3) | 11 |
| **0x802** | Arith256Mod | `arith256Mod` (4-limb) | Bn254Fq12 (5), Bn254Field (2), Bn254Fp2 (2), Bn254Pairing (2), Secp256k1Field (2), P256Verify (1) | 14 |
| **0x803** | Secp256k1Add | `curveAddL secpP 4` | Secp256k1Curve (1) | 1 |
| **0x804** | Secp256k1Dbl | `curveDblL secpP 4` | Secp256k1Curve (1) | 1 |
| **0x805** | Sha256f | `sha256Compress` | HashBridge (3), HashProbes (1) | 4 |
| **0x806** | Bn254CurveAdd | `curveAddL bn254P 4` | Bn254Curve (1) | 1 |
| **0x807** | Bn254CurveDbl | `curveDblL bn254P 4` | Bn254Curve (1) | 1 |
| **0x808** | Bn254ComplexAdd | `complexAddL bn254P 4` | Bn254Fp2 (1) | 1 |
| **0x809** | Bn254ComplexSub | `complexSubL bn254P 4` | Bn254Fp2 (1) | 1 |
| **0x80A** | Bn254ComplexMul | `complexMulL bn254P 4` | Bn254Fp2 (1) | 1 |
| **0x80B** | Arith384Mod | `arith256Mod` (6-limb block) | Bls12Fq12 (5), Bls12Field (3), Bls12G1 (2), Bls12G2 (2), Bls12Pairing (2), Bls12Kzg (1) | 15 |
| **0x80C** | Bls12_381CurveAdd | `curveAddL bls12P 6` | Bls12G1 (2), Bls12Field (1) | 3 |
| **0x80D** | Bls12_381CurveDbl | `curveDblL bls12P 6` | Bls12G1 (2), Bls12Field (1) | 3 |
| **0x80E** | Bls12_381ComplexAdd | `complexAddL bls12P 6` | Bls12Field (1), Bls12G2 (1) | 2 |
| **0x80F** | Bls12_381ComplexSub | `complexSubL bls12P 6` | Bls12Field (1), Bls12G2 (1) | 2 |
| **0x810** | Bls12_381ComplexMul | `complexMulL bls12P 6` | Bls12Field (1), Bls12G2 (1) | 2 |
| **0x819** | Blake2bRound | `blake2bRound` | Blake2f (1) | 1 |

**Every one of these 64 sites is class NEEDS-DOTWORD** (raw pre-encoded word, not
yet a `.CSRS` `Instr`) — this is exactly the set of points where guest glue meets
accelerator semantics, and where every glue proof must discharge the
`csrsWrite`/`Accel.*` correspondence. A `.4byte`→`.CSRS` decoder (or word-literal
`Instr`) unblocks pure-`Program` conversion of the whole crypto tree at once.

### 2b. Kernel-checked KATs (the only concrete-value proofs today)

`ZiskAccel.lean`: `keccakF_kat_empty` (:124), `sha256Compress_kat_empty` (:193),
`blake2bRound_kat_abc` (:273), `secp_curveDbl_kat` (:351), `secp_curveAdd_kat`
(:361), `bn254_curveDbl_kat` (:411), `bn254_curveAdd_kat` (:419),
`bls12_curveDbl_kat` (:431), `bn254_complexMul_kat` (:441). All `by decide`,
kernel-checkable. These validate the *accelerators*, not the guest glue.

---

## 3. Per-kernel inventory

Each kernel uses the fixed 9-field schema: **(1)** code size, **(2)** accelerator
usage, **(3)** software-math + spec gap, **(4)** loop structure, **(5)** memory
footprint, **(6)** conversion status, **(7)** test coverage, **(8)** existing
verification assets, **(9)** risk notes.

### 3.1 SHA-256 / KECCAK bridges (`zkvm_sha256`, `zkvm_keccak256`, `zkvm_keccak256_segments`)

The pattern-setters (beads `.17`/`.18`). All three in
`EvmAsm/Codegen/Programs/HashBridge.lean` (269 LoC, 3 `String` defs), inlined by
every higher-level unit that hashes. **GLUE over 0x800/0x805**: the software part
is sponge/Merkle-Damgård padding + the multi-block absorb loop; the permutation is
the accelerator.

**`zkvm_sha256`** (HashBridge.lean:18-121). (1) ≈119 instr, 1 leaf routine.
(2) **0x805 Sha256f ×3** (:56 block loop, :86 + :103 the two-block final path) =
`Accel.sha256Compress`. (3) byte-plumbing: IV init from `sha256_w_iv`, 64-byte
block copy, MD padding (0x80, 56-byte two-block threshold :83, **big-endian**
64-bit length at offset 56 :92-100), squeeze with per-u32 byte-swap `xori t2,…,3`
(:110). Proof needs: MD padding + `state = fold sha256Compress over padded blocks`
+ the u32 BE↔LE squeeze identity. (4) 3 sequential loops, depth 1 (absorb
data-dep on len/64, bcopy ≤63, squeeze =32). (5) 48-byte frame (s0–s5); `la`
`sha256_w_state/input/iv/params`; region `sha256_scratch` @0xa1b90000/64 KiB
(RegionMap.lean:169). (6) NEEDS-DOTWORD (coverage:438). (7)
`codegen-zisk-zkvm-sha256-check.sh`, `-sha256-from-input-`, `-sha256-probe-le-`.
(8) none for the body; EL surfaces `EvmAsm/EL/Sha256EcallBridge.lean`,
`EvmAsm/Stateless/Bridges/Sha256EcallBridge.lean`. (9) **endianness landmine** —
state is LE-u32-packed but the length field is written **big-endian** and the
squeeze byte-swaps each u32; two-block boundary at remainder ≥56 is off-by-one
prone.

**`zkvm_keccak256`** (HashBridge.lean:123-200). (1) ≈68 instr, 1 leaf — **the
highest-fan-in bridge in the guest** (Mpt, MptInsert, BalAccountPath,
PrecompileRuntime, Header, … ≥15 sites). (2) **0x800 Keccakf ×2** (:161 absorb,
:187 final) = `Accel.keccakF`. (3) byte-plumbing: zero 25 lanes, XOR 17 full lanes
(rate 136) per block, byte-XOR the partial block, Keccak pad10*1 (`xori 0x01` +
`xori 0x80` at byte 135), squeeze 32. Proof: `keccak256 = squeeze32 ∘ fold keccakF
over pad(msg) XOR-absorbed at rate 136`. (4) depth **2** (`.Lzk3_xor` (=17) nested
in `.Lzk3_full` absorb). (5) 32-byte frame; `la zk3_state` — a **shared mutable
200-byte sponge arena reused by 40+ callers**; region `keccak_scratch`
@0xa1b70000/64 KiB (RegionMap.lean:165). (6) NEEDS-DOTWORD (coverage:436). (7)
`codegen-zisk-keccak256-{abc,empty,from-input,multiblock}-check.sh`,
`-keccak-probe.sh`; transitively hit by nearly every MPT/state/header check. (8)
closest is `EvmAsm/Codegen/Programs/KeccakReverseSAsm.lean` (verified
`byteReverse32_verified`) — a byte-reverse helper, **not** the sponge. (9)
`zk3_state` aliasing hazard if two hashes interleave; callers use `jal x1` and
must expect a0/a1/a2 clobbered.

**`zkvm_keccak256_segments`** (HashBridge.lean:219-267). (1) ≈69 instr, 1 leaf.
(2) **0x800 Keccakf ×2** (:248, :257). (3) scatter-gather variant: hashes the
concatenation of an N-element `(ptr,len)` array with **no materialization** —
carries the 0..135 rate-fill in `s4` across segment boundaries. Proof:
`digest = keccak256(concatMap bytes segments)` + the cross-segment fill-carry
invariant. (4) depth **2** (`.Lkss_byte` nested in `.Lkss_seg`); N segments
data-dep, len-0 segments skipped; O(1) extra memory. (5) 64-byte frame (ra,s0–s6);
shared `zk3_state`. (6) NEEDS-DOTWORD (coverage:437). (7) **no dedicated segments
probe (UNKNOWN)** — exercised via tx-signing-hash / eip7702 checks; consumers:
TxSigningHash, TxPubkey, Eip7702Authority, VerifyPublicKeysSenders. (8) none. (9)
designed to hash `prefix || in-place-slice || suffix` from the input region with
no copy; correctness hinges on the `s4` fill-carry and shared `zk3_state`.

### 3.2 secp256k1 recovery (ECRECOVER 0x01 + tx-sender recovery)

Files: `Secp256k1Field.lean` (22 fns), `Secp256k1Curve.lean` (5), `Secp256k1Recover.lean`
(1); call-tree root `secp256k1_recover_pubkey_staged` / `tx_pubkey_recover_raw`
live in `TxPubkey.lean`. **Real software math over the curve+arith accelerators.**

(1) **≈815 instr** across the 3 files (Field ≈557, Curve ≈184, Recover 74),
**28 routines**. Leaf sizes (exact): copy32=9, zero32=5, be_to_le=20, le_to_be=19,
get_bit_lsb=9, is_zero32=12, eq32=15; PointCopy64=9, PointZero64=7. Math sizes
(coverage doc): cmp_p=24, reduce_once=32, add=35, sub=36, pow=50, inv=26, sqrt=74,
scalar_mul=67, PointAdd≈69, PointDouble≈32, RecoverR=74 (mirror set for mod-n).
Deepest chain **~7** (field path): `…_staged → secp256k1_recover_r →
secf_sqrt_mod_p → secf_pow_mod_p → secf_square_mod_p → secf_mul_mod_p →
secf_be_to_le`.
(2) **0x802 Arith256Mod ×2 static** — `secf_mul_mod_p` (Secp256k1Field.lean:491)
and `secf_mul_mod_n` (:777); every multiply/square/pow-step/inversion funnels
through these (hundreds of dynamic calls per sqrt/inv). **0x804 Secp256k1Dbl ×1**
(`secp256k1_point_double`, Secp256k1Curve.lean:86). **0x803 Secp256k1Add ×1**
(`secp256k1_point_add`, :160). `scalar_mul` drives dbl/add up to 256× each.
(3) software: 32-byte BE↔LE marshalling, one-shot conditional reductions,
mod-add/sub, **Fermat inversion** `x^(p−2)`/`x^(n−2)`, **Tonelli-shortcut sqrt**
`x^((p+1)/4)`, **double-and-add scalar-mul** (MSB-first, infinity-tracked), point
decompression `y=sqrt(x³+7)` + parity, and the ECDSA formula
`Q=(−e·r⁻¹)·G+(s·r⁻¹)·R`. Spec gap: **group-law + field-tower**; needs Fermat
facts over `secpP`, double-and-add = scalar mult, recovery correctness (mirrors
execution-specs `crypto/elliptic_curve.py`/`secp256k1_recover`).
(4) `scalar_mul` depth 2 (32 bytes × 8 bits = 256); pow/sqrt/pow_n single 256-iter
ladders; be_to_le/le_to_be nested 4×8 fixed. (5) all scratch is **local `.data`,
NOT in RegionMap** (self-contained, non-reentrant); frames 48–80 B; recover_r uses
**14 reloc `la` symbols**. (6) leaves **ALREADY-STRUCTURED**; the math strings
**READY-WAVE3** (coverage:307-321); the 4 `.4byte` fns (PointDouble, PointAdd,
mul_mod_p, mul_mod_n) **NEEDS-DOTWORD** (coverage:441-443). (7) 10 shell probes
(`-field-`, `-scalar-`, `-curve-`, `-recover-`, `-ecrecover-precompile-`,
`-tx-pubkey-ecrecover-stage-material-`, …); no Lean KAT. (8) **none functional**;
drift guards on the 9 leaves; EL bridges `Secp256k1EcrecoverInput/Ecall/ResultBridge`.
(9) **a0-aliases-x10 landmine CONFIRMED** — `PrecompileRuntime.lean:216` ("a0 IS
x10: stash the status before restoring the EVM code pointer"), :230, :534,541;
ECRECOVER status must be stashed in s10/x16 before the x10 restore.
**Dead-constant/drift risk (P1-D1):** `secf_sqrt_mod_p` hardcodes a skip-bit list
`{255,254,30,7,6,5,4,1}` (Secp256k1Field.lean:620-635) while the declared
`secp256k1_sqrt_exp_be` = (p+1)/4 constant (:48-52) is **referenced nowhere else**
— the magic list must equal the zero-bits of (p+1)/4 and can silently drift.

### 3.3 RIPEMD160 (0x03) — pure software, no accelerator

File: `Ripemd160.lean`. (1) one string holding **3 routines** (`zkvm_ripemd160`
driver/pad, `ripemd_compress`, `ripemd_line160`), ≈**233 instr**; depth 3.
(2) **NONE** — ZisK has no RIPEMD accelerator (Ripemd160.lean:7-14). The genuine
software-math kernel. (3) full RIPEMD-160: MD padding (0x80 + **little-endian**
64-bit length at offset 56), IV init, two parallel 80-step lines over the
`ripemd_rho` permutation / `ripemd_shift` rotations / `ripemd_k` constants, 5
boolean round fns f1–f5, `sllw`/`srlw` rotate-left, `addw` mod-2³² add, cross-line
combine. Spec gap: **byte-plumbing + hash-schedule**; proof = `zkvm_ripemd160 =
execution-specs ripemd160`. (4) block loop (data-dep len/64) → compress → line160
80-step (fixed, ×2/compress) = depth 3. (5) local `.data` (`ripemd_w_state/input`
[8-aligned staging], `ripemd_line_out`, `ripemd_rho/shift/k`); frame 96 B
(ra,s0–s9); not in RegionMap. (6) **unconverted, two blockers**: internal
cross-`jal` (BLOCKED_ON_.6) + 32-bit `li` IV constants (NEEDS-LI-EXPANSION);
file shows COMPOSITE=1 (coverage:794) — `zkvmRipemd160Function` not individually
classified (UNKNOWN exact class). (7) `codegen-zisk-ripemd160-check.sh` (standard
vectors, padding boundaries 55/56/63/64/65, 1 MB multi-block); no Lean KAT.
(8) none functional; EL bridges `Ripemd160Input/Ecall/ResultBridge`. (9) LE
bit-length (unlike SHA-2's BE) is easy to get wrong; large `li` IVs block a clean
`Instr`-list conversion.

### 3.4 BLAKE2F (0x09) — glue over the Blake2bRound accelerator

File: `Blake2f.lean`. (1) 3 routines: `zkvm_blake2f` (≈87), leaves `blk2_ld_le64`
(11), `blk2_st_le64` (10) = ≈**108 instr**; depth 2. (2) **0x819 Blake2bRound ×1
static** (Blake2f.lean:191) = `Accel.blake2bRound`, invoked **`rounds` times at
runtime** (attacker-controlled u32; gas charged upstream). The **glue** kernel —
the whole G-mixing round is in the accelerator. (3) scaffolding only: build
`v=h||IV`, XOR counters `v[12]^=t0`/`v[13]^=t1`, final-flag `v[14]^=~0` when f=1,
load 16 message words, round loop writing SIGMA index `= round mod 10` into
`blk2_params`, finalize `h'[i]=h[i]^v[i]^v[i+8]`. Spec gap:
**protocol-glue/byte-plumbing**; proof = marshalling + `blake2bRound` = one
RFC 7693 round + loop composition = `Blake2b.compress`. (4) 5 flat loops, **depth
1**; only the round loop is data-dep (cap = `rounds`, **no in-kernel cap** — relies
on the gas gate). (5) local `.data` (`blk2_iv/v/m/params`); frame 56 B; not in
RegionMap. (6) leaves ALREADY-STRUCTURED (coverage:34-35, drift guards); kernel
NEEDS-DOTWORD. (7) `codegen-zisk-blake2f-check.sh` (EIP-152 vectors 4-7 incl.
SIGMA-wrap rounds>10 and large round count); no Lean KAT. (8) drift guards on the
two leaves; EL bridges `Blake2fInput/Ecall/Result/PrecompileDispatch/…Bridge`.
(9) round-loop bound is attacker-controlled with no in-kernel cap (termination via
upstream gas); `f<=1` validated by dispatch, trusted here; all h/m/t I/O is
byte-wise because the staged payload is only 4-aligned.

### 3.5 BN254 family (0x06 ADD, 0x07 MUL, 0x08 PAIRING)

Files: `Bn254Field/Fp2/Fq12/Curve/Fq12Point/PairingCore/Pairing.lean` (2857 LoC).
**Key seam fact:** the FQ12 tower does **NOT** use the Fp2 complex accelerators
(0x808–0x80A). The 12-coefficient extension field is built directly on Arith256Mod
(0x802) one Fp coefficient at a time; the Fp2 accelerators are used **only** by the
G2 subgroup-check path (`bng2_*` in PairingCore). The pairing thus carries two
field representations: FQ12 (12×Fp limbs via 0x802) for the Miller loop, and Fp2
(via 0x808/9/A) for the G2 n·Q check.

**Bn254Field** (base Fp helpers, shared by 0x06/07/08). 7 routines, ≈129 instr;
0x802 ×2 (`bnf_mul_mod_p` :269 c=0, `bnf_add_mod_p` :297 b=1). mul/add are
accelerator-glue; converters/comparators are byte-plumbing. 5 leaves converted,
mul/add NEEDS-DOTWORD (coverage:428-429). Tests via `codegen-zisk-bn254-g1-check.sh`.

**Bn254Fp2** (Fp2 = Fp[u]/(u²+1), 0x08). 11 routines, ≈200 instr; 0x808×1 (:72),
0x809×1 (:81), 0x80A×1 (:90), 0x802×2 (fp_mul :217, fp_add :232). fp2 add/sub/mul
= thin glue; **real math**: `bnp_fp_pow` (254-bit Fermat ladder :239-276),
`bnp_fp2_inv` (norm=x0²+x1², inverse=norm^(p−2) :282-328). Spec gap: tower-field.
4 leaves converted, inv/pow READY-WAVE3, 5 fns NEEDS-DOTWORD (coverage:430-434).
KAT `bn254_complexMul_kat` (ZiskAccel.lean:441). Risk: dst◦=src mutating
convention (aliasing discipline); inv(0)=0 (callers must gate on is_zero).

**Bn254Fq12** (FQ12 = Fp[w]/(w¹²−18w⁶+82), 0x08). 10 routines, ≈250 instr.
**0x802 ONLY** — `bnq_mul` = **166 calls per FQ12 multiply** (144 schoolbook i×j
:164 + 22 reduction :189/201); add/sub/smul = 12 each. **Hardest real
software-math in the family (tower-field):** schoolbook 12×12 into a 23-coeff
accumulator then cascading reduction by w¹²=18w⁶−82 (high-coeff-first), fused MAC
via arith256Mod's `+c`. `bnq_pow` = generic MSB square-and-multiply for Frobenius
x^p, denominator inverse x^(p¹²−2), final exp x^((p¹²−1)/n). Loop: mul nested
i(12)×j(12) depth 2; pow bit-loop **data-dep cap = top-bit index (253/3043/2789)**
→ effective depth 3. Big exponent constants `bnq_exp_final_le` (2790-bit),
`bnq_exp_p12m2_le` (3044-bit); acc buffer 736 B. 4 leaves converted, pow/set_one
READY-WAVE3, rest NEEDS-DOTWORD. Probe `ziskBn254Fq12OpsProbe`. Risk: dst must not
alias `bnq_acc`; `bnq_smul` a2 is a scalar-cell pointer (not FQ12).

**Bn254Curve** (affine G1 + ecAdd 0x06 / ecMul 0x07). 12 routines, ≈330 instr;
0x807×1 (dbl :160), 0x806×1 (add :231); on_curve uses 0x802 for y²=x³+3. software:
the accel-excluded affine special cases (inf, y=0, equal-x → dbl or P+(−P)=∞), the
`bnc_scalar_mul` double-and-add over the **raw 32-byte scalar (no order reduction —
G1 cofactor 1)**, `bnc_validate_g1` (execution-specs `bytes_to_g1`). Spec gap:
group-law (y²=x³+3, infinity=(0,0)). Chain depth **5**. 5 leaves converted,
on_curve/scalar_mul READY-WAVE3. KATs `bn254_curveDbl/Add_kat`. EL bridges
`Bn254G1Add/Mul{Input,Result,Ecall}Bridge`. Risk: infinity=(0,0) encoding;
`bnc_validate_g1` uses raw x-regs (x8/x10) — a0-aliases-x10 class applies.

**Bn254Fq12Point** (FQ12 projective + Miller line fn, 0x08). 3 routines, ≈370
instr; no direct accel — all via `bnq_*` (each `bnq_mul` = 166 accel calls). Verbatim
port of py_ecc `optimized_curve.double`/`add` + `linefunc`. Spec gap:
protocol-level on tower-field. All COMPOSITE. Temp pool `bnq_d0..d9` (10×384 B).

**Bn254PairingCore** (G2 Fp2-projective + subgroup check, 0x08). 3 routines, ≈285
instr; **the only BN254 path using the Fp2 accelerators** (0x808/9/A via
`bnp_fp2_*`). same projective formulas over the accel-backed Fp2 layer;
`bng2_subgroup_ok` = EIP-197 G2 subgroup check (is_inf(n·Q), 254-bit
double-and-add) — **real** (twist has large cofactor). All COMPOSITE.

**Bn254Pairing** (Miller loop + `zkvm_bn254_pairing`, 0x08). 3 routines, ≈370
instr; transitively 0x802 + 0x808/9/A, **plus 2 direct 0x802** (twist step :335/354
computing xc0−9·xc1, yc0−9·yc1). The pairing proper (**protocol-level, hardest**):
64-iteration Miller loop accumulating f=f²·line as a fraction (fn/fd separate),
Frobenius corrections Q1/−Q2, per-pair validate + G2 subgroup, then
F=(tn·td⁻¹)^((p¹²−1)/n). Outer loop over k pairs (**data-dep, cap = k**, ~22 M
steps/pair). Two semantically-exact hoisting rewrites (single denom inverse +
single final exp across pairs). Chain depth **5**. `bnq_pt_copy` converted, rest
COMPOSITE. `codegen-zisk-bn254-pairing-check.sh` (bilinearity, e(P,Q)·e(−P,Q)=1,
rejection paths) vs py_ecc, gated 1e9 steps. EL bridges `Bn254Pairing{…}Bridge`.

### 3.6 BLS12-381 family (0x0A KZG, 0x0B–0x11) — largest family (~200 KB)

Files: `Bls12Field/Fq12/G1/G2/Map/MapG1Real/MapG2Real/Pairing/Kzg.lean`. Seam:
0x80B Arith384Mod (6-limb `arith256Mod`), 0x80C/D curve add/dbl, 0x80E/F/810 Fp2
add/sub/mul. **No G2 curve accelerator** — G2 chord/tangent is software over the
Fp2 accels + Fermat Fp inverse. Difficulty (hardest→easiest): **KZG > pairing >
map-g2 ≈ map-g1 > G2MSM > G2ADD > G1MSM > G1ADD**.

**Bls12Field** (shared base, all of 0x0A–0x11). ≈118 instr + copy_quads prog.
`blsf_fp_mul`/`blsf_fp_add` 1×0x80B each; remaining `.4byte`s are the standalone
accel probe. Pure **glue** (byte-plumbing). copy_quads converted; FpMul/FpAdd
NEEDS-DOTWORD (coverage:411-412). `codegen-zisk-bls12-accel-check.sh`.

**Bls12G1** (0x0B G1ADD, 0x0C G1MSM). 20 routines, ≈453 instr + 8 leaf progs;
0x80C×2, 0x80D×2, 0x80B×2. Point ops = thin glue over curve accels + Arith384Mod;
**software**: affine special-case wrappers (inf, equal-x dbl, P+(−P)=∞), on-curve
y²=x³+4, **real order-n subgroup check** (`blsg_subgroup_g1` — cofactor≠1),
double-and-add scalar_mul with software infinity flag `s3`. Spec gap: group-law
(+subgroup for MSM). scalar_mul depth 2, MSM depth 3–4; **cap k≤128 pairs**
(gas-gated). 7 leaves converted (lt_p with reloc); point ops NEEDS-DOTWORD;
`zkvm_bls12_g1_add/msm` blocked ("first line is `.globl`, not a label"
coverage:449-450). `codegen-zisk-bls12-g1-check.sh`, `-g1-add-backend-probe-`,
`codegen-eest-bls12-g1-frontier-check.sh` (EIP-2537). EL bridges
`Bls12G1Add/Msm{…}Bridge`; accel-id membership `isAccelerator_bls12_g1_add/msm`
(Accelerators/Dispatch.lean:133-134). Risk: **ADD deliberately skips the subgroup
check, MSM requires it** (matches execution-specs — don't "fix" ADD); accel
requires x1≠x2 so the equal-x-ruled-out ordering is load-bearing; `s3` infinity
flag mishandling silently drops terms.

**Bls12G2** (0x0D G2ADD, 0x0E G2MSM). 19 routines, ≈491 instr + 2 progs; **no G2
curve accel** — 0x80E×1, 0x80F×1, 0x80B×2 (0x810 via `blsg2_fp2_mul` helper).
**Real tower-field + group-law**: Fp inverse `x^(p−2)` (~384 iters ×Arith384Mod),
Fp2 inverse `(c0−c1u)/(c0²+c1²)`, affine chord/tangent over Fp2, on-curve
y²=x³+4(u+1), real subgroup check. Deepest chain **≈6**
(`msm→scalar_mul→point_add→point_dbl→fp2_inv→fp_inv→fp_mul`). fp_inv 384-iter
nested; MSM the deepest data-dep nest in the family. 2 progs converted; Fp/Fp2 ops
NEEDS-DOTWORD; kernels blocked (.globl). `codegen-zisk-bls12-g2-check.sh`, eest.
EL bridges `Bls12G2Add/Msm{…}Bridge`. Risk: `blsg2_fp_inv` needs nonzero reduced
input, dst≠`blsg2_facc`; chord_tail alias-safe only via t1/t2 staging;
(0,0) not on the G2 curve so infinity = all-zero (distinct from G1 usage).

**Bls12Fq12 + Bls12Pairing** (0x0F pairing). Fq12 = 10 routines ≈176 instr, 5×0x80B
(mul + 2 reduction folds + add/sub/smul); FQ12 = Fp[w]/(w¹²−2w⁶+2), schoolbook
12×12 → cascading reduction, MSB-first `blq_pow` for x^(p¹²−2) / x^((p¹²−1)/n)
(baked exps top-bit 4568/4313). Pairing = 6 routines ≈380 instr, **2×0x80B direct**
(Fp2→FQ12 twist :548/571); FQ12 projective double/add (py_ecc `optimized_curve`),
`linefunc`, 63-entry Miller loop (no −1 entries / no Frobenius tail for BLS),
cross-pair accumulation with ONE Fermat inverse + ONE final exp, per-pair validate
+ **both** G1 and G2 subgroup checks. Spec gap: **protocol-level** (ate pairing +
final exp = py_ecc `bls12_pairing`). Outer pair loop (cap k) × miller(63) ×
mul-internal → depth 3; the two `blq_pow` (4569/4314 bits) are the cost center.
Largest data arena (projective points `blq_R/Q/P` 1728 B each). 4 Fq12 leaves +
pt_copy converted; mul/add/sub/smul NEEDS-DOTWORD; kernels blocked.
`codegen-zisk-bls12-pairing-check.sh`, eest. EL bridges `Bls12Pairing{…}Bridge`
(dispatch holds pairLength=384). Risk: twist coefficient placement (X→coeffs 1/7,
Y→0/6, Z→coeff 3=w³) is hardcoded raw `ld/sd` offsets — brittle to any FQ12 layout
change.

**Bls12Map + MapG1Real + MapG2Real** (0x10 map-fp-to-g1, 0x11 map-fp2-to-g2).
`Bls12Map` holds constants (11-isogeny `blm_k11_*`, 3-isogeny `blm_k3_*`, SSWU
`iso*_a/b/z`, η/root8 tables) + the two `blm_fp_pow`/`blm_fp2_pow` helpers.
**MapG1Real** = ≈907 instr, **single unrolled routine, ~900 LoC real software
math** = optimized_swu_G1 (eprint 2019/403): numerator/denominator, sqrt via
`blm_fp_pow` + `sqrt_m11c` fallback, parity sign-fix, the **11-isogeny map** as
fully-unrolled Horner (4 polys, degrees 11/10/15/15 over powers zp0..zp14),
projective→affine, `clear_cofactor` = h_eff scalar mul. **MapG2Real** = ≈760 instr,
single unrolled routine = optimized_swu_G2 over Fp2 with the **(p²−9)/16
sqrt-candidate + 4 root8 × 4 η branch search** (RFC 9380 sqrt_ratio), Fp2 sgn0, the
**3-isogeny map** unrolled Horner, h_eff_G2 cofactor mul. Spec gap:
**protocol-level** (py_ecc `map_to_curve_*`+`clear_cofactor_*`). Both blocked
(.globl). `codegen-zisk-bls12-map-check.sh`, eest. EL bridges
`Bls12MapFpToG1/Fp2ToG2{…}Bridge`. Risk: hand-baked iso-coefficient tables only
differentially checked ("regenerate rather than hand-edit"); MapG2 relies on the
unproved RFC 9380 guarantee that exactly one of the 8 candidates is the root
(else a real input is wrongly rejected).

**Bls12Kzg** (0x0A KZG point-evaluation). 7 routines, ≈272 instr + 2 progs;
**1×0x80B direct** (scalar negation d=v·(n−1) mod n :404). **Protocol-level +
new ground**: (a) **48-byte compressed-G1 decompression** (`blsk_decompress_g1`
:274-369) — c/b/a flag bits, exact `0xc0‖0^47` infinity, x<p, y=(x³+4)^((p+1)/4)
with QR check (p≡3 mod 4), a_flag sign-select via (2y)//p vs (p+1)/2; (b) z/y
canonicality (<n) + `(n−v) mod n` negation; (c) builds X_minus_z / P_minus_y,
encodes to EIP-2537 wire, verifies via `zkvm_bls12_pairing` (2-pair). Baked
constants incl. `blsk_tau2_le` (KZG setup G2 pre-decompressed). Spec gap =
execution-specs `verify_kzg_proof`. Chain depth 4 (→ full pairing stack — the true
cost center). g1_wire/lt_be converted; fp_pow_q14/g2_wire converted-with-reloc;
neg_scalar NEEDS-DOTWORD; kernel blocked (.globl).
`codegen-zisk-bls12-kzg-check.sh` (constant-poly proofs, decompression rejections,
off-subgroup, canonicality), verifying runs gated -n 4e9. EL bridges
`KzgPointEval{…}Bridge`. **Risk — the documented landmine:** compressed-G1
decompression (a_flag sign convention depends on `blsk_phalf_be`=(p+1)/2 being
exact and y reduced; exact-infinity encoding enforced; the pairing kernel
**re-validates** the constructed points and asserts "unreachable on the
constructed input" :573 — a valid proof could be reported invalid if the
KeyValidate/decompress invariant ever regresses). Versioned-hash check is the
dispatcher's job, not this kernel.

### 3.7 MODEXP (0x05) — pure bignum, no accelerator

Files: `ModexpBackend.lean` (backend), `Modexp.lean` (dispatcher). (1) backend
**365 instr / 8 routines** (`modexp_be_to_le` :30, `_le_to_be` :44, `_iszero`
:58, `_cmpge` :67, `_sub` :80, `_mul` :91, `_binmod` :118, `zkvm_modexp` :182);
dispatcher ≈231 template instr (some templates ×3). Deepest chain **4**
(`gas → zkvm_modexp → modexp_binmod → modexp_cmpge/sub`). (2) **NONE** — mul is
RV64 `mul`/`mulhu` (:104-105), division is binary long-division (`modexp_binmod`).
The **purest software-math kernel** — no seam to any `Accel.*`. (3) schoolbook
multiply (`modexp_mul`), binary long-division/mod (`modexp_binmod`),
square-and-multiply ladder (`zkvm_modexp` :247-295), BE↔LE conversion. **Plus a
second, independent implementation**: the dispatcher small-operand fast path
(≤4-byte operands) uses single-register `mul`/`remu` (Modexp.lean:209-226). Spec
gap: byte-plumbing → **bignum** (schoolbook-mul correctness, division-loop
invariant, ladder invariant). (4) `modexp_mul` depth 2 (na×nb); `modexp_binmod`
depth 2 (bit-loop × shift-loop); `zkvm_modexp` **depth 3** worst case. Data-dep
bounds `nb/ne/nm` (runtime); **backend caps ≤2048 B / `modexpBnMaxLimbs=256`**
(ModexpBackend.lean:13,202-205) but **dispatcher caps tighter at 1024 B / EIP-7823**
(Modexp.lean:35-36). (5) backend arenas `modexp_bn_base/exp/mod/result` (2048 B),
`_product` (4096 B), `_remainder` (2056 B); dispatcher staging `*_scratch` (1024 B);
**not in RegionMap (UNKNOWN)**. `zkvm_modexp` spills ra+s0–s11 (128 B). (6)
**unconverted** — monolithic `*Impl`/`*Asm` string with internal `jal`/`la`, not in
MANIFEST, no coverage-doc row (BLOCKED_ON_.6 shape; no `.4byte` so not
NEEDS-DOTWORD). (7) `codegen-zisk-modexp-backend-probe-check.sh`; EEST bridge
noted "gas/return-data framing missing" (eest-precompile-frontier.md:29); no Lean
KAT. (8) **none**. (9) **t2-clobber landmine** documented in-code
(ModexpBackend.lean:117 — the binmod bit counter must live in s5 because
cmpge/sub clobber t2).

### 3.8 P256VERIFY (0x100) — software P-256 over Arith256Mod

File: `P256Verify.lean`. (1) ≈**487 instr / 13 routines** (6 leaf `Program` lists
+ 7 string fns). Leaf exact (`#guard`): copy_n=8, is_zero_n=12, eq32=15, lt_be=16,
be_to_le=20, le_to_be=19. String (est): op_with=18, pow=42, chord_tail=44,
point_dbl=66, point_add=51, scalar_mul=52, `zkvm_secp256r1_verify`=124. Deepest
chain **7** (`verify → scalar_mul → point_add → point_dbl → pow → op_with →
be_to_le`). (2) **0x802 Arith256Mod — ONE static site** (`p256_op_with`
P256Verify.lean:346); **no P-256 curve accelerator exists**. The single `.4byte`
is a thin 18-instr wrapper selected by param blocks
(`p256_pb_mul_p`/`add_p`/`sub_p`/`mul_n`) — every field mul/add/sub/square routes
through it (thousands of dynamic calls). (3) everything except the 4-limb mul is
software: Fermat inversion (`p256_pow` — `a^(p−2)` / `a^(n−2)`), affine group law
(`p256_chord_tail`/`point_dbl`/`point_add`), double-and-add `p256_scalar_mul`, and
the ECDSA verify orchestration (bounds gates, on-curve `qy²=qx³+aqx+b`,
`u1=e·s⁻¹`, `u2=r·s⁻¹`, `R=u1·G+u2·Q`, final `R.x mod n == r`). Spec gap:
**group-law → protocol-level** (matches execution-specs `secp256r1_verify`).
(4) pow depth 2 (32 B × 8 bit = 256 squarings); scalar_mul depth 2 (256 iters);
**no data-dependent bounds** — all sizes fixed (32-byte fields, 256-bit scalars),
constant-trip loops. (5) `p256VerifyDataFragment` (:57-144) — domain params,
Fermat exps, generator, LE staging cells, param blocks, field/point scratch;
frames 56–72 B; **not in RegionMap (UNKNOWN)**. (6) **mixed**: 6 leaves converted
(drift guards + fixtures); the 6 larger string fns BLOCKED_ON_.6/NEEDS-LI
(coverage:299-303); **`p256OpWithFunction` NEEDS-DOTWORD (coverage:440) — the one
routine that gates conversion of the entire arithmetic stack**. (7)
`codegen-zisk-p256verify-check.sh` (vs execution-specs `secp256r1_verify` + the
`cryptography` lib: valid sigs, the n−s malleability twin valid under EIP-7951,
bounds/off-curve/(0,0) gates, the u1=0 corner); EEST bridge "call framing missing"
(eest-precompile-frontier.md:34); Lean = 6 structural drift guards only. (8) **none
functional** — only the 6 `*_eq_prog := rfl` drift guards; the docstring's "proven
Bls12G2 shape" (:9) is a claimed shape-reuse, not an imported proof. (9) infinity
handled by flags not encoding (an `s3` flag through scalar_mul; P=−P/P=Q
special-cased); sub = `(b·(p−1)+a) mod p` relies on the exact `p256_le_pm1`
constant; **e (message hash) is NOT pre-reduced mod n** (:743-744) — relies on
Arith256Mod reducing the full 512-bit product; per-routine alias constraints.

---

## 4. Cross-cutting: shared-infrastructure candidates

Helper routines seen in ≥2 kernels — these determine the shape of the
field-arithmetic library plan the `.11` decision must produce.

| candidate | instances (file:routine) | note |
|---|---|---|
| **BE↔LE limb marshalling** | `bnf_be_to_le`/`le_to_be`, `blsg_be_to_le`/`le_to_be`, `blsf_copy_quads`, `secf_be_to_le`/`le_to_be`, `modexp_be_to_le`/`le_to_be`, `p256_be_to_le`/`le_to_be` | ~6 near-identical 32B/48B converters; the single most duplicated primitive. One verified generic converter serves every 0x802/0x80B client. |
| **Arith256Mod fused-op wrapper** | `p256_op_with`, `bnf_mul/add_mod_p`, `blsf_fp_mul/add`, `secf_mul_mod_p/n`, `bnp_fp_mul/add`, `blsg2_fp_mul/add` | the `{a,b,c,module,d}` param-block convention (mul c=0 / add b=1 / sub b=p−1) is reusable across every Arith256Mod/Arith384Mod client. |
| **MSB-first square-and-multiply ladder** | `p256_pow`, `zkvm_modexp`, `bnp_fp_pow`, `bnq_pow`, `blq_pow`, `blm_fp_pow`/`fp2_pow`, `secf_pow_mod_p/n` | the same algorithm at 254/256/384/3044/4569-bit widths; one modulus-parameterized ladder-correctness lemma covers Fermat inversion everywhere. |
| **Double-and-add scalar-mul skeleton** | `bnc_scalar_mul` (69), `bls*g_scalar_mul` (60–67), `p256_scalar_mul` (52/66), `secp256k1_scalar_mul` (67), `bng2_subgroup_ok` | structurally identical 256-bit ladders parameterized by the curve add/dbl callbacks + a software infinity flag. |
| **32-byte buffer ops** (copy/zero/eq/is_zero/lt) | `p256_*`, `secf_*`, `bnf_*`, `blsg_*` | byte-plumbing leaves already ALREADY-STRUCTURED across families — the cheap, already-converted layer. |
| **Fp2 arithmetic + inverse** | `bnp_fp2_*` (BN254), `blsg2_fp2_*` (BLS) | reused by both pairings + BLS maps; the 0x808–0x810 seam meets here. |
| **Projective double/add formula** | `bnq_pt_double/add` (over FQ12), `bng2_double/add` (over Fp2), `blq_pt_double/add` (over FQ12) | identical algebra at different field layers — one shared group-law spec lemma. |
| **`zkvm_bls12_pairing` wholesale** | reused by KZG (0x0A) | KZG verifies its 2 constructed pairs by calling the pairing kernel outright. |
| **U256 BE primitives** | `u256_add_be`/`sub_be`/`lt_be` (Programs/U256.lean) | already factored; used by secp field reduce/range + tx recovery. |
| **EIP-150 child-gas allotment** | `bn254_call_allotment` (Bn254Curve.lean:461) | 63/64 rule shared across precompile failure paths (cross-family, dispatcher-adjacent). |

---

## 5. Cross-cutting: the accelerator seam per `Accel.*` (proof foundation)

For each concrete accelerator, the kernels whose glue proofs will meet it (from
§2a; "via helper" = reached through a wrapper, not a direct `.4byte` in that file):

- **`keccakF` (0x800)** — hash bridges (`zkvm_keccak256`, `…_segments`), MPT trie-root, keccak probes. *All hashing bottoms out here.*
- **`sha256Compress` (0x805)** — `zkvm_sha256` bridge, sha256 probes.
- **`arith256Mod` 4-limb (0x802)** — BN254 (Field, Fp2, Fq12, Pairing twist), secp256k1 (mul_mod_p, mul_mod_n → all field/scalar/Fermat work), P256VERIFY (`op_with` → the entire group law). *The busiest seam: the whole of P256 and secp256k1 field math + the BN254 FQ12 tower.*
- **`arith256Mod` 6-limb (0x80B / Arith384Mod)** — BLS12 (Field, Fq12 tower, G1/G2 Fp work, pairing twist, KZG scalar-neg, and — via helpers — both maps). *BLS analogue of the above.*
- **`curveAddL`/`curveDblL secpP 4` (0x803/0x804)** — secp256k1 point_add/point_double → scalar_mul → ECDSA recovery.
- **`curveAddL`/`curveDblL bn254P 4` (0x806/0x807)** — BN254 G1 ecAdd/ecMul.
- **`curveAddL`/`curveDblL bls12P 6` (0x80C/0x80D)** — BLS12 G1 point ops → G1ADD/G1MSM, cofactor clearing in map-fp-to-g1.
- **`complexAddL/SubL/MulL bn254P 4` (0x808/0x809/0x80A)** — BN254 Fp2 layer → the G2 subgroup check in the pairing.
- **`complexAddL/SubL/MulL bls12P 6` (0x80E/0x80F/0x810)** — BLS12 Fp2 layer → G2 group law, both BLS maps.
- **`blake2bRound` (0x819)** — BLAKE2F only.

Bead `.1`'s concrete semantics (+ `csrsWrite`/`csrsValid` projection lemmas,
ZiskAccel.lean:674-699) are the shared foundation *every* glue proof reduces to.

---

## 6. Guest ↔ spec divergences noticed (P1 bead candidates)

Per standing policy, divergences found while reading are filed as P1 beads. None
below is a confirmed *behavioral* wrong-answer against execution-specs — they are
verification-gap / drift / brittleness risks a strategy proof must confront. The
three concrete, actionable ones are filed as beads
`evm-asm-4ch8f.11.2` (D1), `.11.3` (D2), `.11.4` (D3); D5–D7 are inherent to the
`.11` strategy scope and are recorded here rather than bead-spammed.

1. **(P1-D1, bead `.11.2`) secp256k1 sqrt dead constant.** `secf_sqrt_mod_p` hardcodes a skip-bit
   list `{255,254,30,7,6,5,4,1}` (Secp256k1Field.lean:620-635) while the declared
   `secp256k1_sqrt_exp_be` = (p+1)/4 constant (:48-52) is **referenced nowhere
   else** (verified by grep). The list must equal the zero-bits of (p+1)/4; the two
   can silently drift. *Confidence: high (dead constant confirmed).*
2. **(P1-D2, bead `.11.3`) MODEXP has two independent implementations** — the dispatcher
   small-operand `mul`/`remu` path (Modexp.lean:209-226) vs the bignum backend.
   Both must be proven to compute the same EIP-198 result, or one is dead code.
3. **(P1-D3, bead `.11.4`) MODEXP length-cap mismatch** — dispatcher enforces 1024 B / EIP-7823
   (Modexp.lean:35-36) while the backend validates ≤2048 B / `modexpBnMaxLimbs=256`
   (ModexpBackend.lean:13,202-205). Effective cap is 128 limbs; a proof keyed off
   `modexpBnMaxLimbs` would over-state the domain.
4. **(P1-D4) P256 `e` not reduced mod n before use** (P256Verify.lean:743-744) —
   relies on `Accel.arith256Mod` reducing the full 512-bit product. If the accel
   were ever specced as 256-bit-only reduction, u1 diverges for hashes ≥ n. Needs
   an explicit lemma pinning the 512-bit reduction.
5. **(P1-D5) No kernel-level functional proofs exist for any crypto kernel.** The
   only assets are 9 accelerator KATs, ~40 `*_eq_prog` string-drift guards, and
   spec-side EL ABI bridges. Correctness of every group-law / tower-field /
   protocol-level kernel rests on the differential `codegen-zisk-*-check.sh`
   probes. (This is the whole reason `.11` exists; recorded here as the baseline.)
6. **(P1-D6) Unproved number-theoretic side conditions** — BN254/BLS G1 subgroup
   check *omitted* (cofactor-1 argument, Bn254PairingCore.lean:20); ecMul uses the
   raw scalar with no order reduction; BLS map-g2 relies on the RFC 9380 guarantee
   that exactly one of the 8 sqrt candidates is the root (Bls12MapG2Real.lean:502-503,
   else a valid input is wrongly rejected); KZG's constructed-point subgroup
   membership is *asserted* "unreachable" (Bls12Kzg.lean:573).
7. **(P1-D7) Hand-baked constant tables only differentially checked** — BLS map
   isogeny coefficients, `blsk_tau2_le`, the giant FQ12/map exponents; a
   transcription error is silent under the current proof set. Twist coefficient
   placement in both pairings is hardcoded raw `ld/sd` offsets with no structural
   guard.

---

## 7. Method appendix (reproduce these numbers)

- Accelerator seam: `grep -rnE '\.4byte 0x8|csrs 0x8' EvmAsm/Codegen/Programs/`
  (executable quoted-emit lines; comment/prose mentions excluded).
- Leaf instruction counts: `wc -l scripts/asm-fixtures/<name>.s` minus label lines,
  confirmed by `#guard <prog>.length = N` in the source.
- String-kernel counts (`≈`): count indented mnemonic-leading + `.4byte` lines in
  the Lean `def …Function : String` literals (excludes labels / `.`-directives /
  comment-only lines). These under-count post-link `Instr`s by ~15–20 % (pseudo-op
  expansion) — treat as lower bounds.
- Concrete accelerator semantics: `EvmAsm/Rv64/ZiskAccel.lean` (`Accel` namespace +
  `csrsWrite`/`csrsValid`).
- Conversion class: `docs/4ch8f-asm-to-program-coverage.md` (grep the function name)
  + `scripts/asm-fixtures/MANIFEST.tsv`.
- Regions: `EvmAsm/Codegen/RegionMap.lean` + `docs/4ch8f-region-map.md`.
- Spec ground truth: `tests-zkevm@v0.4.0` tag of `~/execution-specs`
  (`git show 'tests-zkevm@v0.4.0:src/ethereum/forks/amsterdam/vm/precompiled_contracts/…'`).
