# Notable Specs Index

A curated index of notable proven specifications across the EvmAsm codebase, with
permalinks to the exact theorem statements at a pinned commit. Use this page to
find a spec without grepping; refresh the permalinks when files move.

> **Permalinks pinned to commit `b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1` on
> 2026-05-26.** All sections were repinned in this slice — the previous mixed
> pins (2026-05-05 master, 2026-05-19 DivMod, plus the 2026-05-19/2026-05-21
> StorageArgs / SDiv / MulMod / AddMod additions) now share a single SHA.
> Refresh whenever a major surface lands (e.g. each closure of a #61-class
> umbrella issue) or quarterly, whichever comes first. To refresh, re-run
> `git rev-parse origin/main` and `grep -n` for each declaration name, then
> update the line numbers below.

This index is split by area. Slice 1 landed the page skeleton plus the DivMod
stack-spec surface. Slice 2 added the non-DivMod Evm64 opcode stack specs and
the `EvmWord` arithmetic correctness theorems, alongside the already-populated
EL/RLP and Rv64 infrastructure sections. Slice 3 (2026-05-19) repinned the
DivMod section, removed stale `n4` aliases that were never proved, and
documented the partial-domain caveat tracked by bead `evm-asm-9iqmw` and
gh-61. Slice 4 (this update, 2026-05-26) repins every section to a single
fresh SHA and corrects two off-by-one line drifts
(`Byte/Spec.lean#L849`, `SignExtend/Spec.lean#L65`); no new surface added.

---

## DivMod stack-spec surface

The path-specific stack-level Hoare triples for `DIV` and `MOD` and their
dispatcher-surface aliases. These are the consumer-facing entry points for
downstream verifiers — when proving a higher-level property, prefer the alias
over the underlying `_word_uni` theorem so a future bound relaxation propagates
automatically.

> **Partial-domain caveat (2026-05-19).** The unified case-split specs below
> are parametric over `DivStackSpecCase` / `ModStackSpecCase` whose
> constructors collectively require `b.getLimbN 3 = 0` — the divisor's top
> limb must be zero. Inputs with `b3 ≠ 0` (the full 4-limb Knuth-D path, n=4)
> are not in the domain. This is a spec-level coverage gap, not an executable
> bug: the buggy v1 Phase-1b-1-correction subroutine `divK_div128` was
> superseded by the closed v4 implementation `divK_div128_v4` (full Knuth
> Algorithm D, 2-correction in both Phase 1b and Phase 2b), and the
> executable `evm_div` / `evm_mod` Programs were switched to v4 by
> [PR #4992](https://github.com/Verified-zkEVM/evm-asm/pull/4992)
> (2026-05-19). The remaining spec-layer migration — extending
> `divCode` / `modCode` to v4 and adding full-domain
> `evm_div_stack_spec_unconditional` / `evm_mod_stack_spec_unconditional`
> theorems — is tracked by bead `evm-asm-9iqmw` (epic "SDIV + unconditional
> DIV/MOD stack specs (gh-61)") and the reopened
> [GitHub issue #61](https://github.com/Verified-zkEVM/evm-asm/issues/61).

### Unified case-split specs (single theorem per opcode, b3 = 0 only)

The monolithic stack specs that case-split internally on the dispatcher
branch certificate (`DivStackSpecCase` / `ModStackSpecCase`). Prefer these
when proving a higher-level property that does not need to mention the
specific path — the dispatcher branch is hidden behind the certificate.

| Theorem | Defined at | Pre / Post (plain English) |
|---|---|---|
| [`evm_div_stack_spec`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L998) | `Spec/Unified.lean:998` | Pre: stack at `sp` holds two `EvmWord`s `a, b` (top = `b`), the DivMod scratch buffer at `base + ...` is in a recognized branch state given by `branch : DivStackSpecCase base a b` (b = 0, or n=1/2/3 with `b3 = 0`). Post: `cpsTripleWithin unifiedDivBound` lands at `base + nopOff` with top of stack equal to `EvmWord.div a b` under `evmWordIs`, all framed memory and registers preserved per `divStackDispatchPost`. |
| [`evm_mod_stack_spec`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L1396) | `Spec/Unified.lean:1396` | Pre/post mirror of DIV, with `EvmWord.mod a b` and `modStackDispatchPost`, parametric over `branch : ModStackSpecCase base a b`. Same partial-domain caveat. |

### Per-branch path-specific theorems (b3 = 0 only)

`DivStackSpecCase` / `ModStackSpecCase` have exactly four constructors:
`bzero` (divisor = 0), `n1Full` / `n2Full` / `n3Full` (non-zero divisor with
`b3 = 0`). There is no `n4Full` constructor — the n=4 path has no proven
stack-level dispatcher theorem yet. The previous notable-specs entries
naming `evm_div_n4_stack_spec_within_dispatch_uni` /
`evm_mod_n4_stack_spec_within_dispatch_uni` referenced theorems that were
never landed; they are removed in this refresh.

| Theorem | Defined at |
|---|---|
| `evm_div_bzero_stack_spec_within` | [`Spec/Base.lean:383`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Base.lean#L383) |
| `evm_div_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:119`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L119) |
| `evm_div_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:334`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L334) |
| `evm_div_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:534`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L534) |
| `evm_mod_bzero_stack_spec_within` | [`Spec/Base.lean:490`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Base.lean#L490) |
| `evm_mod_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:1159`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L1159) |
| `evm_mod_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:1200`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L1200) |
| `evm_mod_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:1240`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L1240) |

### Dispatcher registries

The previous registries `evm_div_stack_spec_within` and
`evm_mod_stack_spec_within` lived in the now-removed
`Spec/StackDispatcher.lean` shim. Per-branch step bounds have since been
unified — all non-`bzero` branches share the single `unifiedDivBound`
(`Spec/Unified.lean`) and the `bzero` branches keep their constant-time
short-circuit (`Spec/Base.lean`).

### Closure roadmap (bead `evm-asm-9iqmw`)

The full-domain unconditional public specs (covering the n=4 path) land via:

1. **Phase 0a** (`evm-asm-9iqmw.2`) — partial-domain dispatch wrapper
   `evm_div_stack_spec_unconditional_noNop` covering bzero + n1/n2/n3 + the
   already-closed n4-call-skip branch. In flight.
2. **Phase 2a** (`evm-asm-9iqmw.4`) — migrate `divCode` / `modCode` /
   `divCode_noNop` / `sharedDivModCode` from `divK_div128` (v1) to
   `divK_div128_v4` (executable already migrated by
   [PR #4992](https://github.com/Verified-zkEVM/evm-asm/pull/4992); spec
   layer still pending in `.4.2`–`.4.6`).
3. **Phase 0b** (`evm-asm-9iqmw.7`) — full-domain
   `evm_div_stack_spec_unconditional` / `evm_mod_stack_spec_unconditional`
   retiring `DivStackSpecCase`. Blocks gh-61 closure.

### SDIV (signed division) — conditional stack spec

| Theorem | Defined at | Status |
|---|---|---|
| [`evm_sdiv_stack_spec_within`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/SDiv/Spec.lean#L1061) | `SDiv/Spec.lean:1061` (alias for `evm_sdiv_handler_stack_spec_within`) | **Conditional**: takes an `hStack` premise that discharges unconditionally for `divisor = 0`. For nonzero divisors `hStack` is a `cpsTripleWithin` over `divCode_noNop` that callers supply per branch — unblocked for bzero / n1 / n2 / n3 / n4-call-skip, pending v4 migration for the n4-call-addback path. Closure tracked by bead `evm-asm-9iqmw.5` (Phase 3). |

---

## Other Evm64 opcode stack specs

The following are the dispatcher-surface stack-level Hoare triples for the
remaining (non-`DivMod`) Evm64 opcodes. Each names a concrete program,
states the stack pre/post over `evmStackIs`, and bounds the step count.

### Arithmetic and bitwise

| Theorem | Defined at | Meaning |
|---|---|---|
| `evm_add_stack_spec_within` | [`Add/Spec.lean#L74`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Add/Spec.lean#L74) | ADD: top two stack words → low-256 sum. |
| `evm_sub_stack_spec_within` | [`Sub/Spec.lean#L74`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Sub/Spec.lean#L74) | SUB: a − b mod 2^256. |
| `evm_mul_stack_spec_within` | [`Multiply/Spec.lean#L92`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Multiply/Spec.lean#L92) | MUL: low-256 product. |
| `evm_mul_stack_spec_within_layout` | [`Multiply/Layout.lean#L87`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Multiply/Layout.lean#L87) | MUL with explicit scratch layout exposed to callers. |
| `evm_and_stack_spec_within` | [`And/Spec.lean#L54`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/And/Spec.lean#L54) | AND: bitwise conjunction. |
| `evm_or_stack_spec_within`  | [`Or/Spec.lean#L42`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Or/Spec.lean#L42) | OR: bitwise disjunction. |
| `evm_xor_stack_spec_within` | [`Xor/Spec.lean#L42`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Xor/Spec.lean#L42) | XOR: bitwise xor. |
| `evm_not_stack_spec_within` | [`Not/Spec.lean#L63`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Not/Spec.lean#L63) | NOT: bitwise complement. |
| `evm_shl_stack_spec_within` | [`Shift/ShlSemantic.lean#L132`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Shift/ShlSemantic.lean#L132) | SHL: shift-left, EVM saturation. |
| `evm_shr_stack_spec_within` | [`Shift/Semantic.lean#L132`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Shift/Semantic.lean#L132) | SHR: logical shift-right. |
| `evm_sar_stack_spec_within` | [`Shift/SarSemantic.lean#L144`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Shift/SarSemantic.lean#L144) | SAR: arithmetic shift-right (sign-fill). |
| `evm_byte_stack_spec_within` | [`Byte/Spec.lean#L849`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Byte/Spec.lean#L849) | BYTE: extract i-th byte (big-endian). |
| `evm_signextend_stack_spec_within` | [`SignExtend/Spec.lean#L65`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/SignExtend/Spec.lean#L65) | SIGNEXTEND: sign-extend low (k+1) bytes. |

### Comparators

| Theorem | Defined at | Meaning |
|---|---|---|
| `evm_lt_stack_spec_within`     | [`Lt/Spec.lean#L79`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Lt/Spec.lean#L79) | LT: unsigned less-than → 0/1. |
| `evm_gt_stack_spec_within`     | [`Gt/Spec.lean#L82`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Gt/Spec.lean#L82) | GT: unsigned greater-than → 0/1. |
| `evm_slt_stack_spec_within`    | [`Slt/Spec.lean#L118`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Slt/Spec.lean#L118) | SLT: signed less-than. |
| `evm_sgt_stack_spec_within`    | [`Sgt/Spec.lean#L120`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Sgt/Spec.lean#L120) | SGT: signed greater-than. |
| `evm_eq_stack_spec_within`     | [`Eq/Spec.lean#L79`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Eq/Spec.lean#L79) | EQ: equality → 0/1. |
| `evm_iszero_stack_spec_within` | [`IsZero/Spec.lean#L66`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/IsZero/Spec.lean#L66) | ISZERO: 1 iff top-of-stack is 0. |

### Stack/memory shuffling and constants

| Theorem | Defined at | Meaning |
|---|---|---|
| `evm_pop_stack_spec_within`  | [`Pop/Spec.lean#L30`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Pop/Spec.lean#L30) | POP: drop top of stack. |
| `evm_dup_stack_spec_within`  | [`Dup/Spec.lean#L143`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Dup/Spec.lean#L143) | DUP1..DUP16: duplicate the n-th stack slot. |
| `evm_swap_stack_spec_within` | [`Swap/Spec.lean#L149`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Swap/Spec.lean#L149) | SWAP1..SWAP16: swap top with the (n+1)-th. |
| `evm_push0_stack_spec_within` | [`Push0/Spec.lean#L40`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Push0/Spec.lean#L40) | PUSH0: push the zero word. |
| `evm_push_zero_slot_stack_spec_within` | [`Push/Spec.lean#L172`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Push/Spec.lean#L172) | PUSH1..32 to a zero stack slot (per-limb). |
| `evm_push_zero_slot_full_stack_spec_within` | [`Push/Spec.lean#L200`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Push/Spec.lean#L200) | PUSH1..32 to a zero immediate (zero-slot path only). |
| `evm_push_stack_spec_within` | [`Push/ImmediateCompose.lean`](../EvmAsm/Evm64/Push/ImmediateCompose.lean) | **PUSH2..32 — complete.** Pushes the big-endian immediate `pushImmediateWord n byteAt` (`1 ≤ n ≤ 32`), no input-domain restriction. Registry witness for the `PUSH2..32` `proven` row. Models code source + stack slot as `bytesRegion`s; inductive `n`-byte copy chain. |
| `evm_msize_stack_spec_within` | [`MSize/Spec.lean#L138`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/MSize/Spec.lean#L138) | MSIZE: push current memory size in bytes. |
| `evm_mstore8_stack_spec_within` | [`MStore8/Spec.lean#L140`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/MStore8/Spec.lean#L140) | MSTORE8: write the low byte at memory[offset]. |
| `evm_mstore8_stack_spec_clean_sp_within` | [`MStore8/Spec.lean#L220`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/MStore8/Spec.lean#L220) | MSTORE8 variant that exposes the post-stack-pointer cleanup explicitly. |

> MLOAD / MSTORE stack specs are tracked under #102 / #99 and not yet
> landed; this section will be extended as those PRs merge.

### Storage argument, access, and gas bridges

The SLOAD/SSTORE surface currently exposes pure stack decoders plus
EIP-2929 warm/cold access and dynamic-gas bridges. These are the pieces used
by the storage handler and conformance slices while the ECALL/stack-spec layer
is still being connected.

| Theorem | Defined at | Meaning |
|---|---|---|
| `StorageArgs.decodeStorageStack?_eq_some_iff` | [`StorageArgs.lean#L172`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageArgs.lean#L172) | Successful SLOAD/SSTORE stack decoding is equivalent to one of the concrete stack layouts. |
| `StorageArgs.decodeStorageStack?_eq_none_iff` | [`StorageArgs.lean#L230`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageArgs.lean#L230) | Decoder failure is exactly stack underflow for the selected storage opcode kind. |
| `StorageArgs.decodeStorageStack?_writesStorage_of_some` | [`StorageArgs.lean#L224`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageArgs.lean#L224) | A successful decode exposes whether the opcode writes storage (`SSTORE`) or only reads (`SLOAD`). |
| `StorageAccess.sloadDynamicCostForKey_of_warm` | [`StorageAccess.lean#L73`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccess.lean#L73) | SLOAD dynamic gas collapses to the warm-key cost when the key is already warm. |
| `StorageAccess.sloadDynamicCostForKey_of_cold` | [`StorageAccess.lean#L78`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccess.lean#L78) | SLOAD dynamic gas collapses to the cold-key cost when the key is not warm. |
| `StorageAccess.sstoreDynamicCostForKey_of_warm` | [`StorageAccess.lean#L98`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccess.lean#L98) | SSTORE dynamic gas uses the warm write-cost branch for already-warm keys. |
| `StorageAccess.sstoreDynamicCostForKey_of_cold` | [`StorageAccess.lean#L106`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccess.lean#L106) | SSTORE dynamic gas adds the cold-key surcharge for first touches. |
| `StorageAccessWarm.warmKey_idempotent` | [`StorageAccessWarm.lean#L14`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccessWarm.lean#L14) | Warming an already-present access key leaves the access list unchanged. |
| `StorageAccessWarm.sloadDynamicCostForKey_warmKey_of_isWarm` | [`StorageAccessWarm.lean#L38`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccessWarm.lean#L38) | SLOAD cost is unchanged by a redundant warm-key operation. |
| `StorageGas.sstoreWriteCost_set` | [`StorageGas.lean#L86`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageGas.lean#L86) | SSTORE write cost is the set cost when the current value is zero and the new value is nonzero. |
| `StorageGas.sstoreWriteCost_reset` | [`StorageGas.lean#L93`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageGas.lean#L93) | SSTORE write cost is the reset cost when the current value is nonzero and the write is not a no-op. |
| `StorageAccessOutcome.sloadOutcome_warms` | [`StorageAccessOutcome.lean#L43`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccessOutcome.lean#L43) | SLOAD outcomes warm the accessed key for later operations. |
| `StorageAccessOutcome.sstoreOutcome_warms` | [`StorageAccessOutcome.lean#L59`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/StorageAccessOutcome.lean#L59) | SSTORE outcomes warm the accessed key for later operations. |

### Calldata copy program and partial specs

CALLDATACOPY currently has a concrete RISC-V program plus partial preamble and
memory-effect specs. The full destination-memory stack spec remains tied to
the broader memory model work, but these are the #104 program/spec entry
points already available for composition.

| Declaration / Theorem | Defined at | Meaning |
|---|---|---|
| `evm_calldatacopy` | [`CopyProgram.lean#L107`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Calldata/CopyProgram.lean#L107) | Concrete 19-instruction RV64 program for CALLDATACOPY. |
| `evm_calldatacopy_length` | [`CopyProgram.lean#L141`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Calldata/CopyProgram.lean#L141) | Program length fact used by code-region and byte-offset proofs. |
| `evm_calldatacopy_preamble_spec_within` | [`CopySpec.lean#L77`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Calldata/CopySpec.lean#L77) | Hoare spec for the executable preamble before the byte-copy loop. |
| `evm_calldatacopy_preamble_stack_spec_within` | [`CopySpec.lean#L156`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Calldata/CopySpec.lean#L156) | Stack-form lift of the CALLDATACOPY preamble spec. |
| `evm_calldatacopy_full_code_preamble_stack_spec_within` | [`CopySpec.lean#L257`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Calldata/CopySpec.lean#L257) | Preamble stack spec transported to the full `evm_calldatacopy_code` region. |
| `evm_calldatacopy_partial_memory_effect` | [`CopySpec.lean#L299`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/Calldata/CopySpec.lean#L299) | Partial memory-effect bridge: a destination byte equals the executable calldata byte at the matching source offset. |

### CALL-family argument and returndata bridges

The CALL-family surface currently exposes pure stack decoders and returndata
copy bridges used by handler/conformance proofs for CALL, STATICCALL,
DELEGATECALL, and RETURNDATACOPY.

| Theorem | Defined at | Meaning |
|---|---|---|
| `CallArgs.hasValueArgument_iff_call` | [`CallArgs.lean#L139`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallArgs.lean#L139) | Only CALL carries a value-transfer stack argument. |
| `CallArgs.isStatic_iff_staticcall` | [`CallArgs.lean#L143`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallArgs.lean#L143) | STATICCALL is exactly the static call kind. |
| `CallArgs.preservesCallerContext_iff_delegatecall` | [`CallArgs.lean#L147`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallArgs.lean#L147) | DELEGATECALL is exactly the caller-context-preserving kind. |
| `CallArgsStackDecode.decodeCallFamilyStack?_eq_some_iff` | [`CallArgsStackDecode.lean#L433`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallArgsStackDecode.lean#L433) | Successful CALL-family stack decoding is equivalent to one of the three concrete argument layouts. |
| `CallArgsStackDecode.decodeCallFamilyStack?_eq_none_iff` | [`CallArgsStackDecode.lean#L649`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallArgsStackDecode.lean#L649) | Decoder failure is exactly stack underflow for that call kind. |
| `ReturnData.copyBytes_get` | [`ReturnData/Basic.lean#L49`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/ReturnData/Basic.lean#L49) | RETURNDATACOPY source bytes are copied from returndata, with zero padding handled by the bounds lemmas below. |
| `ReturnData.copyWriteByteAt_at_destination_add_of_in_bounds` | [`ReturnData/CopyMemory.lean#L101`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/ReturnData/CopyMemory.lean#L101) | In-bounds RETURNDATACOPY writes the selected returndata byte at the destination address. |
| `ReturnData.copyWriteByteAt_at_destination_add_of_out_of_bounds` | [`ReturnData/CopyMemory.lean#L110`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/ReturnData/CopyMemory.lean#L110) | Out-of-bounds RETURNDATACOPY writes zero at the destination address. |
| `returnDataHandler?_eq_some_iff` | [`ReturnDataHandlers.lean#L39`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/ReturnDataHandlers.lean#L39) | Characterizes the RETURNDATASIZE handler-table lookup. |
| `returnDataHandler?_eq_none_iff` | [`ReturnDataHandlers.lean#L45`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/ReturnDataHandlers.lean#L45) | Characterizes missing returndata-handler lookups for non-RETURNDATASIZE opcodes. |
| `dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE` | [`ReturnDataHandlers.lean#L70`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/ReturnDataHandlers.lean#L70) | Dispatching RETURNDATASIZE through its handler table runs the concrete handler. |
| `dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE_status` | [`ReturnDataHandlers.lean#L76`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/ReturnDataHandlers.lean#L76) | The RETURNDATASIZE table-dispatch result preserves the status field. |

### Handler table and supported-dispatch bridges

The handler wrapper layer connects opcode-specific handlers to `HandlerTable`,
raw-byte dispatch, and the supported interpreter loop. These are the reusable
#107 entry points for wiring verified opcode handlers into the interpreter.

| Theorem | Defined at | Meaning |
|---|---|---|
| `HandlerTable.dispatchOpcode?_eq_some_iff` | [`HandlerTable.lean#L124`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTable.lean#L124) | Characterizes successful opcode lookup in a handler table. |
| `HandlerTable.dispatchOpcode?_eq_none_iff` | [`HandlerTable.lean#L135`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTable.lean#L135) | Characterizes missing opcode lookup in a handler table. |
| `HandlerTable.dispatchOpcode_some_preserves_status` | [`HandlerTable.lean#L171`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTable.lean#L171) | Lifts a handler status-preservation proof through table dispatch. |
| `HandlerTable.dispatchOpcode_some_preserves_codeLenMatches` | [`HandlerTable.lean#L180`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTable.lean#L180) | Lifts handler `codeLenMatches` preservation through table dispatch. |
| `HandlerTable.orElse_eq_some_iff` | [`HandlerTableCompose.lean#L158`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTableCompose.lean#L158) | Characterizes successful lookup in composed handler tables. |
| `HandlerTable.orElse_eq_none_iff` | [`HandlerTableCompose.lean#L172`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTableCompose.lean#L172) | Characterizes missing lookup in composed handler tables. |
| `HandlerTable.dispatchByte_decoded_lookup` | [`HandlerTableByte.lean#L64`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTableByte.lean#L64) | Raw byte dispatch agrees with opcode dispatch when decoding and lookup succeed. |
| `HandlerTable.dispatchByte_decoded_lookup_preserves_codeLenMatches` | [`HandlerTableByte.lean#L106`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerTableByte.lean#L106) | Raw byte dispatch preserves `codeLenMatches` under decoded lookup. |
| `stepWithSupportedHandler_of_decode` | [`SupportedLoopBridge.lean#L31`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/SupportedLoopBridge.lean#L31) | The supported loop handler agrees with supported table dispatch after byte decoding. |
| `stepWithSupportedHandler_of_lookup` | [`SupportedLoopBridge.lean#L46`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/SupportedLoopBridge.lean#L46) | The supported loop handler agrees with supported table dispatch after table lookup. |

### Interpreter simulation bridges

The interpreter simulation layer relates the concrete handler/interpreter loop
to the executable-spec handler surface. These bridges are the reusable
entry-points for per-handler proofs and whole-loop conformance reasoning.

| Theorem | Defined at | Meaning |
|---|---|---|
| `InterpreterSimulation.stepWithHandler_matchesSpec` | [`InterpreterSimulation.lean#L50`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterSimulation.lean#L50) | One interpreter step with matching handlers agrees with the executable-spec step. |
| `InterpreterSimulation.loopFuel_matchesSpec` | [`InterpreterSimulation.lean#L79`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterSimulation.lean#L79) | Fuel-bounded interpreter execution agrees with the executable-spec loop. |
| `InterpreterTraceSimulation.loopTrace_matchesSpec` | [`InterpreterTraceSimulation.lean#L20`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterTraceSimulation.lean#L20) | Interpreter traces agree with executable-spec traces under a handler match. |
| `InterpreterTraceSimulation.loopFuelAndTrace_matchesSpec` | [`InterpreterTraceSimulation.lean#L56`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterTraceSimulation.lean#L56) | Joint fuel-loop and trace execution agree with the executable spec. |
| `InterpreterLoopSimulation.loopFuel_eq_of_loopResultsMatch` | [`InterpreterLoopSimulation.lean#L48`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterLoopSimulation.lean#L48) | `LoopResultsMatch` transports whole loop-fuel results. |
| `HandlerLoopSimulationBridge.loopFuel_table_matchesSpec_at` | [`HandlerLoopSimulationBridge.lean#L169`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerLoopSimulationBridge.lean#L169) | Handler-table dispatch agrees with the executable spec for a fixed initial state and fuel. |
| `HandlerLoopSimulationBridge.loopFuelAndTrace_table_matchesSpec_at` | [`HandlerLoopSimulationBridge.lean#L356`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerLoopSimulationBridge.lean#L356) | Handler-table fuel+trace execution agrees with the executable spec for a fixed initial state. |
| `HandlerLoopSimulationBridge.loopResultsMatch_table_matchesSpec` | [`HandlerLoopSimulationBridge.lean#L537`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerLoopSimulationBridge.lean#L537) | Bundled `LoopResultsMatch` entry point for handler-table/spec agreement. |
| `InterpreterLoopSimulation.loopFuel_status_eq_of_loopResultsMatch` | [`InterpreterLoopSimulation.lean#L55`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterLoopSimulation.lean#L55) | Projects final status equality out of a bundled `LoopResultsMatch`. |
| `InterpreterLoopSimulation.loopFuel_codeLenMatches_of_loopResultsMatch` | [`InterpreterLoopSimulation.lean#L125`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterLoopSimulation.lean#L125) | Transports `codeLenMatches` from the spec loop to the interpreter loop. |
| `InterpreterTraceSimulation.loopFuelAndTrace_matchesSpec_memory` | [`InterpreterTraceSimulation.lean#L129`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/InterpreterTraceSimulation.lean#L129) | Projects final memory equality from the fuel+trace simulation theorem. |
| `HandlerLoopSimulationBridge.loopFuel_table_matchesSpec_at_stack` | [`HandlerLoopSimulationBridge.lean#L209`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerLoopSimulationBridge.lean#L209) | Projects final stack equality from handler-table/spec fuel-loop agreement. |
| `HandlerLoopSimulationBridge.loopFuelAndTrace_table_matchesSpec_at_codeLenMatches` | [`HandlerLoopSimulationBridge.lean#L501`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/HandlerLoopSimulationBridge.lean#L501) | Transports `codeLenMatches` through handler-table fuel+trace agreement. |

## EvmWord arithmetic correctness

The pure-Lean correctness theorems that say each `EvmWord.<op>` matches the
expected mathematical semantics — these are what `evm_*_stack_spec_within`
ultimately reduces to in the post-condition.

| Theorem | Defined at | Meaning |
|---|---|---|
| `add_carry_chain_correct`  | [`EvmWordArith/Arithmetic.lean#L61`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/Arithmetic.lean#L61)  | 4-limb carry-chain adder = `EvmWord` addition mod 2^256. |
| `sub_borrow_chain_correct` | [`EvmWordArith/Arithmetic.lean#L241`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/Arithmetic.lean#L241) | 4-limb borrow-chain subtractor = `EvmWord` subtraction. |
| `mul_correct`              | [`EvmWordArith/MulCorrect.lean#L492`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/MulCorrect.lean#L492) | 4×4 limb mul (low 256 bits) = `EvmWord` multiplication. |
| `mul_correct_limb0` / `_limb1` / `_limb2` / `_limb3` | [`EvmWordArith/MulCorrect.lean#L84`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/MulCorrect.lean#L84) | Per-output-limb correctness lemmas feeding `mul_correct`. |
| `div_correct`              | [`EvmWordArith/DivCorrect.lean#L15`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L15) | `EvmWord.div a b` matches integer division (with EVM b=0 → 0 convention). |
| `mod_correct`              | [`EvmWordArith/DivCorrect.lean#L26`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L26) | `EvmWord.mod a b` matches integer remainder (with b=0 → 0). |
| `exp_correct`              | [`EvmWordArith/Exp.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/Exp.lean#L19) | `EvmWord.exp` matches `base ^ exponent` mod 2^256. |
| `lt_borrow_chain_correct`  | [`EvmWordArith/Comparison.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L19) | borrow-chain LT matches `EvmWord` unsigned `<`. |
| `slt_result_correct`       | [`EvmWordArith/Comparison.lean#L111`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L111) | sign-aware borrow-chain matches signed `<`. |
| `eq_xor_or_reduce_correct` | [`EvmWordArith/Eq.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/Eq.lean#L19) | xor-then-or-reduce equals `BEq` on `EvmWord`. |
| `iszero_or_reduce_correct` | [`EvmWordArith/IsZero.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/IsZero.lean#L19) | or-reduce of all four limbs equals `iszero`. |
| `byte_correct`             | [`EvmWordArith/ByteOps.lean#L133`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/ByteOps.lean#L133) | per-byte select matches the EVM `BYTE` opcode semantics. |
| `byte_extract_correct`     | [`EvmWordArith/ByteOps.lean#L68`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/ByteOps.lean#L68) | Selecting byte index `i < 32` from `x` returns the spec-level byte. |
| `addCarry_spec`            | [`EvmWordArith/AddMod.lean#L44`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/AddMod.lean#L44) | 257-bit identity: `a.toNat + b.toNat = (carry · 2^256) + truncated`, the algebraic shape downstream proofs use to bridge limb-level RISC-V add-with-carry to EVM word-level. |
| `addmod_correct`           | [`EvmWordArith/AddMod.lean#L71`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/AddMod.lean#L71) | `EvmWord.addmod a b N` matches `(a + b) mod N` at full 257-bit precision, with EVM `N=0 → 0` convention. |
| `sdiv_correct`             | [`EvmWordArith/SDiv.lean#L83`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/SDiv.lean#L83) | `EvmWord.sdiv a b` matches `Int.tdiv` of the signed interpretations; the two short-circuit cases (`b = 0`, signed-overflow `intMin / -1`) are handled by `sdiv_zero_right` and `sdiv_intMin_neg_one`. |
| `smod_correct`             | [`EvmWordArith/SMod.lean#L80`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/SMod.lean#L80) | `EvmWord.smod a b` matches `Int.tmod` of the signed interpretations (sign of result follows the dividend `a`); EVM `b = 0 → 0` short-circuit lives outside this theorem at the dispatcher. |
| `mulmod_correct`           | [`EvmWordArith/MulMod.lean#L40`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/MulMod.lean#L40) | `EvmWord.mulmod a b N` matches `(a * b) mod N` at full 512-bit precision, with EVM `N=0 → 0` convention. |

> _DivMod internal correctness._ The intermediate `div_correct_n{1,2,3,4}_no_shift`,
> `div_correct_normalized` / `mod_correct_normalized`, and `n4_max_*` /
> `mulsub_*_correct` lemmas in
> [`DivAccumulate.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/DivAccumulate.lean),
> [`DivN4DoubleAddback.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/DivN4DoubleAddback.lean),
> [`DivN4Overestimate.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/DivN4Overestimate.lean),
> and [`DivRemainderBound.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/EvmWordArith/DivRemainderBound.lean)
> are not indexed individually — they are private to the DivMod proof tree
> and consumers should use `div_correct` / `mod_correct` instead.

## EL / RLP

Pure (no RISC-V dependency) RLP encoder, decoder, and round-trip lemmas.
These are the executable-spec direction: `encode` is the canonical RLP
encoder, `decode` enforces canonical decoding, and `Properties.lean`
discharges round-trip facts via `native_decide` for byte-string lengths
covered so far.

### Encoder ([`EvmAsm/EL/RLP/Basic.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Basic.lean))

| Declaration | Defined at | Meaning |
|---|---|---|
| `Nat.toBytesBE` | [`Basic.lean:46`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Basic.lean#L46) | Big-endian byte representation of a `Nat`. |
| `Nat.fromBytesBE` | [`Basic.lean:53`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Basic.lean#L53) | Inverse of `toBytesBE` on lists of bytes. |
| `encodeBytes` | [`Basic.lean:60`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Basic.lean#L60) | Canonical RLP encoding of a single byte string. |
| `encode` | [`Basic.lean:87`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Basic.lean#L87) | Canonical RLP encoding of an `RLPItem` (string or list). |
| `encodeBytes_short_of_length_ne_one` | [`Basic.lean:74`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Basic.lean#L74) | Single-byte fast path doesn't apply when length ≠ 1. |

### Decoder ([`EvmAsm/EL/RLP/Decode.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Decode.lean))

| Declaration | Defined at | Meaning |
|---|---|---|
| `takeBytes` | [`Decode.lean:14`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Decode.lean#L14) | Splits a byte list at index `n`, returning `none` if too short. |
| `readLength` | [`Decode.lean:20`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Decode.lean#L20) | Reads a big-endian `n`-byte length prefix, enforcing canonical form. |
| `decodeAux` | [`Decode.lean:36`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Decode.lean#L36) | Fuel-driven canonical RLP decoder for a single item. |
| `decode` | [`Decode.lean:97`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Decode.lean#L97) | Top-level canonical RLP decode (calls `decodeAux` with `bs.length` fuel). |

### Round-trip and length lemmas ([`EvmAsm/EL/RLP/Properties.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Properties.lean))

| Theorem | Defined at | Meaning |
|---|---|---|
| `encode_nonempty` | [`Properties.lean:1841`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Properties.lean#L1841) | `encode` always produces a non-empty byte list. |
| `decode_encode_bytes_empty` | [`Properties.lean:1865`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Properties.lean#L1865) | `decode (encodeBytes [])` returns the empty string. |
| `decode_encode_bytes_single_small` | [`Properties.lean:1858`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Properties.lean#L1858) | Round trip for one byte `< 0x80` (single-byte fast path). |
| `decode_encode_bytes_single_large` | [`Properties.lean:1874`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/Properties.lean#L1874) | Round trip for one byte `≥ 0x80` (uses 0x81 prefix). |

`Properties.lean` also contains a long ladder of per-length
`encodeBytes_<n>tuple` and `decodeAux_<n>_byte_string` lemmas
(`native_decide`-backed) covering byte-string lengths 0..~75 used by
downstream RLP proofs.


### `classifyPrefix` view (`PrefixDecode.lean`)

| Theorem | Defined at | Meaning |
|---|---|---|
| `decode_cons_eq_classifyPrefix_match` | [`EL/RLP/PrefixDecode.lean#L136`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/PrefixDecode.lean#L136) | `decode (pfx :: rest)` matches the case-split implied by `classifyPrefix pfx`. |
| `decodeAux_cons_eq_classifyPrefix_match` | [`EL/RLP/PrefixDecode.lean#L93`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/PrefixDecode.lean#L93) | Same shape, expressed against `decodeAux fuel`. |
| `decodeAux_cons_singleByte_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L13`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/PrefixDecode.lean#L13) | Single-byte branch of the case split. |
| `decodeAux_cons_shortBytes_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L21`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/PrefixDecode.lean#L21) | Short-string branch (`0x81..0xb7`). |
| `decodeAux_cons_longBytes_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L36`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/PrefixDecode.lean#L36) | Long-string branch (`0xb8..0xbf`). |
| `decodeAux_cons_shortList_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L53`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/PrefixDecode.lean#L53) | Short-list branch (`0xc0..0xf7`). |
| `decodeAux_cons_longList_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L69`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/PrefixDecode.lean#L69) | Long-list branch (`0xf8..0xff`). |

### Rv64 prefix-classifier triples (`ProgramSpec.lean`)

| Theorem | Defined at | Meaning |
|---|---|---|
| `rlp_prefix_classify_singleByte_spec_within` | [`EL/RLP/ProgramSpec.lean#L29`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ProgramSpec.lean#L29) | Classifier returns `singleByte` when prefix `< 0x80`. |
| `rlp_prefix_classify_singleByte_of_classifyPrefix_spec_within` | [`EL/RLP/ProgramSpec.lean#L180`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ProgramSpec.lean#L180) | Classifier output matches `classifyPrefix pfx`. |
| `rlp_prefix_short_payload_len_spec_within` | [`EL/RLP/ProgramSpec.lean#L203`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ProgramSpec.lean#L203) | Decode the payload length of a short-form RLP item. |
| `rlp_prefix_long_header_bytes_spec_within` | [`EL/RLP/ProgramSpec.lean#L404`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ProgramSpec.lean#L404) | Number of header-byte slots consumed for a long-form RLP item. |

### Full-decode bridges (`FullDecode.lean`, `ListDecodeBridge.lean`, `LongFormDecodeBridge.lean`)

| Theorem | Defined at | Meaning |
|---|---|---|
| `decodeFully_eq_some_iff` | [`EL/RLP/FullDecode.lean#L20`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/FullDecode.lean#L20) | Top-level wrapper succeeds exactly when `decode` succeeds and consumes the whole input. |
| `decodeFully_eq_none_iff` | [`EL/RLP/FullDecode.lean#L81`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/FullDecode.lean#L81) | Complete-decode failure split: decoder failure or non-empty leftover. |
| `decodeListPayload_eq_some_iff` | [`EL/RLP/ListDecodeBridge.lean#L32`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ListDecodeBridge.lean#L32) | List payload decoding succeeds exactly when `decodeItems` consumes the payload. |
| `decodeAux_cons_shortList_eq_some_iff` | [`EL/RLP/ListDecodeBridge.lean#L140`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ListDecodeBridge.lean#L140) | Short-list branch success in terms of `decodeListPayload`. |
| `decodeAux_cons_longList_eq_some_iff` | [`EL/RLP/ListDecodeBridge.lean#L214`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ListDecodeBridge.lean#L214) | Long-list branch success in terms of the decoded length field and payload decode. |
| `decodeLengthField?_eq_some_iff` | [`EL/RLP/ReadLengthBridge.lean#L34`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/ReadLengthBridge.lean#L34) | Canonical long-form length field success criterion. |
| `decodeAux_long_bytes_lengthField` | [`EL/RLP/LongFormDecodeBridge.lean#L22`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/LongFormDecodeBridge.lean#L22) | Long byte-string branch via a decoded canonical length field. |
| `decodeAux_long_list_lengthField_success` | [`EL/RLP/LongFormDecodeBridge.lean#L175`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/EL/RLP/LongFormDecodeBridge.lean#L175) | Long-list branch success once the list payload decoder succeeds. |

### Rv64 RLP decoder phase triples (`EvmAsm/Rv64/RLP/`)

These are representative CPS triples for the RISC-V decoder pipeline in
GH #120. They are phase-level entry points; individual range, disjointness,
and postcondition-unfold lemmas stay local to their phase files.

| Theorem | Defined at | Meaning |
|---|---|---|
| `rlp_phase1_classifier_spec_class_within` | [`Rv64/RLP/Phase1.lean#L787`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase1.lean#L787) | Phase 1 cascade classifies the prefix byte into the same class as `classifyPrefix`. |
| `rlp_phase3_single_byte_spec_within` | [`Rv64/RLP/Phase3SingleByte.lean#L57`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase3SingleByte.lean#L57) | Single-byte item exit writes a one-byte result shape. |
| `rlp_phase3_short_string_spec_within` | [`Rv64/RLP/Phase3ShortString.lean#L73`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase3ShortString.lean#L73) | Short byte-string exit computes payload pointer and length. |
| `rlp_phase3_long_string_spec_within` | [`Rv64/RLP/Phase3LongString.lean#L83`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase3LongString.lean#L83) | Long byte-string exit extracts length-of-length metadata for Phase 2. |
| `rlp_phase3_short_list_spec_within` | [`Rv64/RLP/Phase3ShortList.lean#L37`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase3ShortList.lean#L37) | Short-list exit computes payload pointer and payload length. |
| `rlp_phase3_long_list_spec_within` | [`Rv64/RLP/Phase3LongList.lean#L37`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase3LongList.lean#L37) | Long-list exit extracts length-of-length metadata for Phase 2. |
| `rlp_phase2_long_loop_body_spec_within` | [`Rv64/RLP/Phase2LongLoopBody.lean#L120`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean#L120) | One loop body for big-endian long-form length accumulation. |
| `rlp_phase1_e3_0xB8_one_byte_length_spec_within` | [`Rv64/RLP/Phase1E3LongStringOne.lean#L44`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase1E3LongStringOne.lean#L44) | Composed Phase 1 → long-string Phase 3 → one-byte Phase 2 path for prefix `0xB8`. |
| `rlp_phase4_hint_len_spec_within` | [`Rv64/RLP/Phase4HintLen.lean#L32`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase4HintLen.lean#L32) | Legacy Phase 4 length query wrapper; this is expected to change under the host-I/O read_input migration. |
| `rlp_phase4_hint_read_whole_one_word_spec_within` | [`Rv64/RLP/Phase4HintRead.lean#L95`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/RLP/Phase4HintRead.lean#L95) | Legacy one-word input streaming wrapper; also slated for read_input migration. |

## Rv64 infrastructure

Generic RISC-V instruction specs and the LP64-aligned calling convention
that EVM opcode handlers and EL routines call into.

### Byte / halfword / word memory specs

Memory-access specs at byte (8-bit), halfword (16-bit), and word (32-bit)
granularity, used by the byte-addressed EVM memory model and the RLP
byte writers. All triples are CPS-style and step-bounded.

| Theorem | Defined at | Meaning |
|---|---|---|
| `byteOffset_lt_8` | [`ByteOps.lean:18`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/ByteOps.lean#L18) | The byte index inside a dword is always `< 8`. |
| `alignToDword_byteOffset_zero` | [`ByteOps.lean:24`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/ByteOps.lean#L24) | `byteOffset (alignToDword addr) = 0`. |
| `alignToDword_idempotent` | [`ByteOps.lean:30`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/ByteOps.lean#L30) | `alignToDword` is idempotent. |
| `alignToDword_add_byteOffset` | [`ByteOps.lean:36`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/ByteOps.lean#L36) | `alignToDword addr + byteOffset addr = addr`. |
| `generic_lbu_spec_within` | [`ByteOps.lean:96`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/ByteOps.lean#L96) | LBU loads one byte zero-extended; the dword at `alignToDword addr` is unchanged. |
| `generic_lb_spec_within` | [`ByteOps.lean:141`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/ByteOps.lean#L141) | LB loads one byte sign-extended. |
| `generic_sb_spec_within` | [`ByteOps.lean:185`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/ByteOps.lean#L185) | SB stores one byte; only the targeted byte slot of the underlying dword is modified. |
| `generic_lhu_spec_within` | [`HalfwordOps.lean:62`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/HalfwordOps.lean#L62) | LHU loads a 16-bit halfword zero-extended. |
| `generic_lh_spec_within` | [`HalfwordOps.lean:106`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/HalfwordOps.lean#L106) | LH loads a 16-bit halfword sign-extended. |
| `generic_sh_spec_within` | [`HalfwordOps.lean:150`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/HalfwordOps.lean#L150) | SH stores a 16-bit halfword. |
| `generic_lwu_spec_within` | [`WordOps.lean:47`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/WordOps.lean#L47) | LWU loads a 32-bit word zero-extended. |
| `generic_lw_spec_within` | [`WordOps.lean:91`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/WordOps.lean#L91) | LW loads a 32-bit word sign-extended. |
| `generic_sw_spec_within` | [`WordOps.lean:135`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/WordOps.lean#L135) | SW stores a 32-bit word. |

### `runBlock` registry highlights ([`EvmAsm/Rv64/SyscallSpecs.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/SyscallSpecs.lean))

The `@[spec_gen_rv64]` registry registers per-instruction specs that
`runBlock` consumes during auto-mode block elaboration. A representative
sample of the LD/SD entry points (the rest follow the same pattern;
the file lists ~50 ALU, branch, and memory specs):

| Theorem | Defined at | Meaning |
|---|---|---|
| `ld_spec_gen_within` | [`SyscallSpecs.lean:28`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/SyscallSpecs.lean#L28) | LD loads a 64-bit doubleword from `[rs1+offset]`. |
| `sd_spec_gen_within` | [`SyscallSpecs.lean:35`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/SyscallSpecs.lean#L35) | SD stores a 64-bit doubleword to `[rs1+offset]`. |
| `sd_spec_gen_own_within` | [`SyscallSpecs.lean:41`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Rv64/SyscallSpecs.lean#L41) | SD-own variant for `rs1 = rs2`. |

### Calling convention ([`EvmAsm/Evm64/CallingConvention.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean))

LP64-aligned register roles (`x1` ra, `x2` sp, `x5–x7` t0–t2, `x10–x11`
a0–a1, `x12` a2/EVM-sp). Reusable program snippets and their proved
specs.

| Snippet / Theorem | Defined at | Meaning |
|---|---|---|
| `cc_ret` | [`CallingConvention.lean:42`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L42) | Return: `JALR x0 x1 0`. |
| `cc_prologue` | [`CallingConvention.lean:46`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L46) | Non-leaf prologue: allocate 16-byte frame, save `ra`. |
| `cc_epilogue` | [`CallingConvention.lean:51`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L51) | Non-leaf epilogue: restore `ra`, deallocate, return. |
| `callNear_spec_within` | [`CallingConvention.lean:65`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L65) | `JAL x1 offset` jumps to `base + offset` and saves the return address in `x1`. |
| `callFar_spec_within` | [`CallingConvention.lean:75`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L75) | `JALR x1 target 0` indirect call: jumps to `target` and saves the return address. |
| `ret_spec_within` | [`CallingConvention.lean:84`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L84) | `JALR x0 x1 0` returns to the caller (jumps to `ra`). |
| `ret_spec_within'` | [`CallingConvention.lean:92`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L92) | Variant of `ret_spec_within` with a different post-shape. |
| `cc_prologue_spec_within` | [`CallingConvention.lean:109`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L109) | Block spec for the 2-instruction prologue: `sp` decremented by 16, `ra` saved at `sp+8`. |
| `cc_epilogue_spec_within` | [`CallingConvention.lean:129`](https://github.com/Verified-zkEVM/evm-asm/blob/b6f749defdd3fd8ca7dd581e9c5ec2b988b6ddc1/EvmAsm/Evm64/CallingConvention.lean#L129) | Block spec for the 3-instruction epilogue: `ra` restored, `sp` incremented by 16, jumps to saved `ra`. |


## Maintenance

- See parent backlog: `evm-asm-prwe` / GH issue tracking forthcoming.
- Trigger: refresh when a `#61`-class umbrella closes or quarterly,
  whichever comes first.

### Refresh procedure (5 steps)

1. **Survey the spec surface.** Grep for the canonical entry-point names so
   nothing has been added or renamed since the last refresh:

   ```bash
   rg -n '@\[stack_spec_' EvmAsm/
   rg -n 'theorem evm_[a-z_]*_stack_spec' EvmAsm/
   rg -n 'theorem EvmWord\.[a-z_]*_correct' EvmAsm/
   ```

   Add an entry to the appropriate section for any name not already listed;
   delete entries whose underlying theorem is gone.

2. **Capture `file:line` for every entry.** For each theorem name, locate
   its current declaration site:

   ```bash
   grep -n '<theorem-name>' EvmAsm/<path>.lean
   ```

   Record the `path:line` pair — both the alias line and (if separate) the
   underlying proof-bearing theorem line.

3. **Mint commit-pinned permalinks.** Capture the current upstream sha and
   build URLs against it:

   ```bash
   SHA=$(git rev-parse origin/main)
   gh browse <path>:<line> --commit "$SHA" --no-browser
   # or directly:
   echo "https://github.com/Verified-zkEVM/evm-asm/blob/$SHA/<path>#L<line>"
   ```

   Replace each existing permalink in the table cells with the freshly
   minted one.

4. **Update the top-of-page pin.** Replace the `Permalinks pinned to commit
   <sha> on <date>` blockquote near the top with the new sha and today's
   date.

5. **Verify with `lake build`.** Run `lake build` from the repo root to
   confirm every referenced declaration still elaborates under the pinned
   sha. Any rename or relocation discovered here loops back to step 1.
