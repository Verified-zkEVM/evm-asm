# Correspondence: extracted Sail RISC-V model ↔ the zkVM RISC-V standard

**Status:** Hand-authored from verified facts (2026-06-24); intended to become a
CI-regenerated artifact (see [`sail-zkvm-integration-design.md`](sail-zkvm-integration-design.md) §6).
**Audience:** Ethereum client developers and auditors — *no Lean expertise
required to read this page.*
**Sources of truth:** the zkVM standard
[`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)
(`standards/riscv-target/target.md` + siblings); the official Sail model
[`riscv/sail-riscv`](https://github.com/riscv/sail-riscv); the vendored, scoped
Lean export consumed at `vendor/sail-riscv-zkvm-lean/` (lib `Out`); and the deep review in
[`sail-zkvm-model-review.md`](sail-zkvm-model-review.md).

---

## How to read this document

The zkVM RISC-V standard defines a target triple. This page maps **every
normative clause of that standard** to the concrete element of the
Sail-extracted RISC-V model that realizes it, and records the current status in
`evm-asm`. The intent: an auditor reads this one page top to bottom, follows
each link, and can answer *"does this project's RISC-V semantics correspond to
the exact zkVM standard, and where are the gaps?"* without grepping the
codebase.

### Status legend

| Symbol | Meaning |
|---|---|
| ✅ **proven** | A kernel-checked theorem in `evm-asm` ties our semantics to the Sail model for this item. |
| 🟦 **config** | Satisfied by an import-configuration choice (a Sail `config` key / module selection), not a theorem. |
| 🟡 **modeled, equiv pending / by-design divergence** | Present in our model but *not* tied to Sail by a `RETIRE_SUCCESS`-shaped theorem — either a known semantic divergence (e.g. ECALL) or pending work. |
| 🔴 **gap** | Required by the standard but **not present** in our model today. |
| ⚪ **planned gate** | The drift-detecting CI check named here is proposed, not yet implemented. |

> **Honesty note.** Most rows below are ✅ at the *instruction-execute* level
> (the 51 `*_sail_equiv` lemmas) but the supporting machinery — scoped import,
> the consolidated simulation theorem, decode tie, and the drift gates — is
> **planned, not yet built**. This page states current reality, not aspiration.

---

## 1. The target triple, decomposed

`riscv64im_zicclsm-unknown-none-elf` (`standards/riscv-target/target.md`):

| Clause | Requirement | Corresponds to (Sail) | Status |
|---|---|---|---|
| **Base ISA** | RV64I (64-bit integer) | modules `core` + `I` (`I_types`,`I_insts`); `config base.xlen = 64` | ✅ instr-level / 🟦 config |
| **M extension** | mul/div | modules `M` (`M_types`,`M_insts`); `config extensions.M.supported = true` | ✅ instr-level / 🟦 config |
| **Zicclsm** | misaligned load/store to main memory | `config extensions.Zicclsm.supported = true`; semantics in `sys/vmem_utils.sail::split_misaligned`; `memory.misaligned.exceptions.load_store = None` | 🟦 config (semantics already in model) |
| **XLEN** | 64 | `type xlen = config base.xlen` (64) | 🟦 config |
| **Endianness** | little-endian | model is LE; `config` memory layout | 🟦 config |
| **Privilege** | Machine (M) mode only | `config extensions.{S,U}.supported = false` (must be set together — `validate_config.sail`) | 🟦 config |
| **Excluded: C** | no compressed | module `C`/`Zca`/`Zcb` **not imported** | 🟦 config / ⚪ scope gate |
| **Excluded: F/D** | soft-float ABI | modules `FD`/`Zfh`/… **not imported** | 🟦 config / ⚪ scope gate |
| **No syscall/env** | — | ECALL is the *host interface*, trapped, not a Linux syscall | 🟡 divergence (see §3, §4) |
| **Memory** | flat, no MMU, no paging | `satp` Bare mode; single RAM `config memory.regions` | 🟦 config |
| **Linking / ABI** | static ELF, LP64 soft-float | property of codegen + linker script, not the ISA model | out of model scope |

**Sibling standards** that also constrain semantics:

| Standard | Corresponds to | Status |
|---|---|---|
| `instruction-address-misaligned-exception-semantics` | Sail fetch / `F_Error` path; toy model requires aligned PC | 🟡 cross-check pending |
| `standard-termination-semantics` | ECALL/COMMIT/halt handling (`SyscallSpecs`) | 🟡 modeled, see §4 |
| `memory-layout-restrictions`, `memory-safety-guard-regions` | `config memory.regions`; guest static layout | 🟦 config |
| `io-interface`, `c-interface-accelerators` | ECALL host ABI (`docs/zkvm-host-io-interface.md`, `docs/zkvm-accelerators-interface.md`) | 🟡 modeled |

---

## 2. Instruction inventory — RV64IM, instruction by instruction

This is the heart of the correspondence. Each standard instruction maps to a
Sail `instruction` AST constructor (executed by `execute_*` in
`vendor/sail-riscv-zkvm-lean/.../InstsEnd.lean`) and, where present, to the `evm-asm` theorem
proving our model agrees with Sail.

### 2.1 RV64I — integer computation (register-register)

| Instr | Sail constructor | `evm-asm` correspondence | Status |
|---|---|---|---|
| ADD SUB SLL SLT SLTU XOR SRL SRA OR AND | `RTYPE(_,_,_,rop.*)` | `add/sub/sll/slt/sltu/xor/srl/sra/or/and_sail_equiv` (`ALUProofs.lean`) | ✅ |

### 2.2 RV64I — integer computation (register-immediate)

| Instr | Sail constructor | `evm-asm` correspondence | Status |
|---|---|---|---|
| ADDI SLTI SLTIU XORI ORI ANDI | `ITYPE(_,_,_,iop.*)` | `addi/slti/sltiu/xori/ori/andi_sail_equiv` (`ImmProofs.lean`) | ✅ |
| SLLI SRLI SRAI | `SHIFTIOP(_,_,_,sop.*)` | `slli/srli/srai_sail_equiv` (`ShiftProofs.lean`) | ✅ |
| LUI AUIPC | `UTYPE(_,_,uop.*)` | `lui_sail_equiv`, `auipc_sail_equiv` (`ALUProofs.lean`) | ✅ |

### 2.3 RV64I — control transfer

| Instr | Sail constructor | `evm-asm` correspondence | Status |
|---|---|---|---|
| BEQ BNE BLT BGE BLTU BGEU | `BTYPE(_,_,_,bop.*)` | `beq/bne/blt/bge/bltu/bgeu_sail_equiv` (`BranchProofs.lean`) | ✅ |
| JAL | `JAL(_,_)` | `jal_sail_equiv` (`BranchProofs.lean`) | ✅ |
| JALR | `JALR(_,_,_)` | `jalr_sail_equiv` (`BranchProofs.lean`) | ✅ |

### 2.4 RV64I — loads and stores

| Instr | Sail constructor | `evm-asm` correspondence | Status |
|---|---|---|---|
| LB LH LW LD LBU LHU LWU | `LOAD(_,_,_,unsigned,width)` | `lb/lh/lw/ld/lbu/lhu/lwu_sail_equiv` (`MemProofs.lean`) | ✅ |
| SB SH SW SD | `STORE(_,_,_,width)` | `sb/sh/sw/sd_sail_equiv` (`MemProofs.lean`) | ✅ |

### 2.5 RV64I — system / fence

| Instr | Sail constructor | `evm-asm` correspondence | Status |
|---|---|---|---|
| ECALL | `ECALL ()` | mapped in `toSailInstr?`; **no `ecall_sail_equiv`** — Sail traps to M-mode, our model uses a host-call abstraction (§4) | 🟡 by-design divergence |
| EBREAK | `EBREAK ()` | mapped; no equiv lemma (Sail traps; toy model treats as no-op) | 🟡 divergence |
| FENCE | `FENCE(…)` | mapped; no equiv lemma (near-no-op both sides) | 🟡 equiv pending |

### 2.6 M extension (RV64)

| Instr | Sail constructor | `evm-asm` correspondence | Status |
|---|---|---|---|
| MUL MULH MULHSU MULHU | `MUL(_,_,_,mul_op)` | `mul/mulh/mulhsu/mulhu_sail_equiv` (`ALUProofs.lean`/`MExtProofs.lean`) | ✅ |
| DIV DIVU | `DIV(_,_,_,unsigned)` | `div_sail_equiv`, `divu_sail_equiv` (`MExtProofs.lean`) | ✅ |
| REM REMU | `REM(_,_,_,unsigned)` | `rem_sail_equiv`, `remu_sail_equiv` (`MExtProofs.lean`) | ✅ |

### 2.7 🔴 RV64 word-ops — **the coverage gap**

The standard's RV64IM includes 32-bit "word" operations (`.W` suffix), which
sign-extend a 32-bit result to 64 bits. Our model has **only `ADDIW`** of this
family; the rest are **absent from `EvmAsm.Rv64.Instr`**:

| Standard instr | Sail constructor | `evm-asm` | Status |
|---|---|---|---|
| ADDIW | `ADDIW(_,_,_)` | `addiw_sail_equiv` (`ALUProofs.lean`) | ✅ |
| SLLIW SRLIW SRAIW | `SHIFTIWOP(…)` | — | 🔴 not modeled |
| ADDW SUBW SLLW SRLW SRAW | `RTYPEW(…)` | — | 🔴 not modeled |
| MULW | `MUL` (W width) / `MULW` clause | — | 🔴 not modeled |
| DIVW DIVUW REMW REMUW | `DIV`/`REM` (W) clauses | — | 🔴 not modeled |

**What this means for compliance.** The standard requires the *platform* to
implement full RV64IM. Our verified guest does not currently *use* the missing
`.W` ops, so the proofs are sound for the code we actually emit — but our RISC-V
**model does not cover all of RV64IM**, so "evm-asm's semantics = the zkVM ISA"
is **not yet true for the word-op family**. Resolution options:
- **(i)** add the `.W` constructors + `*_sail_equiv` lemmas (closes the gap), or
- **(ii)** state an *audited restriction*: "the verified guest emits no `.W`
  instructions," enforced by a codegen scan (a `check-no-word-ops.sh` gate).

This gap is exactly the kind of thing the proposed `check-isa-coverage.sh` gate
(§3) would surface automatically against the standard's instruction list.

### 2.8 Pseudo-instructions (not part of the ISA)

`MV`, `LI`, `NOP` are `evm-asm` conveniences that re-encode real instructions
(`ADDI rd rs 0`, `LUI`/`ADDI`/`SLLI` sequences, `ADDI x0 x0 0`). They are
**intentionally not mapped** to Sail (`mv_sail_equiv`/`nop_sail_equiv` exist as
sanity ties; `LI` desugars to mapped instructions). Surface code desugars these
before bridging.

### Coverage summary

- **Proven against Sail (✅):** 51 instruction forms — all of RV64I integer
  compute / control / load-store, plus the 8 M-extension XLEN ops.
- **Modeled, equiv pending / divergent (🟡):** ECALL, EBREAK, FENCE.
- **Gap vs. RV64IM (🔴):** 12 word-ops (SLLIW SRLIW SRAIW ADDW SUBW SLLW SRLW
  SRAW MULW DIVW DIVUW REMW REMUW).

---

## 3. Drift gates (how "evident if something breaks" is enforced)

All ⚪ planned (per design-doc §6.2); each seeded green on the current tree.

| Gate | Guards | Detects |
|---|---|---|
| `check-sail-pin.sh` | the pinned Sail / sail-riscv / lean-sail commits + module list + config hash (`PROVENANCE.toml`) | dependency drift, the moving-`rev` problem |
| `check-isa-scope.sh` | `toSailInstr?` / decode tie reference **only** in-target `instruction` constructors | accidental import of C/F/D/V/CSR surface |
| `check-isa-coverage.sh` | our covered-instruction set **equals** the standard's RV64IM list | regressions *and* the §2.7 word-op gap |
| `check-sail-config.sh` | the import config matches the §1 keys (xlen=64, M on, S/U off, Zicclsm on, misaligned≠AccessFault) | silent config drift away from the target |
| differential-test CI | generated *executable* Lean model vs. Sail C sim / `riscv-tests` | unfaithful backend output (§4) |

---

## 4. Trust boundary (what is assumed, not proven)

Restated from design-doc §7 so this page stands alone:

1. **Sail faithfully encodes RISC-V.** The Sail model is the accepted reference;
   we do not prove Sail against silicon.
2. **🔴 The Sail→Lean backend is faithful — headline assumption.** It is
   *experimental* and carries no soundness claim (review §1). It fails loud
   (`failwith`) rather than mistranslating silently. **Mitigation:**
   differential-test the generated executable model against the Sail C
   reference on the RV64IM subset.
3. **ECALL / termination is a deliberate divergence.** Sail traps environment
   calls to M-mode; `evm-asm` interprets ECALL as the zkVM **host interface**
   (input/output/halt/accelerators) per the `io-interface` and
   `standard-termination-semantics` standards. This is correct *for a zkVM
   guest* but means ECALL is **not** tied to Sail by a `RETIRE_SUCCESS`
   theorem — it is governed by the host-ABI specs instead.
4. **Configuration is set correctly** (§1 keys) — a config-review item.
5. **Trusted axiom base** unchanged: the 3 classical axioms; no
   `native_decide`/`bv_decide` (CI-gated). *Watch:* confirm the generated
   decoder is `bv_decide`-free (`match_bv` fallback, review §5.6).

---

## 5. One-line bottom line for an auditor

> *Today:* `evm-asm`'s RISC-V semantics are tied to the official Sail model by 51
> kernel-checked per-instruction theorems covering all of RV64I + the
> M-extension XLEN ops; ECALL is a deliberate host-interface divergence; the
> RV64 word-op family is a known coverage gap; and the tie rests on an
> experimental Sail→Lean backend whose output is not yet differential-tested.
> *Planned* (design doc P0–P5b): a pinned/scoped import of exactly the
> `riscv64im_zicclsm` modules, one consolidated simulation theorem, a decode
> tie, differential testing of the backend output, and the drift gates above.
</content>
