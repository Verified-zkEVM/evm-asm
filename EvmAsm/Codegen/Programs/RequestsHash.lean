/-
  EvmAsm.Codegen.Programs.RequestsHash

  RISC-V helper for the EIP-7685 execution header `requests_hash`:
  `sha256(concat(sha256(type_byte || request_payload) for non-empty request
  kinds in ascending type order))`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def executionRequestsHash_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LI .x5 (20 : Word),
    .BLTU .x9 .x5 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 68)),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.execution_requests_hash + 76)),
    .MV .x19 .x10,
    .ADDI .x10 .x8 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.execution_requests_hash + 88)),
    .MV .x20 .x10,
    .ADDI .x10 .x8 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.execution_requests_hash + 100)),
    .MV .x21 .x10,
    .ADDI .x10 .x8 (12 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.execution_requests_hash + 112)),
    .MV .x22 .x10,
    .ADDI .x10 .x8 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.execution_requests_hash + 124)),
    .MV .x23 .x10,
    .LI .x5 (20 : Word),
    .BNE .x19 .x5 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 136)),
    .BLTU .x20 .x19 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 140)),
    .BLTU .x21 .x20 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 144)),
    .BLTU .x22 .x21 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 148)),
    .BLTU .x23 .x22 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 152)),
    .BLTU .x9 .x23 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 156)),
    .SUB .x5 .x20 .x19,
    .LI .x6 (192 : Word),
    .REMU .x7 .x5 .x6,
    .BNE .x7 .x0 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 172)),
    .DIVU .x7 .x5 .x6,
    .LUI .x28 (2 : BitVec 20),
    .BLTU .x28 .x7 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 184)),
    .SUB .x5 .x21 .x20,
    .LI .x6 (76 : Word),
    .REMU .x7 .x5 .x6,
    .BNE .x7 .x0 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 200)),
    .DIVU .x7 .x5 .x6,
    .LI .x28 (16 : Word),
    .BLTU .x28 .x7 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 212)),
    .SUB .x5 .x22 .x21,
    .LI .x6 (116 : Word),
    .REMU .x7 .x5 .x6,
    .BNE .x7 .x0 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 228)),
    .DIVU .x7 .x5 .x6,
    .LI .x28 (2 : Word),
    .BLTU .x28 .x7 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 240)),
    .SUB .x5 .x23 .x22,
    .LI .x6 (184 : Word),
    .REMU .x7 .x5 .x6,
    .BNE .x7 .x0 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 256)),
    .DIVU .x7 .x5 .x6,
    .LI .x28 (64 : Word),
    .BLTU .x28 .x7 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 268)),
    .SUB .x5 .x9 .x23,
    .LI .x6 (68 : Word),
    .REMU .x7 .x5 .x6,
    .BNE .x7 .x0 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 284)),
    .DIVU .x7 .x5 .x6,
    .LI .x28 (16 : Word),
    .BLTU .x28 .x7 (brOff (GuestAddrs.execution_requests_hash + 480) (GuestAddrs.execution_requests_hash + 296)),
    .AUIPC .x24 (laHi GuestAddrs.erh_digests (GuestAddrs.execution_requests_hash + 300)),
    .ADDI .x24 .x24 (laLo GuestAddrs.erh_digests (GuestAddrs.execution_requests_hash + 300)),
    .LI .x25 (0 : Word),
    .SUB .x26 .x20 .x19,
    .BEQ .x26 .x0 (24 : BitVec 13),
    .ADD .x13 .x8 .x19,
    .LI .x14 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.erh_hash_one (GuestAddrs.execution_requests_hash + 328)),
    .ADDI .x24 .x24 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x26 .x21 .x20,
    .BEQ .x26 .x0 (24 : BitVec 13),
    .ADD .x13 .x8 .x20,
    .LI .x14 (1 : Word),
    .JAL .x1 (jalOff GuestAddrs.erh_hash_one (GuestAddrs.execution_requests_hash + 356)),
    .ADDI .x24 .x24 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x26 .x22 .x21,
    .BEQ .x26 .x0 (24 : BitVec 13),
    .ADD .x13 .x8 .x21,
    .LI .x14 (2 : Word),
    .JAL .x1 (jalOff GuestAddrs.erh_hash_one (GuestAddrs.execution_requests_hash + 384)),
    .ADDI .x24 .x24 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x26 .x23 .x22,
    .BEQ .x26 .x0 (24 : BitVec 13),
    .ADD .x13 .x8 .x22,
    .LI .x14 (3 : Word),
    .JAL .x1 (jalOff GuestAddrs.erh_hash_one (GuestAddrs.execution_requests_hash + 412)),
    .ADDI .x24 .x24 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x26 .x9 .x23,
    .BEQ .x26 .x0 (24 : BitVec 13),
    .ADD .x13 .x8 .x23,
    .LI .x14 (4 : Word),
    .JAL .x1 (jalOff GuestAddrs.erh_hash_one (GuestAddrs.execution_requests_hash + 440)),
    .ADDI .x24 .x24 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.erh_digests (GuestAddrs.execution_requests_hash + 452)),
    .ADDI .x10 .x10 (laLo GuestAddrs.erh_digests (GuestAddrs.execution_requests_hash + 452)),
    .SLLI .x11 .x25 (5 : BitVec 6),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.execution_requests_hash + 468)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `executionRequestsHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def executionRequestsHash_relocs : RelocTable :=
  [ (19, .jal .x1 "bgv_u32le"),
    (22, .jal .x1 "bgv_u32le"),
    (25, .jal .x1 "bgv_u32le"),
    (28, .jal .x1 "bgv_u32le"),
    (31, .jal .x1 "bgv_u32le"),
    (75, .la .x24 "erh_digests"),
    (82, .jal .x1 "erh_hash_one"),
    (89, .jal .x1 "erh_hash_one"),
    (96, .jal .x1 "erh_hash_one"),
    (103, .jal .x1 "erh_hash_one"),
    (110, .jal .x1 "erh_hash_one"),
    (113, .la .x10 "erh_digests"),
    (117, .jal .x1 "zkvm_sha256") ]

def executionRequestsHashFunction : String :=
  "execution_requests_hash:\n" ++ emitProgramR executionRequestsHash_prog executionRequestsHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `executionRequestsHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem executionRequestsHashFunction_eq_prog :
    executionRequestsHashFunction = "execution_requests_hash:\n" ++ emitProgramR executionRequestsHash_prog executionRequestsHash_relocs := rfl

#guard executionRequestsHashFunction.startsWith "execution_requests_hash:\n"
/-- `erh_hash_one` — `sha256(type_byte ‖ body)` into `*s8`.

    ⚠️ **Split out of `executionRequestsHashFunction` rather than left inline
    (#11578), and the reason is mechanical, not stylistic.** A def carrying two
    non-`.L` labels is a *multi-entry bundle*: `emitProgram` strips internal
    labels and turns branches into PC-relative offsets, which is safe for `.L`
    locals but silently unlinks a secondary symbol that another file might `jal`.
    `scripts/asm_to_program.py:492-495` refuses such defs on exactly that ground,
    so `execution_requests_hash` had **no `Program`** and no `cpsTripleWithin`
    was statable for it.

    The refusal is conservative and here it is a false positive — `erh_hash_one`
    is referenced only by the five local `jal`s in `execution_requests_hash` and
    by nothing else in the tree. But the fix is not to weaken the rule: it is to
    make each half single-entry, which is also what the linker already thinks
    (`symbol-addresses.tsv:144` gives `erh_hash_one` its own address). The five
    call sites become ordinary cross-function relocs.

    ⚠️ **This is NOT a standard-ABI function.** It reads `s10` (body length) and
    `s8` (digest destination) out of `execution_requests_hash`'s live frame, so
    it is callable only from there. Splitting the *text* does not make it
    independent, and a triple over it must carry those registers as inputs. -/
def erhHashOne_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8)),
    .ADDI .x5 .x5 (laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8)),
    .SB .x5 .x14 (0 : BitVec 12),
    .ADDI .x6 .x5 (1 : BitVec 12),
    .MV .x7 .x13,
    .MV .x28 .x26,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60)),
    .ADDI .x10 .x10 (laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60)),
    .ADDI .x11 .x26 (1 : BitVec 12),
    .MV .x12 .x24,
    .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `erhHashOne_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def erhHashOne_relocs : RelocTable :=
  [ (2, .la .x5 "erh_blob"),
    (15, .la .x10 "erh_blob"),
    (19, .jal .x1 "zkvm_sha256") ]

def erhHashOneFunction : String :=
  "erh_hash_one:\n" ++ emitProgramR erhHashOne_prog erhHashOne_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `erhHashOne_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem erhHashOneFunction_eq_prog :
    erhHashOneFunction = "erh_hash_one:\n" ++ emitProgramR erhHashOne_prog erhHashOne_relocs := rfl

#guard erhHashOneFunction.startsWith "erh_hash_one:\n"
/-- The two halves, concatenated exactly as the single def used to read.

    ⚠️ **The `"\n"` is load-bearing and is the one thing the per-function gate
    cannot see.** `emitProgramR` emits **no trailing newline**, so both halves
    now end mid-line; without the separator this renders `…  ret` immediately
    followed by `erh_hash_one:` on the same line, and the aggregate stops
    assembling while every per-function check stays green — `check-asm-to-program`
    assembles each converted def in isolation and never the concatenation.

    (Before conversion the halves were plain string literals and
    `executionRequestsHashFunction` ended `"  ret\n"`, so the seam needed nothing.
    That is why this comment exists: the requirement appeared *because of* the
    conversion, silently.)

    Every call site uses this rather than the halves, so a future edit to one
    half cannot reach the image without the other. Verified by assembling the
    aggregate by hand, not by inference — see the PR for #11578. -/
def executionRequestsHashFunctions : String :=
  executionRequestsHashFunction ++ "\n" ++ erhHashOneFunction

def executionRequestsHashDataSection : String :=
  ".balign 32\n" ++
  "erh_digests:\n  .zero 160\n" ++
  ".balign 32\n" ++
  "erh_requests_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "erh_blob:\n  .zero 1572865\n"

def executionRequestsHashShaDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".section .bss, \"aw\", @nobits\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n  .zero 64\n" ++
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".section .bss, \"aw\", @nobits\n"

end EvmAsm.Codegen
