/-
  EvmAsm.Codegen.Programs.CreateDescend

  bmvmx/.61.8a: `create2_descend` — the CREATE2 (0xf5) handler logic over the
  existing inline init-code machinery (CreateRuntime.lean). CREATE2 needs no nonce
  (address = keccak(0xff‖sender‖salt‖keccak(initcode))[12:]), so it is the cleanest
  first slice of the CREATE family.

  Model (NOT a call_frame_descend): the handler stages the init code + runs the
  bounded mini-interpreter (`create_execute_initcode_frame`), then pushes the new
  address on success or 0 on failure. It reads the dispatcher registers directly
  (x12 = stack top, grows down; x13 = mem base; x20 = env base) and returns the new
  stack top in a0, so a 0xf5 handler can `jal create2_descend; mv x12, a0`.

  CREATE2 stack (x12, top first): value@0, offset@32, length@64, salt@96. Pops 4
  words, pushes 1 → new top = x12 + 96. Byte orders: the salt stack word is EVM-stack
  LE and is reversed to big-endian for the preimage; the 20-byte big-endian result
  address is reversed back to an LE stack word for the push.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## create2_descend
    Reads x12 (stack top) / x13 (mem base) / x20 (env base). Returns a0 = new stack
    top (x12 + 96). On `create_child_status == 2` (deployed) the new address is pushed;
    otherwise 0 is pushed. Reuses create_sender_be/create_salt_be/create_init_offset/
    create_init_size/create_address_be + address_compute_create2 + the staging/exec
    helpers. Preserves nothing the caller needs except the documented a0. -/
def create2Descend_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .MV .x18 .x20,
    .LD .x5 .x8 (32 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.create_init_offset 2147483684),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_init_offset 2147483684),
    .SD .x6 .x5 (0 : BitVec 12),
    .LD .x5 .x8 (64 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.create_init_size 2147483700),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_init_size 2147483700),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.create_sender_be 2147483712),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_sender_be 2147483712),
    .LD .x7 .x18 (0 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .LD .x7 .x18 (8 : BitVec 12),
    .SD .x6 .x7 (8 : BitVec 12),
    .LD .x7 .x18 (16 : BitVec 12),
    .SD .x6 .x7 (16 : BitVec 12),
    .LD .x7 .x18 (24 : BitVec 12),
    .SD .x6 .x7 (24 : BitVec 12),
    .ADDI .x7 .x8 (127 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.create_salt_be 2147483756),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_salt_be 2147483756),
    .LI .x5 (32 : Word),
    .BEQ .x5 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.create_sender_be 2147483796),
    .ADDI .x10 .x10 (laLo GuestAddrs.create_sender_be 2147483796),
    .AUIPC .x11 (laHi GuestAddrs.create_salt_be 2147483804),
    .ADDI .x11 .x11 (laLo GuestAddrs.create_salt_be 2147483804),
    .AUIPC .x5 (laHi GuestAddrs.create_init_offset 2147483812),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_init_offset 2147483812),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x12 .x9 .x5,
    .AUIPC .x5 (laHi GuestAddrs.create_init_size 2147483828),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_init_size 2147483828),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.create_address_be 2147483840),
    .ADDI .x14 .x14 (laLo GuestAddrs.create_address_be 2147483840),
    .JAL .x1 (jalOff GuestAddrs.address_compute_create2 2147483848),
    .MV .x10 .x9,
    .MV .x11 .x8,
    .LI .x12 (1 : Word),
    .JAL .x1 (jalOff GuestAddrs.create_stage_initcode_frame 2147483864),
    .JAL .x1 (jalOff GuestAddrs.create_execute_initcode_frame 2147483868),
    .ADDI .x29 .x8 (96 : BitVec 12),
    .SD .x29 .x0 (0 : BitVec 12),
    .SD .x29 .x0 (8 : BitVec 12),
    .SD .x29 .x0 (16 : BitVec 12),
    .SD .x29 .x0 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_status 2147483892),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_status 2147483892),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (2 : Word),
    .BNE .x5 .x6 (52 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.create_address_be 2147483912),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_address_be 2147483912),
    .ADDI .x7 .x7 (19 : BitVec 12),
    .MV .x6 .x29,
    .LI .x5 (20 : Word),
    .BEQ .x5 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x10 .x8 (96 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `create2Descend_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def create2Descend_relocs : RelocTable :=
  [ (9, .la .x6 "create_init_offset"),
    (13, .la .x6 "create_init_size"),
    (16, .la .x6 "create_sender_be"),
    (27, .la .x6 "create_salt_be"),
    (37, .la .x10 "create_sender_be"),
    (39, .la .x11 "create_salt_be"),
    (41, .la .x5 "create_init_offset"),
    (45, .la .x5 "create_init_size"),
    (48, .la .x14 "create_address_be"),
    (50, .jal .x1 "address_compute_create2"),
    (54, .jal .x1 "create_stage_initcode_frame"),
    (55, .jal .x1 "create_execute_initcode_frame"),
    (61, .la .x5 "create_child_status"),
    (66, .la .x7 "create_address_be") ]

def create2DescendFunction : String :=
  "create2_descend:\n" ++ emitProgramR create2Descend_prog create2Descend_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `create2Descend_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem create2DescendFunction_eq_prog :
    create2DescendFunction = "create2_descend:\n" ++ emitProgramR create2Descend_prog create2Descend_relocs := rfl

#guard create2DescendFunction.startsWith "create2_descend:\n"
/-! ## create_descend
    The CREATE (0xf0) analog of create2_descend. CREATE stack (x12, top first):
    value@0, offset@32, length@64 (3 words, no salt) — pops 3, pushes 1 → new top
    = x12 + 64. Address = keccak(rlp([sender, nonce]))[12:] via address_compute_create;
    the nonce is read from `create_nonce` (the handler populates it with the creator's
    current nonce — a wiring concern, not this logic). Otherwise identical to
    create2_descend (stage + bounded mini-interpreter + push address/0). -/
def createDescend_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .MV .x18 .x20,
    .LD .x5 .x8 (32 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.create_init_offset 2147483684),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_init_offset 2147483684),
    .SD .x6 .x5 (0 : BitVec 12),
    .LD .x5 .x8 (64 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.create_init_size 2147483700),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_init_size 2147483700),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.create_sender_be 2147483712),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_sender_be 2147483712),
    .LD .x7 .x18 (0 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .LD .x7 .x18 (8 : BitVec 12),
    .SD .x6 .x7 (8 : BitVec 12),
    .LD .x7 .x18 (16 : BitVec 12),
    .SD .x6 .x7 (16 : BitVec 12),
    .LD .x7 .x18 (24 : BitVec 12),
    .SD .x6 .x7 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.create_sender_be 2147483752),
    .ADDI .x10 .x10 (laLo GuestAddrs.create_sender_be 2147483752),
    .AUIPC .x5 (laHi GuestAddrs.create_nonce 2147483760),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_nonce 2147483760),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.create_address_be 2147483772),
    .ADDI .x12 .x12 (laLo GuestAddrs.create_address_be 2147483772),
    .JAL .x1 (jalOff GuestAddrs.address_compute_create 2147483780),
    .MV .x10 .x9,
    .MV .x11 .x8,
    .LI .x12 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.create_stage_initcode_frame 2147483796),
    .JAL .x1 (jalOff GuestAddrs.create_execute_initcode_frame 2147483800),
    .ADDI .x29 .x8 (64 : BitVec 12),
    .SD .x29 .x0 (0 : BitVec 12),
    .SD .x29 .x0 (8 : BitVec 12),
    .SD .x29 .x0 (16 : BitVec 12),
    .SD .x29 .x0 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_status 2147483824),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_status 2147483824),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (2 : Word),
    .BNE .x5 .x6 (52 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.create_address_be 2147483844),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_address_be 2147483844),
    .ADDI .x7 .x7 (19 : BitVec 12),
    .MV .x6 .x29,
    .LI .x5 (20 : Word),
    .BEQ .x5 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x10 .x8 (64 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `createDescend_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def createDescend_relocs : RelocTable :=
  [ (9, .la .x6 "create_init_offset"),
    (13, .la .x6 "create_init_size"),
    (16, .la .x6 "create_sender_be"),
    (26, .la .x10 "create_sender_be"),
    (28, .la .x5 "create_nonce"),
    (31, .la .x12 "create_address_be"),
    (33, .jal .x1 "address_compute_create"),
    (37, .jal .x1 "create_stage_initcode_frame"),
    (38, .jal .x1 "create_execute_initcode_frame"),
    (44, .la .x5 "create_child_status"),
    (49, .la .x7 "create_address_be") ]

def createDescendFunction : String :=
  "create_descend:\n" ++ emitProgramR createDescend_prog createDescend_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `createDescend_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem createDescendFunction_eq_prog :
    createDescendFunction = "create_descend:\n" ++ emitProgramR createDescend_prog createDescend_relocs := rfl

#guard createDescendFunction.startsWith "create_descend:\n"
/-- `zisk_create_descend`: CREATE (0xf0) known-answer probe (mirrors zisk_create2_descend
    without salt). Sets create_nonce, computes the expected address with a DIRECT
    address_compute_create, runs create_descend, asserts the pushed LE stack word equals
    the LE-reversed expected address and status==2.
    Output (0xa0010000): +0 status; +8 pushed low8; +16 expected-LE low8; +24 match. -/
def ziskCreateDescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, evm_env\n" ++
  "  li t1, 0; sd t1, 0(t0); sd t1, 8(t0); sd t1, 16(t0); sd t1, 24(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, evm_memory\n" ++
  "  li t1, 0x60; sb t1, 0(t0); li t1, 0x42; sb t1, 1(t0)\n" ++
  "  li t1, 0x60; sb t1, 2(t0); li t1, 0x00; sb t1, 3(t0)\n" ++
  "  li t1, 0x52; sb t1, 4(t0)\n" ++
  "  li t1, 0x60; sb t1, 5(t0); li t1, 0x01; sb t1, 6(t0)\n" ++
  "  li t1, 0x60; sb t1, 7(t0); li t1, 0x1f; sb t1, 8(t0)\n" ++
  "  li t1, 0xf3; sb t1, 9(t0)\n" ++
  "  la t0, create_nonce; li t1, 7; sd t1, 0(t0)\n" ++
  "  la t0, cd_stack\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  sd x0, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  li t1, 10; sd t1, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  la a0, evm_env; li a1, 7; la a2, cd_expected\n" ++
  "  jal ra, address_compute_create\n" ++
  "  la x12, cd_stack; la x13, evm_memory; la x20, evm_env\n" ++
  "  jal ra, create_descend\n" ++
  "  la t0, create_child_status; ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  la t0, cd_stack; addi t0, t0, 64; ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  la t2, cd_expected; addi t2, t2, 19; la t1, cd_exple; li t3, 20\n" ++
  "1:\n  beqz t3, 2f\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t3, t3, -1; j 1b\n" ++
  "2:\n" ++
  "  la t0, cd_exple; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  la t0, cd_stack; addi t0, t0, 64; la t1, cd_exple; li t3, 20; li t4, 1\n" ++
  "3:\n  beqz t3, 4f\n  lbu t5, 0(t0); lbu t6, 0(t1); bne t5, t6, 5f\n  addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; j 3b\n" ++
  "5:\n  li t4, 0\n" ++
  "4:\n  sd t4, 24(s0)\n" ++
  "  j .Lcdp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  createStageInitcodeFrameRuntimeFunction ++ "\n" ++
  createExecuteInitcodeFrameRuntimeFunction ++ "\n" ++
  createDescendFunction ++ "\n" ++
  ".Lcdp_done:"

def ziskCreateDescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_memory:\n  .zero 0x20000\n" ++
  ".balign 8\n" ++
  "evm_env:\n  .zero 656\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "create_nonce:\n  .zero 8\n" ++
  "create_init_offset:\n  .zero 8\n" ++
  "create_init_size:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "create_sender_be:\n  .zero 32\n" ++
  "create_salt_be:\n  .zero 32\n" ++
  "create_address_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_buffer:\n  .zero 32\n" ++
  "ac_nonce_be:\n  .zero 8\n" ++
  "ac_digest:\n  .zero 32\n" ++
  emitCreateChildFrameData ++
  ".balign 8\n" ++
  "cd_stack:\n  .zero 256\n" ++
  ".balign 32\n" ++
  "cd_expected:\n  .zero 32\n" ++
  "cd_exple:\n  .zero 32\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n  .zero 262144\n" ++
  "lp64_sp_top:\n"


/-- `zisk_create2_descend`: known-answer probe. Lays out a synthetic CREATE2 stack +
    init code + env, computes the expected address with a DIRECT address_compute_create2
    call, then runs create2_descend and asserts the pushed stack word equals the
    LE-reversed expected address and that status==2 (the mini-interp RETURNs code).
    Init code = PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 1; PUSH1 31; RETURN (deploys 0x42).
    Output (0xa0010000): +0 status (2); +8 pushed addr low8 vs +16 expected-LE low8;
    +24 match flag (1 if the full 20 bytes agree). -/
def ziskCreate2DescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- env at evm_env: ADDRESS@0 = sender 0x11..(low20 BE). Set a recognizable sender.
  "  la t0, evm_env\n" ++
  "  li t1, 0; sd t1, 0(t0); sd t1, 8(t0); sd t1, 16(t0); sd t1, 24(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++   -- sender BE: byte0=0xAA .. byte19=0xBB
  -- init code into evm_memory at offset 0: 60 42 60 00 52 60 01 60 1f f3 (10 bytes).
  "  la t0, evm_memory\n" ++
  "  li t1, 0x60; sb t1, 0(t0); li t1, 0x42; sb t1, 1(t0)\n" ++
  "  li t1, 0x60; sb t1, 2(t0); li t1, 0x00; sb t1, 3(t0)\n" ++
  "  li t1, 0x52; sb t1, 4(t0)\n" ++
  "  li t1, 0x60; sb t1, 5(t0); li t1, 0x01; sb t1, 6(t0)\n" ++
  "  li t1, 0x60; sb t1, 7(t0); li t1, 0x1f; sb t1, 8(t0)\n" ++
  "  li t1, 0xf3; sb t1, 9(t0)\n" ++
  -- synthetic stack at cd2_stack: value@0=0, offset@32=0, length@64=10, salt@96 (LE word).
  "  la t0, cd2_stack\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++          -- value = 0
  "  sd x0, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++        -- offset = 0
  "  li t1, 10; sd t1, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++ -- length = 10
  "  li t1, 0x99; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++ -- salt LE low byte 0x99
  -- Expected: direct address_compute_create2(sender, salt_be, mem, 10) -> cd2_expected.
  -- salt_be = reverse(salt LE word) -> byte31 = 0x99 (BE last byte).
  "  la t0, cd2_saltbe\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x99; sb t1, 31(t0)\n" ++                                        -- salt_be[31] = 0x99
  "  la a0, evm_env; la a1, cd2_saltbe; la a2, evm_memory; li a3, 10; la a4, cd2_expected\n" ++
  "  jal ra, address_compute_create2\n" ++
  -- Run create2_descend with x12=stack, x13=mem, x20=env.
  "  la x12, cd2_stack; la x13, evm_memory; la x20, evm_env\n" ++
  "  jal ra, create2_descend\n" ++
  "  mv s1, a0                    # new stack top\n" ++
  -- status
  "  la t0, create_child_status; ld t1, 0(t0); sd t1, 0(s0)\n" ++
  -- pushed addr (at new top = cd2_stack+96) low8, expected-LE low8, full-20 match
  "  la t0, cd2_stack; addi t0, t0, 96; ld t1, 0(t0); sd t1, 8(s0)\n" ++     -- pushed low8 (LE)
  -- build expected-LE = reverse(cd2_expected[0..20]) into cd2_exple, compare 20 bytes
  "  la t2, cd2_expected; addi t2, t2, 19; la t1, cd2_exple; li t3, 20\n" ++
  "1:\n  beqz t3, 2f\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t3, t3, -1; j 1b\n" ++
  "2:\n" ++
  "  la t0, cd2_exple; ld t1, 0(t0); sd t1, 16(s0)\n" ++                     -- expected-LE low8
  "  la t0, cd2_stack; addi t0, t0, 96; la t1, cd2_exple; li t3, 20; li t4, 1\n" ++
  "3:\n  beqz t3, 4f\n  lbu t5, 0(t0); lbu t6, 0(t1); bne t5, t6, 5f\n  addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; j 3b\n" ++
  "5:\n  li t4, 0\n" ++
  "4:\n  sd t4, 24(s0)\n" ++                                                 -- match flag
  "  j .Lcd2_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  createStageInitcodeFrameRuntimeFunction ++ "\n" ++
  createExecuteInitcodeFrameRuntimeFunction ++ "\n" ++
  create2DescendFunction ++ "\n" ++
  ".Lcd2_done:"

def ziskCreate2DescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_memory:\n  .zero 0x20000\n" ++
  ".balign 8\n" ++
  "evm_env:\n  .zero 656\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "create_init_offset:\n  .zero 8\n" ++
  "create_init_size:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "create_sender_be:\n  .zero 32\n" ++
  "create_salt_be:\n  .zero 32\n" ++
  "create_address_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_inner_digest:\n  .zero 32\n" ++
  "ac2_outer_digest:\n  .zero 32\n" ++
  "ac2_preimage:\n  .zero 88\n" ++
  emitCreateChildFrameData ++
  ".balign 8\n" ++
  "cd2_stack:\n  .zero 256\n" ++
  ".balign 32\n" ++
  "cd2_saltbe:\n  .zero 32\n" ++
  "cd2_expected:\n  .zero 32\n" ++
  "cd2_exple:\n  .zero 32\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n  .zero 262144\n" ++
  "lp64_sp_top:\n"


end EvmAsm.Codegen
