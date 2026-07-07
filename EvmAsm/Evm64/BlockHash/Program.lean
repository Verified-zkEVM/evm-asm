/-
  EvmAsm.Evm64.BlockHash.Program

  RISC-V program implementing the EVM `BLOCKHASH` opcode (0x40).

  BLOCKHASH pops a target block number and pushes the hash of that block if it
  lies within the 256-ancestor window, else zero. The runtime trailer supplies
  the current block number (`cur`, env+552), the number of loaded recent
  hashes (`count`, env+560, clamped to 256), and the `evm_block_hashes` table
  (`count` 32-byte hashes in increasing block-number order, matching
  execution-specs `block_env.block_hashes`). Semantics (Amsterdam
  `block_hash`, u64 targets):

    - nonzero high limb in the target word          → 0
    - target ≥ cur                                  → 0
    - age := cur - target;  age > count             → 0
    - else push `block_hashes[count - age]`

  Like BLOBHASH, the link-time `la` of the table address stays in handler
  `preBody` glue seeding `tableBaseReg`; the verified body replaces the popped
  word in place at the stack top (`x12` unchanged).

  Layout (28 instructions = 112 bytes; zero arm at +96):

     +0   LD   tmpReg x12  8         ; target limb 1
     +4   BNE  tmpReg x0   +92       ; nonzero high limb → zero
     +8   LD   tmpReg x12  16
     +12  BNE  tmpReg x0   +84
     +16  LD   tmpReg x12  24
     +20  BNE  tmpReg x0   +76
     +24  LD   tgtReg x12  0         ; target block number (low u64)
     +28  LD   tmpReg envBaseReg 552 ; cur
     +32  BGEU tgtReg tmpReg +64     ; target ≥ cur → zero
     +36  SUB  tgtReg tmpReg tgtReg  ; tgtReg := age = cur - target (≥ 1)
     +40  LD   tmpReg envBaseReg 560 ; count
     +44  BLTU tmpReg tgtReg +52     ; count < age (i.e. age > count) → zero
     +48  SUB  tmpReg tmpReg tgtReg  ; tmpReg := index = count - age
     +52  SLLI tmpReg tmpReg 5       ; 32 bytes per hash
     +56  ADD  tableBaseReg tableBaseReg tmpReg
     +60  LD   valReg tableBaseReg 0 ; copy hash limbs to stack top
     +64  SD   x12 valReg 0
     +68  LD   valReg tableBaseReg 8
     +72  SD   x12 valReg 8
     +76  LD   valReg tableBaseReg 16
     +80  SD   x12 valReg 16
     +84  LD   valReg tableBaseReg 24
     +88  SD   x12 valReg 24
     +92  JAL  x0 +20                ; skip the zero arm → +112
     +96  SD   x12 x0 0              ; zero arm
     +100 SD   x12 x0 8
     +104 SD   x12 x0 16
     +108 SD   x12 x0 24
     +112 (exit)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace BlockHash

open EvmAsm.Rv64

/-- Byte offset of the current block number (u64) in the dispatcher env
    block. Seeded by the runtime prologue from the block-history trailer. -/
def blockNumberOff : Nat := 552

/-- Byte offset of the loaded recent-hash count (u64, ≤ 256) in the
    dispatcher env block. -/
def blockHashCountOff : Nat := 560

/-- Parameterized RISC-V program implementing `BLOCKHASH`. Registers:
    `envBaseReg` env-block base; `tableBaseReg` seeded with the
    `evm_block_hashes` address by handler glue (clobbered on the taken path);
    `tgtReg`/`tmpReg`/`valReg` caller-saved temporaries (`tgtReg` ends holding
    the age, `tmpReg` the scaled index, on the taken path). All distinct from
    each other and from `x0`/`x12`. 28 instructions = 112 bytes. -/
def evm_blockhash (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg) : Program :=
  LD tmpReg .x12 8 ;;
  BNE tmpReg .x0 (BitVec.ofNat 13 92) ;;
  LD tmpReg .x12 16 ;;
  BNE tmpReg .x0 (BitVec.ofNat 13 84) ;;
  LD tmpReg .x12 24 ;;
  BNE tmpReg .x0 (BitVec.ofNat 13 76) ;;
  LD tgtReg .x12 0 ;;
  LD tmpReg envBaseReg (BitVec.ofNat 12 blockNumberOff) ;;
  BGEU tgtReg tmpReg (BitVec.ofNat 13 64) ;;
  SUB tgtReg tmpReg tgtReg ;;
  LD tmpReg envBaseReg (BitVec.ofNat 12 blockHashCountOff) ;;
  BLTU tmpReg tgtReg (BitVec.ofNat 13 52) ;;
  SUB tmpReg tmpReg tgtReg ;;
  SLLI tmpReg tmpReg 5 ;;
  ADD tableBaseReg tableBaseReg tmpReg ;;
  LD valReg tableBaseReg 0 ;;
  SD .x12 valReg 0 ;;
  LD valReg tableBaseReg 8 ;;
  SD .x12 valReg 8 ;;
  LD valReg tableBaseReg 16 ;;
  SD .x12 valReg 16 ;;
  LD valReg tableBaseReg 24 ;;
  SD .x12 valReg 24 ;;
  JAL .x0 (BitVec.ofNat 21 20) ;;
  SD .x12 .x0 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

abbrev evm_blockhash_code
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_blockhash envBaseReg tableBaseReg tgtReg tmpReg valReg)

/-- `evm_blockhash` is exactly 28 RISC-V instructions = 112 bytes. -/
theorem evm_blockhash_length (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg) :
    (evm_blockhash envBaseReg tableBaseReg tgtReg tmpReg valReg).length = 28 := by
  simp [evm_blockhash, LD, SD, BNE, BGEU, BLTU, SUB, SLLI, ADD, JAL, single, seq,
        Program.length_append]

theorem evm_blockhash_byte_length (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg) :
    4 * (evm_blockhash envBaseReg tableBaseReg tgtReg tmpReg valReg).length = 112 := by
  rw [evm_blockhash_length]

end BlockHash
end EvmAsm.Evm64
