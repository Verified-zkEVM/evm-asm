/-
  EvmAsm.Evm64.Calldata.CopyProgram

  Top-level RISC-V program implementing the EVM `CALLDATACOPY` opcode
  (GH #104).

  Stack convention: CALLDATACOPY pops three EVM words from the EVM stack
  (located at `x12`):

    - top  (`x12 + 0..31`)  : `destOffset` — destination memory offset
    - 2nd  (`x12 + 32..63`) : `dataOffset` — calldata source offset
    - 3rd  (`x12 + 64..95`) : `size`       — byte count

  After the program executes, the EVM stack pointer `x12` is advanced by
  `+96` (three 32-byte pops, no push). The opcode writes `size` bytes
  into EVM memory starting at `memBase + destOffset_lo`. Bytes whose
  source address falls outside the input calldata region are written
  as zeros, matching the executable
  `CallDataCopyMemory.copyWriteByteAt` /
  `CallDataCopyExec.copiedBytesFromArgs` semantics.

  This slice is **program-only** — the stack-level / partial-memory
  spec lands in the next slice (parent `evm-asm-pq9ac`, sibling
  `evm-asm-54bh8`). The byte loop's bounded-vs-out-of-range branching
  is implemented here directly so a future spec can compose against
  the existing `copyWriteByteAt_at_destination_add_*` helpers.

  Layout (19 instructions = 76 bytes):

    Preamble (9 instructions = 36 bytes):
      [0]  LD   destReg     x12 0    -- destOffset (low limb)
      [1]  LD   srcReg      x12 32   -- dataOffset (low limb)
      [2]  LD   cntReg      x12 64   -- size (low limb)
      [3]  ADDI x12 x12     96       -- pop 3 words (3 × 32 bytes)
      [4]  LD   cdpReg      envBaseReg, callDataPtrOff
      [5]  LD   endReg      envBaseReg, callDataLenOff
      [6]  ADD  endReg      endReg cdpReg     -- end = ptr + len
      [7]  ADD  destReg     memBaseReg destReg -- absolute dest addr
      [8]  ADD  srcReg      cdpReg srcReg     -- absolute src addr

    Loop (10 instructions = 40 bytes):
      [9]  loop_top: BEQ cntReg x0,  +40       -- size == 0 → exit
      [10]           BGEU srcReg endReg, +12  -- src ≥ end  → oob
      [11]           LBU byteReg srcReg 0     -- in-bounds: read source
      [12]           JAL x0, +8                -- skip oob fill
      [13]  oob:     ADDI byteReg x0 0        -- out-of-bounds: zero
      [14]  store:   SB destReg byteReg 0
      [15]           ADDI srcReg srcReg 1
      [16]           ADDI destReg destReg 1
      [17]           ADDI cntReg cntReg -1
      [18]           JAL x0, -36               -- back to loop_top
      -- exit at byte 76 (one past [18])

  Branch offsets are relative to the branch instruction's PC, in bytes:

    [9]  BEQ exit:   76 − 36 = 40
    [10] BGEU oob:   52 − 40 = 12
    [12] JAL store:  56 − 48 =  8
    [18] JAL back:   36 − 72 = -36

  Register convention (all caller-saved temporaries per LP64; see
  `AGENTS.md` "Calling Convention (LP64)"; caller chooses concrete
  registers, the spec slice will pin down distinctness side
  conditions):

    `envBaseReg` — caller-supplied environment-block base.
    `memBaseReg` — caller-supplied EVM memory buffer base.
    `destReg`    — initially low limb of `destOffset`; rewritten to
                   the running absolute destination byte pointer.
    `srcReg`     — initially low limb of `dataOffset`; rewritten to
                   the running absolute source byte pointer.
    `cntReg`     — initially low limb of `size`; decremented each
                   iteration and used as the loop guard against `x0`.
    `cdpReg`     — `env.callDataPtr` (calldata buffer base).
    `endReg`     — `env.callDataPtr + env.callDataLen` (one past the
                   last in-bounds calldata byte).
    `byteReg`    — per-iteration scratch holding the byte to store.

  The high three limbs of each input word are assumed zero by the
  spec precondition (matching the existing CALLDATALOAD / MSTORE
  conventions); the program reads only the low limb of each.

  Memory-expansion bookkeeping (`evmMemSizeIs` update) is **not**
  performed by this program; it will either be lifted to the spec
  precondition or added in a later sub-slice — same arrangement as
  `MStore.Program`.

  Slice `evm-asm-pqfmn` (parent `evm-asm-pq9ac`, GH #104).
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Rv64.SepLogic
public import EvmAsm.Evm64.Environment.Layout

@[expose] public section

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv (callDataPtrOff callDataLenOff)

/-- Top-level RISC-V program implementing the EVM `CALLDATACOPY`
    opcode. See the file header for the stack convention, register
    roles, and the byte-by-byte loop layout.

    19 instructions = 76 bytes. -/
def evm_calldatacopy
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg
      byteReg : Reg) : Program :=
  -- Preamble: pop 3 stack words and compute absolute pointers.
  LD destReg .x12 0 ;;
  LD srcReg  .x12 32 ;;
  LD cntReg  .x12 64 ;;
  ADDI .x12 .x12 (BitVec.ofNat 12 96) ;;
  LD cdpReg envBaseReg (BitVec.ofNat 12 callDataPtrOff) ;;
  LD endReg envBaseReg (BitVec.ofNat 12 callDataLenOff) ;;
  ADD endReg endReg cdpReg ;;
  ADD destReg memBaseReg destReg ;;
  ADD srcReg cdpReg srcReg ;;
  -- Loop body.
  single (.BEQ cntReg .x0 (BitVec.ofNat 13 40)) ;;
  single (.BGEU srcReg endReg (BitVec.ofNat 13 12)) ;;
  LBU byteReg srcReg 0 ;;
  single (.JAL .x0 (BitVec.ofNat 21 8)) ;;
  ADDI byteReg .x0 0 ;;
  SB destReg byteReg 0 ;;
  ADDI srcReg srcReg 1 ;;
  ADDI destReg destReg 1 ;;
  ADDI cntReg cntReg (-1 : BitVec 12) ;;
  single (.JAL .x0 (-36 : BitVec 21))

/-- `CodeReq` for `evm_calldatacopy` placed at `base`. -/
abbrev evm_calldatacopy_code
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg
      byteReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_calldatacopy envBaseReg memBaseReg destReg srcReg cntReg
      cdpReg endReg byteReg)

/-- `evm_calldatacopy` is exactly 19 RISC-V instructions. -/
theorem evm_calldatacopy_length
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg
      byteReg : Reg) :
    (evm_calldatacopy envBaseReg memBaseReg destReg srcReg cntReg
        cdpReg endReg byteReg).length = 19 := by
  simp [evm_calldatacopy, LD, ADDI, ADD, LBU, SB, single, seq]

/-- `evm_calldatacopy` occupies 76 bytes in RV64 code memory. -/
theorem evm_calldatacopy_byte_length
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg
      byteReg : Reg) :
    4 * (evm_calldatacopy envBaseReg memBaseReg destReg srcReg cntReg
        cdpReg endReg byteReg).length = 76 := by
  rw [evm_calldatacopy_length]

end Calldata
end EvmAsm.Evm64
