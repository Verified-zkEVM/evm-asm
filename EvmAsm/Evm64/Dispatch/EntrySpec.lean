/-
  EvmAsm.Evm64.Dispatch.EntrySpec

  Slice 3b of GH #106 (parent `evm-asm-77w8s`, this slice
  `evm-asm-96efo`).  Hoare triple for the first three instructions of
  `evm_dispatch`:

      LBU  rOp   rOpPtr opcodeLbuOff   -- opcode byte ← (rOpPtr)[0]
      SLLI rOp   rOp    entryShiftAmt  -- opcode_byte * 8
      ADD  rOp   rOp    rTable         -- table_base + 8 * opcode_byte

  After this block, `rOp` holds the absolute byte address of the
  jump-table entry (`tableBase + (opcodeByte <<< 3)`); `rOpPtr` and
  `rTable` are unchanged, and the source dword carrying the opcode
  byte is preserved.

  This is a structural sub-step toward `dispatch_spec` (slice 3,
  beads `evm-asm-afkny`).  Splitting out the entry-address chunk lets
  the eventual `dispatch_spec` proof handle the table-entry `LD` and
  the `JALR` separately, with the `dispatchTableIs` layout split
  (`dispatchTableIs_split`) framing the table cell into the LD step.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Evm64.Dispatch.Program
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.RunBlock
public import EvmAsm.Rv64.Tactics.XSimp

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Dispatch

open EvmAsm.Rv64

/-- CodeReq for the dispatch entry-address block: the LBU/SLLI/ADD
    triple at addresses `base`, `base + 4`, `base + 8`.  Pulled out so
    callers and `dispatch_spec` can refer to the code requirement
    symbolically. -/
def entryAddrCode (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LBU rOp rOpPtr opcodeLbuOff)).union
    ((CodeReq.singleton (base + 4) (.SLLI rOp rOp entryShiftAmt)).union
     (CodeReq.singleton (base + 8) (.ADD rOp rOp rTable)))

/-- Three-step entry-address spec for `evm_dispatch`.

    Starting from the dispatch entry frame (`rOpPtr` points at the
    next opcode byte, `rTable` holds the jump-table base, `rOp` is a
    scratch), the LBU+SLLI+ADD prefix:

    * loads the opcode byte from `(pcAddr)` into `rOp` (zero-extended
      to 64 bits);
    * shifts it left by 3 (so the value becomes `8 * opcodeByte`);
    * adds the table base, leaving `rOp` holding
      `(opcodeByte <<< 3) + tableBase`, the address of the
      corresponding jump-table entry.

    The dword containing the opcode byte (`dwordAddr ↦ₘ wordVal`) is
    preserved, as are `rOpPtr` and `rTable`.  Distinctness assumptions
    cover the registers used by all three instructions.  No
    `maxHeartbeats`/`maxRecDepth` overrides; the proof is a flat
    `runBlock` of the three leaf specs. -/
theorem evm_dispatch_entry_addr_spec_within
    (base pcAddr tableBase rOpInit wordVal dwordAddr : Word)
    (h_align : alignToDword (pcAddr + signExtend12 opcodeLbuOff) = dwordAddr)
    (h_valid : isValidByteAccess (pcAddr + signExtend12 opcodeLbuOff) = true) :
    let opcodeByte :=
      (extractByte wordVal
        (byteOffset (pcAddr + signExtend12 opcodeLbuOff))).zeroExtend 64
    cpsTripleWithin 3 base (base + 12) (entryAddrCode base)
      ((rOpPtr  ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) **
       (rOp    ↦ᵣ rOpInit) ** (dwordAddr ↦ₘ wordVal))
      ((rOpPtr  ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) **
       (rOp    ↦ᵣ ((opcodeByte <<< (entryShiftAmt.toNat)) + tableBase)) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro opcodeByte
  -- Leaf specs:
  have L := lbu_spec_gen_within rOp rOpPtr pcAddr rOpInit opcodeLbuOff base
              dwordAddr wordVal (by decide) h_align h_valid
  have I := slli_spec_gen_same_within rOp opcodeByte entryShiftAmt (base + 4)
              (by decide)
  have A := add_spec_gen_rd_eq_rs1_within rOp rTable
              (opcodeByte <<< (entryShiftAmt.toNat)) tableBase (base + 8)
              (by decide)
  runBlock L I A

end Dispatch

end EvmAsm.Evm64
