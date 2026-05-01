/-
  EvmAsm.Evm64.MLoad.LimbSpec

  Per-byte spec for the MLOAD per-limb byte-pack loop.

  This sub-slice (#99 slice 3c, beads `evm-asm-8dk7`) lands the level-1
  building block of the MLOAD three-tier proof architecture
  (`docs/99-mload-design.md` §5): a `cpsTripleWithin` spec for the
  3-instruction `LBU + SLLI + OR` triple that folds one byte from EVM
  memory into the running 64-bit accumulator.

  The next sub-slice (#99 slice 3d) composes 8 of these per limb (plus a
  final `SD`) to obtain `mload_one_limb_spec_within`; that step also
  consumes `bytePack8_eq` from `Evm64/MLoad/ByteAlg.lean` to bridge the
  runtime shift-OR chain to a single big-endian-concatenated 64-bit
  value.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Per-byte byte-pack step spec (3 instructions): `LBU byteReg addrReg
    offset`, `SLLI accReg accReg 8`, `OR accReg accReg byteReg`.

    Loads one byte from `addrReg + offset` (zero-extended to 64 bits),
    left-shifts the running accumulator by 8, and ORs the new byte into
    the low 8 bits. The byte and accumulator registers are completely
    rewritten; the address register and the source memory dword are
    unchanged.

    All three roles (`addrReg`, `byteReg`, `accReg`) must be distinct
    and non-`x0`. The byte address must be byte-access valid and align to
    `dwordAddr`, where `wordVal` is the source dword's contents.

    This is the analogue of `EvmAsm.Evm64.push_one_byte_spec_within` for
    MLOAD and is the level-1 building block of the three-tier MLOAD
    proof architecture (`docs/99-mload-design.md` §5). -/
theorem mload_byte_pack_step_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (offset : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = dwordAddr)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext :=
      (extractByte wordVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64
    let accNew := (accOld <<< (8 : Nat)) ||| byteZext
    let cr :=
      (CodeReq.singleton base (.LBU byteReg addrReg offset)).union
        ((CodeReq.singleton (base + 4) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
         (CodeReq.singleton (base + 8) (.OR accReg accReg byteReg)))
    cpsTripleWithin 3 base (base + 12) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (dwordAddr ↦ₘ wordVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteZext) ** (accReg ↦ᵣ accNew) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro byteZext accNew cr
  have L := lbu_spec_gen_within byteReg addrReg addrPtr byteOld offset base
              dwordAddr wordVal h_byte_ne_x0 h_align h_valid
  have I := slli_spec_gen_same_within accReg accOld (BitVec.ofNat 6 8) (base + 4) h_acc_ne_x0
  have O := or_spec_gen_rd_eq_rs1_within accReg byteReg (accOld <<< (8 : Nat)) byteZext
              (base + 8) h_acc_ne_x0
  -- `(BitVec.ofNat 6 8).toNat = 8` definitionally; rewrite the SLLI post
  -- so it matches the OR pre.
  have h8 : ((BitVec.ofNat 6 8 : BitVec 6).toNat) = 8 := by decide
  rw [h8] at I
  runBlock L I O

/-- Init step of the `mload_byte_pack` recursion: a single `LBU accReg
    addrReg offset` that loads the leading (most-significant) byte of a
    limb directly into `accReg`, with no shift/OR (since the accumulator
    is freshly overwritten).

    This is the level-1 base-case spec for sub-slice 3d
    (`mload_one_limb_spec_within`, `docs/99-mload-design.md` §6). The
    inductive step is `mload_byte_pack_step_spec_within` above. Together
    they let the limb-spec slice fold 1 init + 7 triples = 22 instructions
    into a single per-limb postcondition; the SD that closes the limb is
    then a one-instruction `sd_spec_gen_within` application.

    The address register and the source memory dword are unchanged; the
    accumulator and the byte register the spec mentions are limited to
    the accumulator only — the byte register is not used in this step,
    so it does not appear in the spec's footprint. -/
theorem mload_byte_pack_init_spec_within
    (addrReg accReg : Reg)
    (addrPtr accOld wordVal : Word)
    (dwordAddr : Word)
    (offset : BitVec 12) (base : Word)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = dwordAddr)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext :=
      (extractByte wordVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU accReg addrReg offset))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accOld) ** (dwordAddr ↦ₘ wordVal))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ byteZext) ** (dwordAddr ↦ₘ wordVal)) := by
  intro byteZext
  exact lbu_spec_gen_within accReg addrReg addrPtr accOld offset base
    dwordAddr wordVal h_acc_ne_x0 h_align h_valid

end EvmAsm.Evm64
