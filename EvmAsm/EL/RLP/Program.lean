/-
  EvmAsm.EL.RLP.Program

  Executable RISC-V programs for the RLP decoder.
-/

import EvmAsm.EL.RLP.Prefix
import EvmAsm.Rv64.Program

namespace EvmAsm.EL.RLP

open EvmAsm.Rv64

/-- Numeric tag used by executable code for an RLP prefix class. -/
def PrefixClass.toWord : PrefixClass → Word
  | .singleByte => 0
  | .shortBytes => 1
  | .longBytes => 2
  | .shortList => 3
  | .longList => 4

@[simp] theorem PrefixClass.toWord_singleByte :
    PrefixClass.toWord .singleByte = (0 : Word) := rfl

@[simp] theorem PrefixClass.toWord_shortBytes :
    PrefixClass.toWord .shortBytes = (1 : Word) := rfl

@[simp] theorem PrefixClass.toWord_longBytes :
    PrefixClass.toWord .longBytes = (2 : Word) := rfl

@[simp] theorem PrefixClass.toWord_shortList :
    PrefixClass.toWord .shortList = (3 : Word) := rfl

@[simp] theorem PrefixClass.toWord_longList :
    PrefixClass.toWord .longList = (4 : Word) := rfl

/-- All BLTU exits in `rlp_prefix_classify` jump 36 bytes to their class block. -/
def rlpPrefixClassifyBranchOff : BitVec 13 := 36

/-- JAL offset from the long-list block to the common exit. -/
def rlpPrefixClassifyLongListExitOff : BitVec 21 := 36

/-- JAL offset from the single-byte block to the common exit. -/
def rlpPrefixClassifySingleByteExitOff : BitVec 21 := 28

/-- JAL offset from the short-bytes block to the common exit. -/
def rlpPrefixClassifyShortBytesExitOff : BitVec 21 := 20

/-- JAL offset from the long-bytes block to the common exit. -/
def rlpPrefixClassifyLongBytesExitOff : BitVec 21 := 12

/-- JAL offset from the short-list block to the common exit. -/
def rlpPrefixClassifyShortListExitOff : BitVec 21 := 4

/--
  First executable RLP decoder phase: classify a prefix byte already loaded in
  `pfxReg`, writing `PrefixClass.toWord` to `outReg`.

  Register contract:
  * `pfxReg`: input byte value, zero-extended to 64 bits.
  * `outReg`: output class tag (`0..4`).
  * `tmpReg`: caller-provided scratch register for thresholds.
-/
def rlp_prefix_classify (pfxReg outReg tmpReg : Reg) : Program :=
  LI tmpReg (0x80 : Word) ;;
  BLTU pfxReg tmpReg rlpPrefixClassifyBranchOff ;;
  LI tmpReg (0xB8 : Word) ;;
  BLTU pfxReg tmpReg rlpPrefixClassifyBranchOff ;;
  LI tmpReg (0xC0 : Word) ;;
  BLTU pfxReg tmpReg rlpPrefixClassifyBranchOff ;;
  LI tmpReg (0xF8 : Word) ;;
  BLTU pfxReg tmpReg rlpPrefixClassifyBranchOff ;;
  LI outReg (PrefixClass.toWord .longList) ;;
  JAL .x0 rlpPrefixClassifyLongListExitOff ;;
  LI outReg (PrefixClass.toWord .singleByte) ;;
  JAL .x0 rlpPrefixClassifySingleByteExitOff ;;
  LI outReg (PrefixClass.toWord .shortBytes) ;;
  JAL .x0 rlpPrefixClassifyShortBytesExitOff ;;
  LI outReg (PrefixClass.toWord .longBytes) ;;
  JAL .x0 rlpPrefixClassifyLongBytesExitOff ;;
  LI outReg (PrefixClass.toWord .shortList) ;;
  JAL .x0 rlpPrefixClassifyShortListExitOff

theorem rlp_prefix_classify_length (pfxReg outReg tmpReg : Reg) :
    (rlp_prefix_classify pfxReg outReg tmpReg).length = 18 := by
  unfold rlp_prefix_classify LI BLTU JAL seq single
  rfl

theorem rlp_prefix_classify_byte_length (pfxReg outReg tmpReg : Reg) :
    4 * (rlp_prefix_classify pfxReg outReg tmpReg).length = 72 := by
  rw [rlp_prefix_classify_length]

end EvmAsm.EL.RLP
