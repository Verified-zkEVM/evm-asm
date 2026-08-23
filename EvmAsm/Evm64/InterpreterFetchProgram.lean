/-
  EvmAsm.Evm64.InterpreterFetchProgram

  First RV64 opcode-fetch block for the interpreter main loop (GH #108).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
Compute the current EVM bytecode address and load the opcode byte.

Register convention for this leaf block:
* `codeBaseReg` holds the base address of EVM bytecode in RV64 memory.
* `pcReg` holds the current EVM PC as a byte offset.
* `addrReg` is a scratch address register.
* `opcodeReg` receives the zero-extended opcode byte.
-/
def evm_fetch_opcode
    (codeBaseReg pcReg addrReg opcodeReg : Reg) : Program :=
  ADD addrReg codeBaseReg pcReg ;;
  LBU opcodeReg addrReg 0

abbrev evm_fetch_opcode_code
    (codeBaseReg pcReg addrReg opcodeReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_fetch_opcode codeBaseReg pcReg addrReg opcodeReg)

theorem evm_fetch_opcode_length
    (codeBaseReg pcReg addrReg opcodeReg : Reg) :
    (evm_fetch_opcode codeBaseReg pcReg addrReg opcodeReg).length = 2 := by
  simp [evm_fetch_opcode, ADD, LBU, single, seq]

theorem evm_fetch_opcode_byte_length
    (codeBaseReg pcReg addrReg opcodeReg : Reg) :
    4 * (evm_fetch_opcode codeBaseReg pcReg addrReg opcodeReg).length = 8 := by
  rw [evm_fetch_opcode_length]

theorem evm_fetch_opcode_addr_byte_off : 4 * 0 = 0 := by
  rfl

theorem evm_fetch_opcode_load_byte_off : 4 * 1 = 4 := by
  rfl

theorem evm_fetch_opcode_end_byte_off : 4 * 2 = 8 := by
  rfl

/--
Raw RV64 spec for the interpreter opcode fetch block.

The memory precondition owns only the dword containing the target byte. A later
bridge can obtain that dword from `evmCodeIs` via `evmCodeIs_split_at`.

Distinctive token: InterpreterFetchProgram.evm_fetch_opcode_spec_within #108.
-/
theorem evm_fetch_opcode_spec_within
    (codeBaseReg pcReg addrReg opcodeReg : Reg)
    (haddr_ne_x0 : addrReg ≠ .x0)
    (hopcode_ne_x0 : opcodeReg ≠ .x0)
    (base codeBase pcWord addrOld opcodeOld dwordAddr wordVal : Word)
    (halign : alignToDword (codeBase + pcWord) = dwordAddr)
    (hvalid : isValidByteAccess (codeBase + pcWord) = true) :
    let opcodeByte :=
      (extractByte wordVal (byteOffset (codeBase + pcWord))).zeroExtend 64
    cpsTripleWithin 2 base (base + 8)
      (evm_fetch_opcode_code codeBaseReg pcReg addrReg opcodeReg base)
      ((codeBaseReg ↦ᵣ codeBase) ** (pcReg ↦ᵣ pcWord) **
       (addrReg ↦ᵣ addrOld) ** (opcodeReg ↦ᵣ opcodeOld) **
       (dwordAddr ↦ₘ wordVal))
      ((codeBaseReg ↦ᵣ codeBase) ** (pcReg ↦ᵣ pcWord) **
       (addrReg ↦ᵣ (codeBase + pcWord)) **
       (opcodeReg ↦ᵣ opcodeByte) ** (dwordAddr ↦ₘ wordVal)) := by
  dsimp only
  have hAdd := add_spec_gen_within addrReg codeBaseReg pcReg
    codeBase pcWord addrOld base haddr_ne_x0
  have hLbu := lbu_spec_gen_within opcodeReg addrReg
    (codeBase + pcWord) opcodeOld 0 (base + 4) dwordAddr wordVal
    hopcode_ne_x0
    (by
      rw [show (codeBase + pcWord : Word) + signExtend12 0 = codeBase + pcWord by
        rw [signExtend12_0]
        exact BitVec.add_zero (codeBase + pcWord)]
      exact halign)
    (by
      rw [show (codeBase + pcWord : Word) + signExtend12 0 = codeBase + pcWord by
        rw [signExtend12_0]
        exact BitVec.add_zero (codeBase + pcWord)]
      exact hvalid)
  runBlock hAdd hLbu

end EvmAsm.Evm64
