import Out.Flow
import Out.Prelude
import Out.RvfiDii
import Out.PlatformConfig
import Out.Types
import Out.Regs
import Out.PcAccess
import Out.SysRegs
import Out.AddrChecks
import Out.Vmem

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

noncomputable section

namespace Out.Functions

open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vstart_class
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open stateen_bit
open sopw
open sop
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open page_based_mem_type
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_exception
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extension
open exception
open cregidx
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cacheop
open breakpoint_cause
open bop
open barrier_kind
open amoop
open agtype
open XtvecModeReservedBehavior
open XipReadType
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privilege
open PointerMaskingMode
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open PM_Ext
open OOBVstartReservedBehavior
open MemoryRegionType
open MemoryAccessType
open IsaVersion
open InterruptType
open IllegalVtypeReservedBehavior
open ISA_Format
open HartState
open FetchResult
open FetchBytes_Result
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open CSRCheckResult
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

def rvfi_fetch (_ : Unit) : SailM FetchResult := SailME.run do
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 63 0
    (← readReg minstret))
  writeReg rvfi_pc_data (Sail.BitVec.updateSubrange (← readReg rvfi_pc_data) 63 0
    (zero_extend (m := 64) (← (get_arch_pc ()))))
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 159 152
    (zero_extend (m := 8) (privLevel_to_bits (← readReg cur_privilege))))
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 167 160
    (zero_extend (m := 8) (_get_Misa_MXL (← readReg misa))))
  match (ext_fetch_check_pc (← readReg PC) (← readReg PC)) with
  | .some e => SailME.throw ((F_Ext_Error e) : FetchResult)
  | none => (pure ())
  if ((((BitVec.access (← readReg PC) 0) != 0#1) || (((BitVec.access (← readReg PC) 1) != 0#1) && (not
           (← (currentlyEnabled Ext_Zca))))) : Bool)
  then (pure (F_Error ((E_Fetch_Addr_Align ()), (← readReg PC))))
  else
    (do
      match (← (translateAddr (Virtaddr (← readReg PC)) (InstructionFetch ()))) with
      | .Err (e, _) =>
        SailME.throw (← do
            (pure (F_Error (e, (← readReg PC)))))
      | .Ok (_, _, _) => (pure ())
      let i ← do
        (pure (_get_RVFI_DII_Instruction_Packet_rvfi_insn (← readReg rvfi_instruction)))
      writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 127 64
        (zero_extend (m := 64) i))
      if (((Sail.BitVec.extractLsb i 1 0) != 0b11#2) : Bool)
      then (pure (F_RVC (Sail.BitVec.extractLsb i 15 0)))
      else
        (do
          let PC_hi ← do (pure (BitVec.addInt (← readReg PC) 2))
          match (ext_fetch_check_pc (← readReg PC) PC_hi) with
          | .some e => SailME.throw ((F_Ext_Error e) : FetchResult)
          | none => (pure ())
          match (← (translateAddr (Virtaddr PC_hi) (InstructionFetch ()))) with
          | .Err (e, _) => (pure (F_Error (e, (← readReg PC))))
          | .Ok (_, _, _) => (pure (F_Base i))))

