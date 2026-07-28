import Out.Flow
import Out.Prelude
import Out.PlatformConfig
import Out.MemTypeUtils
import Out.Callbacks
import Out.InterruptRegs

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
open csrop
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
open Splittability
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privileged_ISA_Version
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
open InterruptType
open IllegalVtypeReservedBehavior
open ISA_Format
open HartState
open FflagsDirtyPolicy
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

def SIG_VERSION_OFFSET := 0

def SIG_PLATFORM_OFFSET := 4

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def sig_load (access : (MemoryAccessType mem_payload)) (addr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  let .Physaddr paddr := addr
  let VERSION := 0x00010000#32
  if (((width != 4) || ((Sail.BitVec.extractLsb paddr 1 0) != (zeros (n := ((1 -i 0) +i 1))))) : Bool)
  then (pure (Err (addr, (← (accessFaultFromAccessType access)))))
  else
    (do
      if ((paddr == (BitVec.addInt plat_sig_base SIG_VERSION_OFFSET)) : Bool)
      then (pure (Ok VERSION))
      else
        (do
          if ((paddr == (BitVec.addInt plat_sig_base SIG_PLATFORM_OFFSET)) : Bool)
          then (pure (Ok (zeros (n := (8 *i width)))))
          else (pure (Err (addr, (← (accessFaultFromAccessType access)))))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def sig_store (addr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  let .Physaddr paddr := addr
  if (((width != 4) || ((Sail.BitVec.extractLsb paddr 1 0) != (zeros (n := ((1 -i 0) +i 1))))) : Bool)
  then (pure (Err (addr, (E_SAMO_Access_Fault ()))))
  else
    (do
      if ((paddr == (BitVec.addInt plat_sig_base SIG_VERSION_OFFSET)) : Bool)
      then (pure (Ok true))
      else
        (do
          if ((paddr == (BitVec.addInt plat_sig_base SIG_PLATFORM_OFFSET)) : Bool)
          then
            (do
              let value := (BitVec.access data 31)
              let data := (Mk_Minterrupts (zero_extend (m := 64) data))
              if (((Sail.BitVec.extractLsb
                     (_update_Minterrupts_SSI
                       (_update_Minterrupts_MSI
                         (_update_Minterrupts_SEI (_update_Minterrupts_MEI data 0#1) 0#1) 0#1) 0#1)
                     30 0) != (zeros (n := ((30 -i 0) +i 1)))) : Bool)
              then (pure (Err (addr, (E_SAMO_Access_Fault ()))))
              else
                (do
                  if (((_get_Minterrupts_MEI data) == 1#1) : Bool)
                  then writeReg sig_meip value
                  else (pure ())
                  if (((_get_Minterrupts_SEI data) == 1#1) : Bool)
                  then writeReg sig_seip value
                  else (pure ())
                  if (((_get_Minterrupts_MSI data) == 1#1) : Bool)
                  then writeReg mip (Sail.BitVec.updateSubrange (← readReg mip) 3 3 value)
                  else (pure ())
                  if ((((_get_Minterrupts_SSI data) == 1#1) && (← (currentlyEnabled Ext_S))) : Bool)
                  then writeReg mip (Sail.BitVec.updateSubrange (← readReg mip) 1 1 value)
                  else (pure ())
                  (csr_name_write_callback "mip" (← (read_mip IncludePlatformInterrupts)))
                  (pure (Ok true))))
          else (pure (Err (addr, (E_SAMO_Access_Fault ()))))))

