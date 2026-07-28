import Out.Errors
import Out.PlatformConfig
import Out.Types
import Out.SysRegs

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

def ext_check_xret_priv (_p : Privilege) : Bool :=
  true

def ext_fail_xret_priv (_ : Unit) : Unit :=
  ()

def handle_trap_extension (_p : Privilege) (_pc : (BitVec 64)) (_u : (Option Unit)) : Unit :=
  ()

def prepare_trap_vector (p : Privilege) (cause : (BitVec 64)) : SailM (BitVec 64) := do
  let tvec ← (( do
    match p with
    | .Machine => readReg mtvec
    | .Supervisor => readReg stvec
    | .User => (internal_error "exceptions/sys_exceptions.sail" 25 "Invalid privilege level")
    | .VirtualUser =>
      (internal_error "exceptions/sys_exceptions.sail" 26 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "exceptions/sys_exceptions.sail" 27 "Hypervisor extension not supported") ) :
    SailM Mtvec )
  match (tvec_addr tvec cause) with
  | .some epc => (pure epc)
  | none => (internal_error "exceptions/sys_exceptions.sail" 31 "Invalid tvec mode")

def get_xepc (p : Privilege) : SailM (BitVec 64) := do
  match p with
  | .Machine => (align_pc (← readReg mepc))
  | .Supervisor => (align_pc (← readReg sepc))
  | .User => (internal_error "exceptions/sys_exceptions.sail" 45 "Invalid privilege level")
  | .VirtualUser =>
    (internal_error "exceptions/sys_exceptions.sail" 46 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "exceptions/sys_exceptions.sail" 47 "Hypervisor extension not supported")

def set_xepc (p : Privilege) (value : (BitVec 64)) : SailM (BitVec 64) := do
  let target := (legalize_xepc value)
  match p with
  | .Machine => writeReg mepc target
  | .Supervisor => writeReg sepc target
  | .User => (internal_error "exceptions/sys_exceptions.sail" 55 "Invalid privilege level")
  | .VirtualUser =>
    (internal_error "exceptions/sys_exceptions.sail" 56 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "exceptions/sys_exceptions.sail" 57 "Hypervisor extension not supported")
  (pure target)

def prepare_xret_target (p : Privilege) : SailM (BitVec 64) := do
  (get_xepc p)

def get_mtvec (_ : Unit) : SailM (BitVec 64) := do
  readReg mtvec

def get_stvec (_ : Unit) : SailM (BitVec 64) := do
  readReg stvec

def set_mtvec (value : (BitVec 64)) : SailM (BitVec 64) := do
  writeReg mtvec (← (legalize_tvec (← readReg mtvec) value plat_mtvec_direct_mode_supported
      plat_mtvec_direct_base_alignment_exp plat_mtvec_vectored_mode_supported
      plat_mtvec_vectored_base_alignment_exp))
  readReg mtvec

def set_stvec (value : (BitVec 64)) : SailM (BitVec 64) := do
  writeReg stvec (← (legalize_tvec (← readReg stvec) value plat_stvec_direct_mode_supported 2
      plat_stvec_vectored_mode_supported plat_stvec_vectored_base_alignment_exp))
  readReg stvec

def reset_tvecs (_ : Unit) : SailM Unit := do
  if (plat_mtvec_direct_mode_supported : Bool)
  then
    writeReg mtvec (Sail.BitVec.updateSubrange (← readReg mtvec) 1 0
      (trapVectorMode_backwards TV_Direct))
  else
    (do
      if (plat_mtvec_vectored_mode_supported : Bool)
      then
        writeReg mtvec (Sail.BitVec.updateSubrange (← readReg mtvec) 1 0
          (trapVectorMode_backwards TV_Vector))
      else (pure ()))
  if (plat_stvec_direct_mode_supported : Bool)
  then
    writeReg stvec (Sail.BitVec.updateSubrange (← readReg stvec) 1 0
      (trapVectorMode_backwards TV_Direct))
  else
    (do
      if (plat_stvec_vectored_mode_supported : Bool)
      then
        writeReg stvec (Sail.BitVec.updateSubrange (← readReg stvec) 1 0
          (trapVectorMode_backwards TV_Vector))
      else (pure ()))

