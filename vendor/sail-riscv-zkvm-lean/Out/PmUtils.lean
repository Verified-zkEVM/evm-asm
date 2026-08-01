import Out.Flow
import Out.Prelude
import Out.Errors
import Out.PmTypes
import Out.Xlen
import Out.PlatformConfig
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

def get_pmm (eff_privilege : Privilege) : SailM PointerMaskingMode := do
  match eff_privilege with
  | .Machine => (pure (pmm_mode_backwards (_get_Seccfg_PMM (← readReg mseccfg))))
  | .Supervisor => (pure (pmm_mode_backwards (_get_MEnvcfg_PMM (← readReg menvcfg))))
  | .User =>
    (do
      if ((← (currentlyEnabled Ext_S)) : Bool)
      then (pure (pmm_mode_backwards (_get_SEnvcfg_PMM (← (read_senvcfg ())))))
      else (pure (pmm_mode_backwards (_get_MEnvcfg_PMM (← readReg menvcfg)))))
  | .VirtualUser =>
    (internal_error "extensions/pointer_masking/pm_utils.sail" 15
      "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "extensions/pointer_masking/pm_utils.sail" 16
      "Hypervisor extension not supported")

def is_pmm_applicable (access : (MemoryAccessType mem_payload)) (eff_privilege : Privilege) : SailM Bool := do
  (pure ((bne access (InstructionFetch ())) && ((bne access (Load PageTableEntry)) && ((bne access
            (Store PageTableEntry)) && (((eff_privilege == Machine) || ((_get_Mstatus_MXR
                  (← readReg mstatus)) == 0#1)) && (xlen == 64))))))

def get_pmlen (access : (MemoryAccessType mem_payload)) (eff_privilege : Privilege) : SailM Int := do
  if ((← (is_pmm_applicable access eff_privilege)) : Bool)
  then
    (do
      match (← (get_pmm eff_privilege)) with
      | .PMM_Disabled => (pure 0)
      | .PMM_PMLEN_7 => (pure 7)
      | .PMM_PMLEN_16 => (pure 16)
      | .PMM_Reserved =>
        (do
          (internal_error "extensions/pointer_masking/pm_utils.sail" 32
            "Invalid pointer masking mode")
          (pure 0)))
  else (pure 0)

/-- Type quantifiers: pmlen : Nat, pmlen ∈ {0, 7, 16} -/
def pm_transform_VA (typ_0 : virtaddr) (pmlen : Nat) : virtaddr :=
  let .Virtaddr effective_address : virtaddr := typ_0
  (Virtaddr
    (sign_extend (m := 64) (Sail.BitVec.extractLsb effective_address ((xlen -i pmlen) -i 1) 0)))

/-- Type quantifiers: pmlen : Nat, pmlen ∈ {0, 7, 16} -/
def pm_transform_PA (typ_0 : virtaddr) (pmlen : Nat) : virtaddr :=
  let .Virtaddr effective_address : virtaddr := typ_0
  (Virtaddr
    (zero_extend (m := 64) (Sail.BitVec.extractLsb effective_address ((xlen -i pmlen) -i 1) 0)))

