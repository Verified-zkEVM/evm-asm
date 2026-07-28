import Sail
import Out.Defs
import Out.Specialization
import Out.FakeReal
import Out.RiscvExtras

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

def undefined_PM_Ext (_ : Unit) : SailM PM_Ext := do
  (internal_pick [PM_SSNPM, PM_SMNPM, PM_SMMPM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def PM_Ext_of_num (arg_ : Nat) : PM_Ext :=
  match arg_ with
  | 0 => PM_SSNPM
  | 1 => PM_SMNPM
  | _ => PM_SMMPM

def num_of_PM_Ext (arg_ : PM_Ext) : Int :=
  match arg_ with
  | .PM_SSNPM => 0
  | .PM_SMNPM => 1
  | .PM_SMMPM => 2

def undefined_PointerMaskingMode (_ : Unit) : SailM PointerMaskingMode := do
  (internal_pick [PMM_Disabled, PMM_Reserved, PMM_PMLEN_7, PMM_PMLEN_16])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PointerMaskingMode_of_num (arg_ : Nat) : PointerMaskingMode :=
  match arg_ with
  | 0 => PMM_Disabled
  | 1 => PMM_Reserved
  | 2 => PMM_PMLEN_7
  | _ => PMM_PMLEN_16

def num_of_PointerMaskingMode (arg_ : PointerMaskingMode) : Int :=
  match arg_ with
  | .PMM_Disabled => 0
  | .PMM_Reserved => 1
  | .PMM_PMLEN_7 => 2
  | .PMM_PMLEN_16 => 3

def pmm_mode_forwards (arg_ : PointerMaskingMode) : (BitVec 2) :=
  match arg_ with
  | .PMM_Disabled => 0b00#2
  | .PMM_Reserved => 0b01#2
  | .PMM_PMLEN_7 => 0b10#2
  | .PMM_PMLEN_16 => 0b11#2

def pmm_mode_backwards (arg_ : (BitVec 2)) : PointerMaskingMode :=
  match arg_ with
  | 0b00 => PMM_Disabled
  | 0b01 => PMM_Reserved
  | 0b10 => PMM_PMLEN_7
  | _ => PMM_PMLEN_16

def pmm_mode_forwards_matches (arg_ : PointerMaskingMode) : Bool :=
  match arg_ with
  | .PMM_Disabled => true
  | .PMM_Reserved => true
  | .PMM_PMLEN_7 => true
  | .PMM_PMLEN_16 => true

def pmm_mode_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def is_supported_pmm (ext : PM_Ext) (pmm : PointerMaskingMode) : Bool :=
  match (ext, pmm) with
  | (_, .PMM_Disabled) => true
  | (_, .PMM_Reserved) => false
  | (.PM_SSNPM, .PMM_PMLEN_7) => true
  | (.PM_SSNPM, .PMM_PMLEN_16) => true
  | (.PM_SMMPM, .PMM_PMLEN_7) => true
  | (.PM_SMMPM, .PMM_PMLEN_16) => true
  | (.PM_SMNPM, .PMM_PMLEN_7) => true
  | (.PM_SMNPM, .PMM_PMLEN_16) => true

