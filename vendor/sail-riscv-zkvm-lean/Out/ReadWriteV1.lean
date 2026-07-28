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

def undefined_Access_variety (_ : Unit) : SailM Access_variety := do
  (internal_pick [AV_plain, AV_exclusive, AV_atomic_rmw])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_variety_of_num (arg_ : Nat) : Access_variety :=
  match arg_ with
  | 0 => AV_plain
  | 1 => AV_exclusive
  | _ => AV_atomic_rmw

def num_of_Access_variety (arg_ : Access_variety) : Int :=
  match arg_ with
  | .AV_plain => 0
  | .AV_exclusive => 1
  | .AV_atomic_rmw => 2

def undefined_Access_strength (_ : Unit) : SailM Access_strength := do
  (internal_pick [AS_normal, AS_rel_or_acq, AS_acq_rcpc])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_strength_of_num (arg_ : Nat) : Access_strength :=
  match arg_ with
  | 0 => AS_normal
  | 1 => AS_rel_or_acq
  | _ => AS_acq_rcpc

def num_of_Access_strength (arg_ : Access_strength) : Int :=
  match arg_ with
  | .AS_normal => 0
  | .AS_rel_or_acq => 1
  | .AS_acq_rcpc => 2

def undefined_Explicit_access_kind (_ : Unit) : SailM Explicit_access_kind := do
  (pure { variety := ← (undefined_Access_variety ())
          strength := ← (undefined_Access_strength ()) })

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_exclusive (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | .AV_exclusive => true
    | _ => false)
  | _ => false

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_ifetch (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_ifetch () => true
  | _ => false

def __monomorphize_reads : Bool := false

def __monomorphize_writes : Bool := false

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_write_request_is_exclusive (request : (Mem_write_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | .AV_exclusive => true
    | _ => false)
  | _ => false

/-- Type quantifiers: x_0 : Nat, x_0 ≥ 0, x_0 ∈ {32, 64} -/
def sail_address_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

