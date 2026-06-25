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

/-- Type quantifiers: k_ex248634_ : Bool, k_ex248633_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

def num_of_IsaVersion (arg_ : IsaVersion) : Int :=
  match arg_ with
  | .Isa_20191213 => 0
  | .Isa_Draft_20211102 => 1
  | .Isa_20211203 => 2
  | .Isa_20240411 => 3
  | .Isa_Latest => 4

def isa_version_le (x : IsaVersion) (y : IsaVersion) : Bool :=
  ((num_of_IsaVersion x) ≤b (num_of_IsaVersion y))

def num_of_AtomicSupport (arg_ : AtomicSupport) : Int :=
  match arg_ with
  | .AMONone => 0
  | .AMOSwap => 1
  | .AMOLogical => 2
  | .AMOArithmetic => 3
  | .AMOCASW => 4
  | .AMOCASD => 5
  | .AMOCASQ => 6

def pma_atomicity_support_le (x : AtomicSupport) (y : AtomicSupport) : Bool :=
  ((num_of_AtomicSupport x) ≤b (num_of_AtomicSupport y))

def num_of_vector_support (arg_ : vector_support) : Int :=
  match arg_ with
  | .Disabled => 0
  | .Integer => 1
  | .Float_single => 2
  | .Float_double => 3
  | .Full => 4

def vector_support_le (x : vector_support) (y : vector_support) : Bool :=
  ((num_of_vector_support x) ≤b (num_of_vector_support y))

def isa_version_lt (x : IsaVersion) (y : IsaVersion) : Bool :=
  ((num_of_IsaVersion x) <b (num_of_IsaVersion y))

def pma_atomicity_support_lt (x : AtomicSupport) (y : AtomicSupport) : Bool :=
  ((num_of_AtomicSupport x) <b (num_of_AtomicSupport y))

def vector_support_lt (x : vector_support) (y : vector_support) : Bool :=
  ((num_of_vector_support x) <b (num_of_vector_support y))

def isa_version_ge (x : IsaVersion) (y : IsaVersion) : Bool :=
  ((num_of_IsaVersion x) ≥b (num_of_IsaVersion y))

def pma_atomicity_support_ge (x : AtomicSupport) (y : AtomicSupport) : Bool :=
  ((num_of_AtomicSupport x) ≥b (num_of_AtomicSupport y))

def vector_support_ge (x : vector_support) (y : vector_support) : Bool :=
  ((num_of_vector_support x) ≥b (num_of_vector_support y))

def isa_version_gt (x : IsaVersion) (y : IsaVersion) : Bool :=
  ((num_of_IsaVersion x) >b (num_of_IsaVersion y))

def pma_atomicity_support_gt (x : AtomicSupport) (y : AtomicSupport) : Bool :=
  ((num_of_AtomicSupport x) >b (num_of_AtomicSupport y))

def vector_support_gt (x : vector_support) (y : vector_support) : Bool :=
  ((num_of_vector_support x) >b (num_of_vector_support y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

