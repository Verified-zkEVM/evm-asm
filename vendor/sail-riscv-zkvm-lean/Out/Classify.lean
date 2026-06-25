import Out.Nan
import Out.Inf
import Out.Sign
import Out.Zero
import Out.Normal

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

def undefined_float_class (_ : Unit) : SailM float_class := do
  (internal_pick
    [float_class_negative_inf, float_class_negative_normal, float_class_negative_subnormal, float_class_negative_zero, float_class_positive_zero, float_class_positive_subnormal, float_class_positive_normal, float_class_positive_inf, float_class_snan, float_class_qnan])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 9 -/
def float_class_of_num (arg_ : Nat) : float_class :=
  match arg_ with
  | 0 => float_class_negative_inf
  | 1 => float_class_negative_normal
  | 2 => float_class_negative_subnormal
  | 3 => float_class_negative_zero
  | 4 => float_class_positive_zero
  | 5 => float_class_positive_subnormal
  | 6 => float_class_positive_normal
  | 7 => float_class_positive_inf
  | 8 => float_class_snan
  | _ => float_class_qnan

def num_of_float_class (arg_ : float_class) : Int :=
  match arg_ with
  | .float_class_negative_inf => 0
  | .float_class_negative_normal => 1
  | .float_class_negative_subnormal => 2
  | .float_class_negative_zero => 3
  | .float_class_positive_zero => 4
  | .float_class_positive_subnormal => 5
  | .float_class_positive_normal => 6
  | .float_class_positive_inf => 7
  | .float_class_snan => 8
  | .float_class_qnan => 9

/-- Type quantifiers: k_ex250036_ : Nat, k_ex250036_ ∈ {16, 32, 64, 128} -/
def float_classify (f : (BitVec k_ex250036_)) : SailM float_class := do
  if ((float_is_snan f) : Bool)
  then (pure float_class_snan)
  else
    (do
      if ((float_is_qnan f) : Bool)
      then (pure float_class_qnan)
      else
        (do
          if ((float_is_zero f) : Bool)
          then
            (if ((float_is_positive f) : Bool)
            then (pure float_class_positive_zero)
            else (pure float_class_negative_zero))
          else
            (do
              if ((float_is_subnormal f) : Bool)
              then
                (if ((float_is_positive f) : Bool)
                then (pure float_class_positive_subnormal)
                else (pure float_class_negative_subnormal))
              else
                (do
                  if ((float_is_normal f) : Bool)
                  then
                    (if ((float_is_positive f) : Bool)
                    then (pure float_class_positive_normal)
                    else (pure float_class_negative_normal))
                  else
                    (do
                      if ((float_is_inf f) : Bool)
                      then
                        (if ((float_is_positive f) : Bool)
                        then (pure float_class_positive_inf)
                        else (pure float_class_negative_inf))
                      else
                        (do
                          assert false "float_classify internal logic error"
                          throw Error.Exit))))))

