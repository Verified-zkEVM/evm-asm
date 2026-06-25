import Out.PlatformConfig

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

def undefined_CountSmcntrpmf (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CountSmcntrpmf (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CountSmcntrpmf_MINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_CountSmcntrpmf_MINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _set_CountSmcntrpmf_MINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_MINH r v)

def _get_CountSmcntrpmf_SINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_CountSmcntrpmf_SINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _set_CountSmcntrpmf_SINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_SINH r v)

def _get_CountSmcntrpmf_UINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_CountSmcntrpmf_UINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _set_CountSmcntrpmf_UINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_UINH r v)

def _get_CountSmcntrpmf_VSINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_CountSmcntrpmf_VSINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _set_CountSmcntrpmf_VSINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_VSINH r v)

def _get_CountSmcntrpmf_VUINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_CountSmcntrpmf_VUINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _set_CountSmcntrpmf_VUINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_VUINH r v)

def legalize_smcntrpmf (c : (BitVec 64)) (value : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_CountSmcntrpmf value)
  (pure (_update_CountSmcntrpmf_VUINH
      (_update_CountSmcntrpmf_VSINH
        (_update_CountSmcntrpmf_UINH
          (_update_CountSmcntrpmf_SINH (_update_CountSmcntrpmf_MINH c (_get_CountSmcntrpmf_MINH v))
            (← do
              if ((← (currentlyEnabled Ext_S)) : Bool)
              then (pure (_get_CountSmcntrpmf_SINH v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_U)) : Bool)
            then (pure (_get_CountSmcntrpmf_UINH v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_H)) : Bool)
          then (pure (_get_CountSmcntrpmf_VSINH v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_H)) : Bool)
        then (pure (_get_CountSmcntrpmf_VUINH v))
        else (pure 0#1))))

def counter_priv_filter_bit (reg : (BitVec 64)) (priv : Privilege) : (BitVec 1) :=
  match priv with
  | .Machine => (_get_CountSmcntrpmf_MINH reg)
  | .Supervisor => (_get_CountSmcntrpmf_SINH reg)
  | .VirtualSupervisor => (_get_CountSmcntrpmf_VSINH reg)
  | .User => (_get_CountSmcntrpmf_UINH reg)
  | .VirtualUser => (_get_CountSmcntrpmf_VUINH reg)

