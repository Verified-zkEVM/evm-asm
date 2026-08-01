import Out.Prelude
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

def undefined_Minterrupts (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Minterrupts (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Minterrupts_LCOFI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_Minterrupts_LCOFI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_Sinterrupts_LCOFI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _set_Minterrupts_LCOFI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_LCOFI r v)

def _get_Sinterrupts_LCOFI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _set_Sinterrupts_LCOFI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_LCOFI r v)

def _get_Minterrupts_MEI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Minterrupts_MEI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _set_Minterrupts_MEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_MEI r v)

def _get_Minterrupts_MSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Minterrupts_MSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Minterrupts_MSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_MSI r v)

def _get_Minterrupts_MTI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Minterrupts_MTI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Minterrupts_MTI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_MTI r v)

def _get_Minterrupts_SEI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Minterrupts_SEI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_Sinterrupts_SEI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Minterrupts_SEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_SEI r v)

def _get_Sinterrupts_SEI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _set_Sinterrupts_SEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_SEI r v)

def _get_Minterrupts_SGEI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_Minterrupts_SGEI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_Minterrupts_SGEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_SGEI r v)

def _get_Minterrupts_SSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Minterrupts_SSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Sinterrupts_SSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Minterrupts_SSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_SSI r v)

def _get_Sinterrupts_SSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_Sinterrupts_SSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_SSI r v)

def _get_Minterrupts_STI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Minterrupts_STI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_Sinterrupts_STI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Minterrupts_STI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_STI r v)

def _get_Sinterrupts_STI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_Sinterrupts_STI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_STI r v)

def _get_Minterrupts_VSEI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_Minterrupts_VSEI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _set_Minterrupts_VSEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_VSEI r v)

def _get_Minterrupts_VSSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Minterrupts_VSSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Minterrupts_VSSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_VSSI r v)

def _get_Minterrupts_VSTI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Minterrupts_VSTI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_Minterrupts_VSTI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_VSTI r v)

def legalize_mip (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Minterrupts v)
  (pure (_update_Minterrupts_STI
      (_update_Minterrupts_SSI
        (_update_Minterrupts_SEI
          (_update_Minterrupts_LCOFI o
            (← do
              if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
              then (pure (_get_Minterrupts_LCOFI v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_S)) : Bool)
            then (pure (_get_Minterrupts_SEI v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_S)) : Bool)
          then (pure (_get_Minterrupts_SSI v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_S)) : Bool)
        then
          (do
            if (((← (currentlyEnabled Ext_Sstc)) && ((_get_MEnvcfg_STCE (← readReg menvcfg)) == 1#1)) : Bool)
            then (pure (_get_Minterrupts_STI o))
            else (pure (_get_Minterrupts_STI v)))
        else (pure 0#1))))

def legalize_mie (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Minterrupts v)
  (pure (_update_Minterrupts_SSI
      (_update_Minterrupts_STI
        (_update_Minterrupts_SEI
          (_update_Minterrupts_MSI
            (_update_Minterrupts_MTI
              (_update_Minterrupts_MEI
                (_update_Minterrupts_LCOFI o
                  (← do
                    if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                    then (pure (_get_Minterrupts_LCOFI v))
                    else (pure 0#1))) (_get_Minterrupts_MEI v)) (_get_Minterrupts_MTI v))
            (_get_Minterrupts_MSI v))
          (← do
            if ((← (currentlyEnabled Ext_S)) : Bool)
            then (pure (_get_Minterrupts_SEI v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_S)) : Bool)
          then (pure (_get_Minterrupts_STI v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_S)) : Bool)
        then (pure (_get_Minterrupts_SSI v))
        else (pure 0#1))))

def legalize_mideleg (_o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Minterrupts (v &&& plat_mideleg_delegatable_bits))
  (pure (_update_Minterrupts_SSI
      (_update_Minterrupts_STI
        (_update_Minterrupts_SEI
          (_update_Minterrupts_LCOFI v
            (← do
              if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
              then (pure (_get_Minterrupts_LCOFI v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_S)) : Bool)
            then (pure (_get_Minterrupts_SEI v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_S)) : Bool)
          then (pure (_get_Minterrupts_STI v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_S)) : Bool)
        then (pure (_get_Minterrupts_SSI v))
        else (pure 0#1))))

def undefined_Medeleg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Medeleg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Medeleg_Breakpoint (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Medeleg_Breakpoint (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Medeleg_Breakpoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Breakpoint r v)

def _get_Medeleg_Double_Trap (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_Medeleg_Double_Trap (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _set_Medeleg_Double_Trap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Double_Trap r v)

def _get_Medeleg_Fetch_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Medeleg_Fetch_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Medeleg_Fetch_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Access_Fault r v)

def _get_Medeleg_Fetch_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Medeleg_Fetch_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Medeleg_Fetch_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Addr_Align r v)

def _get_Medeleg_Fetch_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_Medeleg_Fetch_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_Medeleg_Fetch_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Page_Fault r v)

def _get_Medeleg_Hardware_Error (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Medeleg_Hardware_Error (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Medeleg_Hardware_Error (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Hardware_Error r v)

def _get_Medeleg_Illegal_Instr (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Medeleg_Illegal_Instr (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Medeleg_Illegal_Instr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Illegal_Instr r v)

def _get_Medeleg_Load_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Medeleg_Load_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Medeleg_Load_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Access_Fault r v)

def _get_Medeleg_Load_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_Medeleg_Load_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Medeleg_Load_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Addr_Align r v)

def _get_Medeleg_Load_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_Medeleg_Load_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _set_Medeleg_Load_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Page_Fault r v)

def _get_Medeleg_MEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Medeleg_MEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _set_Medeleg_MEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_MEnvCall r v)

def _get_Medeleg_SAMO_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Medeleg_SAMO_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Medeleg_SAMO_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Access_Fault r v)

def _get_Medeleg_SAMO_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Medeleg_SAMO_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_Medeleg_SAMO_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Addr_Align r v)

def _get_Medeleg_SAMO_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_Medeleg_SAMO_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _set_Medeleg_SAMO_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Page_Fault r v)

def _get_Medeleg_SEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Medeleg_SEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Medeleg_SEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SEnvCall r v)

def _get_Medeleg_Software_Check (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_Medeleg_Software_Check (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Medeleg_Software_Check (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Software_Check r v)

def _get_Medeleg_UEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Medeleg_UEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Medeleg_UEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_UEnvCall r v)

def legalize_medeleg (_o : (BitVec 64)) (v : (BitVec 64)) : (BitVec 64) :=
  (_update_Medeleg_MEnvCall
    (_update_Medeleg_Double_Trap (Mk_Medeleg (v &&& plat_medeleg_delegatable_bits)) 0#1) 0#1)

def undefined_XipReadType (_ : Unit) : SailM XipReadType := do
  (internal_pick [IncludePlatformInterrupts, ExcludePlatformInterrupts])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def XipReadType_of_num (arg_ : Nat) : XipReadType :=
  match arg_ with
  | 0 => IncludePlatformInterrupts
  | _ => ExcludePlatformInterrupts

def num_of_XipReadType (arg_ : XipReadType) : Int :=
  match arg_ with
  | .IncludePlatformInterrupts => 0
  | .ExcludePlatformInterrupts => 1

def external_interrupts_pending (_ : Unit) : SailM (BitVec 64) := do
  (pure (_update_Minterrupts_SEI
      (_update_Minterrupts_MEI (Mk_Minterrupts (zeros (n := 64))) (← readReg sig_meip))
      (← do
        if ((← (currentlyEnabled Ext_S)) : Bool)
        then readReg sig_seip
        else (pure 0#1))))

def read_mip (read_type : XipReadType) : SailM (BitVec 64) := do
  match read_type with
  | .IncludePlatformInterrupts =>
    (pure (Mk_Minterrupts ((← readReg mip) ||| (← (external_interrupts_pending ())))))
  | .ExcludePlatformInterrupts => readReg mip

def write_mip (value : (BitVec 64)) : SailM Unit := do
  writeReg mip (← (legalize_mip (← readReg mip) value))

def undefined_Sinterrupts (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Sinterrupts (v : (BitVec 64)) : (BitVec 64) :=
  v

def lower_mip (m : (BitVec 64)) (d : (BitVec 64)) : (BitVec 64) :=
  let s : Sinterrupts := (Mk_Sinterrupts (zeros (n := 64)))
  (_update_Sinterrupts_SSI
    (_update_Sinterrupts_STI
      (_update_Sinterrupts_SEI
        (_update_Sinterrupts_LCOFI s ((_get_Minterrupts_LCOFI m) &&& (_get_Minterrupts_LCOFI d)))
        ((_get_Minterrupts_SEI m) &&& (_get_Minterrupts_SEI d)))
      ((_get_Minterrupts_STI m) &&& (_get_Minterrupts_STI d)))
    ((_get_Minterrupts_SSI m) &&& (_get_Minterrupts_SSI d)))

def lower_mie (m : (BitVec 64)) (d : (BitVec 64)) : (BitVec 64) :=
  let s : Sinterrupts := (Mk_Sinterrupts (zeros (n := 64)))
  (_update_Sinterrupts_SSI
    (_update_Sinterrupts_STI
      (_update_Sinterrupts_SEI
        (_update_Sinterrupts_LCOFI s ((_get_Minterrupts_LCOFI m) &&& (_get_Minterrupts_LCOFI d)))
        ((_get_Minterrupts_SEI m) &&& (_get_Minterrupts_SEI d)))
      ((_get_Minterrupts_STI m) &&& (_get_Minterrupts_STI d)))
    ((_get_Minterrupts_SSI m) &&& (_get_Minterrupts_SSI d)))

def lift_sip (o : (BitVec 64)) (d : (BitVec 64)) (s : (BitVec 64)) : (BitVec 64) :=
  (_update_Minterrupts_LCOFI
    (_update_Minterrupts_SSI o
      (if (((_get_Minterrupts_SSI d) == 1#1) : Bool)
      then (_get_Sinterrupts_SSI s)
      else (_get_Minterrupts_SSI o)))
    (if (((_get_Minterrupts_LCOFI d) == 1#1) : Bool)
    then (_get_Sinterrupts_LCOFI s)
    else (_get_Minterrupts_LCOFI o)))

def legalize_sip (m : (BitVec 64)) (d : (BitVec 64)) (v : (BitVec 64)) : (BitVec 64) :=
  (lift_sip m d (Mk_Sinterrupts v))

def read_sip (read_type : XipReadType) : SailM (BitVec 64) := do
  (pure (lower_mip (← (read_mip read_type)) (← readReg mideleg)))

def write_sip (value : (BitVec 64)) : SailM Unit := do
  writeReg mip (legalize_sip (← readReg mip) (← readReg mideleg) value)

def lift_sie (o : (BitVec 64)) (d : (BitVec 64)) (s : (BitVec 64)) : (BitVec 64) :=
  (_update_Minterrupts_LCOFI
    (_update_Minterrupts_SSI
      (_update_Minterrupts_STI
        (_update_Minterrupts_SEI o
          (if (((_get_Minterrupts_SEI d) == 1#1) : Bool)
          then (_get_Sinterrupts_SEI s)
          else (_get_Minterrupts_SEI o)))
        (if (((_get_Minterrupts_STI d) == 1#1) : Bool)
        then (_get_Sinterrupts_STI s)
        else (_get_Minterrupts_STI o)))
      (if (((_get_Minterrupts_SSI d) == 1#1) : Bool)
      then (_get_Sinterrupts_SSI s)
      else (_get_Minterrupts_SSI o)))
    (if (((_get_Minterrupts_LCOFI d) == 1#1) : Bool)
    then (_get_Sinterrupts_LCOFI s)
    else (_get_Minterrupts_LCOFI o)))

def legalize_sie (m : (BitVec 64)) (d : (BitVec 64)) (v : (BitVec 64)) : (BitVec 64) :=
  (lift_sie m d (Mk_Sinterrupts v))

