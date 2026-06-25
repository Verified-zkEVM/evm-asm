import Out.Flow
import Out.Prelude
import Out.PlatformConfig
import Out.Regs
import Out.AddrChecks
import Out.Mem
import Out.Vmem
import Out.FetchRvfi

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

def isRVC (h : (BitVec 16)) : Bool :=
  (not ((Sail.BitVec.extractLsb h 1 0) == 0b11#2))

/-- Type quantifiers: width : Nat, width ∈ {2, 4} -/
def fetch_bytes (fetch_start : (BitVec 64)) (granule_start : (BitVec 64)) (width : Nat) : SailM (FetchBytes_Result width) := SailME.run do
  match (ext_fetch_check_pc fetch_start granule_start) with
  | .some e => SailME.throw ((FetchBytes_Ext_Error e) : (FetchBytes_Result width))
  | none => (pure ())
  let (paddr, pbmt) ← (( do
    match (← (translateAddr (Virtaddr granule_start) (InstructionFetch ()))) with
    | .Err (e, _) => SailME.throw ((FetchBytes_Exception e) : (FetchBytes_Result width))
    | .Ok (paddr, pbmt, _) => (pure (paddr, pbmt)) ) : SailME (FetchBytes_Result width)
    (physaddr × page_based_mem_type) )
  match (← (mem_read (InstructionFetch ()) pbmt paddr width false false false)) with
  | .Err e => (pure (FetchBytes_Exception e))
  | .Ok bytes => (pure (FetchBytes_Success bytes))

def fetch (_ : Unit) : SailM FetchResult := SailME.run do
  if ((get_config_rvfi ()) : Bool)
  then (rvfi_fetch ())
  else
    (do
      match (ext_fetch_check_pc (← readReg PC) (← readReg PC)) with
      | .some e => SailME.throw ((F_Ext_Error e) : FetchResult)
      | none => (pure ())
      if ((((BitVec.access (← readReg PC) 0) != 0#1) || (((BitVec.access (← readReg PC) 1) != 0#1) && (not
               (← (currentlyEnabled Ext_Zca))))) : Bool)
      then (pure (F_Error ((E_Fetch_Addr_Align ()), (← readReg PC))))
      else
        (do
          if (((is_aligned_vaddr (Virtaddr (← readReg PC)) 4) && (← (currentlyEnabled Ext_Ziccif))) : Bool)
          then
            (do
              match (← (fetch_bytes (← readReg PC) (← readReg PC) 4)) with
              | .FetchBytes_Ext_Error e => (pure (F_Ext_Error e))
              | .FetchBytes_Exception e => (pure (F_Error (e, (← readReg PC))))
              | .FetchBytes_Success bytes =>
                (if ((isRVC (Sail.BitVec.extractLsb bytes 15 0)) : Bool)
                then (pure (F_RVC (Sail.BitVec.extractLsb bytes 15 0)))
                else (pure (F_Base bytes))))
          else
            (do
              match (← (fetch_bytes (← readReg PC) (← readReg PC) 2)) with
              | .FetchBytes_Ext_Error e => (pure (F_Ext_Error e))
              | .FetchBytes_Exception e => (pure (F_Error (e, (← readReg PC))))
              | .FetchBytes_Success ilo =>
                (do
                  if ((isRVC ilo) : Bool)
                  then (pure (F_RVC ilo))
                  else
                    (do
                      match (← (fetch_bytes (← readReg PC) (BitVec.addInt (← readReg PC) 2) 2)) with
                      | .FetchBytes_Ext_Error e => (pure (F_Ext_Error e))
                      | .FetchBytes_Exception e =>
                        (pure (F_Error (e, (BitVec.addInt (← readReg PC) 2))))
                      | .FetchBytes_Success ihi => (pure (F_Base (ihi +++ ilo))))))))

