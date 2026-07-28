import Out.Flow
import Out.Prelude
import Out.Errors
import Out.MemAddrtype
import Out.PlatformConfig
import Out.Types
import Out.Regs

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

def undefined_Misa (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_Misa_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Misa_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PTE_Flags_A (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_Pmpcfg_ent_A (v : (BitVec 8)) (x : (BitVec 2)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def _set_Misa_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_A r v)

def _get_PTE_Flags_A (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_Pmpcfg_ent_A (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)

def _set_PTE_Flags_A (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_A r v)

def _set_Pmpcfg_ent_A (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_A r v)

def _get_Misa_B (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Misa_B (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Misa_B (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_B r v)

def _update_Misa_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Hstateen0_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_Mstateen0_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_Sstateen0_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_C r v)

def _get_Hstateen0_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_Mstateen0_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_Sstateen0_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_Hstateen0_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_C r v)

def _set_Mstateen0_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_C r v)

def _set_Sstateen0_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen0_C r v)

def _update_Misa_D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PTE_Flags_D (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_D r v)

def _get_PTE_Flags_D (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_PTE_Flags_D (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_D r v)

def _get_Misa_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_Misa_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Misa_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_E r v)

def _update_Misa_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Misa_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_F r v)

def _get_Misa_G (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Misa_G (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PTE_Flags_G (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Misa_G (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_G r v)

def _get_PTE_Flags_G (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_PTE_Flags_G (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_G r v)

def _get_Misa_H (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Misa_H (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_H (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_H r v)

def _get_Misa_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Misa_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Misa_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_I r v)

def _get_Misa_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Misa_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Misa_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_J r v)

def _get_Misa_K (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_Misa_K (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _set_Misa_K (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_K r v)

def _get_Misa_L (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Misa_L (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_Pmpcfg_ent_L (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_L (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_L r v)

def _get_Pmpcfg_ent_L (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_Pmpcfg_ent_L (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_L r v)

def _update_Misa_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_Misa_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_M r v)

def _get_Misa_MXL (v : (BitVec 64)) : (BitVec (64 - 1 - (64 - 2) + 1)) :=
  (Sail.BitVec.extractLsb v (64 -i 1) (64 -i 2))

def _set_Misa_MXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 1 - (64 - 2) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_MXL r v)

def _get_Misa_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_Misa_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PTE_Ext_N (v : (BitVec 10)) (x : (BitVec 1)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Misa_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_N r v)

def _get_PTE_Ext_N (v : (BitVec 10)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _set_PTE_Ext_N (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_N r v)

def _get_Misa_O (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_Misa_O (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _set_Misa_O (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_O r v)

def _get_Misa_P (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_Misa_P (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _set_Misa_P (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_P r v)

def _get_Misa_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_Misa_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _set_Misa_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Q r v)

def _get_Misa_R (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_Misa_R (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PTE_Flags_R (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Pmpcfg_ent_R (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_R (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_R r v)

def _get_PTE_Flags_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_Pmpcfg_ent_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_PTE_Flags_R (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_R r v)

def _set_Pmpcfg_ent_R (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_R r v)

def _update_Misa_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Misa_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_S r v)

def _get_Misa_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Misa_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Misa_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_T r v)

def _update_Misa_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PTE_Flags_U (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Misa_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_U r v)

def _get_PTE_Flags_U (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _set_PTE_Flags_U (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_U r v)

def _update_Misa_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PTE_Flags_V (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_V r v)

def _get_PTE_Flags_V (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_PTE_Flags_V (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_V r v)

def _get_Misa_W (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Misa_W (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PTE_Flags_W (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Pmpcfg_ent_W (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Misa_W (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_W r v)

def _get_PTE_Flags_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Pmpcfg_ent_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_PTE_Flags_W (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_W r v)

def _set_Pmpcfg_ent_W (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_W r v)

def _get_Misa_X (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_Misa_X (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PTE_Flags_X (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_Pmpcfg_ent_X (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Misa_X (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_X r v)

def _get_PTE_Flags_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Pmpcfg_ent_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_PTE_Flags_X (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_X r v)

def _set_Pmpcfg_ent_X (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_X r v)

def _get_Misa_Y (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_Misa_Y (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _set_Misa_Y (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Y r v)

def _get_Misa_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_Misa_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _set_Misa_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Z r v)

def sys_enable_writable_misa : Bool := true

def sys_writable_hpm_counters : (BitVec 32) := 0b11111111111111111111111111111111#32

def ext_veto_disable_C (_ : Unit) : Bool :=
  false

def legalize_misa (m : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Misa v)
  if (((not sys_enable_writable_misa) || (((_get_Misa_C v) == 0#1) && (((BitVec.access
               (← readReg nextPC) 1) == 1#1) || (ext_veto_disable_C ())))) : Bool)
  then (pure m)
  else
    (pure (_update_Misa_V
        (_update_Misa_U
          (_update_Misa_S
            (_update_Misa_M
              (_update_Misa_E
                (_update_Misa_I
                  (_update_Misa_H
                    (_update_Misa_F
                      (_update_Misa_D
                        (_update_Misa_C
                          (_update_Misa_B
                            (_update_Misa_A m
                              (if ((hartSupports Ext_A) : Bool)
                              then (_get_Misa_A v)
                              else 0#1))
                            (if ((hartSupports Ext_B) : Bool)
                            then (_get_Misa_B v)
                            else 0#1))
                          (if ((hartSupports Ext_C) : Bool)
                          then (_get_Misa_C v)
                          else 0#1))
                        (if (((hartSupports Ext_D) && ((_get_Misa_F v) == 1#1)) : Bool)
                        then (_get_Misa_D v)
                        else 0#1))
                      (if ((hartSupports Ext_F) : Bool)
                      then (_get_Misa_F v)
                      else 0#1))
                    (if ((hartSupports Ext_H) : Bool)
                    then (_get_Misa_H v)
                    else 0#1)) (bool_to_bit (not base_E_enabled))) (bool_to_bit base_E_enabled))
              (if ((hartSupports Ext_M) : Bool)
              then (_get_Misa_M v)
              else 0#1))
            (if (((hartSupports Ext_S) && ((_get_Misa_U v) == 1#1)) : Bool)
            then (_get_Misa_S v)
            else 0#1))
          (if ((hartSupports Ext_U) : Bool)
          then (_get_Misa_U v)
          else 0#1))
        (if (((hartSupports Ext_V) && (((_get_Misa_F v) == 1#1) && ((_get_Misa_D v) == 1#1))) : Bool)
        then (_get_Misa_V v)
        else 0#1)))

def lowest_supported_privLevel (_ : Unit) : SailM Privilege := do
  if ((← (currentlyEnabled Ext_U)) : Bool)
  then (pure User)
  else (pure Machine)

def have_nominal_privLevel (priv : (BitVec 2)) : SailM Bool := do
  match priv with
  | 0b00 => (currentlyEnabled Ext_U)
  | 0b01 => (currentlyEnabled Ext_S)
  | 0b10 => (pure false)
  | _ => (pure true)

def undefined_Mstatus (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _update_Mstatus_FS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 13 x)

def _update_Sstatus_FS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 13 x)

def _set_Mstatus_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_FS r v)

def _get_Sstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _set_Sstatus_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_FS r v)

def _get_Mstatus_MBE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_Mstatus_MBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _set_Mstatus_MBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MBE r v)

def _get_Mstatus_MIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Mstatus_MIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Mstatus_MIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MIE r v)

def _get_Mstatus_MPELP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_Mstatus_MPELP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _set_Mstatus_MPELP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPELP r v)

def _get_Mstatus_MPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Mstatus_MPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Mstatus_MPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPIE r v)

def _get_Mstatus_MPP (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 12 11)

def _update_Mstatus_MPP (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 11 x)

def _set_Mstatus_MPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPP r v)

def _get_Mstatus_MPRV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_Mstatus_MPRV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _set_Mstatus_MPRV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPRV r v)

def _get_Mstatus_MXR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Mstatus_MXR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_Sstatus_MXR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Mstatus_MXR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MXR r v)

def _get_Sstatus_MXR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _set_Sstatus_MXR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_MXR r v)

def _get_Mstatus_SBE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_Mstatus_SBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _set_Mstatus_SBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SBE r v)

def _get_Mstatus_SD (v : (BitVec 64)) : (BitVec (64 - 1 - (64 - 1) + 1)) :=
  (Sail.BitVec.extractLsb v (64 -i 1) (64 -i 1))

def _update_Mstatus_SD (v : (BitVec 64)) (x : (BitVec (64 - 1 - (64 - 1) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) (64 -i 1) x)

def _update_Sstatus_SD (v : (BitVec 64)) (x : (BitVec (64 - 1 - (64 - 1) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) (64 -i 1) x)

def _set_Mstatus_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 1 - (64 - 1) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SD r v)

def _get_Sstatus_SD (v : (BitVec 64)) : (BitVec (64 - 1 - (64 - 1) + 1)) :=
  (Sail.BitVec.extractLsb v (64 -i 1) (64 -i 1))

def _set_Sstatus_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 1 - (64 - 1) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SD r v)

def _get_Mstatus_SIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Mstatus_SIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Sstatus_SIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Mstatus_SIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SIE r v)

def _get_Sstatus_SIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_Sstatus_SIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SIE r v)

def _get_Mstatus_SPELP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_Mstatus_SPELP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_Sstatus_SPELP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _set_Mstatus_SPELP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPELP r v)

def _get_Sstatus_SPELP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _set_Sstatus_SPELP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPELP r v)

def _get_Mstatus_SPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Mstatus_SPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_Sstatus_SPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Mstatus_SPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPIE r v)

def _get_Sstatus_SPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_Sstatus_SPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPIE r v)

def _get_Mstatus_SPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Mstatus_SPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_Sstatus_SPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Mstatus_SPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPP r v)

def _get_Sstatus_SPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _set_Sstatus_SPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPP r v)

def _get_Mstatus_SUM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_Mstatus_SUM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_Sstatus_SUM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Mstatus_SUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SUM r v)

def _get_Sstatus_SUM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _set_Sstatus_SUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SUM r v)

def _get_Mstatus_SXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 35 34)

def _set_Mstatus_SXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SXL r v)

def _get_Mstatus_TSR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Mstatus_TSR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _set_Mstatus_TSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TSR r v)

def _get_Mstatus_TVM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_Mstatus_TVM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _set_Mstatus_TVM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TVM r v)

def _get_Mstatus_TW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_Mstatus_TW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _set_Mstatus_TW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TW r v)

def _get_Mstatus_UXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _update_Sstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _set_Mstatus_UXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_UXL r v)

def _get_Sstatus_UXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _set_Sstatus_UXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_UXL r v)

def _update_Mstatus_VS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 9 x)

def _update_Sstatus_VS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 9 x)

def _set_Mstatus_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_VS r v)

def _get_Sstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def _set_Sstatus_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_VS r v)

def _get_Mstatus_XS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 16 15)

def _update_Mstatus_XS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 15 x)

def _update_Sstatus_XS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 15 x)

def _set_Mstatus_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_XS r v)

def _get_Sstatus_XS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 16 15)

def _set_Sstatus_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_XS r v)

def legalize_mstatus (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Mstatus v)
  let o ← do
    (pure (_update_Mstatus_SIE
        (_update_Mstatus_MIE
          (_update_Mstatus_SPIE
            (_update_Mstatus_MPIE
              (_update_Mstatus_SPP
                (_update_Mstatus_MPP
                  (_update_Mstatus_VS
                    (_update_Mstatus_FS
                      (_update_Mstatus_XS
                        (_update_Mstatus_MPRV
                          (_update_Mstatus_SUM
                            (_update_Mstatus_MXR
                              (_update_Mstatus_TVM
                                (_update_Mstatus_TW
                                  (_update_Mstatus_TSR
                                    (_update_Mstatus_SPELP
                                      (_update_Mstatus_MPELP o
                                        (if ((hartSupports Ext_Zicfilp) : Bool)
                                        then (_get_Mstatus_MPELP v)
                                        else 0#1))
                                      (if ((hartSupports Ext_Zicfilp) : Bool)
                                      then (_get_Mstatus_SPELP v)
                                      else 0#1))
                                    (← do
                                      if ((← (currentlyEnabled Ext_S)) : Bool)
                                      then (pure (_get_Mstatus_TSR v))
                                      else (pure 0#1)))
                                  (← do
                                    if ((← (currentlyEnabled Ext_U)) : Bool)
                                    then (pure (_get_Mstatus_TW v))
                                    else (pure 0#1)))
                                (← do
                                  if ((← (currentlyEnabled Ext_S)) : Bool)
                                  then (pure (_get_Mstatus_TVM v))
                                  else (pure 0#1)))
                              (← do
                                if ((← (currentlyEnabled Ext_S)) : Bool)
                                then (pure (_get_Mstatus_MXR v))
                                else (pure 0#1)))
                            (← do
                              if ((← (virtual_memory_supported ())) : Bool)
                              then (pure (_get_Mstatus_SUM v))
                              else (pure 0#1)))
                          (← do
                            if ((← (currentlyEnabled Ext_U)) : Bool)
                            then (pure (_get_Mstatus_MPRV v))
                            else (pure 0#1))) (extStatus_map_forwards Off))
                      (legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS v)))
                    (legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS v)))
                  (← do
                    if ((← (have_nominal_privLevel (_get_Mstatus_MPP v))) : Bool)
                    then (pure (_get_Mstatus_MPP v))
                    else (pure (privLevel_to_bits (← (lowest_supported_privLevel ()))))))
                (← do
                  if ((← (currentlyEnabled Ext_S)) : Bool)
                  then (pure (_get_Mstatus_SPP v))
                  else (pure 0#1))) (_get_Mstatus_MPIE v))
            (← do
              if ((← (currentlyEnabled Ext_S)) : Bool)
              then (pure (_get_Mstatus_SPIE v))
              else (pure 0#1))) (_get_Mstatus_MIE v))
        (← do
          if ((← (currentlyEnabled Ext_S)) : Bool)
          then (pure (_get_Mstatus_SIE v))
          else (pure 0#1))))
  let dirty :=
    (((extStatus_map_backwards (_get_Mstatus_FS o)) == Dirty) || (((extStatus_map_backwards
            (_get_Mstatus_XS o)) == Dirty) || ((extStatus_map_backwards (_get_Mstatus_VS o)) == Dirty)))
  (pure (_update_Mstatus_SD o (bool_to_bit dirty)))

def architecture (priv : Privilege) : SailM Architecture := do
  (architecture_bits_backwards
    (← do
      match priv with
      | .Machine => (pure (_get_Misa_MXL (← readReg misa)))
      | .Supervisor => (pure (_get_Mstatus_SXL (← readReg mstatus)))
      | .User => (pure (_get_Mstatus_UXL (← readReg mstatus)))
      | .VirtualUser =>
        (internal_error "core/sys_regs.sail" 293 "Hypervisor extension not supported")
      | .VirtualSupervisor =>
        (internal_error "core/sys_regs.sail" 294 "Hypervisor extension not supported")))

def in32BitMode (_ : Unit) : SailM Bool := do
  (pure ((← (architecture (← readReg cur_privilege))) == RV32))

def undefined_Seccfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _set_Seccfg_MLPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_MLPE r v)

def _set_Seccfg_PMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_PMM r v)

def _set_MEnvcfg_PMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_PMM r v)

def _set_SEnvcfg_PMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_PMM r v)

def _set_Seccfg_SSEED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_SSEED r v)

def _set_Seccfg_USEED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_USEED r v)

def undefined_MEnvcfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _set_MEnvcfg_ADUE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_ADUE r v)

def _set_MEnvcfg_CBCFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBCFE r v)

def _set_SEnvcfg_CBCFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBCFE r v)

def _set_MEnvcfg_CBIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBIE r v)

def _set_SEnvcfg_CBIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBIE r v)

def _set_MEnvcfg_CBZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBZE r v)

def _set_SEnvcfg_CBZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBZE r v)

def _set_MEnvcfg_FIOM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_FIOM r v)

def _set_SEnvcfg_FIOM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_FIOM r v)

def _set_MEnvcfg_LPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_LPE r v)

def _set_SEnvcfg_LPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_LPE r v)

def _set_MEnvcfg_PBMTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_PBMTE r v)

def _set_MEnvcfg_SSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_SSE r v)

def _set_SEnvcfg_SSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_SSE r v)

def _set_MEnvcfg_STCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_STCE r v)

def undefined_SEnvcfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def is_fiom_active (_ : Unit) : SailM Bool := do
  match (← readReg cur_privilege) with
  | .Machine => (pure false)
  | .Supervisor => (pure ((_get_MEnvcfg_FIOM (← readReg menvcfg)) == 1#1))
  | .User =>
    (pure (((_get_MEnvcfg_FIOM (← readReg menvcfg)) ||| (_get_SEnvcfg_FIOM (← readReg senvcfg))) == 1#1))
  | .VirtualUser => (internal_error "core/sys_regs.sail" 485 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "core/sys_regs.sail" 486 "Hypervisor extension not supported")

def undefined_Mtvec (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Mtvec (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Mtvec_Base (v : (BitVec 64)) : (BitVec (64 - 2)) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 2)

def _update_Mtvec_Base (v : (BitVec 64)) (x : (BitVec (64 - 2))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 2 x)

def _set_Mtvec_Base (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 2))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_Base r v)

def _get_Mtvec_Mode (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_Mtvec_Mode (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_Satp32_Mode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_Satp64_Mode (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _set_Mtvec_Mode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_Mode r v)

def _get_Satp32_Mode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_Satp64_Mode (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _set_Satp32_Mode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_Mode r v)

def _set_Satp64_Mode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_Mode r v)

/-- Type quantifiers: vectored_alignment_exp : Nat, k_ex479027_ : Bool, direct_alignment_exp : Nat, k_ex479025_
  : Bool, 2 ≤ direct_alignment_exp ∧ direct_alignment_exp ≤ 24, 2 ≤ vectored_alignment_exp
  ∧ vectored_alignment_exp ≤ 24 -/
def legalize_tvec (o : (BitVec 64)) (v : (BitVec 64)) (direct_supported : Bool) (direct_alignment_exp : Nat) (vectored_supported : Bool) (vectored_alignment_exp : Nat) : SailM (BitVec 64) := do
  let v := (Mk_Mtvec v)
  let v ← (( do
    match (trapVectorMode_forwards (_get_Mtvec_Mode v)) with
    | .TV_Direct =>
      (if (direct_supported : Bool)
      then (pure v)
      else (pure (_update_Mtvec_Mode v (_get_Mtvec_Mode o))))
    | .TV_Vector =>
      (if (vectored_supported : Bool)
      then (pure v)
      else (pure (_update_Mtvec_Mode v (_get_Mtvec_Mode o))))
    | _ =>
      (do
        match xtvec_mode_reserved_behavior with
        | .Xtvec_Fatal =>
          (reserved_behavior
            (HAppend.hAppend "Tried to write a reserved value ("
              (HAppend.hAppend (Int.repr (BitVec.toNatInt (_get_Mtvec_Mode v)))
                ") to the MODE field of xtvec.")))
        | .Xtvec_Ignore => (pure (_update_Mtvec_Mode v (_get_Mtvec_Mode o)))) ) : SailM Mtvec )
  let base_alignment ← (( do
    match (trapVectorMode_forwards (_get_Mtvec_Mode v)) with
    | .TV_Direct => (pure direct_alignment_exp)
    | .TV_Vector => (pure vectored_alignment_exp)
    | .TV_Reserved => (internal_error "core/sys_regs.sail" 522 "Reserved mode in xtvec.") ) : SailM
    tvec_alignment )
  if ((base_alignment >b 2) : Bool)
  then
    (pure (_update_Mtvec_Base v
        (Sail.BitVec.updateSubrange (_get_Mtvec_Base v) (base_alignment -i 3) 0
          (zeros (n := ((base_alignment -i 3) -i (0 -i 1)))))))
  else (pure v)

def undefined_Mcause (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Mcause (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Mcause_Cause (v : (BitVec 64)) : (BitVec (64 - 1)) :=
  (Sail.BitVec.extractLsb v (64 -i 2) 0)

def _update_Mcause_Cause (v : (BitVec 64)) (x : (BitVec (64 - 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 2) 0 x)

def _set_Mcause_Cause (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_Cause r v)

def _get_Mcause_IsInterrupt (v : (BitVec 64)) : (BitVec (64 - 1 - (64 - 1) + 1)) :=
  (Sail.BitVec.extractLsb v (64 -i 1) (64 -i 1))

def _update_Mcause_IsInterrupt (v : (BitVec 64)) (x : (BitVec (64 - 1 - (64 - 1) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) (64 -i 1) x)

def _set_Mcause_IsInterrupt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 1 - (64 - 1) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_IsInterrupt r v)

def tvec_addr (m : (BitVec 64)) (c : (BitVec 64)) : (Option (BitVec 64)) :=
  let base : xlenbits := ((_get_Mtvec_Base m) +++ 0b00#2)
  match (trapVectorMode_forwards (_get_Mtvec_Mode m)) with
  | .TV_Direct => (some base)
  | .TV_Vector =>
    (if (((_get_Mcause_IsInterrupt c) == 1#1) : Bool)
    then (some (base + ((zero_extend (m := 64) (_get_Mcause_Cause c)) <<< 2)))
    else (some base))
  | .TV_Reserved => none

def legalize_xepc (v : (BitVec 64)) : (BitVec 64) :=
  if ((hartSupports Ext_Zca) : Bool)
  then (BitVec.update v 0 0#1)
  else (Sail.BitVec.updateSubrange v 1 0 (zeros (n := (1 -i (0 -i 1)))))

def align_pc (addr : (BitVec 64)) : SailM (BitVec 64) := do
  if ((← (currentlyEnabled Ext_Zca)) : Bool)
  then (pure (BitVec.update addr 0 0#1))
  else (pure (Sail.BitVec.updateSubrange addr 1 0 (zeros (n := (1 -i (0 -i 1))))))

def undefined_Counteren (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Counteren (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Counteren_CY (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Counteren_CY (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_Counterin_CY (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Counteren_CY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_CY r v)

def _get_Counterin_CY (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_Counterin_CY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_CY r v)

def _get_Counteren_HPM (v : (BitVec 32)) : (BitVec 29) :=
  (Sail.BitVec.extractLsb v 31 3)

def _update_Counteren_HPM (v : (BitVec 32)) (x : (BitVec 29)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 3 x)

def _update_Counterin_HPM (v : (BitVec 32)) (x : (BitVec 29)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 3 x)

def _set_Counteren_HPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 29)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_HPM r v)

def _get_Counterin_HPM (v : (BitVec 32)) : (BitVec 29) :=
  (Sail.BitVec.extractLsb v 31 3)

def _set_Counterin_HPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 29)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_HPM r v)

def _get_Counteren_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Counteren_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Counterin_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Counteren_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_IR r v)

def _get_Counterin_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_Counterin_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_IR r v)

def _get_Counteren_TM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Counteren_TM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Counteren_TM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_TM r v)

def sys_scounteren_writable_bits : (BitVec 32) := 0b11111111111111111111111111111111#32

def legalize_scounteren (_c : (BitVec 32)) (v : (BitVec 64)) : (BitVec 32) :=
  (Mk_Counteren ((Sail.BitVec.extractLsb v 31 0) &&& sys_scounteren_writable_bits))

def sys_mcounteren_writable_bits : (BitVec 32) := 0b11111111111111111111111111111111#32

def legalize_mcounteren (_c : (BitVec 32)) (v : (BitVec 64)) : (BitVec 32) :=
  (Mk_Counteren ((Sail.BitVec.extractLsb v 31 0) &&& sys_mcounteren_writable_bits))

def undefined_Counterin (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Counterin (v : (BitVec 32)) : (BitVec 32) :=
  v

def legalize_mcountinhibit (_c : (BitVec 32)) (v : (BitVec 64)) : (BitVec 32) :=
  let supported_counters := ((Sail.BitVec.extractLsb sys_writable_hpm_counters 31 3) +++ 0b101#3)
  (Mk_Counterin ((Sail.BitVec.extractLsb v 31 0) &&& supported_counters))

def undefined_Sstatus (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Sstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def lower_mstatus (m : (BitVec 64)) : (BitVec 64) :=
  let s := (Mk_Sstatus (zeros (n := 64)))
  (_update_Sstatus_SIE
    (_update_Sstatus_SPIE
      (_update_Sstatus_SPP
        (_update_Sstatus_VS
          (_update_Sstatus_FS
            (_update_Sstatus_XS
              (_update_Sstatus_SUM
                (_update_Sstatus_MXR
                  (_update_Sstatus_SPELP
                    (_update_Sstatus_UXL (_update_Sstatus_SD s (_get_Mstatus_SD m))
                      (_get_Mstatus_UXL m)) (_get_Mstatus_SPELP m)) (_get_Mstatus_MXR m))
                (_get_Mstatus_SUM m)) (_get_Mstatus_XS m)) (_get_Mstatus_FS m)) (_get_Mstatus_VS m))
        (_get_Mstatus_SPP m)) (_get_Mstatus_SPIE m)) (_get_Mstatus_SIE m))

def lift_sstatus (m : (BitVec 64)) (s : (BitVec 64)) : (BitVec 64) :=
  let dirty :=
    (((extStatus_map_backwards (_get_Sstatus_FS s)) == Dirty) || (((extStatus_map_backwards
            (_get_Sstatus_XS s)) == Dirty) || ((extStatus_map_backwards (_get_Sstatus_VS s)) == Dirty)))
  (_update_Mstatus_SIE
    (_update_Mstatus_SPIE
      (_update_Mstatus_SPP
        (_update_Mstatus_VS
          (_update_Mstatus_FS
            (_update_Mstatus_XS
              (_update_Mstatus_SUM
                (_update_Mstatus_MXR
                  (_update_Mstatus_SPELP
                    (_update_Mstatus_UXL (_update_Mstatus_SD m (bool_to_bit dirty))
                      (_get_Sstatus_UXL s)) (_get_Sstatus_SPELP s)) (_get_Sstatus_MXR s))
                (_get_Sstatus_SUM s)) (_get_Sstatus_XS s)) (_get_Sstatus_FS s)) (_get_Sstatus_VS s))
        (_get_Sstatus_SPP s)) (_get_Sstatus_SPIE s)) (_get_Sstatus_SIE s))

def legalize_sstatus (m : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  (legalize_mstatus m (lift_sstatus m (Mk_Sstatus (zero_extend (m := 64) v))))

def undefined_Satp64 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Satp64 (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Satp64_Asid (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 59 44)

def _update_Satp64_Asid (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 44 x)

def _update_Satp32_Asid (v : (BitVec 32)) (x : (BitVec 9)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 22 x)

def _set_Satp64_Asid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_Asid r v)

def _get_Satp32_Asid (v : (BitVec 32)) : (BitVec 9) :=
  (Sail.BitVec.extractLsb v 30 22)

def _set_Satp32_Asid (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 9)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_Asid r v)

def _get_Satp64_PPN (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 43 0)

def _update_Satp64_PPN (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 0 x)

def _update_Satp32_PPN (v : (BitVec 32)) (x : (BitVec 22)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 0 x)

def _set_Satp64_PPN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_PPN r v)

def _get_Satp32_PPN (v : (BitVec 32)) : (BitVec 22) :=
  (Sail.BitVec.extractLsb v 21 0)

def _set_Satp32_PPN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 22)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_PPN r v)

def undefined_Satp32 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Satp32 (v : (BitVec 32)) : (BitVec 32) :=
  v

def legalize_satp (arch : Architecture) (prev_value : (BitVec 64)) (written_value : (BitVec 64)) : SailM (BitVec 64) := do
  let s := (Mk_Satp64 written_value)
  let s :=
    (_update_Satp64_PPN s
      (zero_extend (m := 44)
        (Sail.BitVec.extractLsb (_get_Satp64_PPN s)
          ((Min.min (physaddr_bits -i pagesize_bits) 44) -i 1) 0)))
  match (satpMode_of_bits arch (_get_Satp64_Mode s)) with
  | none => (pure prev_value)
  | .some Sv_mode =>
    (do
      match Sv_mode with
      | .Bare =>
        (do
          if ((← (currentlyEnabled Ext_Svbare)) : Bool)
          then (pure s)
          else (pure prev_value))
      | .Sv39 =>
        (do
          if ((← (currentlyEnabled Ext_Sv39)) : Bool)
          then (pure s)
          else (pure prev_value))
      | .Sv48 =>
        (do
          if ((← (currentlyEnabled Ext_Sv48)) : Bool)
          then (pure s)
          else (pure prev_value))
      | .Sv57 =>
        (do
          if ((← (currentlyEnabled Ext_Sv57)) : Bool)
          then (pure s)
          else (pure prev_value))
      | _ => (pure prev_value))

def undefined_FeatureEnabledResult (_ : Unit) : SailM FeatureEnabledResult := do
  (internal_pick [FEATURE_ENABLED, FEATURE_ILLEGAL, FEATURE_VIRTUAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def FeatureEnabledResult_of_num (arg_ : Nat) : FeatureEnabledResult :=
  match arg_ with
  | 0 => FEATURE_ENABLED
  | 1 => FEATURE_ILLEGAL
  | _ => FEATURE_VIRTUAL

def num_of_FeatureEnabledResult (arg_ : FeatureEnabledResult) : Int :=
  match arg_ with
  | .FEATURE_ENABLED => 0
  | .FEATURE_ILLEGAL => 1
  | .FEATURE_VIRTUAL => 2

def feature_enabled_for_priv (p : Privilege) (machine_enable_bit : (BitVec 1)) (supervisor_enable_bit : (BitVec 1)) (hypervisor_enable_bit : (BitVec 1)) : SailM FeatureEnabledResult := do
  match p with
  | .Machine => (pure FEATURE_ENABLED)
  | .Supervisor =>
    (if ((machine_enable_bit == 1#1) : Bool)
    then (pure FEATURE_ENABLED)
    else (pure FEATURE_ILLEGAL))
  | .User =>
    (do
      if (((machine_enable_bit == 1#1) && ((not (← (currentlyEnabled Ext_S))) || (supervisor_enable_bit == 1#1))) : Bool)
      then (pure FEATURE_ENABLED)
      else (pure FEATURE_ILLEGAL))
  | .VirtualSupervisor =>
    (if ((machine_enable_bit == 0#1) : Bool)
    then (pure FEATURE_ILLEGAL)
    else
      (if ((hypervisor_enable_bit == 0#1) : Bool)
      then (pure FEATURE_VIRTUAL)
      else (pure FEATURE_ENABLED)))
  | .VirtualUser =>
    (if ((machine_enable_bit == 0#1) : Bool)
    then (pure FEATURE_ILLEGAL)
    else
      (if (((hypervisor_enable_bit == 0#1) || (supervisor_enable_bit == 0#1)) : Bool)
      then (pure FEATURE_VIRTUAL)
      else (pure FEATURE_ENABLED)))

def feature_enabled_for_priv_bool (p : Privilege) (m : (BitVec 1)) (s : (BitVec 1)) (h : (BitVec 1)) : SailM Bool := do
  (pure ((← (feature_enabled_for_priv p m s h)) == FEATURE_ENABLED))

/-- Type quantifiers: index : Nat, 0 ≤ index ∧ index ≤ 31 -/
def counter_enabled (index : Nat) (priv : Privilege) : SailM Bool := do
  (feature_enabled_for_priv_bool priv (BitVec.access (← readReg mcounteren) index)
    (BitVec.access (← readReg scounteren) index) 0#1)

