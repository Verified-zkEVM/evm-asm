import Out.Prelude

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

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 ≤ k_n ∧ k_n ≤ 64 -/
def range_subset (a_begin : (BitVec k_n)) (a_size : (BitVec k_n)) (b_begin : (BitVec k_n)) (b_size : (BitVec k_n)) : Bool :=
  let a_end := ((a_begin + a_size) - b_begin)
  let b_end := ((b_begin + b_size) - b_begin)
  let a_begin := (a_begin - b_begin)
  ((zopz0zIzJ_u a_begin b_end) && ((zopz0zIzJ_u a_end b_end) && (zopz0zIzJ_u a_begin a_end)))

def test_range_subset (_ : Unit) : SailM Unit := do
  assert (range_subset 0x0#4 0x0#4 0x0#4 0x0#4) "core/range_util.sail:27.41-27.42"
  assert (range_subset 0x1#4 0x0#4 0x1#4 0x0#4) "core/range_util.sail:28.41-28.42"
  assert (range_subset 0x0#4 0x0#4 0x0#4 0x1#4) "core/range_util.sail:29.41-29.42"
  assert (range_subset 0x1#4 0x0#4 0x0#4 0x1#4) "core/range_util.sail:30.41-30.42"
  assert (range_subset 0x8#4 0xC#4 0x8#4 0xC#4) "core/range_util.sail:31.41-31.42"
  assert (not (range_subset 0x8#4 0xC#4 0x9#4 0xC#4)) "core/range_util.sail:32.46-32.47"
  assert (not (range_subset 0x8#4 0xC#4 0x8#4 0xB#4)) "core/range_util.sail:33.46-33.47"
  assert (not (range_subset 0x3E#8 0xE0#8 0xC1#8 0x9F#8)) "core/range_util.sail:34.50-34.51"
  assert (not (range_subset 0xC1#8 0x9F#8 0x3E#8 0xE0#8)) "core/range_util.sail:35.50-35.51"

def range_subset_equals (a_begin : (BitVec 8)) (a_size : (BitVec 8)) (b_begin : (BitVec 8)) (b_size : (BitVec 8)) : Bool :=
  (zopz0zJzJzK
    ((range_subset a_begin a_size b_begin b_size) && (range_subset b_begin b_size a_begin a_size))
    ((a_begin == b_begin) && (a_size == b_size)))

def range_subset_precise (a_begin : (BitVec 8)) (a_size : (BitVec 8)) (b_begin : (BitVec 8)) (b_size : (BitVec 8)) (index : (BitVec 8)) : Bool :=
  let index_in_a := (zopz0zI_u (index - a_begin) a_size)
  let index_in_b := (zopz0zI_u (index - b_begin) b_size)
  let is_subset := (range_subset a_begin a_size b_begin b_size)
  ((zopz0zJzJzK (is_subset && index_in_a) index_in_b) && (zopz0zJzJzK
      (index_in_a && (not index_in_b)) (not is_subset)))

