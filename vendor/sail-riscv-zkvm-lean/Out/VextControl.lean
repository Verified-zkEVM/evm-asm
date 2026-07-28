import Out.Flow
import Out.Arith
import Out.Prelude
import Out.Vlen
import Out.VextRegs

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

def max_index_eew_exp : Nat := 6

/-- Type quantifiers: SEW : Nat, LMUL_pow : Int, ((- 3)) ≤ LMUL_pow ∧ LMUL_pow ≤ 3, SEW ∈
  {8, 16, 32, 64} -/
def get_num_elem (LMUL_pow : Int) (SEW : Nat) : SailM Nat := do
  assert (vlen ≥b SEW) "extensions/V/vext_control.sail:40.20-40.21"
  (pure (Int.tdiv ((2 ^i (Max.max 0 LMUL_pow)) *i vlen) SEW))

/-- Type quantifiers: index : Nat, EEW : Nat, EEW ≥ 0, is_sew_bitsize(EEW), 0 ≤ index -/
def read_single_element (EEW : Nat) (index : Nat) (vrid : vregidx) : SailM (BitVec EEW) := do
  assert (EEW ≤b vlen) "extensions/V/vext_control.sail:47.20-47.21"
  let _ : Unit := (static_assert ((Int.tmod vlen EEW) == 0))
  let elem_per_reg := (Int.tdiv vlen EEW)
  let reg_in_group := (Int.tdiv index elem_per_reg)
  assert (reg_in_group <b 8) "extensions/V/vext_control.sail:55.25-55.26"
  let vrid := (vregidx_offset_range vrid reg_in_group)
  let index := (Int.tmod index elem_per_reg)
  let offset := (index *i EEW)
  (pure (Sail.BitVec.extractLsb (← (rV_bits vrid)) ((offset +i EEW) -i 1) offset))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, SEW : Nat, SEW ≥ 0, LMUL_pow : Int, num_elem
  ≥ 0 ∧ is_sew_bitsize(SEW) -/
def read_vreg (num_elem : Nat) (SEW : Nat) (LMUL_pow : Int) (vrid : vregidx) : SailM (Vector (BitVec SEW) num_elem) := do
  let vrid_val := (BitVec.toNatInt (vregidx_bits vrid))
  let LMUL_pow_reg :=
    if ((LMUL_pow <b 0) : Bool)
    then 0
    else LMUL_pow
  let LMUL := (2 ^i LMUL_pow_reg)
  let vrid_end := (vrid_val +i LMUL)
  assert (vrid_end ≤b 32) (HAppend.hAppend "Invalid register group: group "
    (HAppend.hAppend (Int.repr vrid_val)
      (HAppend.hAppend " ends at "
        (HAppend.hAppend (Int.repr vrid_end) " and overflows the largest register number (32)."))))
  assert ((Int.tmod vrid_val LMUL) == 0) (HAppend.hAppend "Invalid register group: group "
    (HAppend.hAppend (Int.repr vrid_val)
      (HAppend.hAppend " is not a multiple of its EMUL " (HAppend.hAppend (Int.repr LMUL) "."))))
  let result : (Vector (BitVec SEW) num_elem) := (vectorInit (zeros (n := SEW)))
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars ← do (pure (vectorUpdate result i (← (read_single_element SEW i vrid))))
  (pure loop_vars)

/-- Type quantifiers: index : Nat, EEW : Nat, EEW ≥ 0, is_sew_bitsize(EEW), 0 ≤ index -/
def write_single_element (EEW : Nat) (index : Nat) (vrid : vregidx) (value : (BitVec EEW)) : SailM Unit := do
  assert (EEW ≤b vlen) "extensions/V/vext_control.sail:89.20-89.21"
  let _ : Unit := (static_assert ((Int.tmod vlen EEW) == 0))
  let elem_per_reg := (Int.tdiv vlen EEW)
  let reg_in_group := (Int.tdiv index elem_per_reg)
  assert (reg_in_group <b 8) "extensions/V/vext_control.sail:97.25-97.26"
  let vrid := (vregidx_offset_range vrid reg_in_group)
  let index := (Int.tmod index elem_per_reg)
  let offset := (index *i EEW)
  (wV_bits vrid
    (Sail.BitVec.updateSubrange (← (rV_bits vrid)) ((offset +i EEW) -i 1) offset value))

/-- Type quantifiers: LMUL_pow : Int, num_elem : Nat, num_elem ≥ 0, SEW : Nat, SEW ≥ 0, num_elem
  ≥ 0 ∧ is_sew_bitsize(SEW), ((- 3)) ≤ LMUL_pow ∧ LMUL_pow ≤ 3 -/
def write_vreg (num_elem : Nat) (SEW : Nat) (LMUL_pow : Int) (vrid : vregidx) (vec : (Vector (BitVec SEW) num_elem)) : SailM Unit := do
  let group_size := (2 ^i (Max.max LMUL_pow 0))
  assert (SEW ≤b vlen) "extensions/V/vext_control.sail:124.20-124.21"
  let _ : Unit := (static_assert ((Int.tmod vlen SEW) == 0))
  let elem_per_reg := (Int.tdiv vlen SEW)
  assert ((num_elem == (group_size *i elem_per_reg)) || (num_elem == ((2 *i group_size) *i elem_per_reg))) "extensions/V/vext_control.sail:139.90-139.91"
  let loop_reg_in_group_lower := 0
  let loop_reg_in_group_upper := (group_size -i 1)
  let mut loop_vars := ()
  for reg_in_group in [loop_reg_in_group_lower:loop_reg_in_group_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let reg_value : vlenbits := (zeros (n := (2 ^i 8)))
      let reg_value ← (( do
        let loop_i_elem_lower := 0
        let loop_i_elem_upper := (elem_per_reg -i 1)
        let mut loop_vars_1 := reg_value
        for i_elem in [loop_i_elem_lower:loop_i_elem_upper:1]i do
          let reg_value := loop_vars_1
          loop_vars_1 :=
            (Sail.BitVec.updateSubrange reg_value (((i_elem *i SEW) +i SEW) -i 1) (i_elem *i SEW)
              (GetElem?.getElem! vec ((reg_in_group *i elem_per_reg) +i i_elem)))
        (pure loop_vars_1) ) : SailM (BitVec (2 ^ 8)) )
      (wV_bits (vregidx_offset_range vrid reg_in_group) reg_value)
  (pure loop_vars)

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, 0 < num_elem ∧ num_elem ≤ vlen -/
def read_vmask (num_elem : Nat) (vm : (BitVec 1)) (vrid : vregidx) : SailM (BitVec num_elem) := do
  if ((vm == 1#1) : Bool)
  then (pure (ones (n := num_elem)))
  else
    (pure ((ones (n := (num_elem -i num_elem))) +++ (Sail.BitVec.extractLsb (← (rV_bits vrid))
          (num_elem -i 1) 0)))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, 0 < num_elem ∧ num_elem ≤ vlen -/
def read_vmask_carry (num_elem : Nat) (vm : (BitVec 1)) (vrid : vregidx) : SailM (BitVec num_elem) := do
  if ((vm == 1#1) : Bool)
  then (pure (zeros (n := num_elem)))
  else
    (pure ((zeros (n := (num_elem -i num_elem))) +++ (Sail.BitVec.extractLsb (← (rV_bits vrid))
          (num_elem -i 1) 0)))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, num_elem > 0 -/
def write_vmask (num_elem : Nat) (vrid : vregidx) (v : (BitVec num_elem)) : SailM Unit := do
  assert ((0 <b num_elem) && (num_elem ≤b vlen)) "extensions/V/vext_control.sail:164.40-164.41"
  (wV_bits vrid (Sail.BitVec.updateSubrange (← (rV_bits vrid)) (num_elem -i 1) 0 v))

