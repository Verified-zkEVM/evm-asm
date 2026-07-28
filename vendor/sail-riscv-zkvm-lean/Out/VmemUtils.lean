import Out.Flow
import Out.Prelude
import Out.Xlen
import Out.MemAddrtype
import Out.PlatformConfig
import Out.Types
import Out.VmemTypes
import Out.AddrChecks
import Out.PmUtils
import Out.SysControl
import Out.SplitAccessUtils
import Out.Mem
import Out.Vmem
import Out.InstsBegin

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

/-- Type quantifiers: k_ex500132_ : Bool -/
def plat_misaligned_exception (access : (MemoryAccessType mem_payload)) (res : Bool) : (Option misaligned_exception) :=
  if ((is_amo_access access) : Bool)
  then plat_misaligned_access.amo
  else
    (if (res : Bool)
    then (some plat_misaligned_access.lrsc)
    else
      (if ((is_vector_access access) : Bool)
      then plat_misaligned_access.vector
      else plat_misaligned_access.load_store))

def offset_virtaddr_by (typ_0 : virtaddr) (typ_1 : physaddr) (typ_2 : physaddr) : virtaddr :=
  let .Virtaddr base_vaddr : virtaddr := typ_0
  let .Physaddr base_paddr : physaddr := typ_1
  let .Physaddr exc_paddr : physaddr := typ_2
  let offset := (Sail.BitVec.extractLsb (exc_paddr - base_paddr) (xlen -i 1) 0)
  (Virtaddr (base_vaddr + offset))

def transform_effective_address (vaddr : virtaddr) (access : (MemoryAccessType mem_payload)) : SailM virtaddr := do
  let eff_privilege ← do
    (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  let pmlen ← do (get_pmlen access eff_privilege)
  let mode ← do (translationMode eff_privilege)
  if ((mode == Bare) : Bool)
  then (pure (pm_transform_PA vaddr pmlen))
  else (pure (pm_transform_VA vaddr pmlen))

/-- Type quantifiers: k_ex500139_ : Bool, k_ex500138_ : Bool, k_ex500137_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def translate_and_read_value (vaddr : virtaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (physaddr × (BitVec (8 * width))) ExecutionResult) := do
  match (← (translateAddr vaddr access)) with
  | .Err (e, _) => (pure (Err (← (memory_exception vaddr e))))
  | .Ok (paddr, pbmt, _) =>
    (do
      match (← (mem_read access pbmt paddr width aq rl res)) with
      | .Err (exc_paddr, e) =>
        (do
          let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
          (pure (Err (← (memory_exception exc_vaddr e)))))
      | .Ok v => (pure (Ok (paddr, v))))

/-- Type quantifiers: k_ex500148_ : Bool, k_ex500147_ : Bool, k_ex500146_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_read_addr (vaddr : virtaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (plat_misaligned_exception access res) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_Load_Access_Fault ()))))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_Load_Addr_Align ()))))))
      | none => (pure ()))
  else (pure ())
  let vaddr_bits := (bits_of_virtaddr vaddr)
  let (in_page_bytes, next_page_bytes) ← do (split_on_page_boundary vaddr_bits width)
  let data := (zeros (n := (8 *i width)))
  let effPriv ← do (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  let do_split_access ← do
    (pure ((bne (← (translationMode effPriv)) Bare) && (next_page_bytes >b 0)))
  let data ← (( do
    if ((sys_misaligned_order_decreasing && do_split_access) : Bool)
    then
      (do
        assert (not res) "sys/vmem_utils.sail:118.19-118.20"
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        match (← (translate_and_read_value access_addr next_page_bytes access aq rl res)) with
        | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
        | .Ok (_, v) =>
          (pure (Sail.BitVec.updateSubrange data ((8 *i width) -i 1) (8 *i in_page_bytes) v)))
    else (pure data) ) : SailME (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  let access_width :=
    if (do_split_access : Bool)
    then in_page_bytes
    else width
  let data ← (( do
    match (← (translate_and_read_value vaddr access_width access aq rl res)) with
    | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
    | .Ok (paddr, v) =>
      (do
        if (res : Bool)
        then
          (do
            assert (width == access_width) "sys/vmem_utils.sail:136.36-136.37"
            (load_reservation (bits_of_physaddr paddr) width))
        else (pure ())
        (pure (Sail.BitVec.updateSubrange data ((8 *i access_width) -i 1) 0 v))) ) : SailME
    (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  let data ← (( do
    if (((not sys_misaligned_order_decreasing) && do_split_access) : Bool)
    then
      (do
        assert (not res) "sys/vmem_utils.sail:145.19-145.20"
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        match (← (translate_and_read_value access_addr next_page_bytes access aq rl res)) with
        | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
        | .Ok (_, v) =>
          (pure (Sail.BitVec.updateSubrange data ((8 *i width) -i 1) (8 *i in_page_bytes) v)))
    else (pure data) ) : SailME (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  (pure (Ok data))

/-- Type quantifiers: k_ex500164_ : Bool, k_ex500163_ : Bool, k_ex500162_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def translate_and_write_value (vaddr : virtaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := do
  match (← (translateAddr vaddr access)) with
  | .Err (e, _) => (pure (Err (← (memory_exception vaddr e))))
  | .Ok (paddr, pbmt, _) =>
    (do
      match (← (mem_write_ea paddr width access pbmt aq rl res)) with
      | .Err (exc_paddr, e) =>
        (do
          let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
          (pure (Err (← (memory_exception exc_vaddr e)))))
      | .Ok () =>
        (do
          match (← (mem_write_value paddr width value access pbmt aq rl res)) with
          | .Err (exc_paddr, e) =>
            (do
              let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
              (pure (Err (← (memory_exception exc_vaddr e)))))
          | .Ok s => (pure (Ok s))))

/-- Type quantifiers: k_ex500178_ : Bool, k_ex500177_ : Bool, k_ex500176_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_write_addr (vaddr : virtaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (plat_misaligned_exception access res) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_SAMO_Access_Fault ()))))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_SAMO_Addr_Align ()))))))
      | none => (pure ()))
  else (pure ())
  let vaddr_bits := (bits_of_virtaddr vaddr)
  let write_success : Bool := true
  let (in_page_bytes, next_page_bytes) ← do (split_on_page_boundary vaddr_bits width)
  let effPriv ← do (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  let do_split_access ← do
    (pure ((bne (← (translationMode effPriv)) Bare) && (next_page_bytes >b 0)))
  let write_success ← (( do
    if ((sys_misaligned_order_decreasing && do_split_access) : Bool)
    then
      (do
        assert (not (is_store_conditional access)) "sys/vmem_utils.sail:215.44-215.45"
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        let write_value := (Sail.BitVec.extractLsb data ((8 *i width) -i 1) (8 *i in_page_bytes))
        match (← (translate_and_write_value access_addr next_page_bytes write_value access aq rl
            res)) with
        | .Err e => SailME.throw ((Err e) : (Result Bool ExecutionResult))
        | .Ok s => (pure (write_success && s)))
    else (pure write_success) ) : SailME (Result Bool ExecutionResult) Bool )
  let access_width :=
    if (do_split_access : Bool)
    then in_page_bytes
    else width
  let write_success ← (( do
    match (← (translateAddr vaddr access)) with
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err (← (memory_exception vaddr e)))))
    | .Ok (paddr, pbmt, _) =>
      (do
        assert (res == (is_store_conditional access)) "sys/vmem_utils.sail:231.48-231.49"
        if ((res && (not (match_reservation (bits_of_physaddr paddr)))) : Bool)
        then
          (do
            let effPriv ← do
              (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
            match (← (phys_access_check access pbmt effPriv paddr access_width true)) with
            | .Err e =>
              SailME.throw (← do
                  (pure (Err (← (memory_exception vaddr e)))))
            | .Ok _ => (pure false))
        else
          (do
            match (← (mem_write_ea paddr access_width access pbmt aq rl res)) with
            | .Err (exc_paddr, e) =>
              SailME.throw (← do
                  let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
                  (pure (Err (← (memory_exception exc_vaddr e)))))
            | .Ok () =>
              (do
                let write_value := (Sail.BitVec.extractLsb data ((8 *i access_width) -i 1) 0)
                match (← (mem_write_value paddr access_width write_value access pbmt aq rl res)) with
                | .Err (exc_paddr, e) =>
                  SailME.throw (← do
                      let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
                      (pure (Err (← (memory_exception exc_vaddr e)))))
                | .Ok s => (pure (write_success && s))))) ) : SailME (Result Bool ExecutionResult)
    Bool )
  let write_success ← (( do
    if (((not sys_misaligned_order_decreasing) && do_split_access) : Bool)
    then
      (do
        assert (not (is_store_conditional access)) "sys/vmem_utils.sail:266.44-266.45"
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        let write_value := (Sail.BitVec.extractLsb data ((8 *i width) -i 1) (8 *i in_page_bytes))
        match (← (translate_and_write_value access_addr next_page_bytes write_value access aq rl
            res)) with
        | .Err e => SailME.throw ((Err e) : (Result Bool ExecutionResult))
        | .Ok s => (pure (write_success && s)))
    else (pure write_success) ) : SailME (Result Bool ExecutionResult) Bool )
  (pure (Ok write_success))

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def get_transformed_data_addr (base : regidx) (offset : (BitVec 64)) (acc : (MemoryAccessType mem_payload)) (width : Nat) : SailM (Ext_DataAddr_Check Unit) := do
  match (← (ext_data_get_addr base offset acc width)) with
  | .Ext_DataAddr_Error e => (pure (Ext_DataAddr_Error e))
  | .Ext_DataAddr_OK vaddr =>
    (do
      let vaddr ← do (transform_effective_address vaddr acc)
      (pure (Ext_DataAddr_OK vaddr)))

/-- Type quantifiers: k_ex500227_ : Bool, k_ex500226_ : Bool, k_ex500225_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_read (rs : regidx) (offset : (BitVec 64)) (width : Nat) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs offset access width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result (BitVec (8 * width)) ExecutionResult))
    ) : SailME (Result (BitVec (8 * width)) ExecutionResult) virtaddr )
  (vmem_read_addr vaddr width access aq rl res)

/-- Type quantifiers: k_ex500237_ : Bool, k_ex500236_ : Bool, k_ex500235_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_write (rs_addr : regidx) (offset : (BitVec 64)) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs_addr offset access width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result Bool ExecutionResult)) ) : SailME
    (Result Bool ExecutionResult) virtaddr )
  (vmem_write_addr vaddr width data access aq rl res)

