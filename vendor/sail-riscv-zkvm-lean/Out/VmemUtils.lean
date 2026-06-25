import Out.Prelude
import Out.MemAddrtype
import Out.PlatformConfig
import Out.Types
import Out.VmemTypes
import Out.AddrChecks
import Out.PmUtils
import Out.SysControl
import Out.MemUtils
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

def sys_misaligned_order_decreasing : Bool := false

def sys_misaligned_byte_by_byte : Bool := false

def sys_misaligned_allowed_within_exp : Nat := 0

/-- Type quantifiers: width : Nat, is_mem_width(width) -/
def split_misaligned (vaddr : virtaddr) (width : Nat) : SailM (Int × Int) := do
  let vaddr_bits := (bits_of_virtaddr vaddr)
  if (((is_aligned_vaddr vaddr width) || (allowed_misaligned vaddr_bits width
         sys_misaligned_allowed_within_exp)) : Bool)
  then (pure (1, width))
  else
    (do
      if (sys_misaligned_byte_by_byte : Bool)
      then (pure (width, 1))
      else
        (do
          let bytes_per_access := (2 ^i (BitVec.countTrailingZeros vaddr_bits))
          let num_accesses := (Int.tdiv width bytes_per_access)
          assert (width == (num_accesses *i bytes_per_access)) "sys/vmem_utils.sail:63.51-63.52"
          (pure (num_accesses, bytes_per_access))))

/-- Type quantifiers: n : Int -/
def misaligned_order (n : Int) : (Int × Int × Int) :=
  if (sys_misaligned_order_decreasing : Bool)
  then ((n -i 1), 0, (Neg.neg 1))
  else (0, (n -i 1), 1)

/-- Type quantifiers: k_ex260155_ : Bool -/
def plat_misaligned_exception (access : (MemoryAccessType mem_payload)) (res : Bool) : SailM (Option misaligned_exception) := do
  assert (not (is_amo_access access)) "sys/vmem_utils.sail:85.35-85.36"
  if (res : Bool)
  then (pure (some plat_misaligned_access.lrsc))
  else
    (if ((is_vector_access access) : Bool)
    then (pure plat_misaligned_access.vector)
    else (pure plat_misaligned_access.load_store))

def transform_effective_address (vaddr : virtaddr) (access : (MemoryAccessType mem_payload)) : SailM virtaddr := do
  let eff_privilege ← do
    (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  let pmlen ← do (get_pmlen access eff_privilege)
  let mode ← do (translationMode eff_privilege)
  if ((mode == Bare) : Bool)
  then (pure (pm_transform_PA vaddr pmlen))
  else (pure (pm_transform_VA vaddr pmlen))

/-- Type quantifiers: k_ex260168_ : Bool, k_ex260167_ : Bool, k_ex260166_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_read_addr (vaddr : virtaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (← (plat_misaligned_exception access res)) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_Load_Access_Fault ()))))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_Load_Addr_Align ()))))))
      | none => (pure ()))
  else (pure ())
  let (n, bytes) ← do (split_misaligned vaddr width)
  let data := (zeros (n := ((8 *i n) *i bytes)))
  let (first, last, step) := (misaligned_order n)
  let i : Nat := first
  let finished : Bool := false
  let vaddr := (bits_of_virtaddr vaddr)
  let (data, finished, i) ← (( do
    let loop_vars ← untilFuelM (fuel :=n) (fun (data, finished, i) => (pure finished)) (data, finished, i)
      fun (data, finished, i) => do
        assert true "loop dummy assert"
        let offset := i
        let vaddr := (BitVec.addInt vaddr (offset *i bytes))
        let data ← (( do
          match (← (translateAddr (Virtaddr vaddr) access)) with
          | .Err (e, _) =>
            SailME.throw (← do
                (pure (Err (← (memory_exception (Virtaddr vaddr) e)))))
          | .Ok (paddr, pbmt, _) =>
            (do
              match (← (mem_read access pbmt paddr bytes aq rl res)) with
              | .Err e =>
                SailME.throw (← do
                    (pure (Err (← (memory_exception (Virtaddr vaddr) e)))))
              | .Ok v =>
                (do
                  if (res : Bool)
                  then (load_reservation (bits_of_physaddr paddr) width)
                  else (pure ())
                  (pure (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i bytes) -i 1)
                      ((8 *i offset) *i bytes) v)))) ) : SailME
          (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * n * bytes)) )
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (data, finished, i))
    (pure loop_vars) ) : SailME (Result (BitVec (8 * width)) ExecutionResult)
    ((BitVec (8 * n * bytes)) × Bool × Nat) )
  (pure (Ok data))

/-- Type quantifiers: k_ex260204_ : Bool, k_ex260203_ : Bool, k_ex260202_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_write_addr (vaddr : virtaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (← (plat_misaligned_exception access res)) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_SAMO_Access_Fault ()))))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err (← (memory_exception vaddr (E_SAMO_Addr_Align ()))))))
      | none => (pure ()))
  else (pure ())
  let (n, bytes) ← do (split_misaligned vaddr width)
  let (first, last, step) := (misaligned_order n)
  let i : Nat := first
  let finished : Bool := false
  let write_success : Bool := true
  let vaddr := (bits_of_virtaddr vaddr)
  let (finished, i, write_success) ← (( do
    let loop_vars ← untilFuelM (fuel :=n) (fun (finished, i, write_success) => (pure finished)) (finished, i, write_success)
      fun (finished, i, write_success) => do
        assert true "loop dummy assert"
        let offset := i
        let vaddr := (BitVec.addInt vaddr (offset *i bytes))
        let write_success ← (( do
          match (← (translateAddr (Virtaddr vaddr) access)) with
          | .Err (e, _) =>
            SailME.throw (← do
                (pure (Err (← (memory_exception (Virtaddr vaddr) e)))))
          | .Ok (paddr, pbmt, _) =>
            (do
              assert (res == (is_store_conditional access)) "sys/vmem_utils.sail:197.50-197.51"
              if ((res && (not (match_reservation (bits_of_physaddr paddr)))) : Bool)
              then
                (do
                  let effPriv ← do
                    (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
                  match (← (phys_access_check access pbmt effPriv paddr bytes true)) with
                  | .some e =>
                    SailME.throw (← do
                        (pure (Err (← (memory_exception (Virtaddr vaddr) e)))))
                  | none => (pure false))
              else
                (do
                  match (← (mem_write_ea paddr bytes access aq rl res)) with
                  | .Err e =>
                    SailME.throw (← do
                        (pure (Err (← (memory_exception (Virtaddr vaddr) e)))))
                  | .Ok () =>
                    (do
                      let write_value :=
                        (Sail.BitVec.extractLsb data (((8 *i (offset +i 1)) *i bytes) -i 1)
                          ((8 *i offset) *i bytes))
                      match (← (mem_write_value paddr bytes write_value access pbmt aq rl res)) with
                      | .Err e =>
                        SailME.throw (← do
                            (pure (Err (← (memory_exception (Virtaddr vaddr) e)))))
                      | .Ok s => (pure (write_success && s))))) ) : SailME
          (Result Bool ExecutionResult) Bool )
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (finished, i, write_success))
    (pure loop_vars) ) : SailME (Result Bool ExecutionResult) (Bool × Nat × Bool) )
  (pure (Ok write_success))

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def get_transformed_data_addr (base : regidx) (offset : (BitVec 64)) (acc : (MemoryAccessType mem_payload)) (width : Nat) : SailM (Ext_DataAddr_Check Unit) := do
  match (← (ext_data_get_addr base offset acc width)) with
  | .Ext_DataAddr_Error e => (pure (Ext_DataAddr_Error e))
  | .Ext_DataAddr_OK vaddr =>
    (do
      let vaddr ← do (transform_effective_address vaddr acc)
      (pure (Ext_DataAddr_OK vaddr)))

/-- Type quantifiers: k_ex260257_ : Bool, k_ex260256_ : Bool, k_ex260255_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_read (rs : regidx) (offset : (BitVec 64)) (width : Nat) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs offset access width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result (BitVec (8 * width)) ExecutionResult))
    ) : SailME (Result (BitVec (8 * width)) ExecutionResult) virtaddr )
  (vmem_read_addr vaddr width access aq rl res)

/-- Type quantifiers: k_ex260267_ : Bool, k_ex260266_ : Bool, k_ex260265_ : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_write (rs_addr : regidx) (offset : (BitVec 64)) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs_addr offset access width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result Bool ExecutionResult)) ) : SailME
    (Result Bool ExecutionResult) virtaddr )
  (vmem_write_addr vaddr width data access aq rl res)

