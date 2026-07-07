import Out.Flow
import Out.Prelude
import Out.Errors
import Out.AextTypes
import Out.MemAddrtype
import Out.MemMetadata
import Out.PhysMemInterface
import Out.PlatformConfig
import Out.Types
import Out.VmemTypes
import Out.MemTypeUtils
import Out.Callbacks
import Out.PmpControl
import Out.SysControl
import Out.Platform
import Out.Pma

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

/-- Type quantifiers: width : Nat, width > 0 -/
def is_aligned_paddr (typ_0 : physaddr) (width : Nat) : Bool :=
  let .Physaddr addr : physaddr := typ_0
  ((Int.tmod (BitVec.toNatInt addr) width) == 0)

/-- Type quantifiers: width : Nat, width > 0 -/
def is_aligned_vaddr (typ_0 : virtaddr) (width : Nat) : Bool :=
  let .Virtaddr addr : virtaddr := typ_0
  ((Int.tmod (BitVec.toNatInt addr) width) == 0)

/-- Type quantifiers: k_ex254881_ : Bool, k_ex254880_ : Bool, k_ex254879_ : Bool -/
def read_kind_of_flags (aq : Bool) (rl : Bool) (res : Bool) : SailM read_kind := do
  match (aq, rl, res) with
  | (false, false, false) => (pure Read_plain)
  | (true, false, false) =>
    (internal_error "sys/mem.sail" 52 "Unreserved load with acquire semantics should be unreachable")
  | (true, true, false) =>
    (internal_error "sys/mem.sail" 53
      "Unreserved load with acquire-release semantics should be unreachable")
  | (false, false, true) => (pure Read_RISCV_reserved)
  | (true, false, true) => (pure Read_RISCV_reserved_acquire)
  | (true, true, true) => (pure Read_RISCV_reserved_strong_acquire)
  | (false, true, false) =>
    (internal_error "sys/mem.sail" 58 "Unreserved Load with release semantics should be unreachable")
  | (false, true, true) =>
    (internal_error "sys/mem.sail" 59 "Load-reserved with release semantics should be unreachable")

/-- Type quantifiers: k_ex254887_ : Bool, k_ex254886_ : Bool, k_ex254885_ : Bool -/
def write_kind_of_flags (aq : Bool) (rl : Bool) (con : Bool) : SailM write_kind := do
  match (aq, rl, con) with
  | (false, false, false) => (pure Write_plain)
  | (false, true, false) =>
    (internal_error "sys/mem.sail" 65
      "Unconditional store with release semantics should be unreachable")
  | (false, false, true) => (pure Write_RISCV_conditional)
  | (false, true, true) => (pure Write_RISCV_conditional_release)
  | (true, true, false) =>
    (internal_error "sys/mem.sail" 68
      "Unconditional store with acquire-release semantics should be unreachable")
  | (true, true, true) => (pure Write_RISCV_conditional_strong_release)
  | (true, false, false) =>
    (internal_error "sys/mem.sail" 71
      "Unconditional store with acquire semantics should be unreachable")
  | (true, false, true) =>
    (internal_error "sys/mem.sail" 72
      "Store-conditional with acquire semantics should be unreachable")

/-- Type quantifiers: k_ex254891_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) : SailM (Option ExceptionType) := do
  match (matching_pma_region (← readReg pma_regions) paddr width) with
  | none => (pure (some (← (accessFaultFromAccessType access))))
  | .some { attributes := attributes, size := _, include_in_device_tree := _, base := _ } =>
    (do
      let attributes := (override_PMA attributes pbmt)
      let misaligned := (not (is_aligned_paddr paddr width))
      let misaligned_exception ← (( do
        if ((not misaligned) : Bool)
        then (pure none)
        else (pma_misaligned_exception attributes access) ) : SailM (Option misaligned_exception) )
      match misaligned_exception with
      | .some .AccessFault => (pure (some (← (accessFaultFromAccessType access))))
      | .some .AlignmentException => (pure (some (← (alignmentFaultFromAccessType access))))
      | none =>
        (do
          let canAccess ← (( do
            match access with
            | .InstructionFetch () => (pure attributes.executable)
            | .Load .Data =>
              (do
                assert (not res_or_con) "sys/mem.sail:103.61-103.62"
                (pure attributes.readable))
            | .Load .Vector =>
              (do
                assert (not res_or_con) "sys/mem.sail:104.61-104.62"
                (pure attributes.readable))
            | .Load .PageTableEntry =>
              (do
                assert (not res_or_con) "sys/mem.sail:105.61-105.62"
                (pure attributes.supports_pte_read))
            | .Store .Data =>
              (do
                assert (not res_or_con) "sys/mem.sail:106.61-106.62"
                (pure attributes.writable))
            | .Store .Vector =>
              (do
                assert (not res_or_con) "sys/mem.sail:107.61-107.62"
                (pure attributes.writable))
            | .Store .PageTableEntry =>
              (do
                assert (not res_or_con) "sys/mem.sail:108.61-108.62"
                (pure attributes.supports_pte_write))
            | .LoadReserved (_, _, .Data) =>
              (do
                assert res_or_con "sys/mem.sail:112.63-112.64"
                (pure (attributes.readable && (bne attributes.reservability RsrvNone))))
            | .StoreConditional (_, _, .Data) =>
              (do
                assert res_or_con "sys/mem.sail:113.63-113.64"
                (pure (attributes.writable && (bne attributes.reservability RsrvNone))))
            | .Atomic (op, _, _, .Data, .Data) =>
              (do
                assert res_or_con "sys/mem.sail:114.63-114.64"
                (pure (attributes.readable && (attributes.writable && (pma_allows_atomic_op
                        attributes.atomic_support op width)))))
            | .Load .ShadowStack =>
              (do
                assert (not res_or_con) "sys/mem.sail:118.61-118.62"
                (pure (attributes.readable && attributes.read_idempotent)))
            | .Store .ShadowStack =>
              (do
                assert (not res_or_con) "sys/mem.sail:119.61-119.62"
                (pure (attributes.writable && attributes.write_idempotent)))
            | .Atomic (.AMOSWAP, _, _, .ShadowStack, .ShadowStack) =>
              (do
                assert res_or_con "sys/mem.sail:120.81-120.82"
                (pure (attributes.readable && (attributes.writable && (attributes.read_idempotent && (attributes.write_idempotent && (pma_allows_atomic_op
                            attributes.atomic_support AMOSWAP width)))))))
            | .CacheAccess (.CB_zero ()) =>
              (pure (attributes.writable && attributes.supports_cbo_zero))
            | .CacheAccess (.CB_manage _) => (pure (attributes.readable || attributes.writable))
            | .CacheAccess (.CB_prefetch p) =>
              (match p with
              | .PREFETCH_R => (pure attributes.readable)
              | .PREFETCH_W => (pure attributes.writable)
              | .PREFETCH_I => (pure attributes.executable))
            | .LoadReserved (_, _, p) =>
              (internal_error "sys/mem.sail" 157
                (HAppend.hAppend "Invalid payload ("
                  (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
            | .StoreConditional (_, _, p) =>
              (internal_error "sys/mem.sail" 158
                (HAppend.hAppend "Invalid payload ("
                  (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
            | .Atomic (op, _, _, .ShadowStack, .ShadowStack) =>
              (internal_error "sys/mem.sail" 160
                (HAppend.hAppend "Invalid op ("
                  (HAppend.hAppend (amo_mnemonic_forwards op) ") for ShadowStack Atomic.")))
            | .Atomic (_, _, _, rp, wp) =>
              (internal_error "sys/mem.sail" 161
                (HAppend.hAppend "Invalid payloads ("
                  (HAppend.hAppend (mem_payload_name_forwards rp)
                    (HAppend.hAppend ", "
                      (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic."))))) ) : SailM
            Bool )
          let _ : Unit :=
            if (((get_config_print_pma ()) && (not canAccess)) : Bool)
            then
              (print_endline
                (HAppend.hAppend "PMA check failed for a "
                  (HAppend.hAppend (Int.repr width)
                    (HAppend.hAppend "-byte wide "
                      (HAppend.hAppend (accessType_to_str access)
                        (HAppend.hAppend " access to address "
                          (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                            (HAppend.hAppend " with PMA {"
                              (HAppend.hAppend (pma_attributes_to_str attributes) "}")))))))))
            else ()
          if (canAccess : Bool)
          then (pure none)
          else (pure (some (← (accessFaultFromAccessType access))))))

def alignmentOrAccessFaultPriority (exc : ExceptionType) : SailM Nat := do
  match exc with
  | .E_Fetch_Access_Fault () => (pure 1)
  | .E_Load_Access_Fault () => (pure 1)
  | .E_SAMO_Access_Fault () => (pure 1)
  | .E_Fetch_Addr_Align () => (pure 0)
  | .E_Load_Addr_Align () => (pure 0)
  | .E_SAMO_Addr_Align () => (pure 0)
  | _ =>
    (internal_error "sys/mem.sail" 182
      (HAppend.hAppend "Invalid exception: " (exceptionType_to_str exc)))

def highestPriorityAlignmentOrAccessFault (l : ExceptionType) (r : ExceptionType) : SailM ExceptionType := do
  if (((← (alignmentOrAccessFaultPriority l)) >b (← (alignmentOrAccessFaultPriority r))) : Bool)
  then (pure l)
  else (pure r)

/-- Type quantifiers: k_ex255008_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_access_check (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (res_or_con : Bool) : SailM (Option ExceptionType) := do
  let pmpError ← (( do (pmpCheck paddr width access priv) ) : SailM (Option ExceptionType) )
  let pmaError ← (( do (pmaCheck paddr width access pbmt res_or_con) ) : SailM
    (Option ExceptionType) )
  match (pmpError, pmaError) with
  | (none, none) => (pure none)
  | (.some e, none) => (pure (some e))
  | (none, .some e) => (pure (some e))
  | (.some e0, .some e1) => (pure (some (← (highestPriorityAlignmentOrAccessFault e0 e1))))

/-- Type quantifiers: k_ex255013_ : Bool, k_ex255012_ : Bool, k_ex255011_ : Bool, k_ex255010_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_read (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  match (← (phys_access_check access pbmt priv paddr width res)) with
  | .some e => (pure (Err e))
  | none =>
    (do
      if ((← (within_mmio_readable paddr width)) : Bool)
      then (pure (MemoryOpResult_add_meta (← (mmio_read access paddr width)) default_meta))
      else
        (do
          let rk ← do (read_kind_of_flags aq rl res)
          (pure (Ok (← (read_ram rk paddr width meta'))))))

/-- Type quantifiers: k_ex255022_ : Bool, k_ex255021_ : Bool, k_ex255020_ : Bool, k_ex255019_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv_meta (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  let result ← (( do
    if (((aq || res) && (not (is_aligned_paddr paddr width))) : Bool)
    then (pure (Err (E_Load_Addr_Align ())))
    else
      (do
        match (aq, rl, res) with
        | (false, true, false) => sailThrow ((Error_not_implemented "load.rl"))
        | (false, true, true) => sailThrow ((Error_not_implemented "lr.rl"))
        | (_, _, _) => (checked_mem_read access pbmt priv paddr width aq rl res meta')) ) : SailM
    (MemoryOpResult ((BitVec (8 * width)) × mem_meta)) )
  let _ : Unit :=
    match result with
    | .Ok (value, _) =>
      (mem_read_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
    | .Err e => (mem_exception_callback (bits_of_physaddr paddr) (exceptionType_bits_forwards e))
  (pure result)

/-- Type quantifiers: k_ex255076_ : Bool, k_ex255075_ : Bool, k_ex255074_ : Bool, k_ex255073_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_meta (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  (mem_read_priv_meta access pbmt
    (← (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))) paddr width
    aq rl res meta')

/-- Type quantifiers: k_ex255079_ : Bool, k_ex255078_ : Bool, k_ex255077_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (pure (MemoryOpResult_drop_meta
      (← (mem_read_priv_meta access pbmt priv paddr width aq rl res false))))

/-- Type quantifiers: k_ex255082_ : Bool, k_ex255081_ : Bool, k_ex255080_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (paddr : physaddr) (width : Nat) (aq : Bool) (rel : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (mem_read_priv access pbmt
    (← (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))) paddr width
    aq rel res)

/-- Type quantifiers: k_ex255085_ : Bool, k_ex255084_ : Bool, k_ex255083_ : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_ea (addr : physaddr) (width : Nat) (_access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Unit ExceptionType) := do
  if (((rl || con) && (not (is_aligned_paddr addr width))) : Bool)
  then (pure (Err (E_SAMO_Addr_Align ())))
  else (pure (Ok (write_ram_ea (← (write_kind_of_flags aq rl con)) addr width)))

/-- Type quantifiers: k_ex255096_ : Bool, k_ex255095_ : Bool, k_ex255094_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  match (← (phys_access_check access pbmt priv paddr width con)) with
  | .some e => (pure (Err e))
  | none =>
    (do
      if ((← (within_mmio_writable paddr width)) : Bool)
      then (mmio_write paddr width data)
      else
        (do
          let wk ← do (write_kind_of_flags aq rl con)
          (pure (Ok (← (write_ram wk paddr width data meta'))))))

/-- Type quantifiers: k_ex255108_ : Bool, k_ex255107_ : Bool, k_ex255106_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_priv_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  if (((rl || con) && (not (is_aligned_paddr paddr width))) : Bool)
  then (pure (Err (E_SAMO_Addr_Align ())))
  else
    (do
      let result ← do (checked_mem_write paddr width value access pbmt priv meta' aq rl con)
      let _ : Unit :=
        match result with
        | .Ok _ =>
          (mem_write_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
        | .Err e =>
          (mem_exception_callback (bits_of_physaddr paddr) (exceptionType_bits_forwards e))
      (pure result))

/-- Type quantifiers: k_ex255120_ : Bool, k_ex255119_ : Bool, k_ex255118_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_priv (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (priv : Privilege) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_priv_meta paddr width value access pbmt priv default_meta aq rl con)

/-- Type quantifiers: k_ex255123_ : Bool, k_ex255122_ : Bool, k_ex255121_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  let ep ← do (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  (mem_write_value_priv_meta paddr width value access pbmt ep meta' aq rl con)

/-- Type quantifiers: k_ex255126_ : Bool, k_ex255125_ : Bool, k_ex255124_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_meta paddr width value access pbmt default_meta aq rl con)

