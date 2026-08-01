import Out.Flow
import Out.Prelude
import Out.Errors
import Out.Xlen
import Out.MemAddrtype
import Out.RangeUtil
import Out.VmemTypes
import Out.MemUtils
import Out.SplitAccessUtils

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

def undefined_AtomicSupport (_ : Unit) : SailM AtomicSupport := do
  (internal_pick [AMONone, AMOSwap, AMOLogical, AMOArithmetic, AMOCASW, AMOCASD, AMOCASQ])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def AtomicSupport_of_num (arg_ : Nat) : AtomicSupport :=
  match arg_ with
  | 0 => AMONone
  | 1 => AMOSwap
  | 2 => AMOLogical
  | 3 => AMOArithmetic
  | 4 => AMOCASW
  | 5 => AMOCASD
  | _ => AMOCASQ

def atomic_support_str_forwards_matches (arg_ : AtomicSupport) : Bool :=
  match arg_ with
  | .AMONone => true
  | .AMOSwap => true
  | .AMOLogical => true
  | .AMOArithmetic => true
  | .AMOCASW => true
  | .AMOCASD => true
  | .AMOCASQ => true

def atomic_support_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "AMONone" => true
  | "AMOSwap" => true
  | "AMOLogical" => true
  | "AMOArithmetic" => true
  | "AMOCASW" => true
  | "AMOCASD" => true
  | "AMOCASQ" => true
  | _ => false

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pma_allows_atomic_op (pma : AtomicSupport) (op : amoop) (width : Nat) : Bool :=
  match pma with
  | .AMONone => false
  | .AMOSwap => (op == AMOSWAP)
  | .AMOLogical => ((op == AMOSWAP) || ((op == AMOAND) || ((op == AMOOR) || (op == AMOXOR))))
  | .AMOArithmetic => (bne op AMOCAS)
  | .AMOCASW => ((bne op AMOCAS) || (width ≤b 4))
  | .AMOCASD => ((bne op AMOCAS) || (width ≤b 8))
  | .AMOCASQ => ((bne op AMOCAS) || (width ≤b 16))

def undefined_Reservability (_ : Unit) : SailM Reservability := do
  (internal_pick [RsrvNone, RsrvNonEventual, RsrvEventual])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Reservability_of_num (arg_ : Nat) : Reservability :=
  match arg_ with
  | 0 => RsrvNone
  | 1 => RsrvNonEventual
  | _ => RsrvEventual

def num_of_Reservability (arg_ : Reservability) : Int :=
  match arg_ with
  | .RsrvNone => 0
  | .RsrvNonEventual => 1
  | .RsrvEventual => 2

def reservability_str_forwards_matches (arg_ : Reservability) : Bool :=
  match arg_ with
  | .RsrvNone => true
  | .RsrvNonEventual => true
  | .RsrvEventual => true

def reservability_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "RsrvNone" => true
  | "RsrvNonEventual" => true
  | "RsrvEventual" => true
  | _ => false

def undefined_MemoryRegionType (_ : Unit) : SailM MemoryRegionType := do
  (internal_pick [MainMemory, IOMemory])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def MemoryRegionType_of_num (arg_ : Nat) : MemoryRegionType :=
  match arg_ with
  | 0 => MainMemory
  | _ => IOMemory

def num_of_MemoryRegionType (arg_ : MemoryRegionType) : Int :=
  match arg_ with
  | .MainMemory => 0
  | .IOMemory => 1

def memory_region_type_str_forwards_matches (arg_ : MemoryRegionType) : Bool :=
  match arg_ with
  | .MainMemory => true
  | .IOMemory => true

def memory_region_type_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "main memory" => true
  | "IO memory" => true
  | _ => false

def override_PMA (pma : PMA) (pbmt : page_based_mem_type) : PMA :=
  match pbmt with
  | .PBMT_PMA => pma
  | .PBMT_NC =>
    { pma with mem_type := MainMemory, cacheable := false, read_idempotent := true, write_idempotent := true }
  | .PBMT_IO =>
    { pma with mem_type := IOMemory, cacheable := false, read_idempotent := false, write_idempotent := false }

def pma_misaligned_exception (pma : PMA) (access : (MemoryAccessType mem_payload)) : SailM (Option misaligned_exception) := do
  let exceptions := pma.misaligned_exceptions
  match access with
  | .Load .Data => (pure exceptions.load_store)
  | .Store .Data => (pure exceptions.load_store)
  | .Load .Vector => (pure exceptions.vector)
  | .Store .Vector => (pure exceptions.vector)
  | .Atomic _ => (pure (some exceptions.amo))
  | .InstructionFetch () =>
    (internal_error "sys/pma.sail" 153 "PMA: Invalid misaligned instruction fetch.")
  | .Load .PageTableEntry =>
    (internal_error "sys/pma.sail" 154 "PMA: Invalid misaligned load of page-table entry.")
  | .Store .PageTableEntry =>
    (internal_error "sys/pma.sail" 155 "PMA: Invalid misaligned store of page-table entry.")
  | .LoadReserved (_, _, p) =>
    (internal_error "sys/pma.sail" 156
      (HAppend.hAppend "PMA: Invalid misaligned load-reserved ("
        (HAppend.hAppend (mem_payload_name_forwards p) ").")))
  | .StoreConditional (_, _, p) =>
    (internal_error "sys/pma.sail" 157
      (HAppend.hAppend "PMA: Invalid misaligned store-conditional ("
        (HAppend.hAppend (mem_payload_name_forwards p) ").")))
  | .Load .ShadowStack =>
    (internal_error "sys/pma.sail" 158 "PMA: Invalid misaligned shadow-stack load.")
  | .Store .ShadowStack =>
    (internal_error "sys/pma.sail" 159 "PMA: Invalid misaligned shadow-stack store.")
  | .CacheAccess _ => (internal_error "sys/pma.sail" 160 "PMA: Invalid misaligned cache-access.")

/-- Type quantifiers: width : Nat, 0 ≤ width -/
def is_mag_applicable_access (access : (MemoryAccessType mem_payload)) (width : Nat) : SailM Bool := do
  match access with
  | .Load .Data => (pure (width ≤b xlen_bytes))
  | .Store .Data => (pure (width ≤b xlen_bytes))
  | .Load .Vector => (pure true)
  | .Store .Vector => (pure true)
  | .Load .PageTableEntry => (pure false)
  | .Store .PageTableEntry => (pure false)
  | .Load .ShadowStack => (pure false)
  | .Store .ShadowStack => (pure false)
  | .Atomic (_, _, _, .Data, .Data) => (pure true)
  | .Atomic (_, _, _, .ShadowStack, .ShadowStack) => (pure true)
  | .InstructionFetch () => (pure false)
  | .LoadReserved (_, _, .Data) => (pure false)
  | .StoreConditional (_, _, .Data) => (pure false)
  | .CacheAccess _ => (pure false)
  | .Atomic (_, _, _, rp, wp) =>
    (internal_error "sys/pma.sail" 192
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic.")))))
  | .LoadReserved (_, _, p) =>
    (internal_error "sys/pma.sail" 193
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | .StoreConditional (_, _, p) =>
    (internal_error "sys/pma.sail" 194
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))

/-- Type quantifiers: k_ex481490_ : Bool -/
def mag_of_pma (pma : PMA) (is_vector : Bool) : (Option Nat) :=
  let mag :=
    if (is_vector : Bool)
    then pma.vector_misaligned_atomicity_granule_size_exp
    else pma.misaligned_atomicity_granule_size_exp
  if ((mag == 0) : Bool)
  then none
  else (some mag)

/-- Type quantifiers: k_ex481496_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_pma_mag (pma : PMA) (typ_1 : physaddr) (width : Nat) (is_vector : Bool) : Bool :=
  let .Physaddr addr : physaddr := typ_1
  match (mag_of_pma pma is_vector) with
  | none => false
  | .some mag => (allowed_misaligned (Sail.BitVec.extractLsb addr (xlen -i 1) 0) width mag)

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def mag_pma_check (pma : PMA) (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) : SailM (Result (Splittability × Nat) misaligned_exception) := do
  let is_mag_applicable ← do (is_mag_applicable_access access width)
  if (((is_aligned_paddr paddr width) || (is_mag_applicable && (within_pma_mag pma paddr width
           (is_vector_access access)))) : Bool)
  then (pure (Ok (CannotSplit, 0)))
  else
    (do
      match (← (pma_misaligned_exception pma access)) with
      | .some e => (pure (Err e))
      | none =>
        (match (is_mag_applicable, (mag_of_pma pma (is_vector_access access))) with
        | (true, .some mag) => (pure (Ok (CanSplit, mag)))
        | (_, _) => (pure (Ok (CanSplit, sys_misaligned_allowed_within_exp)))))

def matching_pma_region_bits_range (regions : (List PMA_Region)) (base : (BitVec 64)) (size : (BitVec 64)) : (Option PMA_Region) :=
  match regions with
  | [] => none
  | (region :: rest) =>
    (if ((range_subset base size region.base region.size) : Bool)
    then (some region)
    else (matching_pma_region_bits_range rest base size))

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def matching_pma_region (regions : (List PMA_Region)) (addr : physaddr) (width : Nat) : (Option PMA_Region) :=
  (matching_pma_region_bits_range regions (zero_extend (m := 64) (bits_of_physaddr addr))
    (to_bits (l := 64) width))

