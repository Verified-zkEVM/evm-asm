import Out.Flow
import Out.Prelude
import Out.Errors
import Out.MemAddrtype
import Out.RangeUtil
import Out.VmemTypes

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
  | .Load .PageTableEntry => (pure exceptions.load_store)
  | .Load .ShadowStack => (pure exceptions.load_store)
  | .Store .Data => (pure exceptions.load_store)
  | .Store .PageTableEntry => (pure exceptions.load_store)
  | .Store .ShadowStack => (pure exceptions.load_store)
  | .Load .Vector => (pure exceptions.vector)
  | .Store .Vector => (pure exceptions.vector)
  | .Atomic _ => (pure (some exceptions.amo))
  | .InstructionFetch () =>
    (internal_error "sys/pma.sail" 153 "PMA: Invalid misaligned instruction fetch.")
  | .LoadReserved (_, _, p) =>
    (internal_error "sys/pma.sail" 154
      (HAppend.hAppend "PMA: Invalid misaligned load-reserved ("
        (HAppend.hAppend (mem_payload_name_forwards p) ").")))
  | .StoreConditional (_, _, p) =>
    (internal_error "sys/pma.sail" 155
      (HAppend.hAppend "PMA: Invalid misaligned store-conditional ("
        (HAppend.hAppend (mem_payload_name_forwards p) ").")))
  | .CacheAccess _ => (internal_error "sys/pma.sail" 156 "PMA: Invalid misaligned cache-access.")

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

