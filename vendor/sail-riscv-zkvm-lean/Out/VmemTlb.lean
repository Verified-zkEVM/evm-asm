import Out.Flow
import Out.Prelude
import Out.Types
import Out.VmemTypes
import Out.VmemPte

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

def tlb_vpn_bits := (57 -i 12)

def tlb_ppn_bits := 44

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, pte_size ∈ {4, 8} -/
def tlb_get_pte (pte_size : Nat) (ent : TLB_Entry) : (BitVec (pte_size * 8)) :=
  (Sail.BitVec.extractLsb ent.pte ((pte_size *i 8) -i 1) 0)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ∈ {4, 8} -/
def tlb_set_pte (ent : TLB_Entry) (pte : (BitVec (k_n * 8))) : TLB_Entry :=
  { ent with pte := (zero_extend (m := 64) pte) }

/-- Type quantifiers: sv_width : Nat, is_sv_mode(sv_width) -/
def tlb_get_ppn (sv_width : Nat) (ent : TLB_Entry) (vpn : (BitVec (sv_width - 12))) : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) :=
  let vpn : (BitVec 64) := (sign_extend (m := 64) vpn)
  let levelMask : (BitVec 64) := (zero_extend (m := 64) ent.levelMask)
  let ppn : (BitVec 64) := (zero_extend (m := 64) ent.ppn)
  (trunc
    (m := (if ((sv_width == 32) : Bool)
    then 22
    else 44)) (ppn ||| (vpn &&& levelMask)))

def tlb_get_pbmt (ent : TLB_Entry) : SailM page_based_mem_type := do
  let pte_ext := (ext_bits_of_PTE ent.pte)
  (page_based_mem_type_forwards (_get_PTE_Ext_PBMT pte_ext))

def num_tlb_entries_exp := 6

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 ≤ (2 ^ 6) -/
def tlb_add_callback (x_0 : (Vector (Option TLB_Entry) (2 ^ 6))) (x_1 : Nat) : Unit :=
  ()

def tlb_flush_begin_callback (x_0 : Unit) : Unit :=
  ()

/-- Type quantifiers: x_0 : Nat, 0 ≤ x_0 ∧ x_0 ≤ (2 ^ 6) -/
def tlb_flush_callback (x_0 : Nat) : Unit :=
  ()

def tlb_flush_end_callback (x_0 : (Vector (Option TLB_Entry) (2 ^ 6))) : Unit :=
  ()

/-- Type quantifiers: _sv_mode : Nat, is_sv_mode(_sv_mode) -/
def tlb_hash (_sv_mode : Nat) (vpn : (BitVec (_sv_mode - 12))) : Nat :=
  (BitVec.toNatInt (Sail.BitVec.extractLsb vpn (num_tlb_entries_exp -i 1) 0))

def reset_TLB (_ : Unit) : SailM Unit := do
  writeReg tlb (vectorInit none)

/-- Type quantifiers: index : Nat, 0 ≤ index ∧ index ≤ (2 ^ 6 - 1) -/
def write_TLB (index : Nat) (entry : TLB_Entry) : SailM Unit := do
  writeReg tlb (vectorUpdate (← readReg tlb) index (some entry))

def match_TLB_Entry (ent : TLB_Entry) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (vpn : (BitVec (57 - 12))) : Bool :=
  ((ent.global || (ent.asid == asid)) && (ent.vpn == (vpn &&& (Complement.complement ent.levelMask))))

def flush_TLB_Entry (ent : TLB_Entry) (asid : (Option (BitVec (if ( 64 = 32  : Bool) then 9 else 16)))) (vaddr : (Option (BitVec 64))) : Bool :=
  let asid_matches : Bool :=
    match asid with
    | .some asid => ((ent.asid == asid) && (not ent.global))
    | none => true
  let addr_matches : Bool :=
    match vaddr with
    | .some vaddr =>
      (let vaddr : (BitVec 64) := (sign_extend (m := 64) vaddr)
      (ent.vpn == ((Sail.BitVec.extractLsb vaddr 56 pagesize_bits) &&& (Complement.complement
            ent.levelMask))))
    | none => true
  (asid_matches && addr_matches)

/-- Type quantifiers: sv_width : Nat, is_sv_mode(sv_width) -/
def lookup_TLB (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (vpn : (BitVec (sv_width - 12))) : SailM (Option (Nat × TLB_Entry)) := do
  let index := (tlb_hash sv_width vpn)
  match (GetElem?.getElem! (← readReg tlb) index) with
  | none => (pure none)
  | .some entry =>
    (if ((match_TLB_Entry entry asid (sign_extend (m := (57 -i 12)) vpn)) : Bool)
    then (pure (some (index, entry)))
    else (pure none))

/-- Type quantifiers: k_ex259838_ : Bool, level : Nat, sv_width : Nat, is_sv_mode(sv_width), 0 ≤
  level ∧
  level ≤
  (if ( sv_width = 32  : Bool) then 1 else (if ( sv_width = 39  : Bool) then 2 else (if ( sv_width =
  48  : Bool) then 3 else 4))) -/
def add_to_TLB (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (vpn : (BitVec (sv_width - 12))) (ppn : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44))) (pte : (BitVec (if ( sv_width = 32  : Bool) then 32 else 64))) (pteAddr : physaddr) (level : Nat) (global : Bool) : SailM Unit := do
  let shift :=
    (level *i (if ((sv_width == 32) : Bool)
      then 10
      else 9))
  let levelMask := (ones (n := shift))
  let index := (tlb_hash sv_width vpn)
  let vpn := (vpn &&& (Complement.complement (zero_extend (m := (sv_width -i 12)) levelMask)))
  let ppn :=
    (ppn &&& (Complement.complement
        (zero_extend
          (m := (if ((sv_width == 32) : Bool)
          then 22
          else 44)) levelMask)))
  let entry : TLB_Entry :=
    { asid := asid
      global := global
      pte := (zero_extend (m := 64) pte)
      pteAddr := pteAddr
      levelMask := (zero_extend (m := (57 -i 12)) levelMask)
      vpn := (sign_extend (m := (57 -i 12)) vpn)
      ppn := (zero_extend (m := 44) ppn) }
  writeReg tlb (vectorUpdate (← readReg tlb) index (some entry))
  (pure (tlb_add_callback (← readReg tlb) index))

def flush_TLB (asid : (Option (BitVec (if ( 64 = 32  : Bool) then 9 else 16)))) (addr : (Option (BitVec 64))) : SailM Unit := do
  let _ : Unit := (tlb_flush_begin_callback ())
  let loop_i_lower := 0
  let loop_i_upper ← do (pure ((Vector.length (← readReg tlb)) -i 1))
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      match (GetElem?.getElem! (← readReg tlb) i) with
      | none => (pure ())
      | .some entry =>
        (do
          if ((flush_TLB_Entry entry asid addr) : Bool)
          then
            (do
              writeReg tlb (vectorUpdate (← readReg tlb) i none)
              (pure (tlb_flush_callback i)))
          else (pure ()))
  (pure loop_vars)
  (pure (tlb_flush_end_callback (← readReg tlb)))

