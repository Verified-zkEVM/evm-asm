import Out.Flow
import Out.Prelude
import Out.Errors
import Out.IsaVersion
import Out.Xlen
import Out.MemAddrtype
import Out.PlatformConfig
import Out.TypesExt
import Out.Types
import Out.VmemTypes
import Out.SysRegs
import Out.SysControl
import Out.Mem
import Out.VmemPte
import Out.VmemPtw
import Out.Callbacks0
import Out.VmemTlb

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

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, pte_size ∈ {4, 8} -/
def write_pte (paddr : physaddr) (pte_size : Nat) (pte : (BitVec (pte_size * 8))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  (mem_write_value_priv paddr pte_size pte Supervisor (Store PageTableEntry) PBMT_PMA false false
    false)

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, pte_size ∈ {4, 8} -/
def read_pte (paddr : physaddr) (pte_size : Nat) : SailM (Result (BitVec (8 * pte_size)) (physaddr × ExceptionType)) := do
  (mem_read_priv (Load PageTableEntry) PBMT_PMA Supervisor paddr pte_size false false false)

/-- Type quantifiers: pteWidth : Nat, pteWidth ≥ 0, pteWidth ∈ {4, 8} -/
def update_and_write_pte (pteAddr : physaddr) (pteWidth : Nat) (pte : (BitVec (pteWidth * 8))) (access : (MemoryAccessType mem_payload)) : SailM (Result (Option (BitVec (pteWidth * 8))) PTW_Error) := do
  match (update_PTE_Bits pte access) with
  | none => (pure (Ok none))
  | .some pte =>
    (do
      if ((((← (currentlyEnabled Ext_Svadu)) && ((_get_MEnvcfg_ADUE (← readReg menvcfg)) == 1#1)) || ((not
               (← (currentlyEnabled Ext_Svadu))) && (not (← (currentlyEnabled Ext_Svade))))) : Bool)
      then
        (do
          match (← (write_pte pteAddr pteWidth pte)) with
          | .Ok _ => (pure (Ok (some pte)))
          | .Err _ => (pure (Err (PTW_No_Access ()))))
      else (pure (Err (PTW_PTE_Needs_Update ()))))

/-- Type quantifiers: k_ex499955_ : Bool, level : Nat, k_ex499953_ : Bool, k_ex499952_ : Bool, sv_width
  : Nat, is_sv_mode(sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32  : Bool) then 1 else (if ( sv_width = 39  : Bool) then 2 else (if ( sv_width =
  48  : Bool) then 3 else 4))) -/
def pt_walk (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44))) (level : Nat) (global : Bool) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let _ : Unit := (ptw_start_callback (zero_extend (m := 64) vpn) access (priv, ()))
  let vpn_i_size :=
    if ((sv_width == 32) : Bool)
    then 10
    else 9
  let vpn_i :=
    (Sail.BitVec.extractLsb vpn (((level +i 1) *i vpn_i_size) -i 1) (level *i vpn_i_size))
  let log_pte_size_bytes :=
    if ((sv_width == 32) : Bool)
    then 2
    else 3
  let pte_addr := (pt_base +++ (vpn_i +++ (zeros (n := log_pte_size_bytes))))
  assert ((sv_width == 32) || (xlen == 64)) "sys/vmem.sail:128.36-128.37"
  let pte_addr := (Physaddr (zero_extend (m := 64) pte_addr))
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ =>
    (let _ : Unit := (ptw_fail_callback (PTW_No_Access ()) level (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_No_Access ()), ext_ptw))))
  | .Ok pte =>
    (do
      let _ : Unit :=
        (ptw_step_callback level (bits_of_physaddr pte_addr) (zero_extend (m := 64) pte))
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let pte_ext := (ext_bits_of_PTE pte)
      if ((← (pte_is_invalid pte_flags pte_ext)) : Bool)
      then
        (let _ : Unit := (ptw_fail_callback (PTW_Invalid_PTE ()) level (bits_of_physaddr pte_addr))
        (pure (Err ((PTW_Invalid_PTE ()), ext_ptw))))
      else
        (do
          let ppn := (PPN_of_PTE pte)
          let global := (global || ((_get_PTE_Flags_G pte_flags) == 1#1))
          if ((pte_is_non_leaf pte_flags) : Bool)
          then
            (do
              if ((level >b 0) : Bool)
              then (pt_walk sv_width vpn access priv mxr do_sum ppn (level -i 1) global ext_ptw)
              else
                (let _ : Unit :=
                  (ptw_fail_callback (PTW_Invalid_PTE ()) level (bits_of_physaddr pte_addr))
                (pure (Err ((PTW_Invalid_PTE ()), ext_ptw)))))
          else
            (do
              let ppn_size_bits :=
                if ((sv_width == 32) : Bool)
                then 10
                else 9
              if ((level >b 0) : Bool)
              then
                (do
                  let low_bits := (ppn_size_bits *i level)
                  if (((Sail.BitVec.extractLsb ppn (low_bits -i 1) 0) != (zeros
                         (n := (((((if ((sv_width == 32) : Bool)
                                 then 10
                                 else 9) *i level) -i 1) -i 0) +i 1)))) : Bool)
                  then
                    SailME.throw (let _ : Unit :=
                        (ptw_fail_callback (PTW_Misaligned ()) level (bits_of_physaddr pte_addr))
                      (Err ((PTW_Misaligned ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                  else (pure ()))
              else (pure ())
              match (← (check_PTE_permission access priv mxr do_sum pte_flags pte_ext ext_ptw)) with
              | .PTE_Check_Failure (ext_ptw, pte_failure) =>
                (let _ : Unit :=
                  (ptw_fail_callback (ext_get_ptw_error pte_failure) level
                    (bits_of_physaddr pte_addr))
                (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw))))
              | .PTE_Check_Success ext_ptw =>
                (do
                  let ppn ← do
                    if ((level >b 0) : Bool)
                    then
                      (do
                        if ((((_get_PTE_Ext_N pte_ext) == 1#1) && pte_reserved_bits_must_be_zero) : Bool)
                        then
                          SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                        else
                          (let low_bits := (ppn_size_bits *i level)
                          (pure ((Sail.BitVec.extractLsb ppn ((Sail.BitVec.length ppn) -i 1)
                                low_bits) +++ (Sail.BitVec.extractLsb vpn (low_bits -i 1) 0)))))
                    else
                      (do
                        if (((← (currentlyEnabled Ext_Svnapot)) && ((_get_PTE_Ext_N pte_ext) == 1#1)) : Bool)
                        then
                          (do
                            let pte_napot_bits := 4
                            if (((Sail.BitVec.extractLsb ppn (pte_napot_bits -i 1) 0) != 0b1000#4) : Bool)
                            then
                              SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                            else
                              (pure (Sail.BitVec.updateSubrange ppn (pte_napot_bits -i 1) 0
                                  (Sail.BitVec.extractLsb vpn (pte_napot_bits -i 1) 0))))
                        else (pure ppn))
                  let pbmt ← do
                    if (((_get_MEnvcfg_PBMTE (← readReg menvcfg)) == 0#1) : Bool)
                    then (pure PBMT_PMA)
                    else (page_based_mem_type_forwards (_get_PTE_Ext_PBMT pte_ext))
                  let _ : Unit := (ptw_success_callback (zero_extend (m := 64) ppn) level)
                  (pure (Ok
                      ({ ppn := ppn
                         pte := pte
                         pteAddr := pte_addr
                         level := level
                         pbmt := pbmt
                         global := global }, ext_ptw)))))))
termination_by (let (_, _, _, _, _, _, _, level, _, _) :=
  (sv_width, vpn, access, priv, mxr, do_sum, pt_base, level, global, ext_ptw)
level).toNat

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ∈ {32, 64} -/
def satp_to_asid (satp_val : (BitVec k_n)) : (BitVec (if ( k_n = 32  : Bool) then 9 else 16)) :=
  if (((Sail.BitVec.length satp_val) == 32) : Bool)
  then (_get_Satp32_Asid (Mk_Satp32 satp_val))
  else (_get_Satp64_Asid (Mk_Satp64 satp_val))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ∈ {32, 64} -/
def satp_to_ppn (satp_val : (BitVec k_n)) : (BitVec (if ( k_n = 32  : Bool) then 22 else 44)) :=
  if (((Sail.BitVec.length satp_val) == 32) : Bool)
  then (_get_Satp32_PPN (Mk_Satp32 satp_val))
  else (_get_Satp64_PPN (Mk_Satp64 satp_val))

def translationMode (priv : Privilege) : SailM SATPMode := do
  if ((priv == Machine) : Bool)
  then (pure Bare)
  else
    (do
      let arch ← do (architecture Supervisor)
      let mbits ← (( do
        match arch with
        | .RV64 =>
          (do
            assert (xlen ≥b 64) "sys/vmem.sail:255.25-255.26"
            (pure (_get_Satp64_Mode (Mk_Satp64 (← readReg satp)))))
        | .RV32 =>
          (pure (0b000#3 +++ (_get_Satp32_Mode
                (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg satp) 31 0)))))
        | .RV128 => (internal_error "sys/vmem.sail" 259 "RV128 not supported") ) : SailM satp_mode )
      match (satpMode_of_bits arch mbits) with
      | .some m => (pure m)
      | none => (internal_error "sys/vmem.sail" 264 "invalid translation mode in satp"))

/-- Type quantifiers: tlb_index : Nat, k_ex500032_ : Bool, k_ex500031_ : Bool, sv_width : Nat, is_sv_mode(sv_width), 0
  ≤ tlb_index ∧ tlb_index ≤ (2 ^ 6 - 1) -/
def translate_TLB_hit (sv_width : Nat) (_asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) (tlb_index : Nat) (ent : TLB_Entry) : SailM (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let pte_size :=
    if ((sv_width == 32) : Bool)
    then 4
    else 8
  let pte := (tlb_get_pte pte_size ent)
  let ext_pte := (ext_bits_of_PTE pte)
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_check ← do (check_PTE_permission access priv mxr do_sum pte_flags ext_pte ext_ptw)
  match pte_check with
  | .PTE_Check_Failure (ext_ptw, pte_failure) =>
    (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw)))
  | .PTE_Check_Success ext_ptw =>
    (do
      match (← (update_and_write_pte ent.pteAddr pte_size pte access)) with
      | .Ok (.some pte) =>
        (do
          (write_TLB tlb_index (tlb_set_pte ent pte))
          (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw))))
      | .Ok none => (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw)))
      | .Err (.PTW_PTE_Needs_Update ()) => (pure (Err ((PTW_PTE_Needs_Update ()), ext_ptw)))
      | .Err e => (pure (Err (e, ext_ptw))))

/-- Type quantifiers: k_ex500052_ : Bool, k_ex500051_ : Bool, sv_width : Nat, is_sv_mode(sv_width) -/
def translate_TLB_miss (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (base_ppn : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let initial_level :=
    if ((sv_width == 32) : Bool)
    then 1
    else
      (if ((sv_width == 39) : Bool)
      then 2
      else
        (if ((sv_width == 48) : Bool)
        then 3
        else 4))
  let pte_size :=
    if ((sv_width == 32) : Bool)
    then 4
    else 8
  let ptw_result ← do
    (pt_walk sv_width vpn access priv mxr do_sum base_ppn initial_level false ext_ptw)
  match ptw_result with
  | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw)))
  | .Ok ({ ppn := ppn, pte := pte, pteAddr := pteAddr, level := level, pbmt := pbmt, global := global }, ext_ptw) =>
    (do
      let ext_pte := (ext_bits_of_PTE pte)
      match (← (update_and_write_pte pteAddr pte_size pte access)) with
      | .Ok (.some new_pte) =>
        (do
          (add_to_TLB sv_width asid vpn ppn new_pte pteAddr level global)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Ok none =>
        (do
          (add_to_TLB sv_width asid vpn ppn pte pteAddr level global)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Err e => (pure (Err (e, ext_ptw))))

def satp_mode_width_forwards (arg_ : SATPMode) : SailM Int := do
  match arg_ with
  | .Sv32 => (pure 32)
  | .Sv39 => (pure 39)
  | .Sv48 => (pure 48)
  | .Sv57 => (pure 57)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {32, 39, 48, 57} -/
def satp_mode_width_backwards (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 32 => Sv32
  | 39 => Sv39
  | 48 => Sv48
  | _ => Sv57

def satp_mode_width_forwards_matches (arg_ : SATPMode) : Bool :=
  match arg_ with
  | .Sv32 => true
  | .Sv39 => true
  | .Sv48 => true
  | .Sv57 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {32, 39, 48, 57} -/
def satp_mode_width_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 32 => true
  | 39 => true
  | 48 => true
  | 57 => true
  | _ => false

/-- Type quantifiers: k_ex500087_ : Bool, k_ex500086_ : Bool, sv_width : Nat, is_sv_mode(sv_width) -/
def translate (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (base_ppn : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vpn)) with
  | .some (index, ent) =>
    (translate_TLB_hit sv_width asid vpn access priv mxr do_sum ext_ptw index ent)
  | none => (translate_TLB_miss sv_width asid base_ppn vpn access priv mxr do_sum ext_ptw)

/-- Type quantifiers: sv_width : Nat, is_sv_mode(sv_width) -/
def get_satp (sv_width : Nat) : SailM (BitVec (if ( sv_width = 32  : Bool) then 32 else 64)) := do
  assert ((sv_width == 32) || (xlen == 64)) "sys/vmem.sail:396.30-396.31"
  if ((sv_width == 32) : Bool)
  then (pure (Sail.BitVec.extractLsb (← readReg satp) 31 0))
  else readReg satp

def translateAddr (vAddr : virtaddr) (access : (MemoryAccessType mem_payload)) : SailM (Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) := SailME.run do
  let effPriv ← do (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  let mode ← do (translationMode effPriv)
  if ((← (is_shadow_stack_access access)) : Bool)
  then
    (do
      if ((((mode == Bare) && (bne effPriv Machine)) || (effPriv == Machine)) : Bool)
      then
        SailME.throw ((Err ((E_SAMO_Access_Fault ()), init_ext_ptw)) : (Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)))
      else (pure ()))
  else (pure ())
  if ((mode == Bare) : Bool)
  then
    (pure (Ok ((Physaddr (zero_extend (m := 64) (bits_of_virtaddr vAddr))), PBMT_PMA, init_ext_ptw)))
  else
    (do
      let sv_width ← do (satp_mode_width_forwards mode)
      let satp_sxlen ← do (get_satp sv_width)
      assert ((sv_width == 32) || (xlen == 64)) "sys/vmem.sail:432.36-432.37"
      let svAddr := (Sail.BitVec.extractLsb (bits_of_virtaddr vAddr) (sv_width -i 1) 0)
      if (((bits_of_virtaddr vAddr) != (sign_extend (m := 64) svAddr)) : Bool)
      then (pure (Err ((← (translationException access (PTW_Invalid_Addr ()))), init_ext_ptw)))
      else
        (do
          let mxr ← do (pure ((_get_Mstatus_MXR (← readReg mstatus)) == 1#1))
          let do_sum ← do (pure ((_get_Mstatus_SUM (← readReg mstatus)) == 1#1))
          let asid := (satp_to_asid satp_sxlen)
          let base_ppn := (satp_to_ppn satp_sxlen)
          let res ← do
            (translate sv_width (zero_extend (m := 16) asid) base_ppn
              (Sail.BitVec.extractLsb svAddr (sv_width -i 1) pagesize_bits) access effPriv mxr
              do_sum init_ext_ptw)
          match res with
          | .Ok (ppn, pbmt, ext_ptw) =>
            (let paddr :=
              (ppn +++ (Sail.BitVec.extractLsb (bits_of_virtaddr vAddr) (pagesize_bits -i 1) 0))
            (pure (Ok ((Physaddr (zero_extend (m := 64) paddr)), pbmt, ext_ptw))))
          | .Err (f, ext_ptw) => (pure (Err ((← (translationException access f)), ext_ptw)))))

def reset_vmem (_ : Unit) : SailM Unit := do
  (reset_TLB ())

