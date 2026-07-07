import Out.HexBits
import Out.Xlen
import Out.PlatformConfig

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

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ∈ {16, 32} -/
def fetch_callback (x_0 : (BitVec k_n)) : Unit :=
  ()

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_write_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_read_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

def mem_exception_callback (x_0 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_1 : (BitVec 6)) : Unit :=
  ()

def pc_write_callback (x_0 : (BitVec 64)) : Unit :=
  ()

def xreg_full_write_callback (x_0 : String) (x_1 : regidx) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_write_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_read_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def redirect_callback (x_0 : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: k_ex252464_ : Bool -/
def trap_callback (x_0 : Bool) (x_1 : (BitVec 6)) : Unit :=
  ()

/-- Type quantifiers: k_ex252465_ : Bool -/
def xret_callback (x_0 : Bool) : Unit :=
  ()

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | "misa" => (pure (some 0x301#12))
    | "mstatus" => (pure (some 0x300#12))
    | "mstatush" => (pure (some 0x310#12))
    | "mseccfg" => (pure (some 0x747#12))
    | "mseccfgh" => (pure (some 0x757#12))
    | "menvcfg" => (pure (some 0x30A#12))
    | "menvcfgh" => (pure (some 0x31A#12))
    | "senvcfg" => (pure (some 0x10A#12))
    | "mcause" => (pure (some 0x342#12))
    | "mtval" => (pure (some 0x343#12))
    | "mscratch" => (pure (some 0x340#12))
    | "scounteren" => (pure (some 0x106#12))
    | "mcounteren" => (pure (some 0x306#12))
    | "mcountinhibit" => (pure (some 0x320#12))
    | "mvendorid" => (pure (some 0xF11#12))
    | "marchid" => (pure (some 0xF12#12))
    | "mimpid" => (pure (some 0xF13#12))
    | "mhartid" => (pure (some 0xF14#12))
    | "mconfigptr" => (pure (some 0xF15#12))
    | "sstatus" => (pure (some 0x100#12))
    | "sscratch" => (pure (some 0x140#12))
    | "scause" => (pure (some 0x142#12))
    | "stval" => (pure (some 0x143#12))
    | "tselect" => (pure (some 0x7A0#12))
    | "tdata1" => (pure (some 0x7A1#12))
    | "tdata2" => (pure (some 0x7A2#12))
    | "tdata3" => (pure (some 0x7A3#12))
    | "mie" => (pure (some 0x304#12))
    | "mip" => (pure (some 0x344#12))
    | "medeleg" => (pure (some 0x302#12))
    | "medelegh" => (pure (some 0x312#12))
    | "mideleg" => (pure (some 0x303#12))
    | "sip" => (pure (some 0x144#12))
    | "sie" => (pure (some 0x104#12))
    | "stvec" => (pure (some 0x105#12))
    | "sepc" => (pure (some 0x141#12))
    | "mtvec" => (pure (some 0x305#12))
    | "mepc" => (pure (some 0x341#12))
    | "pmpcfg0" => (pure (some 0x3A0#12))
    | "pmpcfg1" => (pure (some 0x3A1#12))
    | "pmpcfg2" => (pure (some 0x3A2#12))
    | "pmpcfg3" => (pure (some 0x3A3#12))
    | "pmpcfg4" => (pure (some 0x3A4#12))
    | "pmpcfg5" => (pure (some 0x3A5#12))
    | "pmpcfg6" => (pure (some 0x3A6#12))
    | "pmpcfg7" => (pure (some 0x3A7#12))
    | "pmpcfg8" => (pure (some 0x3A8#12))
    | "pmpcfg9" => (pure (some 0x3A9#12))
    | "pmpcfg10" => (pure (some 0x3AA#12))
    | "pmpcfg11" => (pure (some 0x3AB#12))
    | "pmpcfg12" => (pure (some 0x3AC#12))
    | "pmpcfg13" => (pure (some 0x3AD#12))
    | "pmpcfg14" => (pure (some 0x3AE#12))
    | "pmpcfg15" => (pure (some 0x3AF#12))
    | "pmpaddr0" => (pure (some 0x3B0#12))
    | "pmpaddr1" => (pure (some 0x3B1#12))
    | "pmpaddr2" => (pure (some 0x3B2#12))
    | "pmpaddr3" => (pure (some 0x3B3#12))
    | "pmpaddr4" => (pure (some 0x3B4#12))
    | "pmpaddr5" => (pure (some 0x3B5#12))
    | "pmpaddr6" => (pure (some 0x3B6#12))
    | "pmpaddr7" => (pure (some 0x3B7#12))
    | "pmpaddr8" => (pure (some 0x3B8#12))
    | "pmpaddr9" => (pure (some 0x3B9#12))
    | "pmpaddr10" => (pure (some 0x3BA#12))
    | "pmpaddr11" => (pure (some 0x3BB#12))
    | "pmpaddr12" => (pure (some 0x3BC#12))
    | "pmpaddr13" => (pure (some 0x3BD#12))
    | "pmpaddr14" => (pure (some 0x3BE#12))
    | "pmpaddr15" => (pure (some 0x3BF#12))
    | "pmpaddr16" => (pure (some 0x3C0#12))
    | "pmpaddr17" => (pure (some 0x3C1#12))
    | "pmpaddr18" => (pure (some 0x3C2#12))
    | "pmpaddr19" => (pure (some 0x3C3#12))
    | "pmpaddr20" => (pure (some 0x3C4#12))
    | "pmpaddr21" => (pure (some 0x3C5#12))
    | "pmpaddr22" => (pure (some 0x3C6#12))
    | "pmpaddr23" => (pure (some 0x3C7#12))
    | "pmpaddr24" => (pure (some 0x3C8#12))
    | "pmpaddr25" => (pure (some 0x3C9#12))
    | "pmpaddr26" => (pure (some 0x3CA#12))
    | "pmpaddr27" => (pure (some 0x3CB#12))
    | "pmpaddr28" => (pure (some 0x3CC#12))
    | "pmpaddr29" => (pure (some 0x3CD#12))
    | "pmpaddr30" => (pure (some 0x3CE#12))
    | "pmpaddr31" => (pure (some 0x3CF#12))
    | "pmpaddr32" => (pure (some 0x3D0#12))
    | "pmpaddr33" => (pure (some 0x3D1#12))
    | "pmpaddr34" => (pure (some 0x3D2#12))
    | "pmpaddr35" => (pure (some 0x3D3#12))
    | "pmpaddr36" => (pure (some 0x3D4#12))
    | "pmpaddr37" => (pure (some 0x3D5#12))
    | "pmpaddr38" => (pure (some 0x3D6#12))
    | "pmpaddr39" => (pure (some 0x3D7#12))
    | "pmpaddr40" => (pure (some 0x3D8#12))
    | "pmpaddr41" => (pure (some 0x3D9#12))
    | "pmpaddr42" => (pure (some 0x3DA#12))
    | "pmpaddr43" => (pure (some 0x3DB#12))
    | "pmpaddr44" => (pure (some 0x3DC#12))
    | "pmpaddr45" => (pure (some 0x3DD#12))
    | "pmpaddr46" => (pure (some 0x3DE#12))
    | "pmpaddr47" => (pure (some 0x3DF#12))
    | "pmpaddr48" => (pure (some 0x3E0#12))
    | "pmpaddr49" => (pure (some 0x3E1#12))
    | "pmpaddr50" => (pure (some 0x3E2#12))
    | "pmpaddr51" => (pure (some 0x3E3#12))
    | "pmpaddr52" => (pure (some 0x3E4#12))
    | "pmpaddr53" => (pure (some 0x3E5#12))
    | "pmpaddr54" => (pure (some 0x3E6#12))
    | "pmpaddr55" => (pure (some 0x3E7#12))
    | "pmpaddr56" => (pure (some 0x3E8#12))
    | "pmpaddr57" => (pure (some 0x3E9#12))
    | "pmpaddr58" => (pure (some 0x3EA#12))
    | "pmpaddr59" => (pure (some 0x3EB#12))
    | "pmpaddr60" => (pure (some 0x3EC#12))
    | "pmpaddr61" => (pure (some 0x3ED#12))
    | "pmpaddr62" => (pure (some 0x3EE#12))
    | "pmpaddr63" => (pure (some 0x3EF#12))
    | "fflags" => (pure (some 0x001#12))
    | "frm" => (pure (some 0x002#12))
    | "fcsr" => (pure (some 0x003#12))
    | "vstart" => (pure (some 0x008#12))
    | "vxsat" => (pure (some 0x009#12))
    | "vxrm" => (pure (some 0x00A#12))
    | "vcsr" => (pure (some 0x00F#12))
    | "vl" => (pure (some 0xC20#12))
    | "vtype" => (pure (some 0xC21#12))
    | "vlenb" => (pure (some 0xC22#12))
    | "mcyclecfg" => (pure (some 0x321#12))
    | "mcyclecfgh" => (pure (some 0x721#12))
    | "minstretcfg" => (pure (some 0x322#12))
    | "minstretcfgh" => (pure (some 0x722#12))
    | "mstateen0" => (pure (some 0x30C#12))
    | "mstateen1" => (pure (some 0x30D#12))
    | "mstateen2" => (pure (some 0x30E#12))
    | "mstateen3" => (pure (some 0x30F#12))
    | "mstateen0h" => (pure (some 0x31C#12))
    | "mstateen1h" => (pure (some 0x31D#12))
    | "mstateen2h" => (pure (some 0x31E#12))
    | "mstateen3h" => (pure (some 0x31F#12))
    | "hstateen0" => (pure (some 0x60C#12))
    | "hstateen1" => (pure (some 0x60D#12))
    | "hstateen2" => (pure (some 0x60E#12))
    | "hstateen3" => (pure (some 0x60F#12))
    | "hstateen0h" => (pure (some 0x61C#12))
    | "hstateen1h" => (pure (some 0x61D#12))
    | "hstateen2h" => (pure (some 0x61E#12))
    | "hstateen3h" => (pure (some 0x61F#12))
    | "sstateen0" => (pure (some 0x10C#12))
    | "sstateen1" => (pure (some 0x10D#12))
    | "sstateen2" => (pure (some 0x10E#12))
    | "sstateen3" => (pure (some 0x10F#12))
    | "satp" => (pure (some 0x180#12))
    | mapping0_ =>
      (do
        if ((hex_bits_12_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (hex_bits_12_backwards mapping0_)) with
            | reg => (pure (some reg)))
        else (pure none))) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_name_write_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_write_callback name csr value))

def csr_id_write_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_write_callback name csr value))

def csr_name_read_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_read_callback name csr value))

def csr_id_read_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_read_callback name csr value))

def long_csr_write_callback (name : String) (name_high : String) (value : (BitVec 64)) : SailM Unit := do
  (csr_name_write_callback name (Sail.BitVec.extractLsb value (xlen -i 1) 0))

