import Out.HexBits

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

def csr_name_map_forwards_matches (arg_ : (BitVec 12)) : Bool :=
  match arg_ with
  | 0x301 => true
  | 0x300 => true
  | 0x310 => true
  | 0x747 => true
  | 0x757 => true
  | 0x30A => true
  | 0x31A => true
  | 0x10A => true
  | 0x342 => true
  | 0x343 => true
  | 0x340 => true
  | 0x106 => true
  | 0x306 => true
  | 0x320 => true
  | 0xF11 => true
  | 0xF12 => true
  | 0xF13 => true
  | 0xF14 => true
  | 0xF15 => true
  | 0x100 => true
  | 0x140 => true
  | 0x142 => true
  | 0x143 => true
  | 0x7A0 => true
  | 0x7A1 => true
  | 0x7A2 => true
  | 0x7A3 => true
  | 0x304 => true
  | 0x344 => true
  | 0x302 => true
  | 0x312 => true
  | 0x303 => true
  | 0x144 => true
  | 0x104 => true
  | 0x105 => true
  | 0x141 => true
  | 0x305 => true
  | 0x341 => true
  | 0x3A0 => true
  | 0x3A1 => true
  | 0x3A2 => true
  | 0x3A3 => true
  | 0x3A4 => true
  | 0x3A5 => true
  | 0x3A6 => true
  | 0x3A7 => true
  | 0x3A8 => true
  | 0x3A9 => true
  | 0x3AA => true
  | 0x3AB => true
  | 0x3AC => true
  | 0x3AD => true
  | 0x3AE => true
  | 0x3AF => true
  | 0x3B0 => true
  | 0x3B1 => true
  | 0x3B2 => true
  | 0x3B3 => true
  | 0x3B4 => true
  | 0x3B5 => true
  | 0x3B6 => true
  | 0x3B7 => true
  | 0x3B8 => true
  | 0x3B9 => true
  | 0x3BA => true
  | 0x3BB => true
  | 0x3BC => true
  | 0x3BD => true
  | 0x3BE => true
  | 0x3BF => true
  | 0x3C0 => true
  | 0x3C1 => true
  | 0x3C2 => true
  | 0x3C3 => true
  | 0x3C4 => true
  | 0x3C5 => true
  | 0x3C6 => true
  | 0x3C7 => true
  | 0x3C8 => true
  | 0x3C9 => true
  | 0x3CA => true
  | 0x3CB => true
  | 0x3CC => true
  | 0x3CD => true
  | 0x3CE => true
  | 0x3CF => true
  | 0x3D0 => true
  | 0x3D1 => true
  | 0x3D2 => true
  | 0x3D3 => true
  | 0x3D4 => true
  | 0x3D5 => true
  | 0x3D6 => true
  | 0x3D7 => true
  | 0x3D8 => true
  | 0x3D9 => true
  | 0x3DA => true
  | 0x3DB => true
  | 0x3DC => true
  | 0x3DD => true
  | 0x3DE => true
  | 0x3DF => true
  | 0x3E0 => true
  | 0x3E1 => true
  | 0x3E2 => true
  | 0x3E3 => true
  | 0x3E4 => true
  | 0x3E5 => true
  | 0x3E6 => true
  | 0x3E7 => true
  | 0x3E8 => true
  | 0x3E9 => true
  | 0x3EA => true
  | 0x3EB => true
  | 0x3EC => true
  | 0x3ED => true
  | 0x3EE => true
  | 0x3EF => true
  | 0x001 => true
  | 0x002 => true
  | 0x003 => true
  | 0x008 => true
  | 0x009 => true
  | 0x00A => true
  | 0x00F => true
  | 0xC20 => true
  | 0xC21 => true
  | 0xC22 => true
  | 0x321 => true
  | 0x721 => true
  | 0x322 => true
  | 0x722 => true
  | 0x30C => true
  | 0x30D => true
  | 0x30E => true
  | 0x30F => true
  | 0x31C => true
  | 0x31D => true
  | 0x31E => true
  | 0x31F => true
  | 0x60C => true
  | 0x60D => true
  | 0x60E => true
  | 0x60F => true
  | 0x61C => true
  | 0x61D => true
  | 0x61E => true
  | 0x61F => true
  | 0x10C => true
  | 0x10D => true
  | 0x10E => true
  | 0x10F => true
  | 0x180 => true
  | reg => true

def csr_name_map_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | "misa" => (pure (some true))
    | "mstatus" => (pure (some true))
    | "mstatush" => (pure (some true))
    | "mseccfg" => (pure (some true))
    | "mseccfgh" => (pure (some true))
    | "menvcfg" => (pure (some true))
    | "menvcfgh" => (pure (some true))
    | "senvcfg" => (pure (some true))
    | "mcause" => (pure (some true))
    | "mtval" => (pure (some true))
    | "mscratch" => (pure (some true))
    | "scounteren" => (pure (some true))
    | "mcounteren" => (pure (some true))
    | "mcountinhibit" => (pure (some true))
    | "mvendorid" => (pure (some true))
    | "marchid" => (pure (some true))
    | "mimpid" => (pure (some true))
    | "mhartid" => (pure (some true))
    | "mconfigptr" => (pure (some true))
    | "sstatus" => (pure (some true))
    | "sscratch" => (pure (some true))
    | "scause" => (pure (some true))
    | "stval" => (pure (some true))
    | "tselect" => (pure (some true))
    | "tdata1" => (pure (some true))
    | "tdata2" => (pure (some true))
    | "tdata3" => (pure (some true))
    | "mie" => (pure (some true))
    | "mip" => (pure (some true))
    | "medeleg" => (pure (some true))
    | "medelegh" => (pure (some true))
    | "mideleg" => (pure (some true))
    | "sip" => (pure (some true))
    | "sie" => (pure (some true))
    | "stvec" => (pure (some true))
    | "sepc" => (pure (some true))
    | "mtvec" => (pure (some true))
    | "mepc" => (pure (some true))
    | "pmpcfg0" => (pure (some true))
    | "pmpcfg1" => (pure (some true))
    | "pmpcfg2" => (pure (some true))
    | "pmpcfg3" => (pure (some true))
    | "pmpcfg4" => (pure (some true))
    | "pmpcfg5" => (pure (some true))
    | "pmpcfg6" => (pure (some true))
    | "pmpcfg7" => (pure (some true))
    | "pmpcfg8" => (pure (some true))
    | "pmpcfg9" => (pure (some true))
    | "pmpcfg10" => (pure (some true))
    | "pmpcfg11" => (pure (some true))
    | "pmpcfg12" => (pure (some true))
    | "pmpcfg13" => (pure (some true))
    | "pmpcfg14" => (pure (some true))
    | "pmpcfg15" => (pure (some true))
    | "pmpaddr0" => (pure (some true))
    | "pmpaddr1" => (pure (some true))
    | "pmpaddr2" => (pure (some true))
    | "pmpaddr3" => (pure (some true))
    | "pmpaddr4" => (pure (some true))
    | "pmpaddr5" => (pure (some true))
    | "pmpaddr6" => (pure (some true))
    | "pmpaddr7" => (pure (some true))
    | "pmpaddr8" => (pure (some true))
    | "pmpaddr9" => (pure (some true))
    | "pmpaddr10" => (pure (some true))
    | "pmpaddr11" => (pure (some true))
    | "pmpaddr12" => (pure (some true))
    | "pmpaddr13" => (pure (some true))
    | "pmpaddr14" => (pure (some true))
    | "pmpaddr15" => (pure (some true))
    | "pmpaddr16" => (pure (some true))
    | "pmpaddr17" => (pure (some true))
    | "pmpaddr18" => (pure (some true))
    | "pmpaddr19" => (pure (some true))
    | "pmpaddr20" => (pure (some true))
    | "pmpaddr21" => (pure (some true))
    | "pmpaddr22" => (pure (some true))
    | "pmpaddr23" => (pure (some true))
    | "pmpaddr24" => (pure (some true))
    | "pmpaddr25" => (pure (some true))
    | "pmpaddr26" => (pure (some true))
    | "pmpaddr27" => (pure (some true))
    | "pmpaddr28" => (pure (some true))
    | "pmpaddr29" => (pure (some true))
    | "pmpaddr30" => (pure (some true))
    | "pmpaddr31" => (pure (some true))
    | "pmpaddr32" => (pure (some true))
    | "pmpaddr33" => (pure (some true))
    | "pmpaddr34" => (pure (some true))
    | "pmpaddr35" => (pure (some true))
    | "pmpaddr36" => (pure (some true))
    | "pmpaddr37" => (pure (some true))
    | "pmpaddr38" => (pure (some true))
    | "pmpaddr39" => (pure (some true))
    | "pmpaddr40" => (pure (some true))
    | "pmpaddr41" => (pure (some true))
    | "pmpaddr42" => (pure (some true))
    | "pmpaddr43" => (pure (some true))
    | "pmpaddr44" => (pure (some true))
    | "pmpaddr45" => (pure (some true))
    | "pmpaddr46" => (pure (some true))
    | "pmpaddr47" => (pure (some true))
    | "pmpaddr48" => (pure (some true))
    | "pmpaddr49" => (pure (some true))
    | "pmpaddr50" => (pure (some true))
    | "pmpaddr51" => (pure (some true))
    | "pmpaddr52" => (pure (some true))
    | "pmpaddr53" => (pure (some true))
    | "pmpaddr54" => (pure (some true))
    | "pmpaddr55" => (pure (some true))
    | "pmpaddr56" => (pure (some true))
    | "pmpaddr57" => (pure (some true))
    | "pmpaddr58" => (pure (some true))
    | "pmpaddr59" => (pure (some true))
    | "pmpaddr60" => (pure (some true))
    | "pmpaddr61" => (pure (some true))
    | "pmpaddr62" => (pure (some true))
    | "pmpaddr63" => (pure (some true))
    | "fflags" => (pure (some true))
    | "frm" => (pure (some true))
    | "fcsr" => (pure (some true))
    | "vstart" => (pure (some true))
    | "vxsat" => (pure (some true))
    | "vxrm" => (pure (some true))
    | "vcsr" => (pure (some true))
    | "vl" => (pure (some true))
    | "vtype" => (pure (some true))
    | "vlenb" => (pure (some true))
    | "mcyclecfg" => (pure (some true))
    | "mcyclecfgh" => (pure (some true))
    | "minstretcfg" => (pure (some true))
    | "minstretcfgh" => (pure (some true))
    | "mstateen0" => (pure (some true))
    | "mstateen1" => (pure (some true))
    | "mstateen2" => (pure (some true))
    | "mstateen3" => (pure (some true))
    | "mstateen0h" => (pure (some true))
    | "mstateen1h" => (pure (some true))
    | "mstateen2h" => (pure (some true))
    | "mstateen3h" => (pure (some true))
    | "hstateen0" => (pure (some true))
    | "hstateen1" => (pure (some true))
    | "hstateen2" => (pure (some true))
    | "hstateen3" => (pure (some true))
    | "hstateen0h" => (pure (some true))
    | "hstateen1h" => (pure (some true))
    | "hstateen2h" => (pure (some true))
    | "hstateen3h" => (pure (some true))
    | "sstateen0" => (pure (some true))
    | "sstateen1" => (pure (some true))
    | "sstateen2" => (pure (some true))
    | "sstateen3" => (pure (some true))
    | "satp" => (pure (some true))
    | mapping0_ =>
      (do
        if ((hex_bits_12_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (hex_bits_12_backwards mapping0_)) with
            | reg => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

