import Out.HexBits
import Out.Prelude
import Out.Errors
import Out.Xlen
import Out.PlatformConfig
import Out.SysRegs
import Out.InterruptRegs
import Out.SysExceptions
import Out.PmpRegs
import Out.StateenRegs
import Out.FdextRegs
import Out.VextRegs
import Out.Smcntrpmf
import Out.Vmem

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

def read_CSR (merge_var : (BitVec 12)) : SailM (BitVec 64) := do
  match merge_var with
  | 0x301 => readReg misa
  | 0x300 => (pure (Sail.BitVec.extractLsb (← readReg mstatus) (xlen -i 1) 0))
  | 0x310 =>
    (do
      if ((xlen == 32) : Bool)
      then (pure (Sail.BitVec.extractLsb (← readReg mstatus) 63 32))
      else
        (do
          let v__380 := 0x310#12
          if ((((Sail.BitVec.extractLsb v__380 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                 (Sail.BitVec.extractLsb v__380 3 0)
               (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
              (pmpReadCfgReg (BitVec.toNatInt idx)))
          else
            (do
              if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                  (pmpReadAddrReg (BitVec.toNatInt (0b00#2 +++ idx))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                      (pmpReadAddrReg (BitVec.toNatInt (0b01#2 +++ idx))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                          (pmpReadAddrReg (BitVec.toNatInt (0b10#2 +++ idx))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                              (pmpReadAddrReg (BitVec.toNatInt (0b11#2 +++ idx))))
                          else
                            (do
                              match v__380 with
                              | 0x001 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FFLAGS (← readReg fcsr))))
                              | 0x002 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))
                              | 0x003 => (pure (zero_extend (m := 64) (← readReg fcsr)))
                              | 0x008 => readReg vstart
                              | 0x009 =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxsat (← readReg vcsr))))
                              | 0x00A =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))
                              | 0x00F => (pure (zero_extend (m := 64) (← readReg vcsr)))
                              | 0xC20 => readReg vl
                              | 0xC21 => readReg vtype
                              | 0xC22 => (pure VLENB)
                              | 0x321 =>
                                (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1) 0))
                              | 0x721 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x721#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x322 =>
                                (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1)
                                    0))
                              | 0x722 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x722#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x30C =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen0) (xlen -i 1) 0))
                              | 0x30D =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen1) (xlen -i 1) 0))
                              | 0x30E =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen2) (xlen -i 1) 0))
                              | 0x30F =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen3) (xlen -i 1) 0))
                              | 0x31C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x60C =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen0) &&& (← (get_hstateen_mask 0)))
                                    (xlen -i 1) 0))
                              | 0x60D =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen1) &&& (← (get_hstateen_mask 1)))
                                    (xlen -i 1) 0))
                              | 0x60E =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen2) &&& (← (get_hstateen_mask 2)))
                                    (xlen -i 1) 0))
                              | 0x60F =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen3) &&& (← (get_hstateen_mask 3)))
                                    (xlen -i 1) 0))
                              | 0x61C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen0) &&& (← (get_hstateen_mask 0))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen1) &&& (← (get_hstateen_mask 1))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen2) &&& (← (get_hstateen_mask 2))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen3) &&& (← (get_hstateen_mask 3))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x10C =>
                                (do
                                  let mask ← do (get_sstateen_mask 0)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen0) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10D =>
                                (do
                                  let mask ← do (get_sstateen_mask 1)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen1) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10E =>
                                (do
                                  let mask ← do (get_sstateen_mask 2)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen2) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10F =>
                                (do
                                  let mask ← do (get_sstateen_mask 3)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen3) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x180 => readReg satp
                              | v__380 =>
                                (internal_error "postlude/csr_end.sail" 17
                                  (HAppend.hAppend "Read from CSR that does not exist: "
                                    (BitVec.toFormatted v__380))))))))))
  | 0x747 => (pure (Sail.BitVec.extractLsb (← readReg mseccfg) (xlen -i 1) 0))
  | 0x757 =>
    (do
      if ((xlen == 32) : Bool)
      then (pure (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32))
      else
        (do
          let v__380 := 0x757#12
          if ((((Sail.BitVec.extractLsb v__380 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                 (Sail.BitVec.extractLsb v__380 3 0)
               (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
              (pmpReadCfgReg (BitVec.toNatInt idx)))
          else
            (do
              if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                  (pmpReadAddrReg (BitVec.toNatInt (0b00#2 +++ idx))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                      (pmpReadAddrReg (BitVec.toNatInt (0b01#2 +++ idx))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                          (pmpReadAddrReg (BitVec.toNatInt (0b10#2 +++ idx))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                              (pmpReadAddrReg (BitVec.toNatInt (0b11#2 +++ idx))))
                          else
                            (do
                              match v__380 with
                              | 0x001 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FFLAGS (← readReg fcsr))))
                              | 0x002 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))
                              | 0x003 => (pure (zero_extend (m := 64) (← readReg fcsr)))
                              | 0x008 => readReg vstart
                              | 0x009 =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxsat (← readReg vcsr))))
                              | 0x00A =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))
                              | 0x00F => (pure (zero_extend (m := 64) (← readReg vcsr)))
                              | 0xC20 => readReg vl
                              | 0xC21 => readReg vtype
                              | 0xC22 => (pure VLENB)
                              | 0x321 =>
                                (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1) 0))
                              | 0x721 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x721#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x322 =>
                                (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1)
                                    0))
                              | 0x722 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x722#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x30C =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen0) (xlen -i 1) 0))
                              | 0x30D =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen1) (xlen -i 1) 0))
                              | 0x30E =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen2) (xlen -i 1) 0))
                              | 0x30F =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen3) (xlen -i 1) 0))
                              | 0x31C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x60C =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen0) &&& (← (get_hstateen_mask 0)))
                                    (xlen -i 1) 0))
                              | 0x60D =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen1) &&& (← (get_hstateen_mask 1)))
                                    (xlen -i 1) 0))
                              | 0x60E =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen2) &&& (← (get_hstateen_mask 2)))
                                    (xlen -i 1) 0))
                              | 0x60F =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen3) &&& (← (get_hstateen_mask 3)))
                                    (xlen -i 1) 0))
                              | 0x61C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen0) &&& (← (get_hstateen_mask 0))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen1) &&& (← (get_hstateen_mask 1))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen2) &&& (← (get_hstateen_mask 2))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen3) &&& (← (get_hstateen_mask 3))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x10C =>
                                (do
                                  let mask ← do (get_sstateen_mask 0)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen0) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10D =>
                                (do
                                  let mask ← do (get_sstateen_mask 1)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen1) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10E =>
                                (do
                                  let mask ← do (get_sstateen_mask 2)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen2) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10F =>
                                (do
                                  let mask ← do (get_sstateen_mask 3)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen3) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x180 => readReg satp
                              | v__380 =>
                                (internal_error "postlude/csr_end.sail" 17
                                  (HAppend.hAppend "Read from CSR that does not exist: "
                                    (BitVec.toFormatted v__380))))))))))
  | 0x30A => (pure (Sail.BitVec.extractLsb (← readReg menvcfg) (xlen -i 1) 0))
  | 0x31A =>
    (do
      if ((xlen == 32) : Bool)
      then (pure (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32))
      else
        (do
          let v__380 := 0x31A#12
          if ((((Sail.BitVec.extractLsb v__380 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                 (Sail.BitVec.extractLsb v__380 3 0)
               (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
              (pmpReadCfgReg (BitVec.toNatInt idx)))
          else
            (do
              if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                  (pmpReadAddrReg (BitVec.toNatInt (0b00#2 +++ idx))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                      (pmpReadAddrReg (BitVec.toNatInt (0b01#2 +++ idx))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                          (pmpReadAddrReg (BitVec.toNatInt (0b10#2 +++ idx))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                              (pmpReadAddrReg (BitVec.toNatInt (0b11#2 +++ idx))))
                          else
                            (do
                              match v__380 with
                              | 0x001 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FFLAGS (← readReg fcsr))))
                              | 0x002 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))
                              | 0x003 => (pure (zero_extend (m := 64) (← readReg fcsr)))
                              | 0x008 => readReg vstart
                              | 0x009 =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxsat (← readReg vcsr))))
                              | 0x00A =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))
                              | 0x00F => (pure (zero_extend (m := 64) (← readReg vcsr)))
                              | 0xC20 => readReg vl
                              | 0xC21 => readReg vtype
                              | 0xC22 => (pure VLENB)
                              | 0x321 =>
                                (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1) 0))
                              | 0x721 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x721#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x322 =>
                                (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1)
                                    0))
                              | 0x722 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x722#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x30C =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen0) (xlen -i 1) 0))
                              | 0x30D =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen1) (xlen -i 1) 0))
                              | 0x30E =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen2) (xlen -i 1) 0))
                              | 0x30F =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen3) (xlen -i 1) 0))
                              | 0x31C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x60C =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen0) &&& (← (get_hstateen_mask 0)))
                                    (xlen -i 1) 0))
                              | 0x60D =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen1) &&& (← (get_hstateen_mask 1)))
                                    (xlen -i 1) 0))
                              | 0x60E =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen2) &&& (← (get_hstateen_mask 2)))
                                    (xlen -i 1) 0))
                              | 0x60F =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen3) &&& (← (get_hstateen_mask 3)))
                                    (xlen -i 1) 0))
                              | 0x61C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen0) &&& (← (get_hstateen_mask 0))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen1) &&& (← (get_hstateen_mask 1))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen2) &&& (← (get_hstateen_mask 2))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen3) &&& (← (get_hstateen_mask 3))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x10C =>
                                (do
                                  let mask ← do (get_sstateen_mask 0)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen0) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10D =>
                                (do
                                  let mask ← do (get_sstateen_mask 1)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen1) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10E =>
                                (do
                                  let mask ← do (get_sstateen_mask 2)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen2) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10F =>
                                (do
                                  let mask ← do (get_sstateen_mask 3)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen3) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x180 => readReg satp
                              | v__380 =>
                                (internal_error "postlude/csr_end.sail" 17
                                  (HAppend.hAppend "Read from CSR that does not exist: "
                                    (BitVec.toFormatted v__380))))))))))
  | 0x10A => (pure (Sail.BitVec.extractLsb (← (read_senvcfg ())) (xlen -i 1) 0))
  | 0x342 => readReg mcause
  | 0x343 => readReg mtval
  | 0x340 => readReg mscratch
  | 0x106 => (pure (zero_extend (m := 64) (← readReg scounteren)))
  | 0x306 => (pure (zero_extend (m := 64) (← readReg mcounteren)))
  | 0x320 => (pure (zero_extend (m := 64) (← readReg mcountinhibit)))
  | 0xF11 => (pure (zero_extend (m := 64) (← readReg mvendorid)))
  | 0xF12 => readReg marchid
  | 0xF13 => readReg mimpid
  | 0xF14 => readReg mhartid
  | 0xF15 => readReg mconfigptr
  | 0x100 => (pure (Sail.BitVec.extractLsb (lower_mstatus (← readReg mstatus)) (xlen -i 1) 0))
  | 0x140 => readReg sscratch
  | 0x142 => readReg scause
  | 0x143 => readReg stval
  | 0x7A0 => (pure (Complement.complement (← readReg tselect)))
  | 0x304 => readReg mie
  | 0x344 => (read_mip ExcludePlatformInterrupts)
  | 0x302 => (pure (Sail.BitVec.extractLsb (← readReg medeleg) (xlen -i 1) 0))
  | 0x312 =>
    (do
      if ((xlen == 32) : Bool)
      then (pure (Sail.BitVec.extractLsb (← readReg medeleg) 63 32))
      else
        (do
          let v__380 := 0x312#12
          if ((((Sail.BitVec.extractLsb v__380 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                 (Sail.BitVec.extractLsb v__380 3 0)
               (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
              (pmpReadCfgReg (BitVec.toNatInt idx)))
          else
            (do
              if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                  (pmpReadAddrReg (BitVec.toNatInt (0b00#2 +++ idx))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                      (pmpReadAddrReg (BitVec.toNatInt (0b01#2 +++ idx))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                          (pmpReadAddrReg (BitVec.toNatInt (0b10#2 +++ idx))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                              (pmpReadAddrReg (BitVec.toNatInt (0b11#2 +++ idx))))
                          else
                            (do
                              match v__380 with
                              | 0x001 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FFLAGS (← readReg fcsr))))
                              | 0x002 =>
                                (pure (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))
                              | 0x003 => (pure (zero_extend (m := 64) (← readReg fcsr)))
                              | 0x008 => readReg vstart
                              | 0x009 =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxsat (← readReg vcsr))))
                              | 0x00A =>
                                (pure (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))
                              | 0x00F => (pure (zero_extend (m := 64) (← readReg vcsr)))
                              | 0xC20 => readReg vl
                              | 0xC21 => readReg vtype
                              | 0xC22 => (pure VLENB)
                              | 0x321 =>
                                (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1) 0))
                              | 0x721 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x721#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x322 =>
                                (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1)
                                    0))
                              | 0x722 =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x722#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x30C =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen0) (xlen -i 1) 0))
                              | 0x30D =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen1) (xlen -i 1) 0))
                              | 0x30E =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen2) (xlen -i 1) 0))
                              | 0x30F =>
                                (pure (Sail.BitVec.extractLsb (← readReg mstateen3) (xlen -i 1) 0))
                              | 0x31C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x31F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then (pure (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))
                                  else
                                    (do
                                      let v__380 := 0x31F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x60C =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen0) &&& (← (get_hstateen_mask 0)))
                                    (xlen -i 1) 0))
                              | 0x60D =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen1) &&& (← (get_hstateen_mask 1)))
                                    (xlen -i 1) 0))
                              | 0x60E =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen2) &&& (← (get_hstateen_mask 2)))
                                    (xlen -i 1) 0))
                              | 0x60F =>
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen3) &&& (← (get_hstateen_mask 3)))
                                    (xlen -i 1) 0))
                              | 0x61C =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen0) &&& (← (get_hstateen_mask 0))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61C#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61D =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen1) &&& (← (get_hstateen_mask 1))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61D#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61E =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen2) &&& (← (get_hstateen_mask 2))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61E#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x61F =>
                                (do
                                  if ((xlen == 32) : Bool)
                                  then
                                    (pure (Sail.BitVec.extractLsb
                                        ((← readReg hstateen3) &&& (← (get_hstateen_mask 3))) 63
                                        32))
                                  else
                                    (do
                                      let v__380 := 0x61F#12
                                      (internal_error "postlude/csr_end.sail" 17
                                        (HAppend.hAppend "Read from CSR that does not exist: "
                                          (BitVec.toFormatted v__380)))))
                              | 0x10C =>
                                (do
                                  let mask ← do (get_sstateen_mask 0)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen0) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10D =>
                                (do
                                  let mask ← do (get_sstateen_mask 1)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen1) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10E =>
                                (do
                                  let mask ← do (get_sstateen_mask 2)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen2) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x10F =>
                                (do
                                  let mask ← do (get_sstateen_mask 3)
                                  (pure (zero_extend (m := 64)
                                      ((← readReg sstateen3) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                              | 0x180 => readReg satp
                              | v__380 =>
                                (internal_error "postlude/csr_end.sail" 17
                                  (HAppend.hAppend "Read from CSR that does not exist: "
                                    (BitVec.toFormatted v__380))))))))))
  | 0x303 => readReg mideleg
  | 0x144 => (read_sip ExcludePlatformInterrupts)
  | 0x104 => (pure (lower_mie (← readReg mie) (← readReg mideleg)))
  | 0x105 => (get_stvec ())
  | 0x141 => (get_xepc Supervisor)
  | 0x305 => (get_mtvec ())
  | 0x341 => (get_xepc Machine)
  | v__380 =>
    (do
      if ((((Sail.BitVec.extractLsb v__380 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
             (Sail.BitVec.extractLsb v__380 3 0)
           (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
      then
        (do
          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
          (pmpReadCfgReg (BitVec.toNatInt idx)))
      else
        (do
          if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
              (pmpReadAddrReg (BitVec.toNatInt (0b00#2 +++ idx))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                  (pmpReadAddrReg (BitVec.toNatInt (0b01#2 +++ idx))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                      (pmpReadAddrReg (BitVec.toNatInt (0b10#2 +++ idx))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__380 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__380 3 0)
                          (pmpReadAddrReg (BitVec.toNatInt (0b11#2 +++ idx))))
                      else
                        (do
                          match v__380 with
                          | 0x001 =>
                            (pure (zero_extend (m := 64) (_get_Fcsr_FFLAGS (← readReg fcsr))))
                          | 0x002 =>
                            (pure (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))
                          | 0x003 => (pure (zero_extend (m := 64) (← readReg fcsr)))
                          | 0x008 => readReg vstart
                          | 0x009 =>
                            (pure (zero_extend (m := 64) (_get_Vcsr_vxsat (← readReg vcsr))))
                          | 0x00A =>
                            (pure (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))
                          | 0x00F => (pure (zero_extend (m := 64) (← readReg vcsr)))
                          | 0xC20 => readReg vl
                          | 0xC21 => readReg vtype
                          | 0xC22 => (pure VLENB)
                          | 0x321 =>
                            (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1) 0))
                          | 0x721 =>
                            (do
                              if ((xlen == 32) : Bool)
                              then (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))
                              else
                                (do
                                  let v__380 := 0x721#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x322 =>
                            (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1) 0))
                          | 0x722 =>
                            (do
                              if ((xlen == 32) : Bool)
                              then (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32))
                              else
                                (do
                                  let v__380 := 0x722#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x30C =>
                            (pure (Sail.BitVec.extractLsb (← readReg mstateen0) (xlen -i 1) 0))
                          | 0x30D =>
                            (pure (Sail.BitVec.extractLsb (← readReg mstateen1) (xlen -i 1) 0))
                          | 0x30E =>
                            (pure (Sail.BitVec.extractLsb (← readReg mstateen2) (xlen -i 1) 0))
                          | 0x30F =>
                            (pure (Sail.BitVec.extractLsb (← readReg mstateen3) (xlen -i 1) 0))
                          | 0x31C =>
                            (do
                              if ((xlen == 32) : Bool)
                              then (pure (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))
                              else
                                (do
                                  let v__380 := 0x31C#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x31D =>
                            (do
                              if ((xlen == 32) : Bool)
                              then (pure (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))
                              else
                                (do
                                  let v__380 := 0x31D#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x31E =>
                            (do
                              if ((xlen == 32) : Bool)
                              then (pure (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))
                              else
                                (do
                                  let v__380 := 0x31E#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x31F =>
                            (do
                              if ((xlen == 32) : Bool)
                              then (pure (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))
                              else
                                (do
                                  let v__380 := 0x31F#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x60C =>
                            (pure (Sail.BitVec.extractLsb
                                ((← readReg hstateen0) &&& (← (get_hstateen_mask 0)))
                                (xlen -i 1) 0))
                          | 0x60D =>
                            (pure (Sail.BitVec.extractLsb
                                ((← readReg hstateen1) &&& (← (get_hstateen_mask 1)))
                                (xlen -i 1) 0))
                          | 0x60E =>
                            (pure (Sail.BitVec.extractLsb
                                ((← readReg hstateen2) &&& (← (get_hstateen_mask 2)))
                                (xlen -i 1) 0))
                          | 0x60F =>
                            (pure (Sail.BitVec.extractLsb
                                ((← readReg hstateen3) &&& (← (get_hstateen_mask 3)))
                                (xlen -i 1) 0))
                          | 0x61C =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen0) &&& (← (get_hstateen_mask 0))) 63 32))
                              else
                                (do
                                  let v__380 := 0x61C#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x61D =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen1) &&& (← (get_hstateen_mask 1))) 63 32))
                              else
                                (do
                                  let v__380 := 0x61D#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x61E =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen2) &&& (← (get_hstateen_mask 2))) 63 32))
                              else
                                (do
                                  let v__380 := 0x61E#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x61F =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (pure (Sail.BitVec.extractLsb
                                    ((← readReg hstateen3) &&& (← (get_hstateen_mask 3))) 63 32))
                              else
                                (do
                                  let v__380 := 0x61F#12
                                  (internal_error "postlude/csr_end.sail" 17
                                    (HAppend.hAppend "Read from CSR that does not exist: "
                                      (BitVec.toFormatted v__380)))))
                          | 0x10C =>
                            (do
                              let mask ← do (get_sstateen_mask 0)
                              (pure (zero_extend (m := 64)
                                  ((← readReg sstateen0) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                          | 0x10D =>
                            (do
                              let mask ← do (get_sstateen_mask 1)
                              (pure (zero_extend (m := 64)
                                  ((← readReg sstateen1) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                          | 0x10E =>
                            (do
                              let mask ← do (get_sstateen_mask 2)
                              (pure (zero_extend (m := 64)
                                  ((← readReg sstateen2) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                          | 0x10F =>
                            (do
                              let mask ← do (get_sstateen_mask 3)
                              (pure (zero_extend (m := 64)
                                  ((← readReg sstateen3) &&& (Sail.BitVec.extractLsb mask 31 0)))))
                          | 0x180 => readReg satp
                          | v__380 =>
                            (internal_error "postlude/csr_end.sail" 17
                              (HAppend.hAppend "Read from CSR that does not exist: "
                                (BitVec.toFormatted v__380)))))))))

def write_CSR (arg0 : (BitVec 12)) (arg1 : (BitVec 64)) : SailM (Result (BitVec 64) Unit) := do
  let merge_var := (arg0, arg1)
  match merge_var with
  | (0x301, value) =>
    (do
      writeReg misa (← (legalize_misa (← readReg misa) value))
      (pure (Ok (← readReg misa))))
  | (0x300, value) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (do
          writeReg mstatus (← (legalize_mstatus (← readReg mstatus) value))
          (pure (Ok (← readReg mstatus))))
      else
        (do
          writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
              ((Sail.BitVec.extractLsb (← readReg mstatus) 63 32) +++ value)))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg mstatus) 31 0)))))
  | (0x310, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
              (value +++ (Sail.BitVec.extractLsb (← readReg mstatus) 31 0))))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg mstatus) 63 32))))
      else
        (do
          match (0x310#12, value) with
          | (v__390, value) =>
            (do
              if ((((Sail.BitVec.extractLsb v__390 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                     (Sail.BitVec.extractLsb v__390 3 0)
                   (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                  let idx := (BitVec.toNatInt idx)
                  (pmpWriteCfgReg idx value)
                  (pure (Ok (← (pmpReadCfgReg idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                      let idx := (BitVec.toNatInt (0b00#2 +++ idx))
                      (pmpWriteAddrReg idx value)
                      (pure (Ok (← (pmpReadAddrReg idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                          let idx := (BitVec.toNatInt (0b01#2 +++ idx))
                          (pmpWriteAddrReg idx value)
                          (pure (Ok (← (pmpReadAddrReg idx)))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                              let idx := (BitVec.toNatInt (0b10#2 +++ idx))
                              (pmpWriteAddrReg idx value)
                              (pure (Ok (← (pmpReadAddrReg idx)))))
                          else
                            (do
                              if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                              then
                                (do
                                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                                  let idx := (BitVec.toNatInt (0b11#2 +++ idx))
                                  (pmpWriteAddrReg idx value)
                                  (pure (Ok (← (pmpReadAddrReg idx)))))
                              else
                                (do
                                  match (v__390, value) with
                                  | (0x001, value) =>
                                    (do
                                      (write_fcsr (_get_Fcsr_FRM (← readReg fcsr))
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Fcsr_FFLAGS (← readReg fcsr))))))
                                  | (0x002, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 2 0)
                                        (_get_Fcsr_FFLAGS (← readReg fcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))))
                                  | (0x003, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 7 5)
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg fcsr)))))
                                  | (0x008, value) =>
                                    (do
                                      (set_vstart (Sail.BitVec.extractLsb value 15 0))
                                      (pure (Ok (← readReg vstart))))
                                  | (0x009, value) =>
                                    (do
                                      (write_vcsr (_get_Vcsr_vxrm (← readReg vcsr))
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Vcsr_vxsat (← readReg vcsr))))))
                                  | (0x00A, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 1 0)
                                        (_get_Vcsr_vxsat (← readReg vcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))))
                                  | (0x00F, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 2 1)
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg vcsr)))))
                                  | (0x321, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg) value))
                                          (pure (Ok (← readReg mcyclecfg))))
                                      else
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              ((Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg)
                                                (xlen -i 1) 0)))))
                                  | (0x721, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mcyclecfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))))
                                      else
                                        (do
                                          match (0x721#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x322, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg) value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0))))
                                      else
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              ((Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                  32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0)))))
                                  | (0x722, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg minstretcfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                32))))
                                      else
                                        (do
                                          match (0x722#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x30C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg mstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0) value))
                                          (pure (Ok (← readReg mstateen0)))))
                                  | (0x30D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen1) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1) value)
                                          (pure (Ok (← readReg mstateen1)))))
                                  | (0x30E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen2) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2) value)
                                          (pure (Ok (← readReg mstateen2)))))
                                  | (0x30F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen3) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3) value)
                                          (pure (Ok (← readReg mstateen3)))))
                                  | (0x31C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x31C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen1) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x31D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen2) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x31E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen3) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x31F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x60C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0) value))
                                          (pure (Ok (← readReg hstateen0)))))
                                  | (0x60D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen1) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1) value))
                                          (pure (Ok (← readReg hstateen1)))))
                                  | (0x60E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen2) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2) value))
                                          (pure (Ok (← readReg hstateen2)))))
                                  | (0x60F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen3) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3) value))
                                          (pure (Ok (← readReg hstateen3)))))
                                  | (0x61C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x61C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen1) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x61D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen2) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x61E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen3) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x61F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x10C, value) =>
                                    (do
                                      writeReg sstateen0 (← (legalize_sstateen0
                                          (← readReg sstateen0)
                                          (Sail.BitVec.extractLsb value 31 0)))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen0)))))
                                  | (0x10D, value) =>
                                    (do
                                      writeReg sstateen1 (legalize_sstateen1 (← readReg sstateen1)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen1)))))
                                  | (0x10E, value) =>
                                    (do
                                      writeReg sstateen2 (legalize_sstateen2 (← readReg sstateen2)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen2)))))
                                  | (0x10F, value) =>
                                    (do
                                      writeReg sstateen3 (legalize_sstateen3 (← readReg sstateen3)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen3)))))
                                  | (0x180, value) =>
                                    (do
                                      writeReg satp (← (legalize_satp
                                          (← (architecture Supervisor)) (← readReg satp) value))
                                      (pure (Ok (← readReg satp))))
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))))))))
  | (0x747, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
              ((Sail.BitVec.extractLsb (← readReg mseccfg) 63 32) +++ value)))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0))))
      else
        (do
          writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg) value))
          (pure (Ok (← readReg mseccfg)))))
  | (0x757, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
              (value +++ (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0))))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32))))
      else
        (do
          match (0x757#12, value) with
          | (v__390, value) =>
            (do
              if ((((Sail.BitVec.extractLsb v__390 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                     (Sail.BitVec.extractLsb v__390 3 0)
                   (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                  let idx := (BitVec.toNatInt idx)
                  (pmpWriteCfgReg idx value)
                  (pure (Ok (← (pmpReadCfgReg idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                      let idx := (BitVec.toNatInt (0b00#2 +++ idx))
                      (pmpWriteAddrReg idx value)
                      (pure (Ok (← (pmpReadAddrReg idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                          let idx := (BitVec.toNatInt (0b01#2 +++ idx))
                          (pmpWriteAddrReg idx value)
                          (pure (Ok (← (pmpReadAddrReg idx)))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                              let idx := (BitVec.toNatInt (0b10#2 +++ idx))
                              (pmpWriteAddrReg idx value)
                              (pure (Ok (← (pmpReadAddrReg idx)))))
                          else
                            (do
                              if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                              then
                                (do
                                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                                  let idx := (BitVec.toNatInt (0b11#2 +++ idx))
                                  (pmpWriteAddrReg idx value)
                                  (pure (Ok (← (pmpReadAddrReg idx)))))
                              else
                                (do
                                  match (v__390, value) with
                                  | (0x001, value) =>
                                    (do
                                      (write_fcsr (_get_Fcsr_FRM (← readReg fcsr))
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Fcsr_FFLAGS (← readReg fcsr))))))
                                  | (0x002, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 2 0)
                                        (_get_Fcsr_FFLAGS (← readReg fcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))))
                                  | (0x003, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 7 5)
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg fcsr)))))
                                  | (0x008, value) =>
                                    (do
                                      (set_vstart (Sail.BitVec.extractLsb value 15 0))
                                      (pure (Ok (← readReg vstart))))
                                  | (0x009, value) =>
                                    (do
                                      (write_vcsr (_get_Vcsr_vxrm (← readReg vcsr))
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Vcsr_vxsat (← readReg vcsr))))))
                                  | (0x00A, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 1 0)
                                        (_get_Vcsr_vxsat (← readReg vcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))))
                                  | (0x00F, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 2 1)
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg vcsr)))))
                                  | (0x321, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg) value))
                                          (pure (Ok (← readReg mcyclecfg))))
                                      else
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              ((Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg)
                                                (xlen -i 1) 0)))))
                                  | (0x721, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mcyclecfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))))
                                      else
                                        (do
                                          match (0x721#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x322, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg) value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0))))
                                      else
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              ((Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                  32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0)))))
                                  | (0x722, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg minstretcfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                32))))
                                      else
                                        (do
                                          match (0x722#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x30C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg mstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0) value))
                                          (pure (Ok (← readReg mstateen0)))))
                                  | (0x30D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen1) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1) value)
                                          (pure (Ok (← readReg mstateen1)))))
                                  | (0x30E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen2) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2) value)
                                          (pure (Ok (← readReg mstateen2)))))
                                  | (0x30F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen3) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3) value)
                                          (pure (Ok (← readReg mstateen3)))))
                                  | (0x31C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x31C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen1) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x31D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen2) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x31E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen3) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x31F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x60C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0) value))
                                          (pure (Ok (← readReg hstateen0)))))
                                  | (0x60D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen1) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1) value))
                                          (pure (Ok (← readReg hstateen1)))))
                                  | (0x60E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen2) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2) value))
                                          (pure (Ok (← readReg hstateen2)))))
                                  | (0x60F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen3) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3) value))
                                          (pure (Ok (← readReg hstateen3)))))
                                  | (0x61C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x61C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen1) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x61D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen2) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x61E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen3) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x61F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x10C, value) =>
                                    (do
                                      writeReg sstateen0 (← (legalize_sstateen0
                                          (← readReg sstateen0)
                                          (Sail.BitVec.extractLsb value 31 0)))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen0)))))
                                  | (0x10D, value) =>
                                    (do
                                      writeReg sstateen1 (legalize_sstateen1 (← readReg sstateen1)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen1)))))
                                  | (0x10E, value) =>
                                    (do
                                      writeReg sstateen2 (legalize_sstateen2 (← readReg sstateen2)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen2)))))
                                  | (0x10F, value) =>
                                    (do
                                      writeReg sstateen3 (legalize_sstateen3 (← readReg sstateen3)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen3)))))
                                  | (0x180, value) =>
                                    (do
                                      writeReg satp (← (legalize_satp
                                          (← (architecture Supervisor)) (← readReg satp) value))
                                      (pure (Ok (← readReg satp))))
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))))))))
  | (0x30A, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
              ((Sail.BitVec.extractLsb (← readReg menvcfg) 63 32) +++ value)))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg menvcfg) 31 0))))
      else
        (do
          writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg) value))
          (pure (Ok (← readReg menvcfg)))))
  | (0x31A, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
              (value +++ (Sail.BitVec.extractLsb (← readReg menvcfg) 31 0))))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32))))
      else
        (do
          match (0x31A#12, value) with
          | (v__390, value) =>
            (do
              if ((((Sail.BitVec.extractLsb v__390 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                     (Sail.BitVec.extractLsb v__390 3 0)
                   (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                  let idx := (BitVec.toNatInt idx)
                  (pmpWriteCfgReg idx value)
                  (pure (Ok (← (pmpReadCfgReg idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                      let idx := (BitVec.toNatInt (0b00#2 +++ idx))
                      (pmpWriteAddrReg idx value)
                      (pure (Ok (← (pmpReadAddrReg idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                          let idx := (BitVec.toNatInt (0b01#2 +++ idx))
                          (pmpWriteAddrReg idx value)
                          (pure (Ok (← (pmpReadAddrReg idx)))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                              let idx := (BitVec.toNatInt (0b10#2 +++ idx))
                              (pmpWriteAddrReg idx value)
                              (pure (Ok (← (pmpReadAddrReg idx)))))
                          else
                            (do
                              if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                              then
                                (do
                                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                                  let idx := (BitVec.toNatInt (0b11#2 +++ idx))
                                  (pmpWriteAddrReg idx value)
                                  (pure (Ok (← (pmpReadAddrReg idx)))))
                              else
                                (do
                                  match (v__390, value) with
                                  | (0x001, value) =>
                                    (do
                                      (write_fcsr (_get_Fcsr_FRM (← readReg fcsr))
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Fcsr_FFLAGS (← readReg fcsr))))))
                                  | (0x002, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 2 0)
                                        (_get_Fcsr_FFLAGS (← readReg fcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))))
                                  | (0x003, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 7 5)
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg fcsr)))))
                                  | (0x008, value) =>
                                    (do
                                      (set_vstart (Sail.BitVec.extractLsb value 15 0))
                                      (pure (Ok (← readReg vstart))))
                                  | (0x009, value) =>
                                    (do
                                      (write_vcsr (_get_Vcsr_vxrm (← readReg vcsr))
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Vcsr_vxsat (← readReg vcsr))))))
                                  | (0x00A, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 1 0)
                                        (_get_Vcsr_vxsat (← readReg vcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))))
                                  | (0x00F, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 2 1)
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg vcsr)))))
                                  | (0x321, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg) value))
                                          (pure (Ok (← readReg mcyclecfg))))
                                      else
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              ((Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg)
                                                (xlen -i 1) 0)))))
                                  | (0x721, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mcyclecfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))))
                                      else
                                        (do
                                          match (0x721#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x322, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg) value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0))))
                                      else
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              ((Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                  32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0)))))
                                  | (0x722, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg minstretcfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                32))))
                                      else
                                        (do
                                          match (0x722#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x30C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg mstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0) value))
                                          (pure (Ok (← readReg mstateen0)))))
                                  | (0x30D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen1) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1) value)
                                          (pure (Ok (← readReg mstateen1)))))
                                  | (0x30E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen2) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2) value)
                                          (pure (Ok (← readReg mstateen2)))))
                                  | (0x30F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen3) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3) value)
                                          (pure (Ok (← readReg mstateen3)))))
                                  | (0x31C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x31C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen1) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x31D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen2) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x31E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen3) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x31F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x60C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0) value))
                                          (pure (Ok (← readReg hstateen0)))))
                                  | (0x60D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen1) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1) value))
                                          (pure (Ok (← readReg hstateen1)))))
                                  | (0x60E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen2) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2) value))
                                          (pure (Ok (← readReg hstateen2)))))
                                  | (0x60F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen3) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3) value))
                                          (pure (Ok (← readReg hstateen3)))))
                                  | (0x61C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x61C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen1) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x61D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen2) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x61E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen3) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x61F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x10C, value) =>
                                    (do
                                      writeReg sstateen0 (← (legalize_sstateen0
                                          (← readReg sstateen0)
                                          (Sail.BitVec.extractLsb value 31 0)))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen0)))))
                                  | (0x10D, value) =>
                                    (do
                                      writeReg sstateen1 (legalize_sstateen1 (← readReg sstateen1)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen1)))))
                                  | (0x10E, value) =>
                                    (do
                                      writeReg sstateen2 (legalize_sstateen2 (← readReg sstateen2)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen2)))))
                                  | (0x10F, value) =>
                                    (do
                                      writeReg sstateen3 (legalize_sstateen3 (← readReg sstateen3)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen3)))))
                                  | (0x180, value) =>
                                    (do
                                      writeReg satp (← (legalize_satp
                                          (← (architecture Supervisor)) (← readReg satp) value))
                                      (pure (Ok (← readReg satp))))
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))))))))
  | (0x10A, value) =>
    (do
      writeReg senvcfg (← (legalize_senvcfg (← readReg senvcfg) (zero_extend (m := 64) value)))
      (pure (Ok (Sail.BitVec.extractLsb (← (read_senvcfg ())) (xlen -i 1) 0))))
  | (0x342, value) =>
    (do
      writeReg mcause value
      (pure (Ok (← readReg mcause))))
  | (0x343, value) =>
    (do
      writeReg mtval value
      (pure (Ok (← readReg mtval))))
  | (0x340, value) =>
    (do
      writeReg mscratch value
      (pure (Ok (← readReg mscratch))))
  | (0x106, value) =>
    (do
      writeReg scounteren (legalize_scounteren (← readReg scounteren) value)
      (pure (Ok (zero_extend (m := 64) (← readReg scounteren)))))
  | (0x306, value) =>
    (do
      writeReg mcounteren (legalize_mcounteren (← readReg mcounteren) value)
      (pure (Ok (zero_extend (m := 64) (← readReg mcounteren)))))
  | (0x320, value) =>
    (do
      writeReg mcountinhibit (legalize_mcountinhibit (← readReg mcountinhibit) value)
      (pure (Ok (zero_extend (m := 64) (← readReg mcountinhibit)))))
  | (0x100, value) =>
    (do
      writeReg mstatus (← (legalize_sstatus (← readReg mstatus) value))
      (pure (Ok (Sail.BitVec.extractLsb (lower_mstatus (← readReg mstatus)) (xlen -i 1) 0))))
  | (0x140, value) =>
    (do
      writeReg sscratch value
      (pure (Ok (← readReg sscratch))))
  | (0x142, value) =>
    (do
      writeReg scause value
      (pure (Ok (← readReg scause))))
  | (0x143, value) =>
    (do
      writeReg stval value
      (pure (Ok (← readReg stval))))
  | (0x7A0, value) =>
    (do
      writeReg tselect value
      (pure (Ok (← readReg tselect))))
  | (0x304, value) =>
    (do
      writeReg mie (← (legalize_mie (← readReg mie) value))
      (pure (Ok (← readReg mie))))
  | (0x344, value) =>
    (do
      (write_mip value)
      (pure (Ok (← (read_mip IncludePlatformInterrupts)))))
  | (0x302, value) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (do
          writeReg medeleg (legalize_medeleg (← readReg medeleg) value)
          (pure (Ok (← readReg medeleg))))
      else
        (do
          writeReg medeleg (legalize_medeleg (← readReg medeleg)
            ((Sail.BitVec.extractLsb (← readReg medeleg) 63 32) +++ value))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg medeleg) 31 0)))))
  | (0x312, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg medeleg (legalize_medeleg (← readReg medeleg)
            (value +++ (Sail.BitVec.extractLsb (← readReg medeleg) 31 0)))
          (pure (Ok (Sail.BitVec.extractLsb (← readReg medeleg) 63 32))))
      else
        (do
          match (0x312#12, value) with
          | (v__390, value) =>
            (do
              if ((((Sail.BitVec.extractLsb v__390 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                     (Sail.BitVec.extractLsb v__390 3 0)
                   (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                  let idx := (BitVec.toNatInt idx)
                  (pmpWriteCfgReg idx value)
                  (pure (Ok (← (pmpReadCfgReg idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                      let idx := (BitVec.toNatInt (0b00#2 +++ idx))
                      (pmpWriteAddrReg idx value)
                      (pure (Ok (← (pmpReadAddrReg idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                          let idx := (BitVec.toNatInt (0b01#2 +++ idx))
                          (pmpWriteAddrReg idx value)
                          (pure (Ok (← (pmpReadAddrReg idx)))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                          then
                            (do
                              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                              let idx := (BitVec.toNatInt (0b10#2 +++ idx))
                              (pmpWriteAddrReg idx value)
                              (pure (Ok (← (pmpReadAddrReg idx)))))
                          else
                            (do
                              if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                              then
                                (do
                                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                                  let idx := (BitVec.toNatInt (0b11#2 +++ idx))
                                  (pmpWriteAddrReg idx value)
                                  (pure (Ok (← (pmpReadAddrReg idx)))))
                              else
                                (do
                                  match (v__390, value) with
                                  | (0x001, value) =>
                                    (do
                                      (write_fcsr (_get_Fcsr_FRM (← readReg fcsr))
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Fcsr_FFLAGS (← readReg fcsr))))))
                                  | (0x002, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 2 0)
                                        (_get_Fcsr_FFLAGS (← readReg fcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))))
                                  | (0x003, value) =>
                                    (do
                                      (write_fcsr (Sail.BitVec.extractLsb value 7 5)
                                        (Sail.BitVec.extractLsb value 4 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg fcsr)))))
                                  | (0x008, value) =>
                                    (do
                                      (set_vstart (Sail.BitVec.extractLsb value 15 0))
                                      (pure (Ok (← readReg vstart))))
                                  | (0x009, value) =>
                                    (do
                                      (write_vcsr (_get_Vcsr_vxrm (← readReg vcsr))
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok
                                          (zero_extend (m := 64)
                                            (_get_Vcsr_vxsat (← readReg vcsr))))))
                                  | (0x00A, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 1 0)
                                        (_get_Vcsr_vxsat (← readReg vcsr)))
                                      (pure (Ok
                                          (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))))
                                  | (0x00F, value) =>
                                    (do
                                      (write_vcsr (Sail.BitVec.extractLsb value 2 1)
                                        (Sail.BitVec.extractLsb value 0 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg vcsr)))))
                                  | (0x321, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg) value))
                                          (pure (Ok (← readReg mcyclecfg))))
                                      else
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              ((Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg)
                                                (xlen -i 1) 0)))))
                                  | (0x721, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                              (← readReg mcyclecfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mcyclecfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))))
                                      else
                                        (do
                                          match (0x721#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x322, value) =>
                                    (do
                                      if ((xlen == 64) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg) value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0))))
                                      else
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              ((Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                  32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                                (xlen -i 1) 0)))))
                                  | (0x722, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                              (← readReg minstretcfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg minstretcfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg minstretcfg) 63
                                                32))))
                                      else
                                        (do
                                          match (0x722#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x30C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg mstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0) value))
                                          (pure (Ok (← readReg mstateen0)))))
                                  | (0x30D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen1) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1) value)
                                          (pure (Ok (← readReg mstateen1)))))
                                  | (0x30E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen2) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2) value)
                                          (pure (Ok (← readReg mstateen2)))))
                                  | (0x30F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            ((Sail.BitVec.extractLsb (← readReg mstateen3) 63 32) +++ value))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3) value)
                                          (pure (Ok (← readReg mstateen3)))))
                                  | (0x31C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen0 (← (legalize_mstateen0
                                              (← readReg mstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg mstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x31C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen1 (legalize_mstateen1
                                            (← readReg mstateen1)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen1) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x31D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen2 (legalize_mstateen2
                                            (← readReg mstateen2)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen2) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x31E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x31F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg mstateen3 (legalize_mstateen3
                                            (← readReg mstateen3)
                                            (value +++ (Sail.BitVec.extractLsb
                                                (← readReg mstateen3) 31 0)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x31F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x60C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen0) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0) value))
                                          (pure (Ok (← readReg hstateen0)))))
                                  | (0x60D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen1) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1) value))
                                          (pure (Ok (← readReg hstateen1)))))
                                  | (0x60E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen2) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2) value))
                                          (pure (Ok (← readReg hstateen2)))))
                                  | (0x60F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              ((Sail.BitVec.extractLsb (← readReg hstateen3) 63 32) +++ value)))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 31 0))))
                                      else
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3) value))
                                          (pure (Ok (← readReg hstateen3)))))
                                  | (0x61C, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen0 (← (legalize_hstateen0
                                              (← readReg hstateen0)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen0) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen0) 63 32))))
                                      else
                                        (do
                                          match (0x61C#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61D, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen1 (← (legalize_hstateen1
                                              (← readReg hstateen1)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen1) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen1) 63 32))))
                                      else
                                        (do
                                          match (0x61D#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61E, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen2 (← (legalize_hstateen2
                                              (← readReg hstateen2)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen2) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen2) 63 32))))
                                      else
                                        (do
                                          match (0x61E#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x61F, value) =>
                                    (do
                                      if ((xlen == 32) : Bool)
                                      then
                                        (do
                                          writeReg hstateen3 (← (legalize_hstateen3
                                              (← readReg hstateen3)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg hstateen3) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg hstateen3) 63 32))))
                                      else
                                        (do
                                          match (0x61F#12, value) with
                                          | (v__390, _) =>
                                            (internal_error "postlude/csr_end.sail" 23
                                              (HAppend.hAppend "Write to CSR that does not exist: "
                                                (BitVec.toFormatted v__390)))))
                                  | (0x10C, value) =>
                                    (do
                                      writeReg sstateen0 (← (legalize_sstateen0
                                          (← readReg sstateen0)
                                          (Sail.BitVec.extractLsb value 31 0)))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen0)))))
                                  | (0x10D, value) =>
                                    (do
                                      writeReg sstateen1 (legalize_sstateen1 (← readReg sstateen1)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen1)))))
                                  | (0x10E, value) =>
                                    (do
                                      writeReg sstateen2 (legalize_sstateen2 (← readReg sstateen2)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen2)))))
                                  | (0x10F, value) =>
                                    (do
                                      writeReg sstateen3 (legalize_sstateen3 (← readReg sstateen3)
                                        (Sail.BitVec.extractLsb value 31 0))
                                      (pure (Ok (zero_extend (m := 64) (← readReg sstateen3)))))
                                  | (0x180, value) =>
                                    (do
                                      writeReg satp (← (legalize_satp
                                          (← (architecture Supervisor)) (← readReg satp) value))
                                      (pure (Ok (← readReg satp))))
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))))))))
  | (0x303, value) =>
    (do
      writeReg mideleg (← (legalize_mideleg (← readReg mideleg) value))
      (pure (Ok (← readReg mideleg))))
  | (0x144, value) =>
    (do
      (write_sip value)
      (pure (Ok (← (read_sip IncludePlatformInterrupts)))))
  | (0x104, value) =>
    (do
      writeReg mie (legalize_sie (← readReg mie) (← readReg mideleg) value)
      (pure (Ok (lower_mie (← readReg mie) (← readReg mideleg)))))
  | (0x105, value) => (pure (Ok (← (set_stvec value))))
  | (0x141, value) => (pure (Ok (← (set_xepc Supervisor value))))
  | (0x305, value) => (pure (Ok (← (set_mtvec value))))
  | (0x341, value) => (pure (Ok (← (set_xepc Machine value))))
  | (v__390, value) =>
    (do
      if ((((Sail.BitVec.extractLsb v__390 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
             (Sail.BitVec.extractLsb v__390 3 0)
           (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
      then
        (do
          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
          let idx := (BitVec.toNatInt idx)
          (pmpWriteCfgReg idx value)
          (pure (Ok (← (pmpReadCfgReg idx)))))
      else
        (do
          if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
              let idx := (BitVec.toNatInt (0b00#2 +++ idx))
              (pmpWriteAddrReg idx value)
              (pure (Ok (← (pmpReadAddrReg idx)))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                  let idx := (BitVec.toNatInt (0b01#2 +++ idx))
                  (pmpWriteAddrReg idx value)
                  (pure (Ok (← (pmpReadAddrReg idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                      let idx := (BitVec.toNatInt (0b10#2 +++ idx))
                      (pmpWriteAddrReg idx value)
                      (pure (Ok (← (pmpReadAddrReg idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__390 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__390 3 0)
                          let idx := (BitVec.toNatInt (0b11#2 +++ idx))
                          (pmpWriteAddrReg idx value)
                          (pure (Ok (← (pmpReadAddrReg idx)))))
                      else
                        (do
                          match (v__390, value) with
                          | (0x001, value) =>
                            (do
                              (write_fcsr (_get_Fcsr_FRM (← readReg fcsr))
                                (Sail.BitVec.extractLsb value 4 0))
                              (pure (Ok
                                  (zero_extend (m := 64) (_get_Fcsr_FFLAGS (← readReg fcsr))))))
                          | (0x002, value) =>
                            (do
                              (write_fcsr (Sail.BitVec.extractLsb value 2 0)
                                (_get_Fcsr_FFLAGS (← readReg fcsr)))
                              (pure (Ok (zero_extend (m := 64) (_get_Fcsr_FRM (← readReg fcsr))))))
                          | (0x003, value) =>
                            (do
                              (write_fcsr (Sail.BitVec.extractLsb value 7 5)
                                (Sail.BitVec.extractLsb value 4 0))
                              (pure (Ok (zero_extend (m := 64) (← readReg fcsr)))))
                          | (0x008, value) =>
                            (do
                              (set_vstart (Sail.BitVec.extractLsb value 15 0))
                              (pure (Ok (← readReg vstart))))
                          | (0x009, value) =>
                            (do
                              (write_vcsr (_get_Vcsr_vxrm (← readReg vcsr))
                                (Sail.BitVec.extractLsb value 0 0))
                              (pure (Ok (zero_extend (m := 64) (_get_Vcsr_vxsat (← readReg vcsr))))))
                          | (0x00A, value) =>
                            (do
                              (write_vcsr (Sail.BitVec.extractLsb value 1 0)
                                (_get_Vcsr_vxsat (← readReg vcsr)))
                              (pure (Ok (zero_extend (m := 64) (_get_Vcsr_vxrm (← readReg vcsr))))))
                          | (0x00F, value) =>
                            (do
                              (write_vcsr (Sail.BitVec.extractLsb value 2 1)
                                (Sail.BitVec.extractLsb value 0 0))
                              (pure (Ok (zero_extend (m := 64) (← readReg vcsr)))))
                          | (0x321, value) =>
                            (do
                              if ((xlen == 64) : Bool)
                              then
                                (do
                                  writeReg mcyclecfg (← (legalize_smcntrpmf
                                      (← readReg mcyclecfg) value))
                                  (pure (Ok (← readReg mcyclecfg))))
                              else
                                (do
                                  writeReg mcyclecfg (← (legalize_smcntrpmf
                                      (← readReg mcyclecfg)
                                      ((Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32) +++ value)))
                                  (pure (Ok
                                      (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1) 0)))))
                          | (0x721, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mcyclecfg (← (legalize_smcntrpmf
                                      (← readReg mcyclecfg)
                                      (value +++ (Sail.BitVec.extractLsb (← readReg mcyclecfg) 31
                                          0))))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))))
                              else
                                (do
                                  match (0x721#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x322, value) =>
                            (do
                              if ((xlen == 64) : Bool)
                              then
                                (do
                                  writeReg minstretcfg (← (legalize_smcntrpmf
                                      (← readReg minstretcfg) value))
                                  (pure (Ok
                                      (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1)
                                        0))))
                              else
                                (do
                                  writeReg minstretcfg (← (legalize_smcntrpmf
                                      (← readReg minstretcfg)
                                      ((Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32) +++ value)))
                                  (pure (Ok
                                      (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1)
                                        0)))))
                          | (0x722, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg minstretcfg (← (legalize_smcntrpmf
                                      (← readReg minstretcfg)
                                      (value +++ (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                          31 0))))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32))))
                              else
                                (do
                                  match (0x722#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x30C, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen0 (← (legalize_mstateen0
                                      (← readReg mstateen0)
                                      ((Sail.BitVec.extractLsb (← readReg mstateen0) 63 32) +++ value)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen0) 31 0))))
                              else
                                (do
                                  writeReg mstateen0 (← (legalize_mstateen0
                                      (← readReg mstateen0) value))
                                  (pure (Ok (← readReg mstateen0)))))
                          | (0x30D, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen1 (legalize_mstateen1 (← readReg mstateen1)
                                    ((Sail.BitVec.extractLsb (← readReg mstateen1) 63 32) +++ value))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen1) 31 0))))
                              else
                                (do
                                  writeReg mstateen1 (legalize_mstateen1 (← readReg mstateen1)
                                    value)
                                  (pure (Ok (← readReg mstateen1)))))
                          | (0x30E, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen2 (legalize_mstateen2 (← readReg mstateen2)
                                    ((Sail.BitVec.extractLsb (← readReg mstateen2) 63 32) +++ value))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen2) 31 0))))
                              else
                                (do
                                  writeReg mstateen2 (legalize_mstateen2 (← readReg mstateen2)
                                    value)
                                  (pure (Ok (← readReg mstateen2)))))
                          | (0x30F, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen3 (legalize_mstateen3 (← readReg mstateen3)
                                    ((Sail.BitVec.extractLsb (← readReg mstateen3) 63 32) +++ value))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen3) 31 0))))
                              else
                                (do
                                  writeReg mstateen3 (legalize_mstateen3 (← readReg mstateen3)
                                    value)
                                  (pure (Ok (← readReg mstateen3)))))
                          | (0x31C, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen0 (← (legalize_mstateen0
                                      (← readReg mstateen0)
                                      (value +++ (Sail.BitVec.extractLsb (← readReg mstateen0) 31
                                          0))))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen0) 63 32))))
                              else
                                (do
                                  match (0x31C#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x31D, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen1 (legalize_mstateen1 (← readReg mstateen1)
                                    (value +++ (Sail.BitVec.extractLsb (← readReg mstateen1) 31 0)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen1) 63 32))))
                              else
                                (do
                                  match (0x31D#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x31E, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen2 (legalize_mstateen2 (← readReg mstateen2)
                                    (value +++ (Sail.BitVec.extractLsb (← readReg mstateen2) 31 0)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen2) 63 32))))
                              else
                                (do
                                  match (0x31E#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x31F, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg mstateen3 (legalize_mstateen3 (← readReg mstateen3)
                                    (value +++ (Sail.BitVec.extractLsb (← readReg mstateen3) 31 0)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstateen3) 63 32))))
                              else
                                (do
                                  match (0x31F#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x60C, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen0 (← (legalize_hstateen0
                                      (← readReg hstateen0)
                                      ((Sail.BitVec.extractLsb (← readReg hstateen0) 63 32) +++ value)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen0) 31 0))))
                              else
                                (do
                                  writeReg hstateen0 (← (legalize_hstateen0
                                      (← readReg hstateen0) value))
                                  (pure (Ok (← readReg hstateen0)))))
                          | (0x60D, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen1 (← (legalize_hstateen1
                                      (← readReg hstateen1)
                                      ((Sail.BitVec.extractLsb (← readReg hstateen1) 63 32) +++ value)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen1) 31 0))))
                              else
                                (do
                                  writeReg hstateen1 (← (legalize_hstateen1
                                      (← readReg hstateen1) value))
                                  (pure (Ok (← readReg hstateen1)))))
                          | (0x60E, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen2 (← (legalize_hstateen2
                                      (← readReg hstateen2)
                                      ((Sail.BitVec.extractLsb (← readReg hstateen2) 63 32) +++ value)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen2) 31 0))))
                              else
                                (do
                                  writeReg hstateen2 (← (legalize_hstateen2
                                      (← readReg hstateen2) value))
                                  (pure (Ok (← readReg hstateen2)))))
                          | (0x60F, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen3 (← (legalize_hstateen3
                                      (← readReg hstateen3)
                                      ((Sail.BitVec.extractLsb (← readReg hstateen3) 63 32) +++ value)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen3) 31 0))))
                              else
                                (do
                                  writeReg hstateen3 (← (legalize_hstateen3
                                      (← readReg hstateen3) value))
                                  (pure (Ok (← readReg hstateen3)))))
                          | (0x61C, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen0 (← (legalize_hstateen0
                                      (← readReg hstateen0)
                                      (value +++ (Sail.BitVec.extractLsb (← readReg hstateen0) 31
                                          0))))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen0) 63 32))))
                              else
                                (do
                                  match (0x61C#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x61D, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen1 (← (legalize_hstateen1
                                      (← readReg hstateen1)
                                      (value +++ (Sail.BitVec.extractLsb (← readReg hstateen1) 31
                                          0))))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen1) 63 32))))
                              else
                                (do
                                  match (0x61D#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x61E, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen2 (← (legalize_hstateen2
                                      (← readReg hstateen2)
                                      (value +++ (Sail.BitVec.extractLsb (← readReg hstateen2) 31
                                          0))))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen2) 63 32))))
                              else
                                (do
                                  match (0x61E#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x61F, value) =>
                            (do
                              if ((xlen == 32) : Bool)
                              then
                                (do
                                  writeReg hstateen3 (← (legalize_hstateen3
                                      (← readReg hstateen3)
                                      (value +++ (Sail.BitVec.extractLsb (← readReg hstateen3) 31
                                          0))))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg hstateen3) 63 32))))
                              else
                                (do
                                  match (0x61F#12, value) with
                                  | (v__390, _) =>
                                    (internal_error "postlude/csr_end.sail" 23
                                      (HAppend.hAppend "Write to CSR that does not exist: "
                                        (BitVec.toFormatted v__390)))))
                          | (0x10C, value) =>
                            (do
                              writeReg sstateen0 (← (legalize_sstateen0 (← readReg sstateen0)
                                  (Sail.BitVec.extractLsb value 31 0)))
                              (pure (Ok (zero_extend (m := 64) (← readReg sstateen0)))))
                          | (0x10D, value) =>
                            (do
                              writeReg sstateen1 (legalize_sstateen1 (← readReg sstateen1)
                                (Sail.BitVec.extractLsb value 31 0))
                              (pure (Ok (zero_extend (m := 64) (← readReg sstateen1)))))
                          | (0x10E, value) =>
                            (do
                              writeReg sstateen2 (legalize_sstateen2 (← readReg sstateen2)
                                (Sail.BitVec.extractLsb value 31 0))
                              (pure (Ok (zero_extend (m := 64) (← readReg sstateen2)))))
                          | (0x10F, value) =>
                            (do
                              writeReg sstateen3 (legalize_sstateen3 (← readReg sstateen3)
                                (Sail.BitVec.extractLsb value 31 0))
                              (pure (Ok (zero_extend (m := 64) (← readReg sstateen3)))))
                          | (0x180, value) =>
                            (do
                              writeReg satp (← (legalize_satp (← (architecture Supervisor))
                                  (← readReg satp) value))
                              (pure (Ok (← readReg satp))))
                          | (v__390, _) =>
                            (internal_error "postlude/csr_end.sail" 23
                              (HAppend.hAppend "Write to CSR that does not exist: "
                                (BitVec.toFormatted v__390)))))))))

