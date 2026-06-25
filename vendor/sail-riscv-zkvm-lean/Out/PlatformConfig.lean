import Out.Flow
import Out.Mapping
import Out.HexBits
import Out.HexBitsSigned
import Out.Prelude
import Out.Errors
import Out.PmTypes
import Out.Xlen
import Out.Flen
import Out.Vlen

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

def plat_mtvec_direct_mode_supported : Bool := true

def plat_mtvec_vectored_mode_supported : Bool := true

def plat_stvec_direct_mode_supported : Bool := true

def plat_stvec_vectored_mode_supported : Bool := true

def plat_mtvec_direct_base_alignment_exp : tvec_alignment := 2

def plat_mtvec_vectored_base_alignment_exp : tvec_alignment := 2

def plat_stvec_vectored_base_alignment_exp : tvec_alignment := 2

def plat_cache_block_size_exp : Nat := 6

def plat_reservation_set_size_exp : Nat := 3

def plat_reservation_require_exact_addr_match : Bool := false

def plat_reservation_invalidate_on_same_hart_store : Bool := false

def undefined_misaligned_exception (_ : Unit) : SailM misaligned_exception := do
  (internal_pick [AccessFault, AlignmentException])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def misaligned_exception_of_num (arg_ : Nat) : misaligned_exception :=
  match arg_ with
  | 0 => AccessFault
  | _ => AlignmentException

def num_of_misaligned_exception (arg_ : misaligned_exception) : Int :=
  match arg_ with
  | .AccessFault => 0
  | .AlignmentException => 1

def misaligned_exception_str_forwards (arg_ : misaligned_exception) : String :=
  match arg_ with
  | .AccessFault => "AccessFault"
  | .AlignmentException => "AlignmentException"

def misaligned_exception_str_backwards (arg_ : String) : SailM misaligned_exception := do
  match arg_ with
  | "AccessFault" => (pure AccessFault)
  | "AlignmentException" => (pure AlignmentException)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def misaligned_exception_str_forwards_matches (arg_ : misaligned_exception) : Bool :=
  match arg_ with
  | .AccessFault => true
  | .AlignmentException => true

def misaligned_exception_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "AccessFault" => true
  | "AlignmentException" => true
  | _ => false

def mem_payload_str_forwards (arg_ : mem_payload) : String :=
  match arg_ with
  | .Data => ""
  | .Vector => ""
  | .PageTableEntry => ""
  | .ShadowStack => ".ss"

def sp : regidx := (Regidx (zero_extend (m := 5) 0b10#2))

def accessType_to_str (access : (MemoryAccessType mem_payload)) : String :=
  match access with
  | .Load p => (HAppend.hAppend "R" (mem_payload_str_forwards p))
  | .LoadReserved (_, _, p) => (HAppend.hAppend "R" (mem_payload_str_forwards p))
  | .Store p => (HAppend.hAppend "W" (mem_payload_str_forwards p))
  | .StoreConditional (_, _, p) => (HAppend.hAppend "W" (mem_payload_str_forwards p))
  | .Atomic (_, _, _, lp, sp) =>
    (HAppend.hAppend "R"
      (HAppend.hAppend (mem_payload_str_forwards lp)
        (HAppend.hAppend "W" (mem_payload_str_forwards sp))))
  | .InstructionFetch () => "X"
  | .CacheAccess _ => "C"

def atomic_support_str_backwards (arg_ : String) : SailM AtomicSupport := do
  match arg_ with
  | "AMONone" => (pure AMONone)
  | "AMOSwap" => (pure AMOSwap)
  | "AMOLogical" => (pure AMOLogical)
  | "AMOArithmetic" => (pure AMOArithmetic)
  | "AMOCASW" => (pure AMOCASW)
  | "AMOCASD" => (pure AMOCASD)
  | "AMOCASQ" => (pure AMOCASQ)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def atomic_support_str_forwards (arg_ : AtomicSupport) : String :=
  match arg_ with
  | .AMONone => "AMONone"
  | .AMOSwap => "AMOSwap"
  | .AMOLogical => "AMOLogical"
  | .AMOArithmetic => "AMOArithmetic"
  | .AMOCASW => "AMOCASW"
  | .AMOCASD => "AMOCASD"
  | .AMOCASQ => "AMOCASQ"

def csr_name_map_forwards (arg_ : (BitVec 12)) : SailM String := do
  match arg_ with
  | 0x301 => (pure "misa")
  | 0x300 => (pure "mstatus")
  | 0x310 => (pure "mstatush")
  | 0x747 => (pure "mseccfg")
  | 0x757 => (pure "mseccfgh")
  | 0x30A => (pure "menvcfg")
  | 0x31A => (pure "menvcfgh")
  | 0x10A => (pure "senvcfg")
  | 0x342 => (pure "mcause")
  | 0x343 => (pure "mtval")
  | 0x340 => (pure "mscratch")
  | 0x106 => (pure "scounteren")
  | 0x306 => (pure "mcounteren")
  | 0x320 => (pure "mcountinhibit")
  | 0xF11 => (pure "mvendorid")
  | 0xF12 => (pure "marchid")
  | 0xF13 => (pure "mimpid")
  | 0xF14 => (pure "mhartid")
  | 0xF15 => (pure "mconfigptr")
  | 0x100 => (pure "sstatus")
  | 0x140 => (pure "sscratch")
  | 0x142 => (pure "scause")
  | 0x143 => (pure "stval")
  | 0x7A0 => (pure "tselect")
  | 0x7A1 => (pure "tdata1")
  | 0x7A2 => (pure "tdata2")
  | 0x7A3 => (pure "tdata3")
  | 0x304 => (pure "mie")
  | 0x344 => (pure "mip")
  | 0x302 => (pure "medeleg")
  | 0x312 => (pure "medelegh")
  | 0x303 => (pure "mideleg")
  | 0x144 => (pure "sip")
  | 0x104 => (pure "sie")
  | 0x105 => (pure "stvec")
  | 0x141 => (pure "sepc")
  | 0x305 => (pure "mtvec")
  | 0x341 => (pure "mepc")
  | 0x3A0 => (pure "pmpcfg0")
  | 0x3A1 => (pure "pmpcfg1")
  | 0x3A2 => (pure "pmpcfg2")
  | 0x3A3 => (pure "pmpcfg3")
  | 0x3A4 => (pure "pmpcfg4")
  | 0x3A5 => (pure "pmpcfg5")
  | 0x3A6 => (pure "pmpcfg6")
  | 0x3A7 => (pure "pmpcfg7")
  | 0x3A8 => (pure "pmpcfg8")
  | 0x3A9 => (pure "pmpcfg9")
  | 0x3AA => (pure "pmpcfg10")
  | 0x3AB => (pure "pmpcfg11")
  | 0x3AC => (pure "pmpcfg12")
  | 0x3AD => (pure "pmpcfg13")
  | 0x3AE => (pure "pmpcfg14")
  | 0x3AF => (pure "pmpcfg15")
  | 0x3B0 => (pure "pmpaddr0")
  | 0x3B1 => (pure "pmpaddr1")
  | 0x3B2 => (pure "pmpaddr2")
  | 0x3B3 => (pure "pmpaddr3")
  | 0x3B4 => (pure "pmpaddr4")
  | 0x3B5 => (pure "pmpaddr5")
  | 0x3B6 => (pure "pmpaddr6")
  | 0x3B7 => (pure "pmpaddr7")
  | 0x3B8 => (pure "pmpaddr8")
  | 0x3B9 => (pure "pmpaddr9")
  | 0x3BA => (pure "pmpaddr10")
  | 0x3BB => (pure "pmpaddr11")
  | 0x3BC => (pure "pmpaddr12")
  | 0x3BD => (pure "pmpaddr13")
  | 0x3BE => (pure "pmpaddr14")
  | 0x3BF => (pure "pmpaddr15")
  | 0x3C0 => (pure "pmpaddr16")
  | 0x3C1 => (pure "pmpaddr17")
  | 0x3C2 => (pure "pmpaddr18")
  | 0x3C3 => (pure "pmpaddr19")
  | 0x3C4 => (pure "pmpaddr20")
  | 0x3C5 => (pure "pmpaddr21")
  | 0x3C6 => (pure "pmpaddr22")
  | 0x3C7 => (pure "pmpaddr23")
  | 0x3C8 => (pure "pmpaddr24")
  | 0x3C9 => (pure "pmpaddr25")
  | 0x3CA => (pure "pmpaddr26")
  | 0x3CB => (pure "pmpaddr27")
  | 0x3CC => (pure "pmpaddr28")
  | 0x3CD => (pure "pmpaddr29")
  | 0x3CE => (pure "pmpaddr30")
  | 0x3CF => (pure "pmpaddr31")
  | 0x3D0 => (pure "pmpaddr32")
  | 0x3D1 => (pure "pmpaddr33")
  | 0x3D2 => (pure "pmpaddr34")
  | 0x3D3 => (pure "pmpaddr35")
  | 0x3D4 => (pure "pmpaddr36")
  | 0x3D5 => (pure "pmpaddr37")
  | 0x3D6 => (pure "pmpaddr38")
  | 0x3D7 => (pure "pmpaddr39")
  | 0x3D8 => (pure "pmpaddr40")
  | 0x3D9 => (pure "pmpaddr41")
  | 0x3DA => (pure "pmpaddr42")
  | 0x3DB => (pure "pmpaddr43")
  | 0x3DC => (pure "pmpaddr44")
  | 0x3DD => (pure "pmpaddr45")
  | 0x3DE => (pure "pmpaddr46")
  | 0x3DF => (pure "pmpaddr47")
  | 0x3E0 => (pure "pmpaddr48")
  | 0x3E1 => (pure "pmpaddr49")
  | 0x3E2 => (pure "pmpaddr50")
  | 0x3E3 => (pure "pmpaddr51")
  | 0x3E4 => (pure "pmpaddr52")
  | 0x3E5 => (pure "pmpaddr53")
  | 0x3E6 => (pure "pmpaddr54")
  | 0x3E7 => (pure "pmpaddr55")
  | 0x3E8 => (pure "pmpaddr56")
  | 0x3E9 => (pure "pmpaddr57")
  | 0x3EA => (pure "pmpaddr58")
  | 0x3EB => (pure "pmpaddr59")
  | 0x3EC => (pure "pmpaddr60")
  | 0x3ED => (pure "pmpaddr61")
  | 0x3EE => (pure "pmpaddr62")
  | 0x3EF => (pure "pmpaddr63")
  | 0x001 => (pure "fflags")
  | 0x002 => (pure "frm")
  | 0x003 => (pure "fcsr")
  | 0x008 => (pure "vstart")
  | 0x009 => (pure "vxsat")
  | 0x00A => (pure "vxrm")
  | 0x00F => (pure "vcsr")
  | 0xC20 => (pure "vl")
  | 0xC21 => (pure "vtype")
  | 0xC22 => (pure "vlenb")
  | 0x321 => (pure "mcyclecfg")
  | 0x721 => (pure "mcyclecfgh")
  | 0x322 => (pure "minstretcfg")
  | 0x722 => (pure "minstretcfgh")
  | 0x30C => (pure "mstateen0")
  | 0x30D => (pure "mstateen1")
  | 0x30E => (pure "mstateen2")
  | 0x30F => (pure "mstateen3")
  | 0x31C => (pure "mstateen0h")
  | 0x31D => (pure "mstateen1h")
  | 0x31E => (pure "mstateen2h")
  | 0x31F => (pure "mstateen3h")
  | 0x60C => (pure "hstateen0")
  | 0x60D => (pure "hstateen1")
  | 0x60E => (pure "hstateen2")
  | 0x60F => (pure "hstateen3")
  | 0x61C => (pure "hstateen0h")
  | 0x61D => (pure "hstateen1h")
  | 0x61E => (pure "hstateen2h")
  | 0x61F => (pure "hstateen3h")
  | 0x10C => (pure "sstateen0")
  | 0x10D => (pure "sstateen1")
  | 0x10E => (pure "sstateen2")
  | 0x10F => (pure "sstateen3")
  | 0x180 => (pure "satp")
  | reg => (hex_bits_12_forwards reg)

def csr_name (csr : (BitVec 12)) : SailM String := do
  (csr_name_map_forwards csr)

def ext_exc_type_to_str (_e : Unit) : String :=
  "extension-exception"

def exceptionType_to_str (e : ExceptionType) : String :=
  match e with
  | .E_Fetch_Addr_Align () => "misaligned-fetch"
  | .E_Fetch_Access_Fault () => "fetch-access-fault"
  | .E_Illegal_Instr () => "illegal-instruction"
  | .E_Load_Addr_Align () => "misaligned-load"
  | .E_Load_Access_Fault () => "load-access-fault"
  | .E_SAMO_Addr_Align () => "misaligned-store/amo"
  | .E_SAMO_Access_Fault () => "store/amo-access-fault"
  | .E_U_EnvCall () => "u-call"
  | .E_S_EnvCall () => "s-call"
  | .E_VS_EnvCall () => "vs-call"
  | .E_M_EnvCall () => "m-call"
  | .E_Fetch_Page_Fault () => "fetch-page-fault"
  | .E_Load_Page_Fault () => "load-page-fault"
  | .E_Reserved_14 () => "reserved-1"
  | .E_SAMO_Page_Fault () => "store/amo-page-fault"
  | .E_Reserved_16 () => "reserved-2"
  | .E_Reserved_17 () => "reserved-3"
  | .E_Software_Check () => "software-check-fault"
  | .E_Reserved_19 () => "reserved-19"
  | .E_Fetch_GPage_Fault () => "fetch-guest-page-fault"
  | .E_Load_GPage_Fault () => "load-guest-page-fault"
  | .E_Virtual_Instr () => "virtual-instruction"
  | .E_SAMO_GPage_Fault () => "store/amo-guest-page-fault"
  | .E_Breakpoint .Brk_Software => "software-breakpoint"
  | .E_Breakpoint .Brk_Hardware => "hardware-breakpoint"
  | .E_Extension e => (ext_exc_type_to_str e)

def btype_mnemonic_forwards (arg_ : bop) : String :=
  match arg_ with
  | .BEQ => "beq"
  | .BNE => "bne"
  | .BLT => "blt"
  | .BGE => "bge"
  | .BLTU => "bltu"
  | .BGEU => "bgeu"

def bit_maybe_i_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "i"
  | _ => ""

def bit_maybe_o_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "o"
  | _ => ""

def bit_maybe_r_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "r"
  | _ => ""

def bit_maybe_w_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "w"
  | _ => ""

def fence_bits_forwards (arg_ : (BitVec 4)) : String :=
  match arg_ with
  | 0b0000 => "0"
  | v__8 =>
    (let i : (BitVec 1) := (Sail.BitVec.extractLsb v__8 3 3)
    let w : (BitVec 1) := (Sail.BitVec.extractLsb v__8 0 0)
    let r : (BitVec 1) := (Sail.BitVec.extractLsb v__8 1 1)
    let o : (BitVec 1) := (Sail.BitVec.extractLsb v__8 2 2)
    let i : (BitVec 1) := (Sail.BitVec.extractLsb v__8 3 3)
    (String.append (bit_maybe_i_forwards i)
      (String.append (bit_maybe_o_forwards o)
        (String.append (bit_maybe_r_forwards r) (String.append (bit_maybe_w_forwards w) "")))))

def itype_mnemonic_forwards (arg_ : iop) : String :=
  match arg_ with
  | .ADDI => "addi"
  | .SLTI => "slti"
  | .SLTIU => "sltiu"
  | .XORI => "xori"
  | .ORI => "ori"
  | .ANDI => "andi"

/-- Type quantifiers: k_ex251093_ : Bool -/
def maybe_u_forwards (arg_ : Bool) : String :=
  match arg_ with
  | true => "u"
  | false => ""

def mul_mnemonic_forwards (arg_ : mul_op) : SailM String := do
  match arg_ with
  | { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure "mul")
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure "mulh")
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => (pure "mulhsu")
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => (pure "mulhu")
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_reg_forwards (arg_ : regidx) : (BitVec 5) :=
  match arg_ with
  | .Regidx r => (zero_extend (m := 5) r)

def encdec_reg_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx r => true

def reg_abi_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "zero"
  | 0b00001 => "ra"
  | 0b00010 => "sp"
  | 0b00011 => "gp"
  | 0b00100 => "tp"
  | 0b00101 => "t0"
  | 0b00110 => "t1"
  | 0b00111 => "t2"
  | 0b01000 => "s0"
  | 0b01000 => "fp"
  | 0b01001 => "s1"
  | 0b01010 => "a0"
  | 0b01011 => "a1"
  | 0b01100 => "a2"
  | 0b01101 => "a3"
  | 0b01110 => "a4"
  | 0b01111 => "a5"
  | 0b10000 => "a6"
  | 0b10001 => "a7"
  | 0b10010 => "s2"
  | 0b10011 => "s3"
  | 0b10100 => "s4"
  | 0b10101 => "s5"
  | 0b10110 => "s6"
  | 0b10111 => "s7"
  | 0b11000 => "s8"
  | 0b11001 => "s9"
  | 0b11010 => "s10"
  | 0b11011 => "s11"
  | 0b11100 => "t3"
  | 0b11101 => "t4"
  | 0b11110 => "t5"
  | _ => "t6"

def reg_arch_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "x0"
  | 0b00001 => "x1"
  | 0b00010 => "x2"
  | 0b00011 => "x3"
  | 0b00100 => "x4"
  | 0b00101 => "x5"
  | 0b00110 => "x6"
  | 0b00111 => "x7"
  | 0b01000 => "x8"
  | 0b01001 => "x9"
  | 0b01010 => "x10"
  | 0b01011 => "x11"
  | 0b01100 => "x12"
  | 0b01101 => "x13"
  | 0b01110 => "x14"
  | 0b01111 => "x15"
  | 0b10000 => "x16"
  | 0b10001 => "x17"
  | 0b10010 => "x18"
  | 0b10011 => "x19"
  | 0b10100 => "x20"
  | 0b10101 => "x21"
  | 0b10110 => "x22"
  | 0b10111 => "x23"
  | 0b11000 => "x24"
  | 0b11001 => "x25"
  | 0b11010 => "x26"
  | 0b11011 => "x27"
  | 0b11100 => "x28"
  | 0b11101 => "x29"
  | 0b11110 => "x30"
  | _ => "x31"

def reg_name_forwards (arg_ : regidx) : SailM String := do
  let head_exp_ := arg_
  match (let mapping0_ := head_exp_
  if ((encdec_reg_forwards_matches mapping0_) : Bool)
  then
    (let i := (encdec_reg_forwards mapping0_)
    if ((get_config_use_abi_names ()) : Bool)
    then (some (reg_abi_name_raw_forwards i))
    else none)
  else none) with
  | .some result => (pure result)
  | none =>
    (do
      match (let mapping1_ := head_exp_
      if ((encdec_reg_forwards_matches mapping1_) : Bool)
      then
        (let i := (encdec_reg_forwards mapping1_)
        if ((not (get_config_use_abi_names ())) : Bool)
        then (some (reg_arch_name_raw_forwards i))
        else none)
      else none) with
      | .some result => (pure result)
      | _ =>
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def rtype_mnemonic_forwards (arg_ : rop) : String :=
  match arg_ with
  | .ADD => "add"
  | .SLT => "slt"
  | .SLTU => "sltu"
  | .AND => "and"
  | .OR => "or"
  | .XOR => "xor"
  | .SLL => "sll"
  | .SRL => "srl"
  | .SUB => "sub"
  | .SRA => "sra"

def rtypew_mnemonic_forwards (arg_ : ropw) : String :=
  match arg_ with
  | .ADDW => "addw"
  | .SUBW => "subw"
  | .SLLW => "sllw"
  | .SRLW => "srlw"
  | .SRAW => "sraw"

def shiftiop_mnemonic_forwards (arg_ : sop) : String :=
  match arg_ with
  | .SLLI => "slli"
  | .SRLI => "srli"
  | .SRAI => "srai"

def shiftiwop_mnemonic_forwards (arg_ : sopw) : String :=
  match arg_ with
  | .SLLIW => "slliw"
  | .SRLIW => "srliw"
  | .SRAIW => "sraiw"

def utype_mnemonic_forwards (arg_ : uop) : String :=
  match arg_ with
  | .LUI => "lui"
  | .AUIPC => "auipc"

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def width_mnemonic_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "b"
  | 2 => "h"
  | 4 => "w"
  | _ => "d"

def zreg : regidx := (Regidx (zero_extend (m := 5) 0b00#2))

def assembly_forwards (arg_ : instruction) : SailM String := do
  match arg_ with
  | .LPAD lpl =>
    (pure (String.append "lpad"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_20_forwards lpl)) ""))))
  | .UTYPE (imm, rd, op) =>
    (pure (String.append (utype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_20_forwards imm)) ""))))))
  | .JAL (imm, rd) =>
    (pure (String.append "jal"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_21_forwards imm)) ""))))))
  | .JALR (imm, rs1, rd) =>
    (pure (String.append "jalr"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_12_forwards imm))
                (String.append "("
                  (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))
  | .BTYPE (imm, rs2, rs1, op) =>
    (pure (String.append (btype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_13_forwards imm)) ""))))))))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure (String.append (itype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
  | .SHIFTIOP (shamt, rs1, rd, op) =>
    (pure (String.append (shiftiop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (pure (String.append "l"
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_u_forwards is_unsigned)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm))
                    (String.append "("
                      (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))))
  | .STORE (imm, rs2, rs1, width) =>
    (pure (String.append "s"
        (String.append (width_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rs2))
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (← (reg_name_forwards rs1))
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .ADDIW (imm, rs1, rd) =>
    (pure (String.append "addiw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
  | .RTYPEW (rs2, rs1, rd, op) =>
    (pure (String.append (rtypew_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (pure (String.append (shiftiwop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
  | .FENCE_TSO () => (pure "fence.tso")
  | .FENCE (0b0000, pred, succ, rs, rd) =>
    (do
      if (((rs == zreg) && (rd == zreg)) : Bool)
      then
        (pure (HAppend.hAppend "fence"
            (HAppend.hAppend (spc_forwards ())
              (HAppend.hAppend (fence_bits_forwards pred)
                (HAppend.hAppend (sep_forwards ()) (fence_bits_forwards succ))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ECALL () => (pure "ecall")
  | .MRET () => (pure "mret")
  | .SRET () => (pure "sret")
  | .EBREAK () => (pure "ebreak")
  | .WFI () => (pure "wfi")
  | .SFENCE_VMA (rs1, rs2) =>
    (pure (String.append "sfence.vma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (pure (String.append (← (mul_mnemonic_forwards mul_op))
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "div"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "rem"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .MULW (rs2, rs1, rd) =>
    (pure (String.append "mulw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "div"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append "w"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "rem"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append "w"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))))
  | .ILLEGAL s =>
    (pure (String.append "illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_32_forwards s)) ""))))
  | .C_ILLEGAL s =>
    (pure (String.append "c.illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_16_forwards s)) ""))))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def assembly_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .LPAD lpl => true
  | .UTYPE (imm, rd, op) => true
  | .JAL (imm, rd) => true
  | .JALR (imm, rs1, rd) => true
  | .BTYPE (imm, rs2, rs1, op) => true
  | .ITYPE (imm, rs1, rd, op) => true
  | .SHIFTIOP (shamt, rs1, rd, op) => true
  | .RTYPE (rs2, rs1, rd, op) => true
  | .LOAD (imm, rs1, rd, is_unsigned, width) => true
  | .STORE (imm, rs2, rs1, width) => true
  | .ADDIW (imm, rs1, rd) => true
  | .RTYPEW (rs2, rs1, rd, op) => true
  | .SHIFTIWOP (shamt, rs1, rd, op) => true
  | .FENCE_TSO () => true
  | .FENCE (0b0000, pred, succ, rs, rd) =>
    (if (((rs == zreg) && (rd == zreg)) : Bool)
    then true
    else false)
  | .ECALL () => true
  | .MRET () => true
  | .SRET () => true
  | .EBREAK () => true
  | .WFI () => true
  | .SFENCE_VMA (rs1, rs2) => true
  | .MUL (rs2, rs1, rd, mul_op) => true
  | .DIV (rs2, rs1, rd, is_unsigned) => true
  | .REM (rs2, rs1, rd, is_unsigned) => true
  | .MULW (rs2, rs1, rd) => true
  | .DIVW (rs2, rs1, rd, is_unsigned) => true
  | .REMW (rs2, rs1, rd, is_unsigned) => true
  | .ILLEGAL s => true
  | .C_ILLEGAL s => true
  | _ => false

def undefined_Privilege (_ : Unit) : SailM Privilege := do
  (internal_pick [User, VirtualUser, Supervisor, VirtualSupervisor, Machine])

def Mk_Misa (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_Misa_MXL (v : (BitVec 64)) (x : (BitVec (64 - 1 - (64 - 2) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) (64 -i 2) x)

def architecture_bits_forwards (arg_ : Architecture) : (BitVec 2) :=
  match arg_ with
  | .RV32 => 0b01#2
  | .RV64 => 0b10#2
  | .RV128 => 0b11#2

def Mk_Mstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_Mstatus_SXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _update_Mstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def hartSupports_measure (ext : extension) : Int :=
  match ext with
  | .Ext_D => 1
  | .Ext_Sstvecd => 1
  | .Ext_Ssu64xl => 1
  | .Ext_Zvkn => 1
  | .Ext_Zvks => 1
  | .Ext_Sspm => 1
  | .Ext_Supm => 1
  | .Ext_C => 2
  | .Ext_Zvknc => 2
  | .Ext_Zvkng => 2
  | .Ext_Zvksc => 2
  | .Ext_Zvksg => 2
  | _ => 0

def hartSupports (merge_var : extension) : Bool :=
  match merge_var with
  | .Ext_M => true
  | .Ext_A => true
  | .Ext_F => true
  | .Ext_D => (true && (hartSupports Ext_F))
  | .Ext_B => true
  | .Ext_V => ((8 ≥b 7) && (vector_support_ge vector_support_level Full))
  | .Ext_S => true
  | .Ext_U => true
  | .Ext_H => false
  | .Ext_Zibi => ((sys_enable_experimental_extensions ()) && (true : Bool))
  | .Ext_Zic64b => true
  | .Ext_Zicbom => true
  | .Ext_Zicbop => true
  | .Ext_Zicboz => true
  | .Ext_Zicfilp => true
  | .Ext_Zicfiss => true
  | .Ext_Zicntr => true
  | .Ext_Zicond => true
  | .Ext_Zicsr => true
  | .Ext_Zifencei => true
  | .Ext_Zihintntl => true
  | .Ext_Zihintpause => true
  | .Ext_Zihpm => true
  | .Ext_Zimop => true
  | .Ext_Zmmul => false
  | .Ext_Zaamo => false
  | .Ext_Zabha => true
  | .Ext_Zacas => true
  | .Ext_Zalrsc => false
  | .Ext_Zawrs => true
  | .Ext_Za64rs => ((plat_reservation_set_size_exp ≤b 6) && ((false : Bool) || (true : Bool)))
  | .Ext_Za128rs => ((plat_reservation_set_size_exp ≤b 7) && ((false : Bool) || (true : Bool)))
  | .Ext_Zfa => true
  | .Ext_Zfbfmin => true
  | .Ext_Zfh => true
  | .Ext_Zfhmin => true
  | .Ext_Zfinx => false
  | .Ext_Zdinx => false
  | .Ext_Zca => true
  | .Ext_Zcb => true
  | .Ext_Zcd => true
  | .Ext_Zcf => ((false : Bool) && (xlen == 32))
  | .Ext_Zcmop => true
  | .Ext_C =>
    ((hartSupports Ext_Zca) && (((hartSupports Ext_Zcf) || ((not (hartSupports Ext_F)) || (xlen != 32))) && ((hartSupports
            Ext_Zcd) || (not (hartSupports Ext_D)))))
  | .Ext_Zba => false
  | .Ext_Zbb => false
  | .Ext_Zbc => true
  | .Ext_Zbkb => true
  | .Ext_Zbkc => true
  | .Ext_Zbkx => true
  | .Ext_Zbs => false
  | .Ext_Ziccamoa => true
  | .Ext_Ziccamoc => true
  | .Ext_Ziccif => true
  | .Ext_Zicclsm => true
  | .Ext_Ziccrse => true
  | .Ext_Zknd => true
  | .Ext_Zkne => true
  | .Ext_Zknh => true
  | .Ext_Zkr => true
  | .Ext_Zksed => true
  | .Ext_Zksh => true
  | .Ext_Zkt => true
  | .Ext_Zhinx => false
  | .Ext_Zhinxmin => false
  | .Ext_Zvl32b => (8 ≥b 5)
  | .Ext_Zvl64b => (8 ≥b 6)
  | .Ext_Zvl128b => (8 ≥b 7)
  | .Ext_Zvl256b => (8 ≥b 8)
  | .Ext_Zvl512b => (8 ≥b 9)
  | .Ext_Zvl1024b => (8 ≥b 10)
  | .Ext_Zve32f => ((6 ≥b 5) && (vector_support_ge vector_support_level Float_single))
  | .Ext_Zve32x => ((6 ≥b 5) && (vector_support_ge vector_support_level Integer))
  | .Ext_Zve64d => ((6 ≥b 6) && (vector_support_ge vector_support_level Float_double))
  | .Ext_Zve64f => ((6 ≥b 6) && (vector_support_ge vector_support_level Float_single))
  | .Ext_Zve64x => ((6 ≥b 6) && (vector_support_ge vector_support_level Integer))
  | .Ext_Zvabd => ((sys_enable_experimental_extensions ()) && (true : Bool))
  | .Ext_Zvfbfmin => true
  | .Ext_Zvfbfwma => true
  | .Ext_Zvfh => true
  | .Ext_Zvfhmin => true
  | .Ext_Zvbb => true
  | .Ext_Zvbc => true
  | .Ext_Zvkb => false
  | .Ext_Zvkg => true
  | .Ext_Zvkned => true
  | .Ext_Zvknha => true
  | .Ext_Zvknhb => true
  | .Ext_Zvksed => true
  | .Ext_Zvksh => true
  | .Ext_Zvkt => true
  | .Ext_Zvkn =>
    ((hartSupports Ext_Zvkned) && ((hartSupports Ext_Zvknhb) && ((hartSupports Ext_Zvkb) && (hartSupports
            Ext_Zvkt))))
  | .Ext_Zvknc => ((hartSupports Ext_Zvkn) && (hartSupports Ext_Zvbc))
  | .Ext_Zvkng => ((hartSupports Ext_Zvkn) && (hartSupports Ext_Zvkg))
  | .Ext_Zvks =>
    ((hartSupports Ext_Zvksed) && ((hartSupports Ext_Zvksh) && ((hartSupports Ext_Zvkb) && (hartSupports
            Ext_Zvkt))))
  | .Ext_Zvksc => ((hartSupports Ext_Zvks) && (hartSupports Ext_Zvbc))
  | .Ext_Zvksg => ((hartSupports Ext_Zvks) && (hartSupports Ext_Zvkg))
  | .Ext_Ssccptr => true
  | .Ext_Sscofpmf => true
  | .Ext_Sscounterenw => true
  | .Ext_Ssnpm => ((true : Bool) && (xlen == 64))
  | .Ext_Ssstateen => true
  | .Ext_Sstc => true
  | .Ext_Sstvala => true
  | .Ext_Sstvecd => (hartSupports Ext_S)
  | .Ext_Ssu64xl => ((hartSupports Ext_S) && (xlen == 64))
  | .Ext_Svbare => true
  | .Ext_Sv32 => ((false : Bool) && (xlen == 32))
  | .Ext_Sv39 => ((true : Bool) && (xlen == 64))
  | .Ext_Sv48 => ((true : Bool) && (xlen == 64))
  | .Ext_Sv57 => ((true : Bool) && (xlen == 64))
  | .Ext_Svade => true
  | .Ext_Svadu => true
  | .Ext_Svinval => true
  | .Ext_Svnapot => ((true : Bool) && (xlen == 64))
  | .Ext_Svpbmt => ((true : Bool) && (xlen == 64))
  | .Ext_Svrsw60t59b => true
  | .Ext_Svvptc => true
  | .Ext_Smcntrpmf => true
  | .Ext_Smmpm => ((true : Bool) && (xlen == 64))
  | .Ext_Smnpm => ((true : Bool) && (xlen == 64))
  | .Ext_Smstateen => true
  | .Ext_Ssqosid => true
  | .Ext_Sspm => ((hartSupports Ext_Smnpm) && (hartSupports Ext_S))
  | .Ext_Supm =>
    ((hartSupports Ext_U) && (if ((hartSupports Ext_S) : Bool)
      then (hartSupports Ext_Ssnpm)
      else (hartSupports Ext_Smnpm)))
termination_by (let ext := merge_var
(hartSupports_measure ext)).toNat

def _get_Misa_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Misa_D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Misa_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_Misa_M (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_Misa_S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_Misa_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_Misa_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_Mstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _get_Mstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def currentlyEnabled_measure (ext : extension) : Int :=
  match ext with
  | .Ext_A => 0
  | .Ext_B => 0
  | .Ext_C => 0
  | .Ext_M => 0
  | .Ext_Zicsr => 0
  | .Ext_Zvl128b => 0
  | .Ext_Zvl32b => 0
  | .Ext_Zvl64b => 0
  | .Ext_Zimop => 0
  | .Ext_D => 1
  | .Ext_F => 1
  | .Ext_S => 1
  | .Ext_Zaamo => 1
  | .Ext_Zalrsc => 1
  | .Ext_Zca => 1
  | .Ext_Zicntr => 1
  | .Ext_Zihpm => 1
  | .Ext_Zve32x => 1
  | .Ext_Smstateen => 1
  | .Ext_Ssstateen => 1
  | .Ext_Sscounterenw => 2
  | .Ext_Sv39 => 2
  | .Ext_Zfh => 2
  | .Ext_Zvbb => 2
  | .Ext_Zve32f => 2
  | .Ext_Zve64x => 2
  | .Ext_Zcmop => 2
  | .Ext_Zicfiss => 2
  | .Ext_Ssccptr => 3
  | .Ext_Supm => 3
  | .Ext_Svnapot => 3
  | .Ext_Svpbmt => 3
  | .Ext_Svvptc => 3
  | .Ext_Svrsw60t59b => 3
  | .Ext_Zfhmin => 3
  | .Ext_Zicfilp => 3
  | .Ext_Zvbc => 3
  | .Ext_Zve64f => 3
  | .Ext_Zvfbfmin => 3
  | .Ext_Zvkb => 3
  | .Ext_Zvknhb => 3
  | .Ext_H => 4
  | .Ext_Zve64d => 4
  | .Ext_Zvfbfwma => 4
  | .Ext_Zvfh => 4
  | .Ext_V => 5
  | .Ext_Zvfhmin => 5
  | .Ext_Zfinx => 9
  | .Ext_Zdinx => 10
  | .Ext_Zhinx => 10
  | .Ext_Zhinxmin => 11
  | _ => 2

def Mk_MEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MEnvcfg_ADUE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_MEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_MEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_MEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_MEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_MEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_MEnvcfg_PBMTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_MEnvcfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_MEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_MEnvcfg_STCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_MEnvcfg_ADUE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_MEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_MEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_MEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_MEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_MEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_MEnvcfg_PBMTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_MEnvcfg_PMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_MEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_MEnvcfg_STCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def xenvcfg_cbie_reserved_behavior : XenvcfgCbieReservedBehavior := Xenvcfg_ClearPermissions

def legalize_xenvcfg_cbie (cbie : (BitVec 2)) : SailM (BitVec 2) := do
  if ((cbie != 0b10#2) : Bool)
  then (pure cbie)
  else
    (do
      match xenvcfg_cbie_reserved_behavior with
      | .Xenvcfg_Fatal => (reserved_behavior "xenvcfg.CBIE = 0b10")
      | .Xenvcfg_ClearPermissions => (pure 0b00#2))

def sys_enable_writable_fiom : Bool := true

def Mk_Seccfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Seccfg_MLPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_Seccfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_Seccfg_SSEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_Seccfg_USEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Seccfg_MLPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_Seccfg_PMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_Seccfg_SSEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_Seccfg_USEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_SEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def Mk_SEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_SEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_SEnvcfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_SEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_SEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SEnvcfg_PMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_SEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def Mk_Hstateen0 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen1 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen2 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen3 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen0 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen1 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen2 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen3 (v : (BitVec 64)) : (BitVec 64) :=
  v

def is_mstateen_accessible (_ : Unit) : Bool :=
  (hartSupports Ext_Smstateen)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_mstateen (idx : Nat) : SailM (BitVec 64) := do
  if ((not (is_mstateen_accessible ())) : Bool)
  then (pure (ones (n := 64)))
  else
    (do
      match idx with
      | 0 => readReg mstateen0
      | 1 => readReg mstateen1
      | 2 => readReg mstateen2
      | _ => readReg mstateen3)

def Mk_Sstateen0 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen1 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen2 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen3 (v : (BitVec 32)) : (BitVec 32) :=
  v

def stateen_bit_index_forwards (arg_ : stateen_bit) : Nat :=
  match arg_ with
  | .STATEEN_SE => 63
  | .STATEEN_ENVCFG => 62
  | .STATEEN_SRMCFG => 55
  | .STATEEN_FCSR => 1

def read_senvcfg (_ : Unit) : SailM (BitVec 64) := do
  (pure (_update_SEnvcfg_SSE (← readReg senvcfg)
      ((_get_MEnvcfg_SSE (← readReg menvcfg)) &&& (_get_SEnvcfg_SSE (← readReg senvcfg)))))


mutual
/-- Type quantifiers: stateen_reg : Nat, 0 ≤ stateen_reg ∧ stateen_reg ≤ 3 -/
def check_stateen_bit (priv : Privilege) (bit_idx : stateen_bit) (stateen_reg : Nat) : SailM Bool := do
  let mask ← (( do
    match priv with
    | .Machine => (pure (ones (n := 64)))
    | .Supervisor => (get_mstateen stateen_reg)
    | .User => (pure ((← (get_mstateen stateen_reg)) &&& (← (get_sstateen stateen_reg))))
    | .VirtualSupervisor =>
      (pure ((← (get_mstateen stateen_reg)) &&& (← (get_hstateen stateen_reg))))
    | .VirtualUser =>
      (pure ((← (get_mstateen stateen_reg)) &&& ((← (get_hstateen stateen_reg)) &&& (← (get_sstateen
                stateen_reg))))) ) : SailM (BitVec 64) )
  (pure ((BitVec.access mask (stateen_bit_index_forwards bit_idx)) == 1#1))
termination_by (let (_, _, _) := (priv, bit_idx, stateen_reg)
7).toNat
def currentlyEnabled (merge_var : extension) : SailM Bool := do
  match merge_var with
  | .Ext_Zic64b => (pure (hartSupports Ext_Zic64b))
  | .Ext_Ziccif => (pure (hartSupports Ext_Ziccif))
  | .Ext_Zicclsm => (pure (hartSupports Ext_Zicclsm))
  | .Ext_Zkt => (pure (hartSupports Ext_Zkt))
  | .Ext_Zvkt => (pure (hartSupports Ext_Zvkt))
  | .Ext_Zvkn => (pure (hartSupports Ext_Zvkn))
  | .Ext_Zvknc => (pure (hartSupports Ext_Zvknc))
  | .Ext_Zvkng => (pure (hartSupports Ext_Zvkng))
  | .Ext_Zvks => (pure (hartSupports Ext_Zvks))
  | .Ext_Zvksc => (pure (hartSupports Ext_Zvksc))
  | .Ext_Zvksg => (pure (hartSupports Ext_Zvksg))
  | .Ext_Ssnpm => (pure ((hartSupports Ext_Ssnpm) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sstvala => (pure ((hartSupports Ext_Sstvala) && (← (currentlyEnabled Ext_S))))
  | .Ext_Smmpm => (pure (hartSupports Ext_Smmpm))
  | .Ext_Smnpm => (pure (hartSupports Ext_Smnpm))
  | .Ext_Sspm => (pure ((hartSupports Ext_Sspm) && (← (currentlyEnabled Ext_S))))
  | .Ext_Supm => (pure ((hartSupports Ext_Supm) && (← (currentlyEnabled Ext_U))))
  | .Ext_Sstc => (pure (hartSupports Ext_Sstc))
  | .Ext_U =>
    (pure ((hartSupports Ext_U) && (((_get_Misa_U (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zicsr)))))
  | .Ext_S =>
    (pure ((hartSupports Ext_S) && (((_get_Misa_S (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zicsr)))))
  | .Ext_Ssu64xl => (pure ((hartSupports Ext_Ssu64xl) && (← (currentlyEnabled Ext_S))))
  | .Ext_Svbare => (currentlyEnabled Ext_S)
  | .Ext_Sv32 => (pure ((hartSupports Ext_Sv32) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sv39 => (pure ((hartSupports Ext_Sv39) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sv48 => (pure ((hartSupports Ext_Sv48) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sv57 => (pure ((hartSupports Ext_Sv57) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sstvecd => (pure ((hartSupports Ext_Sstvecd) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sscounterenw => (pure ((hartSupports Ext_Sscounterenw) && (← (currentlyEnabled Ext_S))))
  | .Ext_Smstateen => (pure ((hartSupports Ext_Smstateen) && (← (currentlyEnabled Ext_Zicsr))))
  | .Ext_Ssstateen => (pure ((hartSupports Ext_Ssstateen) && (← (currentlyEnabled Ext_Zicsr))))
  | .Ext_F =>
    (pure ((hartSupports Ext_F) && (((_get_Misa_F (← readReg misa)) == 1#1) && (((_get_Mstatus_FS
                (← readReg mstatus)) != 0b00#2) && (← (currentlyEnabled Ext_Zicsr))))))
  | .Ext_D =>
    (pure ((hartSupports Ext_D) && (((_get_Misa_D (← readReg misa)) == 1#1) && (((_get_Mstatus_FS
                (← readReg mstatus)) != 0b00#2) && ((flen ≥b 64) && (← (currentlyEnabled
                  Ext_Zicsr)))))))
  | .Ext_Zfinx =>
    (pure ((hartSupports Ext_Zfinx) && ((← (currentlyEnabled Ext_Zicsr)) && (← (is_zfinx_enabled_by_stateen
              ())))))
  | .Ext_Zvl32b => (pure (hartSupports Ext_Zvl32b))
  | .Ext_Zvl64b => (pure (hartSupports Ext_Zvl64b))
  | .Ext_Zvl128b => (pure (hartSupports Ext_Zvl128b))
  | .Ext_Zvl256b => (pure (hartSupports Ext_Zvl256b))
  | .Ext_Zvl512b => (pure (hartSupports Ext_Zvl512b))
  | .Ext_Zvl1024b => (pure (hartSupports Ext_Zvl1024b))
  | .Ext_Zve32x =>
    (pure ((hartSupports Ext_Zve32x) && ((← (currentlyEnabled Ext_Zvl32b)) && (((_get_Mstatus_VS
                (← readReg mstatus)) != 0b00#2) && (← (currentlyEnabled Ext_Zicsr))))))
  | .Ext_Zve32f =>
    (pure ((hartSupports Ext_Zve32f) && ((← (currentlyEnabled Ext_Zve32x)) && (← (currentlyEnabled
              Ext_F)))))
  | .Ext_Zve64x =>
    (pure ((hartSupports Ext_Zve64x) && ((← (currentlyEnabled Ext_Zvl64b)) && (← (currentlyEnabled
              Ext_Zve32x)))))
  | .Ext_Zve64f =>
    (pure ((hartSupports Ext_Zve64f) && ((← (currentlyEnabled Ext_Zve64x)) && (← (currentlyEnabled
              Ext_Zve32f)))))
  | .Ext_Zve64d =>
    (pure ((hartSupports Ext_Zve64d) && ((← (currentlyEnabled Ext_Zve64f)) && (← (currentlyEnabled
              Ext_D)))))
  | .Ext_V =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && ((← (currentlyEnabled
                Ext_Zvl128b)) && (← (currentlyEnabled Ext_Zve64d))))))
  | .Ext_Zvfh =>
    (pure ((hartSupports Ext_Zvfh) && ((← (currentlyEnabled Ext_Zve32f)) && (← (currentlyEnabled
              Ext_Zfhmin)))))
  | .Ext_Zvfhmin =>
    (pure (((hartSupports Ext_Zvfhmin) && (← (currentlyEnabled Ext_Zve32f))) || (← (currentlyEnabled
            Ext_Zvfh))))
  | .Ext_Smcntrpmf => (pure ((hartSupports Ext_Smcntrpmf) && (← (currentlyEnabled Ext_Zicntr))))
  | .Ext_Zicfilp =>
    (pure ((← (currentlyEnabled Ext_Zicsr)) && ((hartSupports Ext_Zicfilp) && (← (get_xLPE
              (← readReg cur_privilege))))))
  | .Ext_Svnapot => (pure ((hartSupports Ext_Svnapot) && (← (currentlyEnabled Ext_Sv39))))
  | .Ext_Svpbmt => (pure ((hartSupports Ext_Svpbmt) && (← (currentlyEnabled Ext_Sv39))))
  | .Ext_Svrsw60t59b => (pure ((hartSupports Ext_Svrsw60t59b) && (← (currentlyEnabled Ext_Sv39))))
  | .Ext_Svvptc =>
    (pure ((hartSupports Ext_Svvptc) && ((← (currentlyEnabled Ext_Sv32)) || (← (currentlyEnabled
              Ext_Sv39)))))
  | .Ext_Svade => (pure (hartSupports Ext_Svade))
  | .Ext_Svadu => (pure (hartSupports Ext_Svadu))
  | .Ext_Ssccptr =>
    (pure ((hartSupports Ext_Ssccptr) && ((← (currentlyEnabled Ext_Sv32)) || (← (currentlyEnabled
              Ext_Sv39)))))
  | .Ext_C => (pure ((hartSupports Ext_C) && ((_get_Misa_C (← readReg misa)) == 1#1)))
  | .Ext_Zca =>
    (pure ((hartSupports Ext_Zca) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))
  | .Ext_M => (pure ((hartSupports Ext_M) && ((_get_Misa_M (← readReg misa)) == 1#1)))
  | .Ext_Zmmul => (pure ((hartSupports Ext_Zmmul) || (← (currentlyEnabled Ext_M))))
  | _ =>
    (do
      assert false "Pattern match failure at extensions/M/mext_insts.sail:14.0-14.95"
      throw Error.Exit)
termination_by (let ext := merge_var
(currentlyEnabled_measure ext)).toNat
/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_hstateen (idx : Nat) : SailM (BitVec 64) := do
  if ((not (← (is_hstateen_accessible ()))) : Bool)
  then (pure (ones (n := 64)))
  else
    (do
      match idx with
      | 0 => readReg hstateen0
      | 1 => readReg hstateen1
      | 2 => readReg hstateen2
      | _ => readReg hstateen3)
termination_by (let _ := idx
6).toNat
/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_sstateen (idx : Nat) : SailM (BitVec 64) := do
  (pure (0xFFFFFFFF#32 +++ (← do
        if ((not (← (is_sstateen_accessible ()))) : Bool)
        then (pure (ones (n := (64 -i 32))))
        else
          (do
            match idx with
            | 0 => readReg sstateen0
            | 1 => readReg sstateen1
            | 2 => readReg sstateen2
            | _ => readReg sstateen3))))
termination_by (let _ := idx
3).toNat
def get_xLPE (p : Privilege) : SailM Bool := do
  match p with
  | .Machine => (pure (bool_bit_backwards (_get_Seccfg_MLPE (← readReg mseccfg))))
  | .Supervisor => (pure (bool_bit_backwards (_get_MEnvcfg_LPE (← readReg menvcfg))))
  | .User =>
    (do
      if ((← (currentlyEnabled Ext_S)) : Bool)
      then (pure (bool_bit_backwards (_get_SEnvcfg_LPE (← (read_senvcfg ())))))
      else (pure (bool_bit_backwards (_get_MEnvcfg_LPE (← readReg menvcfg)))))
  | .VirtualSupervisor =>
    (internal_error "extensions/cfi/zicfilp_regs.sail" 31 "Hypervisor extension not supported")
  | .VirtualUser =>
    (internal_error "extensions/cfi/zicfilp_regs.sail" 32 "Hypervisor extension not supported")
termination_by (let _ := p
2).toNat
def is_hstateen_accessible (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_H)) && ((← (currentlyEnabled Ext_Smstateen)) || (← (currentlyEnabled
            Ext_Ssstateen)))))
termination_by (let () := ()
5).toNat
def is_sstateen_accessible (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_S)) && ((← (currentlyEnabled Ext_Smstateen)) || (← (currentlyEnabled
            Ext_Ssstateen)))))
termination_by (let () := ()
2).toNat
def is_zfinx_enabled_by_stateen (_ : Unit) : SailM Bool := do
  (check_stateen_bit (← readReg cur_privilege) STATEEN_FCSR 0)
termination_by (let () := ()
8).toNat
end

def legalize_menvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_MEnvcfg v)
  (pure (_update_MEnvcfg_PBMTE
      (_update_MEnvcfg_ADUE
        (_update_MEnvcfg_PMM
          (_update_MEnvcfg_STCE
            (_update_MEnvcfg_CBIE
              (_update_MEnvcfg_CBCFE
                (_update_MEnvcfg_CBZE
                  (_update_MEnvcfg_SSE
                    (_update_MEnvcfg_LPE
                      (_update_MEnvcfg_FIOM o
                        (if (sys_enable_writable_fiom : Bool)
                        then (_get_MEnvcfg_FIOM v)
                        else 0#1))
                      (if ((hartSupports Ext_Zicfilp) : Bool)
                      then (_get_MEnvcfg_LPE v)
                      else 0#1))
                    (if ((hartSupports Ext_Zicfiss) : Bool)
                    then (_get_MEnvcfg_SSE v)
                    else 0#1))
                  (← do
                    if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
                    then (pure (_get_MEnvcfg_CBZE v))
                    else (pure 0#1)))
                (← do
                  if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
                  then (pure (_get_MEnvcfg_CBCFE v))
                  else (pure 0#1)))
              (← do
                if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
                then (legalize_xenvcfg_cbie (_get_MEnvcfg_CBIE v))
                else (pure 0b00#2)))
            (← do
              if ((← (currentlyEnabled Ext_Sstc)) : Bool)
              then (pure (_get_MEnvcfg_STCE v))
              else (pure 0#1)))
          (← do
            if (((← (currentlyEnabled Ext_Smnpm)) && (is_supported_pmm PM_SMNPM
                   (pmm_mode_backwards (_get_MEnvcfg_PMM v)))) : Bool)
            then (pure (_get_MEnvcfg_PMM v))
            else (pure (_get_MEnvcfg_PMM o))))
        (← do
          if ((← (currentlyEnabled Ext_Svadu)) : Bool)
          then (pure (_get_MEnvcfg_ADUE v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_Svpbmt)) : Bool)
        then (pure (_get_MEnvcfg_PBMTE v))
        else (pure 0#1))))

def legalize_mseccfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let sseed_read_only_zero ← do
    (pure ((false : Bool) || ((not (← (currentlyEnabled Ext_S))) || (not
            (← (currentlyEnabled Ext_Zkr))))))
  let useed_read_only_zero ← do
    (pure ((false : Bool) || ((not (← (currentlyEnabled Ext_U))) || (not
            (← (currentlyEnabled Ext_Zkr))))))
  let v := (Mk_Seccfg v)
  (pure (_update_Seccfg_USEED
      (_update_Seccfg_SSEED
        (_update_Seccfg_MLPE
          (_update_Seccfg_PMM o
            (← do
              if (((← (currentlyEnabled Ext_Smmpm)) && (is_supported_pmm PM_SMMPM
                     (pmm_mode_backwards (_get_Seccfg_PMM v)))) : Bool)
              then (pure (_get_Seccfg_PMM v))
              else (pure (_get_Seccfg_PMM o))))
          (if ((hartSupports Ext_Zicfilp) : Bool)
          then (_get_Seccfg_MLPE v)
          else 0#1))
        (if (sseed_read_only_zero : Bool)
        then 0#1
        else (_get_Seccfg_SSEED v)))
      (if (useed_read_only_zero : Bool)
      then 0#1
      else (_get_Seccfg_USEED v))))

def legalize_senvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_SEnvcfg v)
  (pure (_update_SEnvcfg_PMM
      (_update_SEnvcfg_CBIE
        (_update_SEnvcfg_CBCFE
          (_update_SEnvcfg_CBZE
            (_update_SEnvcfg_SSE
              (_update_SEnvcfg_LPE
                (_update_SEnvcfg_FIOM o
                  (if (sys_enable_writable_fiom : Bool)
                  then (_get_SEnvcfg_FIOM v)
                  else 0#1))
                (if ((hartSupports Ext_Zicfilp) : Bool)
                then (_get_SEnvcfg_LPE v)
                else 0#1))
              (if ((hartSupports Ext_Zicfiss) : Bool)
              then (_get_SEnvcfg_SSE v)
              else 0#1))
            (← do
              if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
              then (pure (_get_SEnvcfg_CBZE v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
            then (pure (_get_SEnvcfg_CBCFE v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
          then (legalize_xenvcfg_cbie (_get_SEnvcfg_CBIE v))
          else (pure 0b00#2)))
      (← do
        if (((← (currentlyEnabled Ext_Ssnpm)) && (is_supported_pmm PM_SSNPM
               (pmm_mode_backwards (_get_SEnvcfg_PMM v)))) : Bool)
        then (pure (_get_SEnvcfg_PMM v))
        else (pure (_get_SEnvcfg_PMM o)))))

def encdec_bop_forwards (arg_ : bop) : (BitVec 3) :=
  match arg_ with
  | .BEQ => 0b000#3
  | .BNE => 0b001#3
  | .BLT => 0b100#3
  | .BGE => 0b101#3
  | .BLTU => 0b110#3
  | .BGEU => 0b111#3

def encdec_iop_forwards (arg_ : iop) : (BitVec 3) :=
  match arg_ with
  | .ADDI => 0b000#3
  | .SLTI => 0b010#3
  | .SLTIU => 0b011#3
  | .ANDI => 0b111#3
  | .ORI => 0b110#3
  | .XORI => 0b100#3

def encdec_mul_op_forwards (arg_ : mul_op) : SailM (BitVec 3) := do
  match arg_ with
  | { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure 0b000#3)
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure 0b001#3)
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => (pure 0b010#3)
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => (pure 0b011#3)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_uop_forwards (arg_ : uop) : (BitVec 7) :=
  match arg_ with
  | .LUI => 0b0110111#7
  | .AUIPC => 0b0010111#7

/-- Type quantifiers: k_ex252079_ : Bool, width : Nat, width ∈ {1, 2, 4, 8} -/
def valid_load_encdec (width : Nat) (is_unsigned : Bool) : Bool :=
  ((width <b xlen_bytes) || ((not is_unsigned) && (width ≤b xlen_bytes)))

def virtual_memory_supported (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_Sv32)) || ((← (currentlyEnabled Ext_Sv39)) || ((← (currentlyEnabled
              Ext_Sv48)) || (← (currentlyEnabled Ext_Sv57))))))

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def width_enc_forwards (arg_ : Nat) : (BitVec 2) :=
  match arg_ with
  | 1 => 0b00#2
  | 2 => 0b01#2
  | 4 => 0b10#2
  | _ => 0b11#2

noncomputable def encdec_forwards (arg_ : instruction) : SailM (BitVec 32) := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure ((lpl : (BitVec 20)) +++ (0b00000#5 +++ 0b0010111#7)))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .UTYPE (imm, rd, op) =>
    (pure ((imm : (BitVec 20)) +++ ((encdec_reg_forwards rd) +++ (encdec_uop_forwards op))))
  | .JAL (v__10, rd) =>
    (do
      if (((Sail.BitVec.extractLsb v__10 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm := (Sail.BitVec.extractLsb v__10 20 1)
        let imm := (Sail.BitVec.extractLsb v__10 20 1)
        (pure ((Sail.BitVec.extractLsb imm 19 19) +++ ((Sail.BitVec.extractLsb imm 9 0) +++ ((Sail.BitVec.extractLsb
                  imm 10 10) +++ ((Sail.BitVec.extractLsb imm 18 11) +++ ((encdec_reg_forwards rd) +++ 0b1101111#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .JALR (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                rd) +++ 0b1100111#7)))))
  | .BTYPE (v__12, rs2, rs1, op) =>
    (do
      if (((Sail.BitVec.extractLsb v__12 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm := (Sail.BitVec.extractLsb v__12 12 1)
        let imm := (Sail.BitVec.extractLsb v__12 12 1)
        (pure ((Sail.BitVec.extractLsb imm 11 11) +++ ((Sail.BitVec.extractLsb imm 9 4) +++ ((encdec_reg_forwards
                  rs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_bop_forwards op) +++ ((Sail.BitVec.extractLsb
                        imm 3 0) +++ ((Sail.BitVec.extractLsb imm 10 10) +++ 0b1100011#7)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ ((encdec_iop_forwards op) +++ ((encdec_reg_forwards
                rd) +++ 0b0010011#7)))))
  | .SHIFTIOP (shamt, rs1, rd, .SLLI) =>
    (pure (0b000000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0010011#7))))))
  | .SHIFTIOP (shamt, rs1, rd, .SRLI) =>
    (pure (0b000000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0010011#7))))))
  | .SHIFTIOP (shamt, rs1, rd, .SRAI) =>
    (pure (0b010000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0010011#7))))))
  | .RTYPE (rs2, rs1, rd, .ADD) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLT) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLTU) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b011#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .AND) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .OR) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .XOR) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLL) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SRL) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SUB) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SRA) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (do
      if ((valid_load_encdec width is_unsigned) : Bool)
      then
        (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ ((bool_bit_forwards
                  is_unsigned) +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards rd) +++ 0b0000011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORE (imm, rs2, rs1, width) =>
    (pure ((Sail.BitVec.extractLsb imm 11 5) +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
              rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((Sail.BitVec.extractLsb imm 4 0) +++ 0b0100011#7)))))))
  | .ADDIW (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                rd) +++ 0b0011011#7)))))
  | .RTYPEW (rs2, rs1, rd, .ADDW) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SUBW) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SLLW) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SRLW) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SRAW) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .SHIFTIWOP (shamt, rs1, rd, .SLLIW) =>
    (pure (0b0000000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0011011#7))))))
  | .SHIFTIWOP (shamt, rs1, rd, .SRLIW) =>
    (pure (0b0000000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0011011#7))))))
  | .SHIFTIWOP (shamt, rs1, rd, .SRAIW) =>
    (pure (0b0100000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0011011#7))))))
  | .FENCE_TSO () =>
    (pure (0b1000#4 +++ (0b0011#4 +++ (0b0011#4 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b0001111#7)))))))
  | .FENCE (fm, pred, succ, rs, rd) =>
    (pure ((fm : (BitVec 4)) +++ ((pred : (BitVec 4)) +++ ((succ : (BitVec 4)) +++ ((encdec_reg_forwards
                rs) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0001111#7)))))))
  | .ECALL () =>
    (pure (0b000000000000#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .MRET () =>
    (pure (0b0011000#7 +++ (0b00010#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
  | .SRET () =>
    (pure (0b0001000#7 +++ (0b00010#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
  | .EBREAK () =>
    (pure (0b000000000001#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .WFI () =>
    (pure (0b000100000101#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then
        (pure (0b0001001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      if (((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ ((← (encdec_mul_op_forwards
                      mul_op)) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b10#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b11#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MULW (rs2, rs1, rd) =>
    (do
      if (((xlen == 64) && ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul)))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b10#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0111011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b11#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0111011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def instruction_to_str (insn : instruction) : SailM String := do
  if ((assembly_forwards_matches insn) : Bool)
  then (assembly_forwards insn)
  else (pure (HAppend.hAppend ".insn " (BitVec.toFormatted (← (encdec_forwards insn)))))

def interruptType_to_str (i : InterruptType) : String :=
  match i with
  | .I_Reserved_0 => "reserved-interrupt-0"
  | .I_S_Software => "supervisor-software-interrupt"
  | .I_VS_Software => "virtual-supervisor-software-interrupt"
  | .I_M_Software => "machine-software-interrupt"
  | .I_Reserved_4 => "reserved-interrupt-4"
  | .I_S_Timer => "supervisor-timer-interrupt"
  | .I_VS_Timer => "virtual-supervisor-timer-interrupt"
  | .I_M_Timer => "machine-timer-interrupt"
  | .I_Reserved_8 => "reserved-interrupt-8"
  | .I_S_External => "supervisor-external-interrupt"
  | .I_VS_External => "virtual-supervisor-external-interrupt"
  | .I_M_External => "machine-external-interrupt"
  | .I_SG_External => "supervisor guest-external-interrupt"
  | .I_COF => "counter-overflow interrupt"

def memory_region_type_str_backwards (arg_ : String) : SailM MemoryRegionType := do
  match arg_ with
  | "main memory" => (pure MainMemory)
  | "IO memory" => (pure IOMemory)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def memory_region_type_str_forwards (arg_ : MemoryRegionType) : String :=
  match arg_ with
  | .MainMemory => "main memory"
  | .IOMemory => "IO memory"

def optional_misaligned_exception_str (opt_e : (Option misaligned_exception)) : String :=
  match opt_e with
  | none => "NoFault"
  | .some e => (misaligned_exception_str_forwards e)

def pma_misaligned_to_str (m : PMAMisalignedExceptions) : String :=
  (HAppend.hAppend "misaligned-load-store:"
    (HAppend.hAppend (optional_misaligned_exception_str m.load_store)
      (HAppend.hAppend " misaligned-amo:"
        (HAppend.hAppend (misaligned_exception_str_forwards m.amo)
          (HAppend.hAppend " misaligned-vector:" (optional_misaligned_exception_str m.vector))))))

def reservability_str_forwards (arg_ : Reservability) : String :=
  match arg_ with
  | .RsrvNone => "RsrvNone"
  | .RsrvNonEventual => "RsrvNonEventual"
  | .RsrvEventual => "RsrvEventual"

def pma_attributes_to_str (attr : PMA) : String :=
  (HAppend.hAppend
    (match attr.mem_type with
    | .MainMemory => " main-memory"
    | .IOMemory => " io-memory")
    (HAppend.hAppend
      (if (attr.cacheable : Bool)
      then " cacheable"
      else "")
      (HAppend.hAppend
        (if (attr.coherent : Bool)
        then " coherent"
        else "")
        (HAppend.hAppend
          (if (attr.executable : Bool)
          then " executable"
          else "")
          (HAppend.hAppend
            (if (attr.readable : Bool)
            then " readable"
            else "")
            (HAppend.hAppend
              (if (attr.writable : Bool)
              then " writable"
              else "")
              (HAppend.hAppend
                (if (attr.read_idempotent : Bool)
                then " read-idempotent"
                else "")
                (HAppend.hAppend
                  (if (attr.write_idempotent : Bool)
                  then " write-idempotent"
                  else "")
                  (HAppend.hAppend " "
                    (HAppend.hAppend (pma_misaligned_to_str attr.misaligned_exceptions)
                      (HAppend.hAppend " "
                        (HAppend.hAppend (atomic_support_str_forwards attr.atomic_support)
                          (HAppend.hAppend " "
                            (HAppend.hAppend (reservability_str_forwards attr.reservability)
                              (HAppend.hAppend
                                (if (attr.supports_cbo_zero : Bool)
                                then " supports-cbo-zero"
                                else "")
                                (HAppend.hAppend
                                  (if (attr.supports_pte_read : Bool)
                                  then " supports-pte-read"
                                  else "")
                                  (HAppend.hAppend
                                    (if (attr.supports_pte_write : Bool)
                                    then " supports-pte-write"
                                    else "") " ")))))))))))))))))

def pma_region_to_str (region : PMA_Region) : String :=
  (HAppend.hAppend "base: "
    (HAppend.hAppend (BitVec.toFormatted region.base)
      (HAppend.hAppend " size: "
        (HAppend.hAppend (BitVec.toFormatted region.size) (pma_attributes_to_str region.attributes)))))

def privLevel_to_str (p : Privilege) : SailM String := do
  match p with
  | .User => (pure "U")
  | .VirtualUser => (pure "VU")
  | .Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure "HS")
      else (pure "S"))
  | .VirtualSupervisor => (pure "VS")
  | .Machine => (pure "M")

def ptw_error_to_str (e : PTW_Error) : String :=
  match e with
  | .PTW_Invalid_Addr () => "invalid-source-addr"
  | .PTW_No_Access () => "mem-access-error"
  | .PTW_Invalid_PTE () => "invalid-pte"
  | .PTW_No_Permission () => "no-permission"
  | .PTW_Misaligned () => "misaligned-superpage"
  | .PTW_PTE_Needs_Update () => "pte-update-needed"
  | .PTW_Ext_Error _ => "extension-error"

def reservability_str_backwards (arg_ : String) : SailM Reservability := do
  match arg_ with
  | "RsrvNone" => (pure RsrvNone)
  | "RsrvNonEventual" => (pure RsrvNonEventual)
  | "RsrvEventual" => (pure RsrvEventual)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def trapCause_to_str (t : TrapCause) : String :=
  match t with
  | .Interrupt i => (HAppend.hAppend "int#" (interruptType_to_str i))
  | .Exception e => (HAppend.hAppend "exc#" (exceptionType_to_str e))

def wait_name_backwards (arg_ : String) : SailM WaitReason := do
  match arg_ with
  | "WAIT-WFI" => (pure WAIT_WFI)
  | "WAIT-WRS-STO" => (pure WAIT_WRS_STO)
  | "WAIT-WRS-NTO" => (pure WAIT_WRS_NTO)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def wait_name_forwards (arg_ : WaitReason) : String :=
  match arg_ with
  | .WAIT_WFI => "WAIT-WFI"
  | .WAIT_WRS_STO => "WAIT-WRS-STO"
  | .WAIT_WRS_NTO => "WAIT-WRS-NTO"

def misaligned_exception_is_access_fault (e : (Option misaligned_exception)) : Bool :=
  match e with
  | .some .AccessFault => true
  | _ => false

def plat_misaligned_access : GlobalMisalignedExceptions :=
  { load_store := none
    vector := none
    lrsc := AccessFault
    amo := AccessFault }

def undefined_ExtContextPolicy (_ : Unit) : SailM ExtContextPolicy := do
  (internal_pick [ExtContext_Off, ExtContext_TwoState, ExtContext_FourState])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def ExtContextPolicy_of_num (arg_ : Nat) : ExtContextPolicy :=
  match arg_ with
  | 0 => ExtContext_Off
  | 1 => ExtContext_TwoState
  | _ => ExtContext_FourState

def num_of_ExtContextPolicy (arg_ : ExtContextPolicy) : Int :=
  match arg_ with
  | .ExtContext_Off => 0
  | .ExtContext_TwoState => 1
  | .ExtContext_FourState => 2

def plat_mstatus_legal_fs : ExtContextPolicy := ExtContext_FourState

def plat_mstatus_legal_vs : ExtContextPolicy := ExtContext_FourState

def plat_have_clint : Bool := true

def plat_clint_base : physaddrbits := unwrapValue ((to_bits_checked (l := 64) (33554432 : Int)))

def plat_clint_size : physaddrbits := unwrapValue ((to_bits_checked (l := 64) (786432 : Int)))

def plat_have_sig : Bool := true

def plat_sig_base : physaddrbits := unwrapValue ((to_bits_checked (l := 64) (201326592 : Int)))

def plat_sig_size : physaddrbits := (zero_extend (m := 64) 0x20#8)

def plat_insns_per_tick : nat1 := 2

def plat_wfi_available_to_usermode : Bool := false

def max_wait_time : Nat := 10

def illegal_instruction_writes_xtval : Bool := true

def virtual_instruction_writes_xtval : Bool := false

def software_breakpoint_writes_xtval : Bool := true

def hardware_breakpoint_writes_xtval : Bool := true

def misaligned_load_writes_xtval : Bool := true

def load_access_fault_writes_xtval : Bool := true

def load_page_fault_writes_xtval : Bool := true

def load_guest_page_fault_writes_xtval : Bool := false

def misaligned_samo_writes_xtval : Bool := true

def samo_access_fault_writes_xtval : Bool := true

def samo_page_fault_writes_xtval : Bool := true

def samo_guest_page_fault_writes_xtval : Bool := false

def misaligned_fetch_writes_xtval : Bool := true

def fetch_access_fault_writes_xtval : Bool := true

def fetch_page_fault_writes_xtval : Bool := true

def fetch_guest_page_fault_writes_xtval : Bool := false

def software_check_fault_writes_xtval : Bool := true

def reserved_exceptions_write_xtval : Bool := false

def undefined_AmocasOddRegisterReservedBehavior (_ : Unit) : SailM AmocasOddRegisterReservedBehavior := do
  (internal_pick [AMOCAS_Fatal, AMOCAS_Illegal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def AmocasOddRegisterReservedBehavior_of_num (arg_ : Nat) : AmocasOddRegisterReservedBehavior :=
  match arg_ with
  | 0 => AMOCAS_Fatal
  | _ => AMOCAS_Illegal

def num_of_AmocasOddRegisterReservedBehavior (arg_ : AmocasOddRegisterReservedBehavior) : Int :=
  match arg_ with
  | .AMOCAS_Fatal => 0
  | .AMOCAS_Illegal => 1

def undefined_FcsrRmReservedBehavior (_ : Unit) : SailM FcsrRmReservedBehavior := do
  (internal_pick [Fcsr_RM_Fatal, Fcsr_RM_Illegal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def FcsrRmReservedBehavior_of_num (arg_ : Nat) : FcsrRmReservedBehavior :=
  match arg_ with
  | 0 => Fcsr_RM_Fatal
  | _ => Fcsr_RM_Illegal

def num_of_FcsrRmReservedBehavior (arg_ : FcsrRmReservedBehavior) : Int :=
  match arg_ with
  | .Fcsr_RM_Fatal => 0
  | .Fcsr_RM_Illegal => 1

def undefined_PmpWriteOnlyReservedBehavior (_ : Unit) : SailM PmpWriteOnlyReservedBehavior := do
  (internal_pick [PMP_Fatal, PMP_ClearPermissions])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def PmpWriteOnlyReservedBehavior_of_num (arg_ : Nat) : PmpWriteOnlyReservedBehavior :=
  match arg_ with
  | 0 => PMP_Fatal
  | _ => PMP_ClearPermissions

def num_of_PmpWriteOnlyReservedBehavior (arg_ : PmpWriteOnlyReservedBehavior) : Int :=
  match arg_ with
  | .PMP_Fatal => 0
  | .PMP_ClearPermissions => 1

def undefined_XenvcfgCbieReservedBehavior (_ : Unit) : SailM XenvcfgCbieReservedBehavior := do
  (internal_pick [Xenvcfg_Fatal, Xenvcfg_ClearPermissions])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def XenvcfgCbieReservedBehavior_of_num (arg_ : Nat) : XenvcfgCbieReservedBehavior :=
  match arg_ with
  | 0 => Xenvcfg_Fatal
  | _ => Xenvcfg_ClearPermissions

def num_of_XenvcfgCbieReservedBehavior (arg_ : XenvcfgCbieReservedBehavior) : Int :=
  match arg_ with
  | .Xenvcfg_Fatal => 0
  | .Xenvcfg_ClearPermissions => 1

def undefined_XtvecModeReservedBehavior (_ : Unit) : SailM XtvecModeReservedBehavior := do
  (internal_pick [Xtvec_Fatal, Xtvec_Ignore])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def XtvecModeReservedBehavior_of_num (arg_ : Nat) : XtvecModeReservedBehavior :=
  match arg_ with
  | 0 => Xtvec_Fatal
  | _ => Xtvec_Ignore

def num_of_XtvecModeReservedBehavior (arg_ : XtvecModeReservedBehavior) : Int :=
  match arg_ with
  | .Xtvec_Fatal => 0
  | .Xtvec_Ignore => 1

def undefined_RV32ZdinxOddRegisterReservedBehavior (_ : Unit) : SailM RV32ZdinxOddRegisterReservedBehavior := do
  (internal_pick [Zdinx_Fatal, Zdinx_Illegal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def RV32ZdinxOddRegisterReservedBehavior_of_num (arg_ : Nat) : RV32ZdinxOddRegisterReservedBehavior :=
  match arg_ with
  | 0 => Zdinx_Fatal
  | _ => Zdinx_Illegal

def num_of_RV32ZdinxOddRegisterReservedBehavior (arg_ : RV32ZdinxOddRegisterReservedBehavior) : Int :=
  match arg_ with
  | .Zdinx_Fatal => 0
  | .Zdinx_Illegal => 1

def undefined_IllegalVtypeReservedBehavior (_ : Unit) : SailM IllegalVtypeReservedBehavior := do
  (internal_pick [IllegalVtype_SetVill, IllegalVtype_Illegal, IllegalVtype_Fatal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def IllegalVtypeReservedBehavior_of_num (arg_ : Nat) : IllegalVtypeReservedBehavior :=
  match arg_ with
  | 0 => IllegalVtype_SetVill
  | 1 => IllegalVtype_Illegal
  | _ => IllegalVtype_Fatal

def num_of_IllegalVtypeReservedBehavior (arg_ : IllegalVtypeReservedBehavior) : Int :=
  match arg_ with
  | .IllegalVtype_SetVill => 0
  | .IllegalVtype_Illegal => 1
  | .IllegalVtype_Fatal => 2

def undefined_OOBVstartReservedBehavior (_ : Unit) : SailM OOBVstartReservedBehavior := do
  (internal_pick [Vstart_Illegal, Vstart_Ignore])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def OOBVstartReservedBehavior_of_num (arg_ : Nat) : OOBVstartReservedBehavior :=
  match arg_ with
  | 0 => Vstart_Illegal
  | _ => Vstart_Ignore

def num_of_OOBVstartReservedBehavior (arg_ : OOBVstartReservedBehavior) : Int :=
  match arg_ with
  | .Vstart_Illegal => 0
  | .Vstart_Ignore => 1

def amocas_odd_register_reserved_behavior : AmocasOddRegisterReservedBehavior := AMOCAS_Illegal

def fcsr_rm_reserved_behavior : FcsrRmReservedBehavior := Fcsr_RM_Illegal

def pmp_write_only_reserved_behavior : PmpWriteOnlyReservedBehavior := PMP_ClearPermissions

def xtvec_mode_reserved_behavior : XtvecModeReservedBehavior := Xtvec_Ignore

def rv32zdinx_odd_register_reserved_behavior : RV32ZdinxOddRegisterReservedBehavior := Zdinx_Illegal

def illegal_vtype_reserved_behavior : IllegalVtypeReservedBehavior := IllegalVtype_SetVill

def vstart_reserved_behavior : OOBVstartReservedBehavior := Vstart_Illegal

