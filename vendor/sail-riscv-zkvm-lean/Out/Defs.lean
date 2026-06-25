import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

abbrev bit := (BitVec 1)

inductive IsaVersion where | Isa_20191213 | Isa_Draft_20211102 | Isa_20211203 | Isa_20240411 | Isa_Latest
  deriving BEq, Inhabited, Repr
  open IsaVersion

inductive AtomicSupport where | AMONone | AMOSwap | AMOLogical | AMOArithmetic | AMOCASW | AMOCASD | AMOCASQ
  deriving BEq, Inhabited, Repr
  open AtomicSupport

inductive vector_support where | Disabled | Integer | Float_single | Float_double | Full
  deriving BEq, Inhabited, Repr
  open vector_support

abbrev bits k_n := (BitVec k_n)

inductive regidx where
  | Regidx (_ : (BitVec (if ( false  : Bool) then 4 else 5)))
  deriving Inhabited, BEq, Repr
  open regidx

abbrev base_E_enabled : Bool := false

abbrev regidx_bit_width : Int := (if ( base_E_enabled  : Bool) then 4 else 5)

inductive vregidx where
  | Vregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr
  open vregidx

abbrev xlenbits := (BitVec 64)

inductive virtaddr where
  | Virtaddr (_ : xlenbits)
  deriving Inhabited, BEq, Repr
  open virtaddr

abbrev fp_exception_flags := (BitVec 5)

abbrev fp_rounding_modes := (BitVec 5)



-- Abbreviation fp_bits skipped

/-- Type quantifiers: k_n : Int -/
structure float_bits (k_n : Int) where
  sign : (BitVec 1)
  exp :
  (BitVec (if ( k_n = 16  : Bool) then 5 else (if ( k_n = 32  : Bool) then 8 else (if ( k_n = 64  : Bool) then 11 else 15))))
  mantissa :
  (BitVec (if ( k_n = 16  : Bool) then 10 else (if ( k_n = 32  : Bool) then 23 else (if ( k_n = 64  : Bool) then 52 else 112))))
  deriving BEq, Inhabited, Repr

inductive float_class where | float_class_negative_inf | float_class_negative_normal | float_class_negative_subnormal | float_class_negative_zero | float_class_positive_zero | float_class_positive_subnormal | float_class_positive_normal | float_class_positive_inf | float_class_snan | float_class_qnan
  deriving BEq, Inhabited, Repr
  open float_class

abbrev nat1 := Int

inductive Signedness where | Signed | Unsigned
  deriving BEq, Inhabited, Repr
  open Signedness

inductive VectorHalf where | High | Low
  deriving BEq, Inhabited, Repr
  open VectorHalf

abbrev max_mem_access : Int := 4096

abbrev mem_access_width := Nat

inductive exception where
  | Error_not_implemented (_ : String)
  | Error_internal_error (_ : String)
  | Error_reserved_behavior (_ : String)
  deriving Inhabited, BEq, Repr
  open exception

inductive amoop where | AMOSWAP | AMOAND | AMOOR | AMOXOR | AMOADD | AMOMIN | AMOMAX | AMOMINU | AMOMAXU | AMOCAS
  deriving BEq, Inhabited, Repr
  open amoop

inductive cbop_zicbom where | CBO_CLEAN | CBO_FLUSH | CBO_INVAL
  deriving BEq, Inhabited, Repr
  open cbop_zicbom

inductive cbop_zicbop where | PREFETCH_I | PREFETCH_R | PREFETCH_W
  deriving BEq, Inhabited, Repr
  open cbop_zicbop

abbrev pm_len := Int

inductive PM_Ext where | PM_SSNPM | PM_SMNPM | PM_SMMPM
  deriving BEq, Inhabited, Repr
  open PM_Ext

inductive PointerMaskingMode where | PMM_Disabled | PMM_Reserved | PMM_PMLEN_7 | PMM_PMLEN_16
  deriving BEq, Inhabited, Repr
  open PointerMaskingMode

abbrev xlen : Int := 64

abbrev log2_xlen : Int := (if ( xlen = 32  : Bool) then 5 else 6)

abbrev xlen_bytes : Int := (if ( xlen = 32  : Bool) then 4 else 8)

abbrev physaddrbits_len : Int := (if ( xlen = 32  : Bool) then 34 else 64)

abbrev asidlen : Int := (if ( xlen = 32  : Bool) then 9 else 16)

abbrev asidbits := (BitVec (if ( 64 = 32  : Bool) then 9 else 16))

abbrev ext_d_supported : Bool := true

abbrev flen_bytes : Int := (if ( ext_d_supported  : Bool) then 8 else 4)

abbrev flen : Int := (if ( true  : Bool) then 8 else 4 * 8)

abbrev flenbits := (BitVec (if ( true  : Bool) then 8 else 4 * 8))

abbrev vlen_exp : Int := 8

abbrev elen_exp : Int := 6

abbrev vlen : Int := (2 ^ 8)

abbrev elen : Int := (2 ^ 6)

abbrev physaddrbits := (BitVec (if ( 64 = 32  : Bool) then 34 else 64))

inductive physaddr where
  | Physaddr (_ : physaddrbits)
  deriving Inhabited, BEq, Repr
  open physaddr

abbrev mem_meta := Unit

inductive write_kind where | Write_plain | Write_RISCV_release | Write_RISCV_strong_release | Write_RISCV_conditional | Write_RISCV_conditional_release | Write_RISCV_conditional_strong_release
  deriving BEq, Inhabited, Repr
  open write_kind

inductive read_kind where | Read_plain | Read_ifetch | Read_RISCV_acquire | Read_RISCV_strong_acquire | Read_RISCV_reserved | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire
  deriving BEq, Inhabited, Repr
  open read_kind

inductive barrier_kind where | Barrier_RISCV_rw_rw | Barrier_RISCV_r_rw | Barrier_RISCV_r_r | Barrier_RISCV_rw_w | Barrier_RISCV_w_w | Barrier_RISCV_w_rw | Barrier_RISCV_rw_r | Barrier_RISCV_r_w | Barrier_RISCV_w_r | Barrier_RISCV_tso | Barrier_RISCV_i
  deriving BEq, Inhabited, Repr
  open barrier_kind

structure RISCV_strong_access where
  variety : Access_variety
  deriving BEq, Inhabited, Repr

abbrev RVFI_DII_Instruction_Packet := (BitVec 64)

abbrev RVFI_DII_Execution_Packet_InstMetaData := (BitVec 192)

abbrev RVFI_DII_Execution_Packet_PC := (BitVec 128)

abbrev RVFI_DII_Execution_Packet_Ext_Integer := (BitVec 320)

abbrev RVFI_DII_Execution_Packet_Ext_MemAccess := (BitVec 704)

abbrev RVFI_DII_Execution_Packet_V1 := (BitVec 704)

abbrev RVFI_DII_Execution_PacketV2 := (BitVec 512)

abbrev tvec_alignment := Nat

inductive misaligned_exception where | AccessFault | AlignmentException
  deriving BEq, Inhabited, Repr
  open misaligned_exception

inductive mem_payload where | Data | Vector | PageTableEntry | ShadowStack
  deriving BEq, Inhabited, Repr
  open mem_payload

inductive cacheop where
  | CB_manage (_ : cbop_zicbom)
  | CB_zero (_ : Unit)
  | CB_prefetch (_ : cbop_zicbop)
  deriving Inhabited, BEq, Repr
  open cacheop

/-- Type quantifiers: k_a : Type -/
inductive MemoryAccessType (k_a : Type) where
  | Load (_ : k_a)
  | Store (_ : k_a)
  | LoadReserved (_ : (Bool × Bool × k_a))
  | StoreConditional (_ : (Bool × Bool × k_a))
  | Atomic (_ : (amoop × Bool × Bool × k_a × k_a))
  | InstructionFetch (_ : Unit)
  | CacheAccess (_ : cacheop)
  deriving Inhabited, BEq, Repr
  open MemoryAccessType

abbrev csreg := (BitVec 12)

abbrev ext_exc_type := Unit

inductive breakpoint_cause where | Brk_Software | Brk_Hardware
  deriving BEq, Inhabited, Repr
  open breakpoint_cause

inductive ExceptionType where
  | E_Fetch_Addr_Align (_ : Unit)
  | E_Fetch_Access_Fault (_ : Unit)
  | E_Illegal_Instr (_ : Unit)
  | E_Breakpoint (_ : breakpoint_cause)
  | E_Load_Addr_Align (_ : Unit)
  | E_Load_Access_Fault (_ : Unit)
  | E_SAMO_Addr_Align (_ : Unit)
  | E_SAMO_Access_Fault (_ : Unit)
  | E_U_EnvCall (_ : Unit)
  | E_S_EnvCall (_ : Unit)
  | E_VS_EnvCall (_ : Unit)
  | E_M_EnvCall (_ : Unit)
  | E_Fetch_Page_Fault (_ : Unit)
  | E_Load_Page_Fault (_ : Unit)
  | E_Reserved_14 (_ : Unit)
  | E_SAMO_Page_Fault (_ : Unit)
  | E_Reserved_16 (_ : Unit)
  | E_Reserved_17 (_ : Unit)
  | E_Software_Check (_ : Unit)
  | E_Reserved_19 (_ : Unit)
  | E_Fetch_GPage_Fault (_ : Unit)
  | E_Load_GPage_Fault (_ : Unit)
  | E_Virtual_Instr (_ : Unit)
  | E_SAMO_GPage_Fault (_ : Unit)
  | E_Extension (_ : ext_exc_type)
  deriving Inhabited, BEq, Repr
  open ExceptionType

inductive bop where | BEQ | BNE | BLT | BGE | BLTU | BGEU
  deriving BEq, Inhabited, Repr
  open bop

inductive iop where | ADDI | SLTI | SLTIU | XORI | ORI | ANDI
  deriving BEq, Inhabited, Repr
  open iop

structure mul_op where
  result_part : VectorHalf
  signed_rs1 : Signedness
  signed_rs2 : Signedness
  deriving BEq, Inhabited, Repr

inductive rop where | ADD | SUB | SLL | SLT | SLTU | XOR | SRL | SRA | OR | AND
  deriving BEq, Inhabited, Repr
  open rop

inductive ropw where | ADDW | SUBW | SLLW | SRLW | SRAW
  deriving BEq, Inhabited, Repr
  open ropw

inductive sop where | SLLI | SRLI | SRAI
  deriving BEq, Inhabited, Repr
  open sop

inductive sopw where | SLLIW | SRLIW | SRAIW
  deriving BEq, Inhabited, Repr
  open sopw

inductive uop where | LUI | AUIPC
  deriving BEq, Inhabited, Repr
  open uop

abbrev half := (BitVec 16)

abbrev landing_pad_label := (BitVec 20)

abbrev word := (BitVec 32)

abbrev word_width := Int

inductive instruction where
  | ILLEGAL (_ : word)
  | C_ILLEGAL (_ : half)
  | LPAD (_ : landing_pad_label)
  | UTYPE (_ : ((BitVec 20) × regidx × uop))
  | JAL (_ : ((BitVec 21) × regidx))
  | JALR (_ : ((BitVec 12) × regidx × regidx))
  | BTYPE (_ : ((BitVec 13) × regidx × regidx × bop))
  | ITYPE (_ : ((BitVec 12) × regidx × regidx × iop))
  | SHIFTIOP (_ : ((BitVec 6) × regidx × regidx × sop))
  | RTYPE (_ : (regidx × regidx × regidx × rop))
  | LOAD (_ : ((BitVec 12) × regidx × regidx × Bool × word_width))
  | STORE (_ : ((BitVec 12) × regidx × regidx × word_width))
  | ADDIW (_ : ((BitVec 12) × regidx × regidx))
  | RTYPEW (_ : (regidx × regidx × regidx × ropw))
  | SHIFTIWOP (_ : ((BitVec 5) × regidx × regidx × sopw))
  | FENCE_TSO (_ : Unit)
  | FENCE (_ : ((BitVec 4) × (BitVec 4) × (BitVec 4) × regidx × regidx))
  | ECALL (_ : Unit)
  | MRET (_ : Unit)
  | SRET (_ : Unit)
  | EBREAK (_ : Unit)
  | WFI (_ : Unit)
  | SFENCE_VMA (_ : (regidx × regidx))
  | MUL (_ : (regidx × regidx × regidx × mul_op))
  | DIV (_ : (regidx × regidx × regidx × Bool))
  | REM (_ : (regidx × regidx × regidx × Bool))
  | MULW (_ : (regidx × regidx × regidx))
  | DIVW (_ : (regidx × regidx × regidx × Bool))
  | REMW (_ : (regidx × regidx × regidx × Bool))
  deriving Inhabited, Repr
  open instruction

inductive Privilege where | User | VirtualUser | Supervisor | VirtualSupervisor | Machine
  deriving BEq, Inhabited, Repr
  open Privilege

inductive Architecture where | RV32 | RV64 | RV128
  deriving BEq, Inhabited, Repr
  open Architecture

abbrev Misa := (BitVec 64)

inductive extension where | Ext_M | Ext_A | Ext_F | Ext_D | Ext_B | Ext_V | Ext_S | Ext_U | Ext_H | Ext_Zibi | Ext_Zic64b | Ext_Zicbom | Ext_Zicbop | Ext_Zicboz | Ext_Zicfilp | Ext_Zicfiss | Ext_Zicntr | Ext_Zicond | Ext_Zicsr | Ext_Zifencei | Ext_Zihintntl | Ext_Zihintpause | Ext_Zihpm | Ext_Zimop | Ext_Zmmul | Ext_Zaamo | Ext_Zabha | Ext_Zacas | Ext_Zalrsc | Ext_Zawrs | Ext_Za64rs | Ext_Za128rs | Ext_Zfa | Ext_Zfbfmin | Ext_Zfh | Ext_Zfhmin | Ext_Zfinx | Ext_Zdinx | Ext_Zca | Ext_Zcb | Ext_Zcd | Ext_Zcf | Ext_Zcmop | Ext_C | Ext_Zba | Ext_Zbb | Ext_Zbc | Ext_Zbkb | Ext_Zbkc | Ext_Zbkx | Ext_Zbs | Ext_Ziccamoa | Ext_Ziccamoc | Ext_Ziccif | Ext_Zicclsm | Ext_Ziccrse | Ext_Zknd | Ext_Zkne | Ext_Zknh | Ext_Zkr | Ext_Zksed | Ext_Zksh | Ext_Zkt | Ext_Zhinx | Ext_Zhinxmin | Ext_Zvl32b | Ext_Zvl64b | Ext_Zvl128b | Ext_Zvl256b | Ext_Zvl512b | Ext_Zvl1024b | Ext_Zve32f | Ext_Zve32x | Ext_Zve64d | Ext_Zve64f | Ext_Zve64x | Ext_Zvabd | Ext_Zvfbfmin | Ext_Zvfbfwma | Ext_Zvfh | Ext_Zvfhmin | Ext_Zvbb | Ext_Zvbc | Ext_Zvkb | Ext_Zvkg | Ext_Zvkned | Ext_Zvknha | Ext_Zvknhb | Ext_Zvksed | Ext_Zvksh | Ext_Zvkt | Ext_Zvkn | Ext_Zvknc | Ext_Zvkng | Ext_Zvks | Ext_Zvksc | Ext_Zvksg | Ext_Ssccptr | Ext_Sscofpmf | Ext_Sscounterenw | Ext_Ssnpm | Ext_Ssstateen | Ext_Sstc | Ext_Sstvala | Ext_Sstvecd | Ext_Ssu64xl | Ext_Svbare | Ext_Sv32 | Ext_Sv39 | Ext_Sv48 | Ext_Sv57 | Ext_Svade | Ext_Svadu | Ext_Svinval | Ext_Svnapot | Ext_Svpbmt | Ext_Svrsw60t59b | Ext_Svvptc | Ext_Smcntrpmf | Ext_Smmpm | Ext_Smnpm | Ext_Smstateen | Ext_Ssqosid | Ext_Sspm | Ext_Supm
  deriving BEq, Inhabited, Repr
  open extension

abbrev Mstatus := (BitVec 64)

inductive XenvcfgCbieReservedBehavior where | Xenvcfg_Fatal | Xenvcfg_ClearPermissions
  deriving BEq, Inhabited, Repr
  open XenvcfgCbieReservedBehavior

abbrev MEnvcfg := (BitVec 64)

abbrev Seccfg := (BitVec 64)

abbrev SEnvcfg := (BitVec 64)

abbrev Hstateen0 := (BitVec 64)

abbrev Hstateen1 := (BitVec 64)

abbrev Hstateen2 := (BitVec 64)

abbrev Hstateen3 := (BitVec 64)

abbrev Mstateen0 := (BitVec 64)

abbrev Mstateen1 := (BitVec 64)

abbrev Mstateen2 := (BitVec 64)

abbrev Mstateen3 := (BitVec 64)

abbrev Sstateen0 := (BitVec 32)

abbrev Sstateen1 := (BitVec 32)

abbrev Sstateen2 := (BitVec 32)

abbrev Sstateen3 := (BitVec 32)

inductive stateen_bit where | STATEEN_FCSR | STATEEN_SRMCFG | STATEEN_ENVCFG | STATEEN_SE
  deriving BEq, Inhabited, Repr
  open stateen_bit

inductive InterruptType where | I_Reserved_0 | I_S_Software | I_VS_Software | I_M_Software | I_Reserved_4 | I_S_Timer | I_VS_Timer | I_M_Timer | I_Reserved_8 | I_S_External | I_VS_External | I_M_External | I_SG_External | I_COF
  deriving BEq, Inhabited, Repr
  open InterruptType

inductive MemoryRegionType where | MainMemory | IOMemory
  deriving BEq, Inhabited, Repr
  open MemoryRegionType

structure PMAMisalignedExceptions where
  load_store : (Option misaligned_exception)
  vector : (Option misaligned_exception)
  amo : misaligned_exception
  deriving BEq, Inhabited, Repr

inductive Reservability where | RsrvNone | RsrvNonEventual | RsrvEventual
  deriving BEq, Inhabited, Repr
  open Reservability

structure PMA where
  mem_type : MemoryRegionType
  cacheable : Bool
  coherent : Bool
  executable : Bool
  readable : Bool
  writable : Bool
  read_idempotent : Bool
  write_idempotent : Bool
  misaligned_exceptions : PMAMisalignedExceptions
  atomic_support : AtomicSupport
  reservability : Reservability
  supports_cbo_zero : Bool
  supports_pte_read : Bool
  supports_pte_write : Bool
  deriving BEq, Inhabited, Repr

structure PMA_Region where
  base : (BitVec 64)
  size : (BitVec 64)
  attributes : PMA
  include_in_device_tree : Bool
  deriving BEq, Inhabited, Repr

abbrev ext_ptw_error := Unit

inductive PTW_Error where
  | PTW_Invalid_Addr (_ : Unit)
  | PTW_No_Access (_ : Unit)
  | PTW_Invalid_PTE (_ : Unit)
  | PTW_No_Permission (_ : Unit)
  | PTW_Misaligned (_ : Unit)
  | PTW_PTE_Needs_Update (_ : Unit)
  | PTW_Ext_Error (_ : ext_ptw_error)
  deriving Inhabited, BEq, Repr
  open PTW_Error

inductive TrapCause where
  | Interrupt (_ : InterruptType)
  | Exception (_ : ExceptionType)
  deriving Inhabited, BEq, Repr
  open TrapCause

inductive WaitReason where | WAIT_WFI | WAIT_WRS_STO | WAIT_WRS_NTO
  deriving BEq, Inhabited, Repr
  open WaitReason

structure GlobalMisalignedExceptions where
  load_store : (Option misaligned_exception)
  vector : (Option misaligned_exception)
  lrsc : misaligned_exception
  amo : misaligned_exception
  deriving BEq, Inhabited, Repr

inductive ExtContextPolicy where | ExtContext_Off | ExtContext_TwoState | ExtContext_FourState
  deriving BEq, Inhabited, Repr
  open ExtContextPolicy

inductive AmocasOddRegisterReservedBehavior where | AMOCAS_Fatal | AMOCAS_Illegal
  deriving BEq, Inhabited, Repr
  open AmocasOddRegisterReservedBehavior

inductive FcsrRmReservedBehavior where | Fcsr_RM_Fatal | Fcsr_RM_Illegal
  deriving BEq, Inhabited, Repr
  open FcsrRmReservedBehavior

inductive PmpWriteOnlyReservedBehavior where | PMP_Fatal | PMP_ClearPermissions
  deriving BEq, Inhabited, Repr
  open PmpWriteOnlyReservedBehavior

inductive XtvecModeReservedBehavior where | Xtvec_Fatal | Xtvec_Ignore
  deriving BEq, Inhabited, Repr
  open XtvecModeReservedBehavior

inductive RV32ZdinxOddRegisterReservedBehavior where | Zdinx_Fatal | Zdinx_Illegal
  deriving BEq, Inhabited, Repr
  open RV32ZdinxOddRegisterReservedBehavior

inductive IllegalVtypeReservedBehavior where | IllegalVtype_SetVill | IllegalVtype_Illegal | IllegalVtype_Fatal
  deriving BEq, Inhabited, Repr
  open IllegalVtypeReservedBehavior

inductive OOBVstartReservedBehavior where | Vstart_Illegal | Vstart_Ignore
  deriving BEq, Inhabited, Repr
  open OOBVstartReservedBehavior

abbrev exc_code := (BitVec 6)

abbrev ext_ptw := Unit

abbrev ext_ptw_fail := Unit

abbrev instbits := (BitVec 32)

abbrev pagesize_bits : Int := 12

inductive cregidx where
  | Cregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr
  open cregidx

inductive regno where
  | Regno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open regno

abbrev arch_xlen := (BitVec 2)

abbrev nom_priv_bits := (BitVec 2)

abbrev virt_mode_bit := (BitVec 1)

inductive CSRAccessType where | CSRRead | CSRWrite | CSRReadWrite
  deriving BEq, Inhabited, Repr
  open CSRAccessType



inductive SWCheckCodes where | LANDING_PAD_FAULT
  deriving BEq, Inhabited, Repr
  open SWCheckCodes

abbrev tv_mode := (BitVec 2)

inductive TrapVectorMode where | TV_Direct | TV_Vector | TV_Reserved
  deriving BEq, Inhabited, Repr
  open TrapVectorMode

inductive xRET_type where | mRET | sRET
  deriving BEq, Inhabited, Repr
  open xRET_type

abbrev ext_status := (BitVec 2)

inductive ExtStatus where | Off | Initial | Clean | Dirty
  deriving BEq, Inhabited, Repr
  open ExtStatus

abbrev satp_mode := (BitVec 4)

inductive SATPMode where | Bare | Sv32 | Sv39 | Sv48 | Sv57
  deriving BEq, Inhabited, Repr
  open SATPMode

abbrev csrRW := (BitVec 2)

abbrev word_width_wide := Int



abbrev level_range (k_v : Nat) := Nat

abbrev pte_bits k_v := (BitVec (if ( k_v = 32  : Bool) then 32 else 64))

abbrev ppn_bits k_v := (BitVec (if ( k_v = 32  : Bool) then 22 else 44))

abbrev vpn_bits k_v := (BitVec (k_v - 12))

inductive page_based_mem_type where | PBMT_PMA | PBMT_NC | PBMT_IO
  deriving BEq, Inhabited, Repr
  open page_based_mem_type

abbrev regtype := xlenbits

abbrev Mtvec := (BitVec 64)

abbrev Mcause := (BitVec 64)

abbrev Counteren := (BitVec 32)

abbrev Counterin := (BitVec 32)

abbrev Sstatus := (BitVec 64)

abbrev Satp64 := (BitVec 64)

abbrev Satp32 := (BitVec 32)

inductive FeatureEnabledResult where | FEATURE_ENABLED | FEATURE_ILLEGAL | FEATURE_VIRTUAL
  deriving BEq, Inhabited, Repr
  open FeatureEnabledResult

abbrev Minterrupts := (BitVec 64)

abbrev Medeleg := (BitVec 64)

inductive XipReadType where | IncludePlatformInterrupts | ExcludePlatformInterrupts
  deriving BEq, Inhabited, Repr
  open XipReadType

abbrev Sinterrupts := (BitVec 64)

/-- Type quantifiers: k_a : Type -/
inductive Ext_DataAddr_Check (k_a : Type) where
  | Ext_DataAddr_OK (_ : virtaddr)
  | Ext_DataAddr_Error (_ : k_a)
  deriving Inhabited, BEq, Repr
  open Ext_DataAddr_Check

abbrev ext_fetch_addr_error := Unit

abbrev ext_control_addr_error := Unit

abbrev ext_data_addr_error := Unit

abbrev bits_rm := (BitVec 3)

abbrev bits_fflags := (BitVec 5)

abbrev bits_BF16 := (BitVec 16)

abbrev bits_H := (BitVec 16)

abbrev bits_S := (BitVec 32)

abbrev bits_D := (BitVec 64)

abbrev bits_W := (BitVec 32)

abbrev bits_WU := (BitVec 32)

abbrev bits_L := (BitVec 64)

abbrev bits_LU := (BitVec 64)

abbrev ext_exception := Unit

structure sync_exception where
  trap : ExceptionType
  excinfo : (Option xlenbits)
  ext : (Option ext_exception)
  deriving BEq, Inhabited, Repr

inductive PmpAddrMatchType where | OFF | TOR | NA4 | NAPOT
  deriving BEq, Inhabited, Repr
  open PmpAddrMatchType

abbrev Pmpcfg_ent := (BitVec 8)

inductive pmpAddrMatch where | PMP_NoMatch | PMP_PartialMatch | PMP_Match
  deriving BEq, Inhabited, Repr
  open pmpAddrMatch

abbrev fregtype := flenbits

inductive f_madd_op_H where | FMADD_H | FMSUB_H | FNMSUB_H | FNMADD_H
  deriving BEq, Inhabited, Repr
  open f_madd_op_H

inductive f_bin_rm_op_H where | FADD_H | FSUB_H | FMUL_H | FDIV_H
  deriving BEq, Inhabited, Repr
  open f_bin_rm_op_H

inductive f_un_rm_ff_op_H where | FSQRT_H | FCVT_H_S | FCVT_H_D | FCVT_S_H | FCVT_D_H
  deriving BEq, Inhabited, Repr
  open f_un_rm_ff_op_H

inductive f_un_rm_fx_op_H where | FCVT_W_H | FCVT_WU_H | FCVT_L_H | FCVT_LU_H
  deriving BEq, Inhabited, Repr
  open f_un_rm_fx_op_H

inductive f_un_rm_xf_op_H where | FCVT_H_W | FCVT_H_WU | FCVT_H_L | FCVT_H_LU
  deriving BEq, Inhabited, Repr
  open f_un_rm_xf_op_H

inductive f_un_x_op_H where | FCLASS_H | FMV_X_H
  deriving BEq, Inhabited, Repr
  open f_un_x_op_H

inductive f_un_f_op_H where | FMV_H_X
  deriving BEq, Inhabited, Repr
  open f_un_f_op_H

inductive f_bin_f_op_H where | FSGNJ_H | FSGNJN_H | FSGNJX_H | FMIN_H | FMAX_H
  deriving BEq, Inhabited, Repr
  open f_bin_f_op_H

inductive f_bin_x_op_H where | FEQ_H | FLT_H | FLE_H
  deriving BEq, Inhabited, Repr
  open f_bin_x_op_H

inductive rounding_mode where | RM_RNE | RM_RTZ | RM_RDN | RM_RUP | RM_RMM | RM_DYN
  deriving BEq, Inhabited, Repr
  open rounding_mode

inductive f_madd_op_S where | FMADD_S | FMSUB_S | FNMSUB_S | FNMADD_S
  deriving BEq, Inhabited, Repr
  open f_madd_op_S

inductive f_bin_rm_op_S where | FADD_S | FSUB_S | FMUL_S | FDIV_S
  deriving BEq, Inhabited, Repr
  open f_bin_rm_op_S

inductive f_un_rm_ff_op_S where | FSQRT_S
  deriving BEq, Inhabited, Repr
  open f_un_rm_ff_op_S

inductive f_un_rm_fx_op_S where | FCVT_W_S | FCVT_WU_S | FCVT_L_S | FCVT_LU_S
  deriving BEq, Inhabited, Repr
  open f_un_rm_fx_op_S

inductive f_un_rm_xf_op_S where | FCVT_S_W | FCVT_S_WU | FCVT_S_L | FCVT_S_LU
  deriving BEq, Inhabited, Repr
  open f_un_rm_xf_op_S

inductive f_un_op_f_S where | FMV_W_X
  deriving BEq, Inhabited, Repr
  open f_un_op_f_S

inductive f_un_op_x_S where | FCLASS_S | FMV_X_W
  deriving BEq, Inhabited, Repr
  open f_un_op_x_S

inductive f_bin_op_f_S where | FSGNJ_S | FSGNJN_S | FSGNJX_S | FMIN_S | FMAX_S
  deriving BEq, Inhabited, Repr
  open f_bin_op_f_S

inductive f_bin_op_x_S where | FEQ_S | FLT_S | FLE_S
  deriving BEq, Inhabited, Repr
  open f_bin_op_x_S

inductive f_madd_op_D where | FMADD_D | FMSUB_D | FNMSUB_D | FNMADD_D
  deriving BEq, Inhabited, Repr
  open f_madd_op_D

inductive f_bin_rm_op_D where | FADD_D | FSUB_D | FMUL_D | FDIV_D
  deriving BEq, Inhabited, Repr
  open f_bin_rm_op_D

inductive f_un_rm_ff_op_D where | FSQRT_D | FCVT_S_D | FCVT_D_S
  deriving BEq, Inhabited, Repr
  open f_un_rm_ff_op_D

inductive f_un_rm_fx_op_D where | FCVT_W_D | FCVT_WU_D | FCVT_L_D | FCVT_LU_D
  deriving BEq, Inhabited, Repr
  open f_un_rm_fx_op_D

inductive f_un_rm_xf_op_D where | FCVT_D_W | FCVT_D_WU | FCVT_D_L | FCVT_D_LU
  deriving BEq, Inhabited, Repr
  open f_un_rm_xf_op_D

inductive f_bin_f_op_D where | FSGNJ_D | FSGNJN_D | FSGNJX_D | FMIN_D | FMAX_D
  deriving BEq, Inhabited, Repr
  open f_bin_f_op_D

inductive f_bin_x_op_D where | FEQ_D | FLT_D | FLE_D
  deriving BEq, Inhabited, Repr
  open f_bin_x_op_D

inductive f_un_x_op_D where | FCLASS_D | FMV_X_D
  deriving BEq, Inhabited, Repr
  open f_un_x_op_D

inductive f_un_f_op_D where | FMV_D_X
  deriving BEq, Inhabited, Repr
  open f_un_f_op_D

inductive fregidx where
  | Fregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr
  open fregidx

inductive fregno where
  | Fregno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open fregno

inductive cfregidx where
  | Cfregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr
  open cfregidx

abbrev Fcsr := (BitVec 32)

abbrev vlenbits := (BitVec (2 ^ 8))

inductive vvfunct6 where | VV_VADD | VV_VSUB | VV_VMINU | VV_VMIN | VV_VMAXU | VV_VMAX | VV_VAND | VV_VOR | VV_VXOR | VV_VRGATHER | VV_VRGATHEREI16 | VV_VSADDU | VV_VSADD | VV_VSSUBU | VV_VSSUB | VV_VSLL | VV_VSMUL | VV_VSRL | VV_VSRA | VV_VSSRL | VV_VSSRA
  deriving BEq, Inhabited, Repr
  open vvfunct6

inductive vvcmpfunct6 where | VVCMP_VMSEQ | VVCMP_VMSNE | VVCMP_VMSLTU | VVCMP_VMSLT | VVCMP_VMSLEU | VVCMP_VMSLE
  deriving BEq, Inhabited, Repr
  open vvcmpfunct6

inductive vvmfunct6 where | VVM_VMADC | VVM_VMSBC
  deriving BEq, Inhabited, Repr
  open vvmfunct6

inductive vvmcfunct6 where | VVMC_VMADC | VVMC_VMSBC
  deriving BEq, Inhabited, Repr
  open vvmcfunct6

inductive vvmsfunct6 where | VVMS_VADC | VVMS_VSBC
  deriving BEq, Inhabited, Repr
  open vvmsfunct6

inductive vxmfunct6 where | VXM_VMADC | VXM_VMSBC
  deriving BEq, Inhabited, Repr
  open vxmfunct6

inductive vxmcfunct6 where | VXMC_VMADC | VXMC_VMSBC
  deriving BEq, Inhabited, Repr
  open vxmcfunct6

inductive vxmsfunct6 where | VXMS_VADC | VXMS_VSBC
  deriving BEq, Inhabited, Repr
  open vxmsfunct6

inductive vimfunct6 where | VIM_VMADC
  deriving BEq, Inhabited, Repr
  open vimfunct6

inductive vimcfunct6 where | VIMC_VMADC
  deriving BEq, Inhabited, Repr
  open vimcfunct6

inductive vimsfunct6 where | VIMS_VADC
  deriving BEq, Inhabited, Repr
  open vimsfunct6

inductive vxcmpfunct6 where | VXCMP_VMSEQ | VXCMP_VMSNE | VXCMP_VMSLTU | VXCMP_VMSLT | VXCMP_VMSLEU | VXCMP_VMSLE | VXCMP_VMSGTU | VXCMP_VMSGT
  deriving BEq, Inhabited, Repr
  open vxcmpfunct6

inductive vicmpfunct6 where | VICMP_VMSEQ | VICMP_VMSNE | VICMP_VMSLEU | VICMP_VMSLE | VICMP_VMSGTU | VICMP_VMSGT
  deriving BEq, Inhabited, Repr
  open vicmpfunct6

inductive nvfunct6 where | NV_VNCLIPU | NV_VNCLIP
  deriving BEq, Inhabited, Repr
  open nvfunct6

inductive nvsfunct6 where | NVS_VNSRL | NVS_VNSRA
  deriving BEq, Inhabited, Repr
  open nvsfunct6

inductive nxfunct6 where | NX_VNCLIPU | NX_VNCLIP
  deriving BEq, Inhabited, Repr
  open nxfunct6

inductive nxsfunct6 where | NXS_VNSRL | NXS_VNSRA
  deriving BEq, Inhabited, Repr
  open nxsfunct6

inductive mmfunct6 where | MM_VMAND | MM_VMNAND | MM_VMANDN | MM_VMXOR | MM_VMOR | MM_VMNOR | MM_VMORN | MM_VMXNOR
  deriving BEq, Inhabited, Repr
  open mmfunct6

inductive nifunct6 where | NI_VNCLIPU | NI_VNCLIP
  deriving BEq, Inhabited, Repr
  open nifunct6

inductive nisfunct6 where | NIS_VNSRL | NIS_VNSRA
  deriving BEq, Inhabited, Repr
  open nisfunct6

inductive wvvfunct6 where | WVV_VADD | WVV_VSUB | WVV_VADDU | WVV_VSUBU | WVV_VWMUL | WVV_VWMULU | WVV_VWMULSU
  deriving BEq, Inhabited, Repr
  open wvvfunct6

inductive wvfunct6 where | WV_VADD | WV_VSUB | WV_VADDU | WV_VSUBU
  deriving BEq, Inhabited, Repr
  open wvfunct6

inductive wvxfunct6 where | WVX_VADD | WVX_VSUB | WVX_VADDU | WVX_VSUBU | WVX_VWMUL | WVX_VWMULU | WVX_VWMULSU
  deriving BEq, Inhabited, Repr
  open wvxfunct6

inductive wxfunct6 where | WX_VADD | WX_VSUB | WX_VADDU | WX_VSUBU
  deriving BEq, Inhabited, Repr
  open wxfunct6

inductive vextfunct6 where | VEXT2_ZVF2 | VEXT2_SVF2 | VEXT4_ZVF4 | VEXT4_SVF4 | VEXT8_ZVF8 | VEXT8_SVF8
  deriving BEq, Inhabited, Repr
  open vextfunct6

inductive vxfunct6 where | VX_VADD | VX_VSUB | VX_VRSUB | VX_VMINU | VX_VMIN | VX_VMAXU | VX_VMAX | VX_VAND | VX_VOR | VX_VXOR | VX_VSADDU | VX_VSADD | VX_VSSUBU | VX_VSSUB | VX_VSLL | VX_VSMUL | VX_VSRL | VX_VSRA | VX_VSSRL | VX_VSSRA
  deriving BEq, Inhabited, Repr
  open vxfunct6

inductive vifunct6 where | VI_VADD | VI_VRSUB | VI_VAND | VI_VOR | VI_VXOR | VI_VSADDU | VI_VSADD | VI_VSLL | VI_VSRL | VI_VSRA | VI_VSSRL | VI_VSSRA
  deriving BEq, Inhabited, Repr
  open vifunct6

inductive vxsgfunct6 where | VX_VSLIDEUP | VX_VSLIDEDOWN | VX_VRGATHER
  deriving BEq, Inhabited, Repr
  open vxsgfunct6

inductive visgfunct6 where | VI_VSLIDEUP | VI_VSLIDEDOWN | VI_VRGATHER
  deriving BEq, Inhabited, Repr
  open visgfunct6

inductive mvvfunct6 where | MVV_VAADDU | MVV_VAADD | MVV_VASUBU | MVV_VASUB | MVV_VMUL | MVV_VMULH | MVV_VMULHU | MVV_VMULHSU | MVV_VDIVU | MVV_VDIV | MVV_VREMU | MVV_VREM
  deriving BEq, Inhabited, Repr
  open mvvfunct6

inductive mvvmafunct6 where | MVV_VMACC | MVV_VNMSAC | MVV_VMADD | MVV_VNMSUB
  deriving BEq, Inhabited, Repr
  open mvvmafunct6

inductive rmvvfunct6 where | MVV_VREDSUM | MVV_VREDAND | MVV_VREDOR | MVV_VREDXOR | MVV_VREDMINU | MVV_VREDMIN | MVV_VREDMAXU | MVV_VREDMAX
  deriving BEq, Inhabited, Repr
  open rmvvfunct6

inductive rivvfunct6 where | IVV_VWREDSUMU | IVV_VWREDSUM
  deriving BEq, Inhabited, Repr
  open rivvfunct6

inductive rfvvfunct6 where | FVV_VFREDOSUM | FVV_VFREDUSUM | FVV_VFREDMAX | FVV_VFREDMIN
  deriving BEq, Inhabited, Repr
  open rfvvfunct6

inductive rfwvvfunct6 where | FVV_VFWREDOSUM | FVV_VFWREDUSUM
  deriving BEq, Inhabited, Repr
  open rfwvvfunct6

inductive wmvvfunct6 where | WMVV_VWMACCU | WMVV_VWMACC | WMVV_VWMACCSU
  deriving BEq, Inhabited, Repr
  open wmvvfunct6

inductive mvxfunct6 where | MVX_VAADDU | MVX_VAADD | MVX_VASUBU | MVX_VASUB | MVX_VSLIDE1UP | MVX_VSLIDE1DOWN | MVX_VMUL | MVX_VMULH | MVX_VMULHU | MVX_VMULHSU | MVX_VDIVU | MVX_VDIV | MVX_VREMU | MVX_VREM
  deriving BEq, Inhabited, Repr
  open mvxfunct6

inductive mvxmafunct6 where | MVX_VMACC | MVX_VNMSAC | MVX_VMADD | MVX_VNMSUB
  deriving BEq, Inhabited, Repr
  open mvxmafunct6

inductive wmvxfunct6 where | WMVX_VWMACCU | WMVX_VWMACC | WMVX_VWMACCUS | WMVX_VWMACCSU
  deriving BEq, Inhabited, Repr
  open wmvxfunct6

inductive maskfunct3 where | VV_VMERGE | VI_VMERGE | VX_VMERGE
  deriving BEq, Inhabited, Repr
  open maskfunct3

inductive vlewidth where | VLE8 | VLE16 | VLE32 | VLE64
  deriving BEq, Inhabited, Repr
  open vlewidth

inductive fvvfunct6 where | FVV_VADD | FVV_VSUB | FVV_VMIN | FVV_VMAX | FVV_VSGNJ | FVV_VSGNJN | FVV_VSGNJX | FVV_VDIV | FVV_VMUL
  deriving BEq, Inhabited, Repr
  open fvvfunct6

inductive fvvmafunct6 where | FVV_VMADD | FVV_VNMADD | FVV_VMSUB | FVV_VNMSUB | FVV_VMACC | FVV_VNMACC | FVV_VMSAC | FVV_VNMSAC
  deriving BEq, Inhabited, Repr
  open fvvmafunct6

inductive fwvvfunct6 where | FWVV_VADD | FWVV_VSUB | FWVV_VMUL
  deriving BEq, Inhabited, Repr
  open fwvvfunct6

inductive fwvvmafunct6 where | FWVV_VMACC | FWVV_VNMACC | FWVV_VMSAC | FWVV_VNMSAC
  deriving BEq, Inhabited, Repr
  open fwvvmafunct6

inductive fwvfunct6 where | FWV_VADD | FWV_VSUB
  deriving BEq, Inhabited, Repr
  open fwvfunct6

inductive fvvmfunct6 where | FVVM_VMFEQ | FVVM_VMFLE | FVVM_VMFLT | FVVM_VMFNE
  deriving BEq, Inhabited, Repr
  open fvvmfunct6

inductive vfunary0 where | FV_CVT_XU_F | FV_CVT_X_F | FV_CVT_F_XU | FV_CVT_F_X | FV_CVT_RTZ_XU_F | FV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr
  open vfunary0

inductive vfwunary0 where | FWV_CVT_XU_F | FWV_CVT_X_F | FWV_CVT_F_XU | FWV_CVT_F_X | FWV_CVT_F_F | FWV_CVT_RTZ_XU_F | FWV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr
  open vfwunary0

inductive vfnunary0 where | FNV_CVT_XU_F | FNV_CVT_X_F | FNV_CVT_F_XU | FNV_CVT_F_X | FNV_CVT_F_F | FNV_CVT_ROD_F_F | FNV_CVT_RTZ_XU_F | FNV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr
  open vfnunary0

inductive vfunary1 where | FVV_VSQRT | FVV_VRSQRT7 | FVV_VREC7 | FVV_VCLASS
  deriving BEq, Inhabited, Repr
  open vfunary1

inductive fvffunct6 where | VF_VADD | VF_VSUB | VF_VMIN | VF_VMAX | VF_VSGNJ | VF_VSGNJN | VF_VSGNJX | VF_VDIV | VF_VRDIV | VF_VMUL | VF_VRSUB | VF_VSLIDE1UP | VF_VSLIDE1DOWN
  deriving BEq, Inhabited, Repr
  open fvffunct6

inductive fvfmafunct6 where | VF_VMADD | VF_VNMADD | VF_VMSUB | VF_VNMSUB | VF_VMACC | VF_VNMACC | VF_VMSAC | VF_VNMSAC
  deriving BEq, Inhabited, Repr
  open fvfmafunct6

inductive fwvffunct6 where | FWVF_VADD | FWVF_VSUB | FWVF_VMUL
  deriving BEq, Inhabited, Repr
  open fwvffunct6

inductive fwvfmafunct6 where | FWVF_VMACC | FWVF_VNMACC | FWVF_VMSAC | FWVF_VNMSAC
  deriving BEq, Inhabited, Repr
  open fwvfmafunct6

inductive fwffunct6 where | FWF_VADD | FWF_VSUB
  deriving BEq, Inhabited, Repr
  open fwffunct6

inductive fvfmfunct6 where | VFM_VMFEQ | VFM_VMFLE | VFM_VMFLT | VFM_VMFNE | VFM_VMFGT | VFM_VMFGE
  deriving BEq, Inhabited, Repr
  open fvfmfunct6

inductive vmlsop where | VLM | VSM
  deriving BEq, Inhabited, Repr
  open vmlsop

inductive indexed_mop where | INDEXED_UNORDERED | INDEXED_ORDERED
  deriving BEq, Inhabited, Repr
  open indexed_mop

inductive vstart_class where | VSTART_ARITH | VSTART_LOAD_STORE | VSTART_SCALAR_MOVE | VSTART_MANDATORY
  deriving BEq, Inhabited, Repr
  open vstart_class

inductive vregno where
  | Vregno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open vregno

abbrev Vtype := (BitVec 64)

abbrev SEW_pow := Nat

abbrev LMUL_pow := Int

abbrev sew_bitsize := Int



inductive agtype where | UNDISTURBED | AGNOSTIC
  deriving BEq, Inhabited, Repr
  open agtype

abbrev Vcsr := (BitVec 3)

abbrev CountSmcntrpmf := (BitVec 64)

inductive Software_Check_Code where | SWC_NO_INFO | SWC_LANDING_PAD_FAULT | SWC_SHADOW_STACK_FAULT
  deriving BEq, Inhabited, Repr
  open Software_Check_Code

inductive landing_pad_expectation where | NO_LP_EXPECTED | LP_EXPECTED
  deriving BEq, Inhabited, Repr
  open landing_pad_expectation

inductive CSRCheckResult where
  | CSR_Check_OK (_ : Unit)
  | CSR_Illegal (_ : Unit)
  | CSR_Virtual (_ : Unit)
  deriving Inhabited, BEq, Repr
  open CSRCheckResult

abbrev MemoryOpResult k_a := (Result k_a ExceptionType)

abbrev htif_cmd := (BitVec 64)

abbrev pte_flags_bits := (BitVec 8)

abbrev pte_ext_bits := (BitVec 10)

abbrev PTE_Ext := (BitVec 10)

abbrev PTE_Flags := (BitVec 8)

inductive pte_check_failure where
  | PTE_No_Permission (_ : Unit)
  | PTE_No_Access (_ : Unit)
  | PTE_Ext_Failure (_ : ext_ptw_fail)
  deriving Inhabited, BEq, Repr
  open pte_check_failure

inductive PTE_Check where
  | PTE_Check_Success (_ : ext_ptw)
  | PTE_Check_Failure (_ : (ext_ptw × pte_check_failure))
  deriving Inhabited, BEq, Repr
  open PTE_Check

abbrev tlb_vpn_bits : Int := (57 - 12)

abbrev tlb_ppn_bits : Int := 44

structure TLB_Entry where
  asid : asidbits
  global : Bool
  vpn : (BitVec (57 - 12))
  levelMask : (BitVec (57 - 12))
  ppn : (BitVec 44)
  pte : (BitVec 64)
  pteAddr : physaddr
  deriving BEq, Inhabited, Repr

abbrev num_tlb_entries_exp : Int := 6

abbrev num_tlb_entries : Int := (2 ^ 6)

abbrev tlb_index_range := Nat

/-- Type quantifiers: k_v : Int, is_sv_mode(k_v) -/
structure PTW_Output (k_v : Nat) where
  ppn : (ppn_bits k_v)
  pte : (pte_bits k_v)
  pteAddr : physaddr
  level : (level_range k_v)
  pbmt : page_based_mem_type
  global : Bool
  deriving BEq, Inhabited, Repr

abbrev PTW_Result k_v := (Result ((PTW_Output k_v) × ext_ptw) (PTW_Error × ext_ptw))

abbrev TR_Result k_paddr k_failure :=
  (Result (k_paddr × page_based_mem_type × ext_ptw) (k_failure × ext_ptw))

inductive ExecutionResult where
  | Retire_Success (_ : Unit)
  | ExecuteAs (_ : instruction)
  | Enter_Wait (_ : WaitReason)
  | Illegal_Instruction (_ : Unit)
  | Virtual_Instruction (_ : Unit)
  | Trap (_ : (Privilege × sync_exception × xlenbits))
  | Ext_CSR_Check_Failure (_ : Unit)
  | Ext_ControlAddr_Check_Failure (_ : ext_control_addr_error)
  | Ext_DataAddr_Check_Failure (_ : ext_data_addr_error)
  | Ext_XRET_Priv_Failure (_ : Unit)
  deriving Inhabited, Repr
  open ExecutionResult



inductive HartState where
  | HART_ACTIVE (_ : Unit)
  | HART_WAITING (_ : (WaitReason × instbits))
  deriving Inhabited, BEq, Repr
  open HartState

inductive FetchResult where
  | F_Ext_Error (_ : ext_fetch_addr_error)
  | F_Base (_ : word)
  | F_RVC (_ : half)
  | F_Error (_ : (ExceptionType × xlenbits))
  deriving Inhabited, BEq, Repr
  open FetchResult

/-- Type quantifiers: k_width : Int, k_width ≥ 0 -/
inductive FetchBytes_Result (k_width : Nat) where
  | FetchBytes_Ext_Error (_ : ext_fetch_addr_error)
  | FetchBytes_Exception (_ : ExceptionType)
  | FetchBytes_Success (_ : (BitVec (k_width * 8)))
  deriving Inhabited, BEq, Repr
  open FetchBytes_Result

inductive Step where
  | Step_Pending_Interrupt (_ : (InterruptType × Privilege))
  | Step_Ext_Fetch_Failure (_ : ext_fetch_addr_error)
  | Step_Fetch_Failure (_ : (virtaddr × ExceptionType))
  | Step_Execute (_ : (ExecutionResult × instbits))
  | Step_Waiting (_ : WaitReason)
  deriving Inhabited, Repr
  open Step

structure pma_check_opts where
  ziccamoa : Bool
  ziccamoc : Bool
  ziccif : Bool
  zicclsm : Bool
  ziccrse : Bool
  ssccptr : Bool
  svadu : Bool
  deriving BEq, Inhabited, Repr

inductive ISA_Format where | Canonical_Lowercase | DeviceTree_ISA_Extensions
  deriving BEq, Inhabited, Repr
  open ISA_Format

inductive Register : Type where
  | hart_state
  | satp
  | tlb
  | pma_regions
  | htif_payload_writes
  | htif_cmd_write
  | htif_exit_code
  | htif_done
  | htif_tohost
  | stimecmp
  | mtimecmp
  | htif_tohost_base
  | pc_reset_address
  | elp
  | minstretcfg
  | mcyclecfg
  | vcsr
  | vtype
  | vl
  | vstart
  | vr31
  | vr30
  | vr29
  | vr28
  | vr27
  | vr26
  | vr25
  | vr24
  | vr23
  | vr22
  | vr21
  | vr20
  | vr19
  | vr18
  | vr17
  | vr16
  | vr15
  | vr14
  | vr13
  | vr12
  | vr11
  | vr10
  | vr9
  | vr8
  | vr7
  | vr6
  | vr5
  | vr4
  | vr3
  | vr2
  | vr1
  | vr0
  | fcsr
  | f31
  | f30
  | f29
  | f28
  | f27
  | f26
  | f25
  | f24
  | f23
  | f22
  | f21
  | f20
  | f19
  | f18
  | f17
  | f16
  | f15
  | f14
  | f13
  | f12
  | f11
  | f10
  | f9
  | f8
  | f7
  | f6
  | f5
  | f4
  | f3
  | f2
  | f1
  | f0
  | pmpaddr_n
  | pmpcfg_n
  | sig_seip
  | sig_meip
  | mideleg
  | medeleg
  | mip
  | mie
  | tselect
  | stval
  | scause
  | sepc
  | sscratch
  | stvec
  | mconfigptr
  | mhartid
  | marchid
  | mimpid
  | mvendorid
  | minstret_increment
  | minstret
  | mtime
  | mcycle
  | mcountinhibit
  | mcounteren
  | scounteren
  | mscratch
  | mtval
  | mepc
  | mcause
  | mtvec
  | cur_inst
  | x31
  | x30
  | x29
  | x28
  | x27
  | x26
  | x25
  | x24
  | x23
  | x22
  | x21
  | x20
  | x19
  | x18
  | x17
  | x16
  | x15
  | x14
  | x13
  | x12
  | x11
  | x10
  | x9
  | x8
  | x7
  | x6
  | x5
  | x4
  | x3
  | x2
  | x1
  | nextPC
  | PC
  | menvcfg
  | mseccfg
  | senvcfg
  | sstateen3
  | sstateen2
  | sstateen1
  | sstateen0
  | mstateen3
  | mstateen2
  | mstateen1
  | mstateen0
  | hstateen3
  | hstateen2
  | hstateen1
  | hstateen0
  | mstatus
  | misa
  | cur_privilege
  | rvfi_mem_data_present
  | rvfi_mem_data
  | rvfi_int_data_present
  | rvfi_int_data
  | rvfi_pc_data
  | rvfi_inst_data
  | rvfi_instruction
  | fp_rounding_global
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .hart_state => HartState
  | .satp => (BitVec 64)
  | .tlb => (Vector (Option TLB_Entry) (2 ^ 6))
  | .pma_regions => (List PMA_Region)
  | .htif_payload_writes => (BitVec 4)
  | .htif_cmd_write => (BitVec 1)
  | .htif_exit_code => (BitVec 64)
  | .htif_done => Bool
  | .htif_tohost => (BitVec 64)
  | .stimecmp => (BitVec 64)
  | .mtimecmp => (BitVec 64)
  | .htif_tohost_base => (Option (BitVec (if ( 64 = 32  : Bool) then 34 else 64)))
  | .pc_reset_address => (BitVec 64)
  | .elp => (BitVec 1)
  | .minstretcfg => (BitVec 64)
  | .mcyclecfg => (BitVec 64)
  | .vcsr => (BitVec 3)
  | .vtype => (BitVec 64)
  | .vl => (BitVec 64)
  | .vstart => (BitVec 64)
  | .vr31 => (BitVec (2 ^ 8))
  | .vr30 => (BitVec (2 ^ 8))
  | .vr29 => (BitVec (2 ^ 8))
  | .vr28 => (BitVec (2 ^ 8))
  | .vr27 => (BitVec (2 ^ 8))
  | .vr26 => (BitVec (2 ^ 8))
  | .vr25 => (BitVec (2 ^ 8))
  | .vr24 => (BitVec (2 ^ 8))
  | .vr23 => (BitVec (2 ^ 8))
  | .vr22 => (BitVec (2 ^ 8))
  | .vr21 => (BitVec (2 ^ 8))
  | .vr20 => (BitVec (2 ^ 8))
  | .vr19 => (BitVec (2 ^ 8))
  | .vr18 => (BitVec (2 ^ 8))
  | .vr17 => (BitVec (2 ^ 8))
  | .vr16 => (BitVec (2 ^ 8))
  | .vr15 => (BitVec (2 ^ 8))
  | .vr14 => (BitVec (2 ^ 8))
  | .vr13 => (BitVec (2 ^ 8))
  | .vr12 => (BitVec (2 ^ 8))
  | .vr11 => (BitVec (2 ^ 8))
  | .vr10 => (BitVec (2 ^ 8))
  | .vr9 => (BitVec (2 ^ 8))
  | .vr8 => (BitVec (2 ^ 8))
  | .vr7 => (BitVec (2 ^ 8))
  | .vr6 => (BitVec (2 ^ 8))
  | .vr5 => (BitVec (2 ^ 8))
  | .vr4 => (BitVec (2 ^ 8))
  | .vr3 => (BitVec (2 ^ 8))
  | .vr2 => (BitVec (2 ^ 8))
  | .vr1 => (BitVec (2 ^ 8))
  | .vr0 => (BitVec (2 ^ 8))
  | .fcsr => (BitVec 32)
  | .f31 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f30 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f29 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f28 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f27 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f26 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f25 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f24 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f23 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f22 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f21 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f20 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f19 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f18 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f17 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f16 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f15 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f14 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f13 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f12 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f11 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f10 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f9 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f8 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f7 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f6 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f5 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f4 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f3 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f2 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f1 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f0 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .pmpaddr_n => (Vector (BitVec 64) 64)
  | .pmpcfg_n => (Vector (BitVec 8) 64)
  | .sig_seip => (BitVec 1)
  | .sig_meip => (BitVec 1)
  | .mideleg => (BitVec 64)
  | .medeleg => (BitVec 64)
  | .mip => (BitVec 64)
  | .mie => (BitVec 64)
  | .tselect => (BitVec 64)
  | .stval => (BitVec 64)
  | .scause => (BitVec 64)
  | .sepc => (BitVec 64)
  | .sscratch => (BitVec 64)
  | .stvec => (BitVec 64)
  | .mconfigptr => (BitVec 64)
  | .mhartid => (BitVec 64)
  | .marchid => (BitVec 64)
  | .mimpid => (BitVec 64)
  | .mvendorid => (BitVec 32)
  | .minstret_increment => Bool
  | .minstret => (BitVec 64)
  | .mtime => (BitVec 64)
  | .mcycle => (BitVec 64)
  | .mcountinhibit => (BitVec 32)
  | .mcounteren => (BitVec 32)
  | .scounteren => (BitVec 32)
  | .mscratch => (BitVec 64)
  | .mtval => (BitVec 64)
  | .mepc => (BitVec 64)
  | .mcause => (BitVec 64)
  | .mtvec => (BitVec 64)
  | .cur_inst => (BitVec 64)
  | .x31 => (BitVec 64)
  | .x30 => (BitVec 64)
  | .x29 => (BitVec 64)
  | .x28 => (BitVec 64)
  | .x27 => (BitVec 64)
  | .x26 => (BitVec 64)
  | .x25 => (BitVec 64)
  | .x24 => (BitVec 64)
  | .x23 => (BitVec 64)
  | .x22 => (BitVec 64)
  | .x21 => (BitVec 64)
  | .x20 => (BitVec 64)
  | .x19 => (BitVec 64)
  | .x18 => (BitVec 64)
  | .x17 => (BitVec 64)
  | .x16 => (BitVec 64)
  | .x15 => (BitVec 64)
  | .x14 => (BitVec 64)
  | .x13 => (BitVec 64)
  | .x12 => (BitVec 64)
  | .x11 => (BitVec 64)
  | .x10 => (BitVec 64)
  | .x9 => (BitVec 64)
  | .x8 => (BitVec 64)
  | .x7 => (BitVec 64)
  | .x6 => (BitVec 64)
  | .x5 => (BitVec 64)
  | .x4 => (BitVec 64)
  | .x3 => (BitVec 64)
  | .x2 => (BitVec 64)
  | .x1 => (BitVec 64)
  | .nextPC => (BitVec 64)
  | .PC => (BitVec 64)
  | .menvcfg => (BitVec 64)
  | .mseccfg => (BitVec 64)
  | .senvcfg => (BitVec 64)
  | .sstateen3 => (BitVec 32)
  | .sstateen2 => (BitVec 32)
  | .sstateen1 => (BitVec 32)
  | .sstateen0 => (BitVec 32)
  | .mstateen3 => (BitVec 64)
  | .mstateen2 => (BitVec 64)
  | .mstateen1 => (BitVec 64)
  | .mstateen0 => (BitVec 64)
  | .hstateen3 => (BitVec 64)
  | .hstateen2 => (BitVec 64)
  | .hstateen1 => (BitVec 64)
  | .hstateen0 => (BitVec 64)
  | .mstatus => (BitVec 64)
  | .misa => (BitVec 64)
  | .cur_privilege => Privilege
  | .rvfi_mem_data_present => Bool
  | .rvfi_mem_data => (BitVec 704)
  | .rvfi_int_data_present => Bool
  | .rvfi_int_data => (BitVec 320)
  | .rvfi_pc_data => (BitVec 128)
  | .rvfi_inst_data => (BitVec 192)
  | .rvfi_instruction => (BitVec 64)
  | .fp_rounding_global => (BitVec 5)

instance : Inhabited (RegisterRef RegisterType HartState) where
  default := .Reg hart_state
instance : Inhabited (RegisterRef RegisterType Privilege) where
  default := .Reg cur_privilege
instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg sig_meip
instance : Inhabited (RegisterRef RegisterType (BitVec 128)) where
  default := .Reg rvfi_pc_data
instance : Inhabited (RegisterRef RegisterType (BitVec 192)) where
  default := .Reg rvfi_inst_data
instance : Inhabited (RegisterRef RegisterType (BitVec 3)) where
  default := .Reg vcsr
instance : Inhabited (RegisterRef RegisterType (BitVec 32)) where
  default := .Reg sstateen0
instance : Inhabited (RegisterRef RegisterType (BitVec 320)) where
  default := .Reg rvfi_int_data
instance : Inhabited (RegisterRef RegisterType (BitVec 4)) where
  default := .Reg htif_payload_writes
instance : Inhabited (RegisterRef RegisterType (BitVec 5)) where
  default := .Reg fp_rounding_global
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg rvfi_instruction
instance : Inhabited (RegisterRef RegisterType (BitVec 704)) where
  default := .Reg rvfi_mem_data
instance : Inhabited (RegisterRef RegisterType (BitVec (2 ^ 8))) where
  default := .Reg vr0
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg rvfi_int_data_present
instance : Inhabited (RegisterRef RegisterType (List PMA_Region)) where
  default := .Reg pma_regions
instance : Inhabited (RegisterRef RegisterType (Option (BitVec (if ( 64 = 32  : Bool) then 34 else 64)))) where
  default := .Reg htif_tohost_base
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 64)) where
  default := .Reg pmpaddr_n
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 8) 64)) where
  default := .Reg pmpcfg_n
instance : Inhabited (RegisterRef RegisterType (Vector (Option TLB_Entry) (2 ^ 6))) where
  default := .Reg tlb
abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, m : Nat, m ≥ 0, m ≥ k_n -/
def zero_extend {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.zeroExtend v m)

def physaddrbits_zero_extend (xs : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) : (BitVec 64) :=
  (zero_extend (m := 64) xs)

instance : Arch where
  va_size := 64
  pa := (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  abort := Unit
  translation := Unit
  trans_start := Unit
  trans_end := Unit
  fault := Unit
  tlb_op := Unit
  cache_op := Unit
  barrier := barrier_kind
  arch_ak := RISCV_strong_access
  sys_reg_id := Unit

