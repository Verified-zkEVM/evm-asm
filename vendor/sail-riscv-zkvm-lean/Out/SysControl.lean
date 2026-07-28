import Out.Flow
import Out.Prelude
import Out.Errors
import Out.IsaVersion
import Out.Xlen
import Out.PlatformConfig
import Out.Types
import Out.Callbacks
import Out.Regs
import Out.PcAccess
import Out.SysRegs
import Out.InterruptRegs
import Out.SysExceptions
import Out.PmpRegs
import Out.PmpControl
import Out.StateenRegs
import Out.VextRegs
import Out.ZicfilpRegs
import Out.StateenAccessChecks

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

def effectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) : SailM Privilege := do
  if (((bne access (InstructionFetch ())) && ((_get_Mstatus_MPRV m) == 1#1)) : Bool)
  then (privLevel_bits_forwards ((_get_Mstatus_MPP m), 0#1))
  else (pure priv)

def csrAccess (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 11 10)

def csrPriv (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 9 8)

def privLevel_to_CSR_privbits (p : Privilege) : SailM (BitVec 2) := do
  match p with
  | .User => (pure 0b00#2)
  | .VirtualUser => (pure 0b00#2)
  | .Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure 0b10#2)
      else (pure 0b01#2))
  | .VirtualSupervisor => (pure 0b01#2)
  | .Machine => (pure 0b11#2)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  (pure (zopz0zKzJ_u (← (privLevel_to_CSR_privbits p)) (csrPriv csr)))

def check_CSR_access (csr : (BitVec 12)) (access_type : CSRAccessType) : Bool :=
  (not (((access_type == CSRWrite) || (access_type == CSRReadWrite)) && ((csrAccess csr) == 0b11#2)))

def satp_accessible (priv : Privilege) : SailM Bool := do
  match priv with
  | .Machine => (pure (hartSupports Ext_S))
  | .Supervisor => (pure ((_get_Mstatus_TVM (← readReg mstatus)) == 0#1))
  | .VirtualSupervisor => (pure false)
  | .User => (pure false)
  | .VirtualUser => (pure false)

def is_CSR_accessible (arg0 : (BitVec 12)) (arg1 : Privilege) (arg2 : CSRAccessType) : SailM Bool := do
  let merge_var := (arg0, arg1, arg2)
  match merge_var with
  | (0x301, g__24, g__25) => (pure true)
  | (0x300, g__26, g__27) => (pure true)
  | (0x310, g__28, g__29) => (pure (mstatush_is_defined && (xlen == 32)))
  | (0x747, g__30, g__31) =>
    (pure (mseccfg_csrs_are_defined && ((← (currentlyEnabled Ext_Zkr)) || ((hartSupports
              Ext_Zicfilp) || (← (currentlyEnabled Ext_Smmpm))))))
  | (0x757, g__32, g__33) =>
    (pure (mseccfg_csrs_are_defined && (((← (currentlyEnabled Ext_Zkr)) || (hartSupports
              Ext_Zicfilp)) && (xlen == 32))))
  | (0x30A, g__34, g__35) => (pure ((← (currentlyEnabled Ext_U)) && xenvcfg_csrs_are_defined))
  | (0x31A, g__36, g__37) =>
    (pure ((← (currentlyEnabled Ext_U)) && ((xlen == 32) && xenvcfg_csrs_are_defined)))
  | (0x10A, g__38, g__39) => (pure ((← (currentlyEnabled Ext_S)) && xenvcfg_csrs_are_defined))
  | (0x342, g__40, g__41) => (pure true)
  | (0x343, g__42, g__43) => (pure true)
  | (0x340, g__44, g__45) => (pure true)
  | (0x106, g__46, g__47) => (currentlyEnabled Ext_S)
  | (0x306, g__48, g__49) => (currentlyEnabled Ext_U)
  | (0x320, g__50, g__51) => (pure true)
  | (0xF11, g__52, g__53) => (pure true)
  | (0xF12, g__54, g__55) => (pure true)
  | (0xF13, g__56, g__57) => (pure true)
  | (0xF14, g__58, g__59) => (pure true)
  | (0xF15, g__60, g__61) => (pure mconfigptr_is_defined)
  | (0x100, g__62, g__63) => (currentlyEnabled Ext_S)
  | (0x140, g__64, g__65) => (currentlyEnabled Ext_S)
  | (0x142, g__66, g__67) => (currentlyEnabled Ext_S)
  | (0x143, g__68, g__69) => (currentlyEnabled Ext_S)
  | (0x7A0, g__70, g__71) => (pure true)
  | (0x304, g__72, g__73) => (pure true)
  | (0x344, g__74, g__75) => (pure true)
  | (0x302, g__76, g__77) => (currentlyEnabled Ext_S)
  | (0x312, g__78, g__79) =>
    (pure (delegh_csrs_are_defined && ((← (currentlyEnabled Ext_S)) && (xlen == 32))))
  | (0x303, g__80, g__81) => (currentlyEnabled Ext_S)
  | (0x144, g__82, g__83) => (currentlyEnabled Ext_S)
  | (0x104, g__84, g__85) => (currentlyEnabled Ext_S)
  | (0x105, g__86, g__87) => (currentlyEnabled Ext_S)
  | (0x141, g__88, g__89) => (currentlyEnabled Ext_S)
  | (0x305, g__90, g__91) => (pure true)
  | (0x341, g__92, g__93) => (pure true)
  | (v__382, g__94, g__95) =>
    (do
      if (((Sail.BitVec.extractLsb v__382 11 4) == (0x3A#8 : (BitVec 8))) : Bool)
      then
        (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__382 3 0)
        (pure ((sys_pmp_count >b (4 *i (BitVec.toNatInt idx))) && (((BitVec.access idx 0) == 0#1) || (xlen == 32)))))
      else
        (do
          if (((Sail.BitVec.extractLsb v__382 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
          then
            (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__382 3 0)
            (pure (sys_pmp_count >b (BitVec.toNatInt (0b00#2 +++ idx)))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__382 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
              then
                (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__382 3 0)
                (pure (sys_pmp_count >b (BitVec.toNatInt (0b01#2 +++ idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__382 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                  then
                    (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__382 3 0)
                    (pure (sys_pmp_count >b (BitVec.toNatInt (0b10#2 +++ idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__382 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                      then
                        (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__382 3 0)
                        (pure (sys_pmp_count >b (BitVec.toNatInt (0b11#2 +++ idx)))))
                      else
                        (do
                          match (v__382, g__94, g__95) with
                          | (0x001, g__96, g__97) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x002, g__98, g__99) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x003, g__100, g__101) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x008, g__102, g__103) => (currentlyEnabled Ext_Zve32x)
                          | (0x009, g__104, g__105) => (currentlyEnabled Ext_Zve32x)
                          | (0x00A, g__106, g__107) => (currentlyEnabled Ext_Zve32x)
                          | (0x00F, g__108, g__109) => (currentlyEnabled Ext_Zve32x)
                          | (0xC20, g__110, g__111) => (currentlyEnabled Ext_Zve32x)
                          | (0xC21, g__112, g__113) => (currentlyEnabled Ext_Zve32x)
                          | (0xC22, g__114, g__115) => (currentlyEnabled Ext_Zve32x)
                          | (0x321, g__116, g__117) => (currentlyEnabled Ext_Smcntrpmf)
                          | (0x721, g__118, g__119) =>
                            (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
                          | (0x322, g__120, g__121) => (currentlyEnabled Ext_Smcntrpmf)
                          | (0x722, g__122, g__123) =>
                            (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
                          | (0x30C, g__124, g__125) => (pure (is_mstateen_accessible ()))
                          | (0x30D, g__126, g__127) => (pure (is_mstateen_accessible ()))
                          | (0x30E, g__128, g__129) => (pure (is_mstateen_accessible ()))
                          | (0x30F, g__130, g__131) => (pure (is_mstateen_accessible ()))
                          | (0x31C, g__132, g__133) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x31D, g__134, g__135) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x31E, g__136, g__137) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x31F, g__138, g__139) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x60C, g__140, g__141) => (is_hstateen_accessible ())
                          | (0x60D, g__142, g__143) => (is_hstateen_accessible ())
                          | (0x60E, g__144, g__145) => (is_hstateen_accessible ())
                          | (0x60F, g__146, g__147) => (is_hstateen_accessible ())
                          | (0x61C, g__148, g__149) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x61D, g__150, g__151) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x61E, g__152, g__153) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x61F, g__154, g__155) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x10C, g__156, g__157) => (is_sstateen_accessible ())
                          | (0x10D, g__158, g__159) => (is_sstateen_accessible ())
                          | (0x10E, g__160, g__161) => (is_sstateen_accessible ())
                          | (0x10F, g__162, g__163) => (is_sstateen_accessible ())
                          | (0x180, g__94, g__164) => (satp_accessible g__94)
                          | _ => (pure false)))))))

def check_CSR (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) : SailM Bool := do
  (pure ((← (check_CSR_priv csr p)) && ((check_CSR_access csr access_type) && ((← (is_CSR_accessible
              csr p access_type)) && (← (stateen_allows_CSR_access csr p access_type))))))

def is_CSR_exception_virtual (arg0 : (BitVec 12)) (arg1 : Privilege) (arg2 : CSRAccessType) : SailM Bool := do
  let merge_var := (arg0, arg1, arg2)
  match merge_var with
  | (0x001, g__2, g__3) => (pure false)
  | (0x002, g__4, g__5) => (pure false)
  | (0x003, g__6, g__7) => (pure false)
  | (0x008, g__8, g__9) => (pure false)
  | (0x009, g__10, g__11) => (pure false)
  | (0x00A, g__12, g__13) => (pure false)
  | (0x00F, g__14, g__15) => (pure false)
  | (0xC20, g__16, g__17) => (pure false)
  | (0xC21, g__18, g__19) => (pure false)
  | (0xC22, g__20, g__21) => (pure false)
  | (0x180, g__22, g__23) => (pure true)
  | (csr, _, access_type) => (check_CSR csr Supervisor access_type)

def check_CSR_result (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) : SailM CSRCheckResult := do
  if ((← (check_CSR csr p access_type)) : Bool)
  then (pure (CSR_Check_OK ()))
  else
    (do
      if ((((p == VirtualSupervisor) || (p == VirtualUser)) && (← (is_CSR_exception_virtual csr p
               access_type))) : Bool)
      then (pure (CSR_Virtual ()))
      else (pure (CSR_Illegal ())))

def exception_delegatee (e : ExceptionType) (p : Privilege) : SailM Privilege := do
  let idx := (BitVec.toNatInt (exceptionType_bits_forwards e))
  let super ← do (pure (bit_to_bool (BitVec.access (← readReg medeleg) idx)))
  let deleg ← do
    if (((← (currentlyEnabled Ext_S)) && super) : Bool)
    then (pure Supervisor)
    else (pure Machine)
  if ((zopz0zI_u (privLevel_to_bits deleg) (privLevel_to_bits p)) : Bool)
  then (pure p)
  else (pure deleg)

def findPendingInterrupt (ip : (BitVec 64)) : (Option InterruptType) :=
  let ip := (Mk_Minterrupts ip)
  if (((_get_Minterrupts_MEI ip) == 1#1) : Bool)
  then (some I_M_External)
  else
    (if (((_get_Minterrupts_MSI ip) == 1#1) : Bool)
    then (some I_M_Software)
    else
      (if (((_get_Minterrupts_MTI ip) == 1#1) : Bool)
      then (some I_M_Timer)
      else
        (if (((_get_Minterrupts_SEI ip) == 1#1) : Bool)
        then (some I_S_External)
        else
          (if (((_get_Minterrupts_SSI ip) == 1#1) : Bool)
          then (some I_S_Software)
          else
            (if (((_get_Minterrupts_STI ip) == 1#1) : Bool)
            then (some I_S_Timer)
            else
              (if (((_get_Minterrupts_LCOFI ip) == 1#1) : Bool)
              then (some I_COF)
              else none))))))

def getPendingSet (priv : Privilege) : SailM (Option ((BitVec 64) × Privilege)) := do
  let mideleg_bits ← do
    if ((← (currentlyEnabled Ext_S)) : Bool)
    then readReg mideleg
    else (pure (zeros (n := 64)))
  let mip_bits ← do (read_mip IncludePlatformInterrupts)
  let pending_m ← do
    (pure (mip_bits &&& ((← readReg mie) &&& (Complement.complement (← readReg mideleg)))))
  let pending_s ← do (pure (mip_bits &&& ((← readReg mie) &&& (← readReg mideleg))))
  let mIE ← do
    (pure (((priv == Machine) && ((_get_Mstatus_MIE (← readReg mstatus)) == 1#1)) || ((priv == Supervisor) || (priv == User))))
  let sIE ← do
    (pure (((priv == Supervisor) && ((_get_Mstatus_SIE (← readReg mstatus)) == 1#1)) || (priv == User)))
  if ((mIE && (pending_m != (zeros (n := 64)))) : Bool)
  then (pure (some (pending_m, Machine)))
  else
    (if ((sIE && (pending_s != (zeros (n := 64)))) : Bool)
    then (pure (some (pending_s, Supervisor)))
    else (pure none))

def shouldWakeForInterrupt (_ : Unit) : SailM Bool := do
  (pure (((← readReg mip) &&& (← readReg mie)) != (zeros (n := 64))))

def dispatchInterrupt (priv : Privilege) : SailM (Option (InterruptType × Privilege)) := do
  match (← (getPendingSet priv)) with
  | none => (pure none)
  | .some (ip, p) =>
    (match (findPendingInterrupt ip) with
    | none => (pure none)
    | .some i => (pure (some (i, p))))

def tval (excinfo : (Option (BitVec 64))) : (BitVec 64) :=
  match excinfo with
  | .some e => e
  | none => (zeros (n := 64))

/-- Type quantifiers: k_ex480742_ : Bool -/
def track_trap (p : Privilege) (is_interrupt : Bool) (cause : (BitVec 6)) : SailM Unit := do
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  match p with
  | .Machine =>
    (do
      (csr_name_write_callback "mcause" (← readReg mcause))
      (csr_name_write_callback "mtval" (← readReg mtval))
      (csr_name_write_callback "mepc" (← readReg mepc)))
  | .Supervisor =>
    (do
      (csr_name_write_callback "scause" (← readReg scause))
      (csr_name_write_callback "stval" (← readReg stval))
      (csr_name_write_callback "sepc" (← readReg sepc)))
  | .User => (internal_error "sys/sys_control.sail" 187 "Invalid privilege level")
  | .VirtualUser => (internal_error "sys/sys_control.sail" 188 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "sys/sys_control.sail" 189 "Hypervisor extension not supported")
  (pure (trap_callback is_interrupt cause))

def trap_handler (del_priv : Privilege) (c : TrapCause) (pc : (BitVec 64)) (info : (Option (BitVec 64))) (ext : (Option Unit)) : SailM (BitVec 64) := do
  let is_interrupt := (trapCause_is_interrupt c)
  let cause := (trapCause_bits_forwards c)
  if (((get_config_print_exception ()) || (get_config_print_interrupt ())) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "handling "
          (HAppend.hAppend (trapCause_to_str c)
            (HAppend.hAppend " at priv "
              (HAppend.hAppend (← (privLevel_to_str del_priv))
                (HAppend.hAppend " with tval " (BitVec.toFormatted (tval info)))))))))
  else (pure ())
  if ((hartSupports Ext_Zicfilp) : Bool)
  then (zicfilp_preserve_elp_on_trap del_priv)
  else (pure ())
  match del_priv with
  | .Machine =>
    (do
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (64 -i 1) (64 -i 1)
        (bool_to_bit is_interrupt))
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (64 -i 2) 0
        (zero_extend (m := (64 -i 1)) cause))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7
        (_get_Mstatus_MIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits (← readReg cur_privilege)))
      writeReg mtval (tval info)
      writeReg mepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv is_interrupt cause)
      (prepare_trap_vector del_priv (← readReg mcause)))
  | .Supervisor =>
    (do
      assert (← (currentlyEnabled Ext_S)) "no supervisor mode present for delegation"
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (64 -i 1) (64 -i 1)
        (bool_to_bit is_interrupt))
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (64 -i 2) 0
        (zero_extend (m := (64 -i 1)) cause))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5
        (_get_Mstatus_SIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1 0#1)
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8
        (← do
          match (← readReg cur_privilege) with
          | .User => (pure 0#1)
          | .Supervisor => (pure 1#1)
          | .Machine =>
            (internal_error "sys/sys_control.sail" 238 "invalid privilege for s-mode trap")
          | .VirtualUser =>
            (internal_error "sys/sys_control.sail" 239 "Hypervisor extension not supported")
          | .VirtualSupervisor =>
            (internal_error "sys/sys_control.sail" 240 "Hypervisor extension not supported")))
      writeReg stval (tval info)
      writeReg sepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv is_interrupt cause)
      (prepare_trap_vector del_priv (← readReg scause)))
  | .User => (internal_error "sys/sys_control.sail" 253 "Invalid privilege level")
  | .VirtualUser => (internal_error "sys/sys_control.sail" 254 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "sys/sys_control.sail" 255 "Hypervisor extension not supported")

def exception_handler (cur_priv : Privilege) (exc : sync_exception) (pc : (BitVec 64)) : SailM (BitVec 64) := do
  let del_priv ← do (exception_delegatee exc.trap cur_priv)
  if ((get_config_print_exception ()) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "trapping from "
          (HAppend.hAppend (← (privLevel_to_str cur_priv))
            (HAppend.hAppend " to "
              (HAppend.hAppend (← (privLevel_to_str del_priv))
                (HAppend.hAppend " to handle " (exceptionType_to_str exc.trap))))))))
  else (pure ())
  (trap_handler del_priv (Exception exc.trap) pc exc.excinfo exc.ext)

def xtval_exception_value (e : ExceptionType) (excinfo : (BitVec 64)) : (Option (BitVec 64)) :=
  if ((match e with
     | .E_Illegal_Instr () => illegal_instruction_writes_xtval
     | .E_Virtual_Instr () => virtual_instruction_writes_xtval
     | .E_Breakpoint .Brk_Software => software_breakpoint_writes_xtval
     | .E_Breakpoint .Brk_Hardware => hardware_breakpoint_writes_xtval
     | .E_Load_Addr_Align () => misaligned_load_writes_xtval
     | .E_Load_Access_Fault () => load_access_fault_writes_xtval
     | .E_Load_Page_Fault () => load_page_fault_writes_xtval
     | .E_Load_GPage_Fault () => load_guest_page_fault_writes_xtval
     | .E_SAMO_Addr_Align () => misaligned_samo_writes_xtval
     | .E_SAMO_Access_Fault () => samo_access_fault_writes_xtval
     | .E_SAMO_Page_Fault () => samo_page_fault_writes_xtval
     | .E_SAMO_GPage_Fault () => samo_guest_page_fault_writes_xtval
     | .E_Fetch_Addr_Align () => misaligned_fetch_writes_xtval
     | .E_Fetch_Access_Fault () => fetch_access_fault_writes_xtval
     | .E_Fetch_Page_Fault () => fetch_page_fault_writes_xtval
     | .E_Fetch_GPage_Fault () => fetch_guest_page_fault_writes_xtval
     | .E_Software_Check () => software_check_fault_writes_xtval
     | .E_U_EnvCall () => false
     | .E_S_EnvCall () => false
     | .E_VS_EnvCall () => false
     | .E_M_EnvCall () => false
     | .E_Extension _ => true
     | .E_Reserved_14 () => reserved_exceptions_write_xtval
     | .E_Reserved_16 () => reserved_exceptions_write_xtval
     | .E_Reserved_17 () => reserved_exceptions_write_xtval
     | .E_Reserved_19 () => reserved_exceptions_write_xtval) : Bool)
  then (some excinfo)
  else none

def make_sync_exception (e : ExceptionType) (xtval : (BitVec 64)) : sync_exception :=
  { trap := e
    excinfo := (xtval_exception_value e xtval)
    ext := none }

def handle_exception (xtval : (BitVec 64)) (e : ExceptionType) : SailM Unit := do
  (set_next_pc
    (← (exception_handler (← readReg cur_privilege) (make_sync_exception e xtval)
        (← readReg PC))))

def handle_interrupt (i : InterruptType) (del_priv : Privilege) : SailM Unit := do
  (set_next_pc (← (trap_handler del_priv (Interrupt i) (← readReg PC) none none)))

def reset_misa (_ : Unit) : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 0 0
    (bool_to_bit (hartSupports Ext_A)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 2 2
    (bool_to_bit (hartSupports Ext_C)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 1 1
    (bool_to_bit (hartSupports Ext_B)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12
    (bool_to_bit (hartSupports Ext_M)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 20 20
    (bool_to_bit (hartSupports Ext_U)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 18 18
    (bool_to_bit (hartSupports Ext_S)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 21 21
    (bool_to_bit (hartSupports Ext_V)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 4 4 (bool_to_bit base_E_enabled))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 8 8
    (Complement.complement (_get_Misa_E (← readReg misa))))
  if (((hartSupports Ext_F) && (hartSupports Ext_Zfinx)) : Bool)
  then (internal_error "sys/sys_control.sail" 325 "F and Zfinx cannot both be enabled!")
  else (pure ())
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 5 5
    (bool_to_bit (hartSupports Ext_F)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3
    (bool_to_bit (hartSupports Ext_D)))
  (csr_name_write_callback "misa" (← readReg misa))

def set_pc_reset_address (addr : (BitVec 64)) : SailM Unit := do
  writeReg pc_reset_address (trunc (m := 64) addr)

def reset_sys (_ : Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
  (reset_tvecs ())
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  (reset_misa ())
  (cancel_reservation ())
  writeReg PC (← readReg pc_reset_address)
  writeReg nextPC (← readReg pc_reset_address)
  writeReg mcause (zeros (n := 64))
  (csr_name_write_callback "mcause" (← readReg mcause))
  (reset_pmp ())
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 9 9
    (bool_to_bit (false : Bool)))
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 8 8
    (bool_to_bit (false : Bool)))
  if ((hartSupports Ext_Zicfilp) : Bool)
  then writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 10 10 0#1)
  else (pure ())
  (reset_stateen ())
  writeReg vstart (zeros (n := 64))
  writeReg vl (zeros (n := 64))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 0b00#2)
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 1) (64 -i 1) 1#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 2) 8
    (zeros (n := (64 -i 9))))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 7 7 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 6 6 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 5 3 0b000#3)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 2 0 0b000#3)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_add_meta (r : (Result k_t (physaddr × ExceptionType))) (m : Unit) : (Result (k_t × Unit) (physaddr × ExceptionType)) :=
  match r with
  | .Ok v => (Ok (v, m))
  | .Err e => (Err e)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_drop_meta (r : (Result (k_t × Unit) (physaddr × ExceptionType))) : (Result k_t (physaddr × ExceptionType)) :=
  match r with
  | .Ok (v, _m) => (Ok v)
  | .Err e => (Err e)

