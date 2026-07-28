import Out.Flow
import Out.Prelude
import Out.Errors
import Out.MemAddrtype
import Out.Common0
import Out.RvfiDii
import Out.PlatformConfig
import Out.Types
import Out.Callbacks
import Out.Regs
import Out.PcAccess
import Out.SysRegs
import Out.ExtRegs
import Out.AddrChecks
import Out.SysExceptions
import Out.ZicfilpRegs
import Out.SysControl
import Out.Platform
import Out.Callbacks0
import Out.InstsBegin
import Out.ZicfilpInsts
import Out.InstsEnd
import Out.StepCommon
import Out.StepExt
import Out.DecodeExt
import Out.Fetch

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

/-- Type quantifiers: k_ex503796_ : Bool, _step_no : Nat, 0 ≤ _step_no -/
def run_hart_waiting (_step_no : Nat) (wr : WaitReason) (instbits : (BitVec 32)) (exit_wait : Bool) : SailM Step := do
  if ((← (shouldWakeForInterrupt ())) : Bool)
  then
    (do
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "interrupt exit from "
              (HAppend.hAppend (wait_name_forwards wr)
                (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
      else (pure ())
      writeReg hart_state (HART_ACTIVE ())
      (pure (Step_Execute ((Retire_Success ()), instbits))))
  else
    (do
      match (wr, (valid_reservation ()), exit_wait) with
      | (.WAIT_WRS_STO, false, _) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "reservation invalid exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_STO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          (pure (Step_Execute ((Retire_Success ()), instbits))))
      | (.WAIT_WRS_NTO, false, _) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "reservation invalid exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_NTO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          (pure (Step_Execute ((Retire_Success ()), instbits))))
      | (.WAIT_WFI, _, true) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "forced exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WFI)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          let is_illegal ← do
            (pure (((bne (← readReg cur_privilege) Machine) && ((_get_Mstatus_TW
                      (← readReg mstatus)) == 1#1)) || (((← readReg cur_privilege) == User) && (← (currentlyEnabled
                      Ext_S)))))
          if (is_illegal : Bool)
          then (pure (Step_Execute ((Illegal_Instruction ()), instbits)))
          else (pure (Step_Execute ((Retire_Success ()), instbits))))
      | (.WAIT_WRS_STO, _, true) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "timed-out exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_STO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          (pure (Step_Execute ((Retire_Success ()), instbits))))
      | (.WAIT_WRS_NTO, _, true) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "timed-out exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_NTO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          if ((((← readReg cur_privilege) == Machine) || ((_get_Mstatus_TW (← readReg mstatus)) == 0#1)) : Bool)
          then (pure (Step_Execute ((Retire_Success ()), instbits)))
          else (pure (Step_Execute ((Illegal_Instruction ()), instbits))))
      | (_, _, false) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "remaining in "
                  (HAppend.hAppend (wait_name_forwards wr)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          (pure (Step_Waiting wr))))

/-- Type quantifiers: step_no : Nat, 0 ≤ step_no -/
def run_hart_active (step_no : Nat) : SailM Step := SailME.run do
  match (← (dispatchInterrupt (← readReg cur_privilege))) with
  | .some (intr, priv) => SailME.throw ((Step_Pending_Interrupt (intr, priv)) : Step)
  | none => (pure ())
  match (ext_fetch_hook (← (fetch ()))) with
  | .F_Ext_Error e => (pure (Step_Ext_Fetch_Failure e))
  | .F_Error (e, addr) => (pure (Step_Fetch_Failure ((Virtaddr addr), e)))
  | .F_RVC h =>
    (do
      let _ : Unit := (sail_instr_announce h)
      let _ : Unit := (fetch_callback h)
      let instbits : instbits := (zero_extend (m := 32) h)
      let instruction := (ext_decode_compressed h)
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_log_instr
            (HAppend.hAppend "["
              (HAppend.hAppend (Int.repr step_no)
                (HAppend.hAppend "] ["
                  (HAppend.hAppend (← (privLevel_to_str (← readReg cur_privilege)))
                    (HAppend.hAppend "]: "
                      (HAppend.hAppend (BitVec.toFormatted (← readReg PC))
                        (HAppend.hAppend " ("
                          (HAppend.hAppend (BitVec.toFormatted h)
                            (HAppend.hAppend ") " (← (instruction_to_str instruction)))))))))))
            (zero_extend (m := 64) (← readReg PC))))
      else (pure ())
      if ((← (is_landing_pad_expected ())) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          (pure (Step_Execute (r, instbits))))
      else
        (do
          if ((← (currentlyEnabled Ext_Zca)) : Bool)
          then
            (do
              writeReg nextPC (BitVec.addInt (← readReg PC) 2)
              let result ← (( do
                match (← (execute instruction)) with
                | .ExecuteAs other_inst => (execute other_inst)
                | result => (pure result) ) : SailME Step ExecutionResult )
              (pure (Step_Execute (result, instbits))))
          else (pure (Step_Execute ((Illegal_Instruction ()), instbits)))))
  | .F_Base w =>
    (do
      let _ : Unit := (sail_instr_announce w)
      let _ : Unit := (fetch_callback w)
      let instbits : instbits := (zero_extend (m := 32) w)
      let instruction ← do (ext_decode w)
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_log_instr
            (HAppend.hAppend "["
              (HAppend.hAppend (Int.repr step_no)
                (HAppend.hAppend "] ["
                  (HAppend.hAppend (← (privLevel_to_str (← readReg cur_privilege)))
                    (HAppend.hAppend "]: "
                      (HAppend.hAppend (BitVec.toFormatted (← readReg PC))
                        (HAppend.hAppend " ("
                          (HAppend.hAppend (BitVec.toFormatted w)
                            (HAppend.hAppend ") " (← (instruction_to_str instruction)))))))))))
            (zero_extend (m := 64) (← readReg PC))))
      else (pure ())
      if (((← (is_landing_pad_expected ())) && (not (is_lpad_instruction instruction))) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          (pure (Step_Execute (r, instbits))))
      else
        (do
          writeReg nextPC (BitVec.addInt (← readReg PC) 4)
          let result ← (( do
            match (← (execute instruction)) with
            | .ExecuteAs other_inst => (execute other_inst)
            | result => (pure result) ) : SailME Step ExecutionResult )
          (pure (Step_Execute (result, instbits)))))

def wait_is_nop (wr : WaitReason) : Bool :=
  match wr with
  | .WAIT_WFI => false
  | .WAIT_WRS_STO => false
  | .WAIT_WRS_NTO => false

/-- Type quantifiers: k_ex503851_ : Bool, step_no : Nat, 0 ≤ step_no -/
def try_step (step_no : Nat) (exit_wait : Bool) : SailM Bool := do
  let _ : Unit := (ext_pre_step_hook ())
  writeReg minstret_increment (← (should_inc_minstret (← readReg cur_privilege)))
  let step_val ← (( do
    match (← readReg hart_state) with
    | .HART_WAITING (wr, instbits) => (run_hart_waiting step_no wr instbits exit_wait)
    | .HART_ACTIVE () => (run_hart_active step_no) ) : SailM Step )
  match step_val with
  | .Step_Pending_Interrupt (intr, priv) =>
    (do
      let _ : Unit :=
        if ((get_config_print_instr ()) : Bool)
        then (print_bits "Handling interrupt: " (interruptType_bits_forwards intr))
        else ()
      (handle_interrupt intr priv))
  | .Step_Ext_Fetch_Failure e => (pure (ext_handle_fetch_check_error e))
  | .Step_Fetch_Failure (vaddr, e) => (handle_exception (bits_of_virtaddr vaddr) e)
  | .Step_Waiting _ =>
    assert (hart_is_waiting (← readReg hart_state)) "cannot be Waiting in a non-Wait state"
  | .Step_Execute (.Retire_Success (), _) =>
    assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:219.74-219.75"
  | .Step_Execute (.ExecuteAs _, _) =>
    (internal_error "postlude/step.sail" 223
      "Multiple chained ExecuteAs (only one redirection is supported).")
  | .Step_Execute (.Trap (priv, exc, pc), _) => (set_next_pc (← (exception_handler priv exc pc)))
  | .Step_Execute (.Illegal_Instruction (), instbits) =>
    (handle_exception (zero_extend (m := 64) instbits) (E_Illegal_Instr ()))
  | .Step_Execute (.Virtual_Instruction (), instbits) =>
    (handle_exception (zero_extend (m := 64) instbits) (E_Virtual_Instr ()))
  | .Step_Execute (.Enter_Wait wr, instbits) =>
    (do
      if ((wait_is_nop wr) : Bool)
      then assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:232.41-232.42"
      else
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "entering "
                  (HAppend.hAppend (wait_name_forwards wr)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_WAITING (wr, instbits))))
  | .Step_Execute (.Ext_CSR_Check_Failure (), _) => (pure (ext_check_CSR_fail ()))
  | .Step_Execute (.Ext_ControlAddr_Check_Failure e, _) => (pure (ext_handle_control_check_error e))
  | .Step_Execute (.Ext_DataAddr_Check_Failure e, _) => (pure (ext_handle_data_check_error e))
  | .Step_Execute (.Ext_XRET_Priv_Failure (), _) => (pure (ext_fail_xret_priv ()))
  match (← readReg hart_state) with
  | .HART_WAITING _ => (pure true)
  | .HART_ACTIVE () =>
    (do
      (tick_pc ())
      let retired : Bool :=
        match step_val with
        | .Step_Execute (.Retire_Success (), g__0) => true
        | .Step_Execute (.Enter_Wait wr, g__1) =>
          (if ((wait_is_nop wr) : Bool)
          then true
          else false)
        | _ => false
      if ((retired && (← readReg minstret_increment)) : Bool)
      then writeReg minstret (BitVec.addInt (← readReg minstret) 1)
      else (pure ())
      if ((get_config_rvfi ()) : Bool)
      then
        writeReg rvfi_pc_data (Sail.BitVec.updateSubrange (← readReg rvfi_pc_data) 127 64
          (zero_extend (m := 64) (← (get_arch_pc ()))))
      else (pure ())
      let _ : Unit := (ext_post_step_hook ())
      let _ : Unit :=
        if (retired : Bool)
        then (instret_callback ())
        else ()
      (pure false))

def loop (_ : Unit) : SailM Nat := do
  let i : Nat := 0
  let step_no : Nat := 0
  let (i, step_no) ← (( do
    let mut loop_vars := (i, step_no)
    while (← (λ (i, step_no) => do (pure (not (← readReg htif_done)))) loop_vars) do
      let (i, step_no) := loop_vars
      loop_vars ← do
        let stepped ← do (try_step step_no true)
        let step_no ← (( do
          if (stepped : Bool)
          then
            (do
              let step_no : Nat := (step_no +i 1)
              let _ : Unit :=
                if ((get_config_print_instr ()) : Bool)
                then (print_step ())
                else ()
              (cycle_count ())
              (pure step_no))
          else (pure step_no) ) : SailM Nat )
        let i ← (( do
          if ((not (← readReg htif_done)) : Bool)
          then
            (do
              let i : Nat := (i +i 1)
              if ((i == plat_insns_per_tick) : Bool)
              then
                (do
                  (tick_clock ())
                  (pure 0))
              else (pure i))
          else (pure i) ) : SailM Nat )
        (pure (i, step_no))
    (pure loop_vars) ) : SailM (Nat × Nat) )
  let exit_val ← do (pure (BitVec.toNatInt (← readReg htif_exit_code)))
  let _ : Unit :=
    if ((exit_val == 0) : Bool)
    then (print_endline "SUCCESS")
    else (print_int "FAILURE: " exit_val)
  (pure exit_val)

