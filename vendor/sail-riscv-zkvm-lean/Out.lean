import Out.Flow
import Out.Common
import Out.Prelude
import Out.Xlen
import Out.PlatformConfig
import Out.SysRegs
import Out.InterruptRegs
import Out.SysControl
import Out.Platform
import Out.Pma
import Out.VmemTlb
import Out.Step
import Out.Main

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

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg fp_rounding_global fp_rounding_default
  writeReg misa (_update_Misa_MXL (Mk_Misa (zeros (n := 64))) (architecture_bits_forwards RV64))
  writeReg mstatus (let mxl := (architecture_bits_forwards RV64)
  (_update_Mstatus_UXL
    (_update_Mstatus_SXL (Mk_Mstatus (zeros (n := 64)))
      (if (((xlen != 32) && (hartSupports Ext_S)) : Bool)
      then mxl
      else (zeros (n := 2))))
    (if (((xlen != 32) && (hartSupports Ext_U)) : Bool)
    then mxl
    else (zeros (n := 2)))))
  writeReg hstateen0 (Mk_Hstateen0 (zeros (n := 64)))
  writeReg hstateen1 (Mk_Hstateen1 (zeros (n := 64)))
  writeReg hstateen2 (Mk_Hstateen2 (zeros (n := 64)))
  writeReg hstateen3 (Mk_Hstateen3 (zeros (n := 64)))
  writeReg mstateen0 (Mk_Mstateen0 (zeros (n := 64)))
  writeReg mstateen1 (Mk_Mstateen1 (zeros (n := 64)))
  writeReg mstateen2 (Mk_Mstateen2 (zeros (n := 64)))
  writeReg mstateen3 (Mk_Mstateen3 (zeros (n := 64)))
  writeReg sstateen0 (Mk_Sstateen0 (zeros (n := 32)))
  writeReg sstateen1 (Mk_Sstateen1 (zeros (n := 32)))
  writeReg sstateen2 (Mk_Sstateen2 (zeros (n := 32)))
  writeReg sstateen3 (Mk_Sstateen3 (zeros (n := 32)))
  writeReg senvcfg (← (legalize_senvcfg (Mk_SEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg mseccfg (← (legalize_mseccfg (Mk_Seccfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg menvcfg (← (legalize_menvcfg (Mk_MEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg mvendorid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg mimpid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg marchid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg mhartid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg mconfigptr (zeros (n := 64))
  writeReg sig_meip 0#1
  writeReg sig_seip 0#1
  writeReg pc_reset_address (zeros (n := 64))
  writeReg htif_tohost_base none
  writeReg htif_tohost (zeros (n := 64))
  writeReg htif_done false
  writeReg htif_exit_code (zeros (n := 64))
  writeReg htif_cmd_write (zeros (n := 1))
  writeReg htif_payload_writes (zeros (n := 4))
  writeReg pma_regions [{ base := 0b0000000000000000000000000000000000000000000000000001000000000000#64
                          size := 0b0000000000000000000000000000000000000000000000000001000000000000#64
                          attributes := { mem_type := IOMemory
                                          cacheable := true
                                          coherent := false
                                          executable := false
                                          readable := true
                                          writable := false
                                          read_idempotent := true
                                          write_idempotent := true
                                          misaligned_exceptions := { load_store := none
                                                                     vector := none
                                                                     amo := AccessFault }
                                          atomic_support := AMONone
                                          reservability := RsrvNone
                                          supports_cbo_zero := false
                                          supports_pte_read := false
                                          supports_pte_write := false }
                          include_in_device_tree := false }, { base := 0b0000000000000000000000000000000000000010000000000000000000000000#64
                                                               size := 0b0000000000000000000000000000000000010000000000000000000000000000#64
                                                               attributes := { mem_type := IOMemory
                                                                               cacheable := false
                                                                               coherent := true
                                                                               executable := false
                                                                               readable := true
                                                                               writable := true
                                                                               read_idempotent := false
                                                                               write_idempotent := false
                                                                               misaligned_exceptions := { load_store := none
                                                                                                          vector := none
                                                                                                          amo := AccessFault }
                                                                               atomic_support := AMONone
                                                                               reservability := RsrvNone
                                                                               supports_cbo_zero := false
                                                                               supports_pte_read := false
                                                                               supports_pte_write := false }
                                                               include_in_device_tree := false }, { base := 0b0000000000000000000000000000000010000000000000000000000000000000#64
                                                                                                    size := 0b0000000000000000000000000000000010000000000000000000000000000000#64
                                                                                                    attributes := { mem_type := MainMemory
                                                                                                                    cacheable := true
                                                                                                                    coherent := true
                                                                                                                    executable := true
                                                                                                                    readable := true
                                                                                                                    writable := true
                                                                                                                    read_idempotent := true
                                                                                                                    write_idempotent := true
                                                                                                                    misaligned_exceptions := { load_store := none
                                                                                                                                               vector := none
                                                                                                                                               amo := AccessFault }
                                                                                                                    atomic_support := AMOCASQ
                                                                                                                    reservability := RsrvEventual
                                                                                                                    supports_cbo_zero := true
                                                                                                                    supports_pte_read := true
                                                                                                                    supports_pte_write := true }
                                                                                                    include_in_device_tree := true }]
  writeReg tlb (vectorInit none)
  writeReg hart_state (HART_ACTIVE ())
  (pure (initialize_registers ()))

end Out.Functions

open Out.Functions

def main (_ : List String) : IO UInt32 := do
  main_of_sail_main ⟨default, (), default, default, default, default⟩ (sail_model_init >=> sail_main)
