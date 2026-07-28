import Out.Flow
import Out.Prelude
import Out.Errors
import Out.Xlen
import Out.Arithmetic
import Out.PlatformConfig
import Out.Types
import Out.Callbacks
import Out.Regs
import Out.PcAccess
import Out.SysRegs
import Out.SysExceptions
import Out.ZicfilpRegs
import Out.SysControl
import Out.VmemTlb
import Out.InstsBegin
import Out.VmemUtils
import Out.ZicfilpInsts
import Out.BaseInsts
import Out.MextInsts
import Out.ZicsrInsts

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

noncomputable def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__192 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__192 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then
      (let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__192 31 12)
      let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__192 31 12)
      (pure (some (LPAD lpl))))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__192 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__192 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__192 31 12)
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__192 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__192 11 7)
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__192 31 12)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__190 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__190 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__190 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__190 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__190 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__190 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__190 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__190 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__190 20 20)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (let imm := (((imm_19_19_ +++ imm_18_11_) +++ imm_10_10_) +++ imm_9_0_)
                  (JAL ((imm +++ 0#1), rd))))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__187 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__187 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__187 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__187 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__187 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__187 31 20)
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__187 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__187 19 15)
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__187 31 20)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some (JALR (imm, rs1, rd)))))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__185 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__185 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__185 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__185 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__185 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__185 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__185 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__185 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__185 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__185 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__185 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__185 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__185 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (let imm := (((imm_11_11_ +++ imm_10_10_) +++ imm_9_4_) +++ imm_3_0_)
                          (BTYPE ((imm +++ 0#1), rs2, rs1, op))))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__183 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__183 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__183 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__183 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__183 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__183 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__183 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__183 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__183 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__183 31 20)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__179 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__179 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__179 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__179 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__179 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some (SHIFTIOP (shamt, rs1, rd, SLLI))))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__175 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__175 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__175 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__175 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__175 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__175 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__175 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__175 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__175 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some (SHIFTIOP (shamt, rs1, rd, SRLI))))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__171 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__171 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__171 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__171 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__171 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__171 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__171 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__171 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__171 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some (SHIFTIOP (shamt, rs1, rd, SRAI))))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__167 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__167 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__167 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__167 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__167 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__167 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__167 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__167 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__167 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__167 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) =>
                                          (pure (some (RTYPE (rs2, rs1, rd, ADD)))))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__163 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__163 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__163 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__163 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__163 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__163 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__163 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__163 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__163 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__163 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) =>
                                              (pure (some (RTYPE (rs2, rs1, rd, SLT)))))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__159 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__159 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__159 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__159 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__159 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__159 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__159 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__159 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__159 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__159 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) =>
                                                  (pure (some (RTYPE (rs2, rs1, rd, SLTU)))))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__155 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__155 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__155 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__155 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__155 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__155 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__155 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__155 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__155 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__155 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) =>
                                                      (pure (some (RTYPE (rs2, rs1, rd, AND)))))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__151 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__151 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__151 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__151 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__151 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__151 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__151 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__151 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__151 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__151 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) =>
                                                          (pure (some (RTYPE (rs2, rs1, rd, OR)))))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__147 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__147 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__147 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__147 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__147 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__147 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__147 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__147 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__147 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__147 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) =>
                                                              (pure (some
                                                                  (RTYPE (rs2, rs1, rd, XOR)))))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__143 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__143 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__143 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__143 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__143 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__143 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__143 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__143 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__143 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__143 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some
                                                                      (RTYPE (rs2, rs1, rd, SLL)))))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__139 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__139 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__139 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__139 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__139 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__139 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__139 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__139
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__139
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__139
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some
                                                                          (RTYPE (rs2, rs1, rd, SRL)))))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__135 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__135 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__135 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__135 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__135 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__135 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__135 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__135 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__135 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__135 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some
                                                                              (RTYPE
                                                                                (rs2, rs1, rd, SUB)))))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__131 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__131 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__131 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__131 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__131 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__131 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__131 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__131 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__131 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__131 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some
                                                                                  (RTYPE
                                                                                    (rs2, rs1, rd, SRA)))))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__129 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__129 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__129 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__129 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__129 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__129 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__129 31 20)
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__129 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__129 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__129 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__129 19 15)
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__129 31 20)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bit_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some
                                                                                        (LOAD
                                                                                          (imm, rs1, rd, is_unsigned, width))))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__126 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__126 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__126 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__126 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__126 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__126 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__126 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__126 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__126 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__126 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__126 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__126 31 25)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((let imm :=
                                                                                           (imm_11_5_ +++ imm_4_0_)
                                                                                         (width ≤b xlen_bytes)) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (let imm :=
                                                                                              (imm_11_5_ +++ imm_4_0_)
                                                                                            (STORE
                                                                                              (imm, rs2, rs1, width)))))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__123 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__123
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__123
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__123
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__123
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__123
                                                                                            31 20)
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__123
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__123
                                                                                            19 15)
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__123
                                                                                            31 20)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                (ADDIW
                                                                                                  (imm, rs1, rd))))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__119 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__119
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__119
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__119
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__119
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__119
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__119
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__119
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__119
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__119
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    (RTYPEW
                                                                                                      (rs2, rs1, rd, ADDW))))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__115 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__115
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__115
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__115
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__115
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__115
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__115
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__115
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__115
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__115
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        (RTYPEW
                                                                                                          (rs2, rs1, rd, SUBW))))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__111 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__111
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__111
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__111
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__111
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__111
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__111
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__111
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__111
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__111
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            (RTYPEW
                                                                                                              (rs2, rs1, rd, SLLW))))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__107 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__107
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__107
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__107
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__107
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__107
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__107
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__107
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__107
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__107
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                (RTYPEW
                                                                                                                  (rs2, rs1, rd, SRLW))))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__103 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__103
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__103
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__103
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__103
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__103
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__103
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__103
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__103
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__103
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    (RTYPEW
                                                                                                                      (rs2, rs1, rd, SRAW))))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__99 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__99
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__99
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__99
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__99
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__99
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let shamt : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__99
                                                                                                                    24
                                                                                                                    20)
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__99
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__99
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        (SHIFTIWOP
                                                                                                                          (shamt, rs1, rd, SLLIW))))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__95 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__95
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__95
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__95
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__95
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__95
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let shamt : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__95
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__95
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__95
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            (SHIFTIWOP
                                                                                                                              (shamt, rs1, rd, SRLIW))))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__91 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__91
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__91
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__91
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__91
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__91
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let shamt : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__91
                                                                                                                            24
                                                                                                                            20)
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__91
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__91
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                (SHIFTIWOP
                                                                                                                                  (shamt, rs1, rd, SRAIW))))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__80 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__80 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (FENCE_TSO
                                                                                                                                ())))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__80
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__80
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__80
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__80
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__80
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                let succ : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__80
                                                                                                                                    23
                                                                                                                                    20)
                                                                                                                                let pred : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__80
                                                                                                                                    27
                                                                                                                                    24)
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__80
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__80
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__80
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping77_)), (← (encdec_reg_backwards
                                                                                                                                    mapping78_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (pure (some
                                                                                                                                      (FENCE
                                                                                                                                        (fm, pred, succ, rs, rd)))))
                                                                                                                            else
                                                                                                                              (pure none))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__43 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__43 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  (ECALL
                                                                                                                                    ())))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__43 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (MRET
                                                                                                                                        ())))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__43 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          (SRET
                                                                                                                                            ())))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__43 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (EBREAK
                                                                                                                                                ())))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__43 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (WFI
                                                                                                                                                    ())))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__43
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__43
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__43
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__43
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__43
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__43
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping79_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping80_))) with
                                                                                                                                                    | (rs2, rs1) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((← (virtual_memory_supported
                                                                                                                                                                 ())) || (not
                                                                                                                                                               (true : Bool))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (SFENCE_VMA
                                                                                                                                                                (rs1, rs2))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none))))))) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__40 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping84_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__40
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping83_ : (BitVec 3) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__40
                                                                                                                                         14
                                                                                                                                         12)
                                                                                                                                     let mapping82_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__40
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__40
                                                                                                                                         24
                                                                                                                                         20)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_reg_backwards_matches
                                                                                                                                           mapping82_) && ((encdec_mul_op_backwards_matches
                                                                                                                                             mapping83_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping84_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__40
                                                                                                                                           31
                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__40
                                                                                                                                           6
                                                                                                                                           0) == (0b0110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping84_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__40
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping83_ : (BitVec 3) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__40
                                                                                                                                        14
                                                                                                                                        12)
                                                                                                                                    let mapping82_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__40
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__40
                                                                                                                                        24
                                                                                                                                        20)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_reg_backwards
                                                                                                                                        mapping82_)), (← (encdec_mul_op_backwards
                                                                                                                                        mapping83_)), (← (encdec_reg_backwards
                                                                                                                                        mapping84_))) with
                                                                                                                                    | (rs2, rs1, mul_op, rd) =>
                                                                                                                                      (do
                                                                                                                                        if (((← (currentlyEnabled
                                                                                                                                                 Ext_M)) || (← (currentlyEnabled
                                                                                                                                                 Ext_Zmmul))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (MUL
                                                                                                                                                (rs2, rs1, rd, mul_op))))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__36 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping88_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__36
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping87_ : (BitVec 1) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__36
                                                                                                                                             12
                                                                                                                                             12)
                                                                                                                                         let mapping86_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__36
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__36
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping85_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping86_) && ((bool_bit_backwards_matches
                                                                                                                                                 mapping87_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping88_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__36
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                 v__36
                                                                                                                                                 14
                                                                                                                                                 13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__36
                                                                                                                                                 6
                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping88_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__36
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping87_ : (BitVec 1) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__36
                                                                                                                                            12
                                                                                                                                            12)
                                                                                                                                        let mapping86_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__36
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__36
                                                                                                                                            24
                                                                                                                                            20)
                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                            mapping85_)), (← (encdec_reg_backwards
                                                                                                                                            mapping86_)), (bool_bit_backwards
                                                                                                                                          mapping87_), (← (encdec_reg_backwards
                                                                                                                                            mapping88_))) with
                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                          (do
                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                   Ext_M)) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (DIV
                                                                                                                                                    (rs2, rs1, rd, is_unsigned))))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__32 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping92_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__32
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping91_ : (BitVec 1) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__32
                                                                                                                                                 12
                                                                                                                                                 12)
                                                                                                                                             let mapping90_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__32
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping89_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__32
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping89_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping90_) && ((bool_bit_backwards_matches
                                                                                                                                                     mapping91_) && (encdec_reg_backwards_matches
                                                                                                                                                     mapping92_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__32
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__32
                                                                                                                                                     14
                                                                                                                                                     13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__32
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping92_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__32
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping91_ : (BitVec 1) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__32
                                                                                                                                                12
                                                                                                                                                12)
                                                                                                                                            let mapping90_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__32
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping89_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__32
                                                                                                                                                24
                                                                                                                                                20)
                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                mapping89_)), (← (encdec_reg_backwards
                                                                                                                                                mapping90_)), (bool_bit_backwards
                                                                                                                                              mapping91_), (← (encdec_reg_backwards
                                                                                                                                                mapping92_))) with
                                                                                                                                            | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                              (do
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_M)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      (REM
                                                                                                                                                        (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__28 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping95_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__28
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__28
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping93_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__28
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping93_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping94_) && (encdec_reg_backwards_matches
                                                                                                                                                       mapping95_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__28
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__28
                                                                                                                                                         14
                                                                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__28
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping95_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__28
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__28
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping93_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__28
                                                                                                                                                    24
                                                                                                                                                    20)
                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                    mapping93_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping94_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping95_))) with
                                                                                                                                                | (rs2, rs1, rd) =>
                                                                                                                                                  (do
                                                                                                                                                    if (((xlen == 64) && ((← (currentlyEnabled
                                                                                                                                                               Ext_M)) || (← (currentlyEnabled
                                                                                                                                                               Ext_Zmmul)))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (pure (some
                                                                                                                                                          (MULW
                                                                                                                                                            (rs2, rs1, rd))))
                                                                                                                                                    else
                                                                                                                                                      (pure none)))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (do
                                                                                                                                              match (← do
                                                                                                                                                let v__24 :=
                                                                                                                                                  head_exp_
                                                                                                                                                if (((let mapping99_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__24
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping98_ : (BitVec 1) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__24
                                                                                                                                                         12
                                                                                                                                                         12)
                                                                                                                                                     let mapping97_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__24
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping96_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__24
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping96_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping97_) && ((bool_bit_backwards_matches
                                                                                                                                                             mapping98_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping99_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__24
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__24
                                                                                                                                                             14
                                                                                                                                                             13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__24
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping99_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__24
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping98_ : (BitVec 1) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__24
                                                                                                                                                        12
                                                                                                                                                        12)
                                                                                                                                                    let mapping97_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__24
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping96_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__24
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping96_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping97_)), (bool_bit_backwards
                                                                                                                                                      mapping98_), (← (encdec_reg_backwards
                                                                                                                                                        mapping99_))) with
                                                                                                                                                    | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                 Ext_M))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (DIVW
                                                                                                                                                                (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none)) with
                                                                                                                                              | .some result =>
                                                                                                                                                (pure result)
                                                                                                                                              | none =>
                                                                                                                                                (do
                                                                                                                                                  match (← do
                                                                                                                                                    let v__20 :=
                                                                                                                                                      head_exp_
                                                                                                                                                    if (((let mapping103_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__20
                                                                                                                                                             11
                                                                                                                                                             7)
                                                                                                                                                         let mapping102_ : (BitVec 1) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__20
                                                                                                                                                             12
                                                                                                                                                             12)
                                                                                                                                                         let mapping101_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__20
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping100_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__20
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping100_) && ((encdec_reg_backwards_matches
                                                                                                                                                               mapping101_) && ((bool_bit_backwards_matches
                                                                                                                                                                 mapping102_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping103_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__20
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                 v__20
                                                                                                                                                                 14
                                                                                                                                                                 13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                 v__20
                                                                                                                                                                 6
                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping103_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__20
                                                                                                                                                            11
                                                                                                                                                            7)
                                                                                                                                                        let mapping102_ : (BitVec 1) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__20
                                                                                                                                                            12
                                                                                                                                                            12)
                                                                                                                                                        let mapping101_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__20
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping100_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__20
                                                                                                                                                            24
                                                                                                                                                            20)
                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                            mapping100_)), (← (encdec_reg_backwards
                                                                                                                                                            mapping101_)), (bool_bit_backwards
                                                                                                                                                          mapping102_), (← (encdec_reg_backwards
                                                                                                                                                            mapping103_))) with
                                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                          (do
                                                                                                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                     Ext_M))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (pure (some
                                                                                                                                                                  (REMW
                                                                                                                                                                    (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                            else
                                                                                                                                                              (pure none)))
                                                                                                                                                    else
                                                                                                                                                      (pure none)) with
                                                                                                                                                  | .some result =>
                                                                                                                                                    (pure result)
                                                                                                                                                  | none =>
                                                                                                                                                    (do
                                                                                                                                                      match (← do
                                                                                                                                                        let v__17 :=
                                                                                                                                                          head_exp_
                                                                                                                                                        if (((let mapping106_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__17
                                                                                                                                                                 11
                                                                                                                                                                 7)
                                                                                                                                                             let mapping105_ : (BitVec 2) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__17
                                                                                                                                                                 13
                                                                                                                                                                 12)
                                                                                                                                                             let mapping104_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__17
                                                                                                                                                                 19
                                                                                                                                                                 15)
                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                 mapping104_) && ((encdec_csrop_backwards_matches
                                                                                                                                                                   mapping105_) && (encdec_reg_backwards_matches
                                                                                                                                                                   mapping106_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                   v__17
                                                                                                                                                                   14
                                                                                                                                                                   14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                   v__17
                                                                                                                                                                   6
                                                                                                                                                                   0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let csr : (BitVec 12) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__17
                                                                                                                                                                31
                                                                                                                                                                20)
                                                                                                                                                            let mapping106_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__17
                                                                                                                                                                11
                                                                                                                                                                7)
                                                                                                                                                            let mapping105_ : (BitVec 2) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__17
                                                                                                                                                                13
                                                                                                                                                                12)
                                                                                                                                                            let mapping104_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__17
                                                                                                                                                                19
                                                                                                                                                                15)
                                                                                                                                                            let csr : (BitVec 12) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__17
                                                                                                                                                                31
                                                                                                                                                                20)
                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                mapping104_)), (← (encdec_csrop_backwards
                                                                                                                                                                mapping105_)), (← (encdec_reg_backwards
                                                                                                                                                                mapping106_))) with
                                                                                                                                                            | (rs1, op, rd) =>
                                                                                                                                                              (do
                                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                                       Ext_Zicsr)) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (pure (some
                                                                                                                                                                      (CSRReg
                                                                                                                                                                        (csr, rs1, rd, op))))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)))
                                                                                                                                                        else
                                                                                                                                                          (pure none)) with
                                                                                                                                                      | .some result =>
                                                                                                                                                        (pure result)
                                                                                                                                                      | none =>
                                                                                                                                                        (do
                                                                                                                                                          match (← do
                                                                                                                                                            let v__14 :=
                                                                                                                                                              head_exp_
                                                                                                                                                            if (((let mapping108_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__14
                                                                                                                                                                     11
                                                                                                                                                                     7)
                                                                                                                                                                 let mapping107_ : (BitVec 2) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__14
                                                                                                                                                                     13
                                                                                                                                                                     12)
                                                                                                                                                                 ((encdec_csrop_backwards_matches
                                                                                                                                                                     mapping107_) && (encdec_reg_backwards_matches
                                                                                                                                                                     mapping108_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                       v__14
                                                                                                                                                                       14
                                                                                                                                                                       14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                       v__14
                                                                                                                                                                       6
                                                                                                                                                                       0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let csr : (BitVec 12) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__14
                                                                                                                                                                    31
                                                                                                                                                                    20)
                                                                                                                                                                let mapping108_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__14
                                                                                                                                                                    11
                                                                                                                                                                    7)
                                                                                                                                                                let mapping107_ : (BitVec 2) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__14
                                                                                                                                                                    13
                                                                                                                                                                    12)
                                                                                                                                                                let imm : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__14
                                                                                                                                                                    19
                                                                                                                                                                    15)
                                                                                                                                                                let csr : (BitVec 12) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__14
                                                                                                                                                                    31
                                                                                                                                                                    20)
                                                                                                                                                                match ((← (encdec_csrop_backwards
                                                                                                                                                                    mapping107_)), (← (encdec_reg_backwards
                                                                                                                                                                    mapping108_))) with
                                                                                                                                                                | (op, rd) =>
                                                                                                                                                                  (do
                                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                                           Ext_Zicsr)) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (pure (some
                                                                                                                                                                          (CSRImm
                                                                                                                                                                            (csr, imm, rd, op))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure none)))
                                                                                                                                                            else
                                                                                                                                                              (pure none)) with
                                                                                                                                                          | .some result =>
                                                                                                                                                            (pure result)
                                                                                                                                                          | none =>
                                                                                                                                                            (match head_exp_ with
                                                                                                                                                            | s =>
                                                                                                                                                              (pure (ILLEGAL
                                                                                                                                                                  s)))))))))))))))))))))))))))))))))))))))))

noncomputable def encdec_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure true)
      else (pure false))
  | .UTYPE (imm, rd, op) => (pure true)
  | .JAL (v__196, rd) =>
    (if (((Sail.BitVec.extractLsb v__196 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .JALR (imm, rs1, rd) => (pure true)
  | .BTYPE (v__198, rs2, rs1, op) =>
    (if (((Sail.BitVec.extractLsb v__198 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .ITYPE (imm, rs1, rd, op) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SLLI) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SRLI) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SRAI) => (pure true)
  | .RTYPE (rs2, rs1, rd, .ADD) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLT) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLTU) => (pure true)
  | .RTYPE (rs2, rs1, rd, .AND) => (pure true)
  | .RTYPE (rs2, rs1, rd, .OR) => (pure true)
  | .RTYPE (rs2, rs1, rd, .XOR) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLL) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SRL) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SUB) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SRA) => (pure true)
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (if ((valid_load_encdec width is_unsigned) : Bool)
    then (pure true)
    else (pure false))
  | .STORE (imm, rs2, rs1, width) => (pure true)
  | .ADDIW (imm, rs1, rd) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .ADDW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SUBW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SLLW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SRLW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SRAW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SLLIW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SRLIW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SRAIW) => (pure true)
  | .FENCE_TSO () => (pure true)
  | .FENCE (fm, pred, succ, rs, rd) => (pure true)
  | .ECALL () => (pure true)
  | .MRET () => (pure true)
  | .SRET () => (pure true)
  | .EBREAK () => (pure true)
  | .WFI () => (pure true)
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then (pure true)
      else (pure false))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      if (((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul))) : Bool)
      then (pure true)
      else (pure false))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then (pure true)
      else (pure false))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then (pure true)
      else (pure false))
  | .MULW (rs2, rs1, rd) =>
    (do
      if (((xlen == 64) && ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul)))) : Bool)
      then (pure true)
      else (pure false))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then (pure true)
      else (pure false))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then (pure true)
      else (pure false))
  | .CSRReg (csr, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .CSRImm (csr, imm, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .ILLEGAL s => (pure true)
  | _ => (pure false)

noncomputable def encdec_backwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__378 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__378 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then (pure (some true))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__378 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__378 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__378 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__378 11 7)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__376 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__376 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__376 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__376 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__376 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__376 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__376 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__376 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__376 20 20)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (let imm := (((imm_19_19_ +++ imm_18_11_) +++ imm_10_10_) +++ imm_9_0_)
                  true))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__373 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__373 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__373 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__373 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__373 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__373 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__373 19 15)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some true)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__371 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__371 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__371 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__371 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__371 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__371 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__371 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__371 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__371 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__371 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__371 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__371 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__371 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (let imm := (((imm_11_11_ +++ imm_10_10_) +++ imm_9_4_) +++ imm_3_0_)
                          true))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__369 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__369 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__369 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__369 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__369 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__369 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__369 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__369 11 7)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some true)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__365 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__365 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__365 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__365 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__365 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__365 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__365 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__365 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__365 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some true))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__361 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__361 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__361 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__361 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__361 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__361 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__361 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__361 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__361 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some true))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__357 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__357 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__357 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__357 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__357 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__357 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__357 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__357 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__357 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some true))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__353 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__353 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__353 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__353 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__353 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__353 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__353 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__353 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__353 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__353 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) => (pure (some true)))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__349 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__349 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__349 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__349 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__349 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__349 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__349 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__349 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__349 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__349 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) => (pure (some true)))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__345 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__345 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__345 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__345 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__345 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__345 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__345 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__345 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__345 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__345 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) => (pure (some true)))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__341 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__341 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__341 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__341 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__341 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__341 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__341 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__341 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__341 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__341 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) => (pure (some true)))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__337 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__337 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__337 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__337 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__337 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__337 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__337 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__337 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__337 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__337 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) => (pure (some true)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__333 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__333 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__333 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__333 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__333 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__333 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__333 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__333 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__333 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__333 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) => (pure (some true)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__329 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__329 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__329 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__329 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__329 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__329 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__329 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__329 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__329 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__329 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some true)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__325 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__325 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__325 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__325 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__325 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__325 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__325 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__325
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__325
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__325
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some true)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__321 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__321 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__321 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__321 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__321 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__321 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__321 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__321 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__321 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__321 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some true)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__317 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__317 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__317 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__317 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__317 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__317 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__317 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__317 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__317 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__317 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some true)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__315 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__315 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__315 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__315 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__315 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__315 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__315 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__315 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__315 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__315 19 15)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bit_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some true))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__312 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__312 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__312 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__312 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__312 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__312 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__312 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__312 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__312 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__312 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__312 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__312 31 25)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((let imm :=
                                                                                           (imm_11_5_ +++ imm_4_0_)
                                                                                         (width ≤b xlen_bytes)) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (let imm :=
                                                                                              (imm_11_5_ +++ imm_4_0_)
                                                                                            true)))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__309 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__309
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__309
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__309
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__309
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__309
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__309
                                                                                            19 15)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                true))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__305 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__305
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__305
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__305
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__305
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__305
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__305
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__305
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__305
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__305
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    true))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__301 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__301
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__301
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__301
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__301
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__301
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__301
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__301
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__301
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__301
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        true))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__297 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__297
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__297
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__297
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__297
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__297
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__297
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__297
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__297
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__297
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            true))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__293 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__293
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__293
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__293
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__293
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__293
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__293
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__293
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__293
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__293
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                true))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__289 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__289
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__289
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__289
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__289
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__289
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__289
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__289
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__289
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__289
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    true))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__285 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__285
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__285
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__285
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__285
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__285
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__285
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__285
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        true))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__281 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__281
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__281
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__281
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__281
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__281
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__281
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__281
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            true))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__277 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__277
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__277
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__277
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__277
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__277
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__277
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__277
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                true))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__266 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__266 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__266
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__266
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__266
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__266
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__266
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__266
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping77_)), (← (encdec_reg_backwards
                                                                                                                                    mapping78_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (pure (some
                                                                                                                                      true)))
                                                                                                                            else
                                                                                                                              (pure none))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__229 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__229 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  true))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__229 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      true))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__229 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          true))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__229 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__229 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__229
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__229
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__229
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__229
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__229
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__229
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping79_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping80_))) with
                                                                                                                                                    | (rs2, rs1) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((← (virtual_memory_supported
                                                                                                                                                                 ())) || (not
                                                                                                                                                               (true : Bool))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              true))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none))))))) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__226 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping84_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__226
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping83_ : (BitVec 3) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__226
                                                                                                                                         14
                                                                                                                                         12)
                                                                                                                                     let mapping82_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__226
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__226
                                                                                                                                         24
                                                                                                                                         20)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_reg_backwards_matches
                                                                                                                                           mapping82_) && ((encdec_mul_op_backwards_matches
                                                                                                                                             mapping83_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping84_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__226
                                                                                                                                           31
                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__226
                                                                                                                                           6
                                                                                                                                           0) == (0b0110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping84_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__226
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping83_ : (BitVec 3) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__226
                                                                                                                                        14
                                                                                                                                        12)
                                                                                                                                    let mapping82_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__226
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__226
                                                                                                                                        24
                                                                                                                                        20)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_reg_backwards
                                                                                                                                        mapping82_)), (← (encdec_mul_op_backwards
                                                                                                                                        mapping83_)), (← (encdec_reg_backwards
                                                                                                                                        mapping84_))) with
                                                                                                                                    | (rs2, rs1, mul_op, rd) =>
                                                                                                                                      (do
                                                                                                                                        if (((← (currentlyEnabled
                                                                                                                                                 Ext_M)) || (← (currentlyEnabled
                                                                                                                                                 Ext_Zmmul))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__222 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping88_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__222
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping87_ : (BitVec 1) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__222
                                                                                                                                             12
                                                                                                                                             12)
                                                                                                                                         let mapping86_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__222
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__222
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping85_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping86_) && ((bool_bit_backwards_matches
                                                                                                                                                 mapping87_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping88_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__222
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                 v__222
                                                                                                                                                 14
                                                                                                                                                 13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__222
                                                                                                                                                 6
                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping88_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__222
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping87_ : (BitVec 1) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__222
                                                                                                                                            12
                                                                                                                                            12)
                                                                                                                                        let mapping86_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__222
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__222
                                                                                                                                            24
                                                                                                                                            20)
                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                            mapping85_)), (← (encdec_reg_backwards
                                                                                                                                            mapping86_)), (bool_bit_backwards
                                                                                                                                          mapping87_), (← (encdec_reg_backwards
                                                                                                                                            mapping88_))) with
                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                          (do
                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                   Ext_M)) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__218 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping92_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__218
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping91_ : (BitVec 1) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__218
                                                                                                                                                 12
                                                                                                                                                 12)
                                                                                                                                             let mapping90_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__218
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping89_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__218
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping89_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping90_) && ((bool_bit_backwards_matches
                                                                                                                                                     mapping91_) && (encdec_reg_backwards_matches
                                                                                                                                                     mapping92_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__218
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__218
                                                                                                                                                     14
                                                                                                                                                     13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__218
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping92_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__218
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping91_ : (BitVec 1) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__218
                                                                                                                                                12
                                                                                                                                                12)
                                                                                                                                            let mapping90_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__218
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping89_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__218
                                                                                                                                                24
                                                                                                                                                20)
                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                mapping89_)), (← (encdec_reg_backwards
                                                                                                                                                mapping90_)), (bool_bit_backwards
                                                                                                                                              mapping91_), (← (encdec_reg_backwards
                                                                                                                                                mapping92_))) with
                                                                                                                                            | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                              (do
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_M)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      true))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__214 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping95_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__214
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__214
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping93_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__214
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping93_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping94_) && (encdec_reg_backwards_matches
                                                                                                                                                       mapping95_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__214
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__214
                                                                                                                                                         14
                                                                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__214
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping95_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__214
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__214
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping93_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__214
                                                                                                                                                    24
                                                                                                                                                    20)
                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                    mapping93_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping94_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping95_))) with
                                                                                                                                                | (rs2, rs1, rd) =>
                                                                                                                                                  (do
                                                                                                                                                    if (((xlen == 64) && ((← (currentlyEnabled
                                                                                                                                                               Ext_M)) || (← (currentlyEnabled
                                                                                                                                                               Ext_Zmmul)))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (pure (some
                                                                                                                                                          true))
                                                                                                                                                    else
                                                                                                                                                      (pure none)))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (do
                                                                                                                                              match (← do
                                                                                                                                                let v__210 :=
                                                                                                                                                  head_exp_
                                                                                                                                                if (((let mapping99_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__210
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping98_ : (BitVec 1) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__210
                                                                                                                                                         12
                                                                                                                                                         12)
                                                                                                                                                     let mapping97_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__210
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping96_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__210
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping96_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping97_) && ((bool_bit_backwards_matches
                                                                                                                                                             mapping98_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping99_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__210
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__210
                                                                                                                                                             14
                                                                                                                                                             13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__210
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping99_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__210
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping98_ : (BitVec 1) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__210
                                                                                                                                                        12
                                                                                                                                                        12)
                                                                                                                                                    let mapping97_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__210
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping96_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__210
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping96_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping97_)), (bool_bit_backwards
                                                                                                                                                      mapping98_), (← (encdec_reg_backwards
                                                                                                                                                        mapping99_))) with
                                                                                                                                                    | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                 Ext_M))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              true))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none)) with
                                                                                                                                              | .some result =>
                                                                                                                                                (pure result)
                                                                                                                                              | none =>
                                                                                                                                                (do
                                                                                                                                                  match (← do
                                                                                                                                                    let v__206 :=
                                                                                                                                                      head_exp_
                                                                                                                                                    if (((let mapping103_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__206
                                                                                                                                                             11
                                                                                                                                                             7)
                                                                                                                                                         let mapping102_ : (BitVec 1) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__206
                                                                                                                                                             12
                                                                                                                                                             12)
                                                                                                                                                         let mapping101_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__206
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping100_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__206
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping100_) && ((encdec_reg_backwards_matches
                                                                                                                                                               mapping101_) && ((bool_bit_backwards_matches
                                                                                                                                                                 mapping102_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping103_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__206
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                 v__206
                                                                                                                                                                 14
                                                                                                                                                                 13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                 v__206
                                                                                                                                                                 6
                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping103_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__206
                                                                                                                                                            11
                                                                                                                                                            7)
                                                                                                                                                        let mapping102_ : (BitVec 1) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__206
                                                                                                                                                            12
                                                                                                                                                            12)
                                                                                                                                                        let mapping101_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__206
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping100_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__206
                                                                                                                                                            24
                                                                                                                                                            20)
                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                            mapping100_)), (← (encdec_reg_backwards
                                                                                                                                                            mapping101_)), (bool_bit_backwards
                                                                                                                                                          mapping102_), (← (encdec_reg_backwards
                                                                                                                                                            mapping103_))) with
                                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                          (do
                                                                                                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                     Ext_M))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (pure (some
                                                                                                                                                                  true))
                                                                                                                                                            else
                                                                                                                                                              (pure none)))
                                                                                                                                                    else
                                                                                                                                                      (pure none)) with
                                                                                                                                                  | .some result =>
                                                                                                                                                    (pure result)
                                                                                                                                                  | none =>
                                                                                                                                                    (do
                                                                                                                                                      match (← do
                                                                                                                                                        let v__203 :=
                                                                                                                                                          head_exp_
                                                                                                                                                        if (((let mapping106_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__203
                                                                                                                                                                 11
                                                                                                                                                                 7)
                                                                                                                                                             let mapping105_ : (BitVec 2) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__203
                                                                                                                                                                 13
                                                                                                                                                                 12)
                                                                                                                                                             let mapping104_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__203
                                                                                                                                                                 19
                                                                                                                                                                 15)
                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                 mapping104_) && ((encdec_csrop_backwards_matches
                                                                                                                                                                   mapping105_) && (encdec_reg_backwards_matches
                                                                                                                                                                   mapping106_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                   v__203
                                                                                                                                                                   14
                                                                                                                                                                   14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                   v__203
                                                                                                                                                                   6
                                                                                                                                                                   0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let mapping106_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__203
                                                                                                                                                                11
                                                                                                                                                                7)
                                                                                                                                                            let mapping105_ : (BitVec 2) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__203
                                                                                                                                                                13
                                                                                                                                                                12)
                                                                                                                                                            let mapping104_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__203
                                                                                                                                                                19
                                                                                                                                                                15)
                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                mapping104_)), (← (encdec_csrop_backwards
                                                                                                                                                                mapping105_)), (← (encdec_reg_backwards
                                                                                                                                                                mapping106_))) with
                                                                                                                                                            | (rs1, op, rd) =>
                                                                                                                                                              (do
                                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                                       Ext_Zicsr)) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (pure (some
                                                                                                                                                                      true))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)))
                                                                                                                                                        else
                                                                                                                                                          (pure none)) with
                                                                                                                                                      | .some result =>
                                                                                                                                                        (pure result)
                                                                                                                                                      | none =>
                                                                                                                                                        (do
                                                                                                                                                          match (← do
                                                                                                                                                            let v__200 :=
                                                                                                                                                              head_exp_
                                                                                                                                                            if (((let mapping108_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__200
                                                                                                                                                                     11
                                                                                                                                                                     7)
                                                                                                                                                                 let mapping107_ : (BitVec 2) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__200
                                                                                                                                                                     13
                                                                                                                                                                     12)
                                                                                                                                                                 ((encdec_csrop_backwards_matches
                                                                                                                                                                     mapping107_) && (encdec_reg_backwards_matches
                                                                                                                                                                     mapping108_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                       v__200
                                                                                                                                                                       14
                                                                                                                                                                       14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                       v__200
                                                                                                                                                                       6
                                                                                                                                                                       0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let mapping108_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__200
                                                                                                                                                                    11
                                                                                                                                                                    7)
                                                                                                                                                                let mapping107_ : (BitVec 2) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__200
                                                                                                                                                                    13
                                                                                                                                                                    12)
                                                                                                                                                                match ((← (encdec_csrop_backwards
                                                                                                                                                                    mapping107_)), (← (encdec_reg_backwards
                                                                                                                                                                    mapping108_))) with
                                                                                                                                                                | (op, rd) =>
                                                                                                                                                                  (do
                                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                                           Ext_Zicsr)) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (pure (some
                                                                                                                                                                          true))
                                                                                                                                                                    else
                                                                                                                                                                      (pure none)))
                                                                                                                                                            else
                                                                                                                                                              (pure none)) with
                                                                                                                                                          | .some result =>
                                                                                                                                                            (pure result)
                                                                                                                                                          | none =>
                                                                                                                                                            (match head_exp_ with
                                                                                                                                                            | s =>
                                                                                                                                                              (pure true))))))))))))))))))))))))))))))))))))))))

noncomputable def encdec_compressed_forwards (arg_ : instruction) : SailM (BitVec 16) := do
  match arg_ with
  | .C_ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

noncomputable def encdec_compressed_backwards (arg_ : (BitVec 16)) : instruction :=
  match arg_ with
  | s => (C_ILLEGAL s)

noncomputable def encdec_compressed_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .C_ILLEGAL s => true
  | _ => false

noncomputable def encdec_compressed_backwards_matches (arg_ : (BitVec 16)) : Bool :=
  match arg_ with
  | s => true

def execute_WFI (_ : Unit) : SailM ExecutionResult := do
  match (← readReg cur_privilege) with
  | .Machine => (pure (Enter_Wait WAIT_WFI))
  | .Supervisor => (pure (Enter_Wait WAIT_WFI))
  | .User =>
    (if (plat_wfi_available_to_usermode : Bool)
    then (pure (Enter_Wait WAIT_WFI))
    else (pure (Illegal_Instruction ())))
  | .VirtualUser =>
    (internal_error "extensions/I/base_insts.sail" 665 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "extensions/I/base_insts.sail" 666 "Hypervisor extension not supported")

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 64) (imm +++ 0x000#12))
  (wX_bits rd
    (← do
      match op with
      | .LUI => (pure off)
      | .AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, width ∈ {1, 2, 4, 8} -/
def execute_STORE (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  assert (width ≤b xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29"
  let data ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) ((width *i 8) -i 1) 0))
  match (← (vmem_write rs1 offset width data (Store Data) false false false)) with
  | .Ok _ => (pure RETIRE_SUCCESS)
  | .Err e => (pure e)

def execute_SRET (_ : Unit) : SailM ExecutionResult := do
  let sret_illegal ← (( do
    match (← readReg cur_privilege) with
    | .User => (pure true)
    | .Supervisor =>
      (pure ((not (← (currentlyEnabled Ext_S))) || ((_get_Mstatus_TSR (← readReg mstatus)) == 1#1)))
    | .Machine => (pure (not (← (currentlyEnabled Ext_S))))
    | .VirtualUser =>
      (internal_error "extensions/I/base_insts.sail" 607 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 608 "Hypervisor extension not supported") ) :
    SailM Bool )
  if (sret_illegal : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Supervisor)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          let prev_priv ← do readReg cur_privilege
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
            (_get_Mstatus_SPIE (← readReg mstatus)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 1#1)
          writeReg cur_privilege (← do
            if (((_get_Mstatus_SPP (← readReg mstatus)) == 1#1) : Bool)
            then (pure Supervisor)
            else (pure User))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 0#1)
          if ((bne (← readReg cur_privilege) Machine) : Bool)
          then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
          else (pure ())
          if ((hartSupports Ext_Zicfilp) : Bool)
          then (zicfilp_restore_elp_on_xret sRET (← readReg cur_privilege))
          else (pure ())
          (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
          if ((get_config_print_exception ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "ret-ing from "
                  (HAppend.hAppend (← (privLevel_to_str prev_priv))
                    (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
          else (pure ())
          (set_next_pc (← (prepare_xret_target Supervisor)))
          let _ : Unit := (xret_callback false)
          (pure RETIRE_SUCCESS)))

def execute_SHIFTIWOP (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .SLLIW => (shift_bits_left rs1_val shamt)
    | .SRLIW => (shift_bits_right rs1_val shamt)
    | .SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd
    (← do
      match op with
      | .SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | .SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | .SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)

def execute_SFENCE_VMA (rs1 : regidx) (rs2 : regidx) : SailM ExecutionResult := do
  let addr ← do
    if ((bne rs1 zreg) : Bool)
    then (pure (some (← (rX_bits rs1))))
    else (pure none)
  let asid ← do
    if ((bne rs2 zreg) : Bool)
    then (pure (some (Sail.BitVec.extractLsb (← (rX_bits rs2)) (asidlen -i 1) 0)))
    else (pure none)
  match (← readReg cur_privilege) with
  | .User => (pure (Illegal_Instruction ()))
  | .Supervisor =>
    (do
      match (_get_Mstatus_TVM (← readReg mstatus)) with
      | 1 => (pure (Illegal_Instruction ()))
      | _ =>
        (do
          (flush_TLB asid addr)
          (pure RETIRE_SUCCESS)))
  | .Machine =>
    (do
      (flush_TLB asid addr)
      (pure RETIRE_SUCCESS))
  | .VirtualUser => (pure (Virtual_Instruction ()))
  | .VirtualSupervisor =>
    (internal_error "extensions/I/base_insts.sail" 692 "Hypervisor extension not supported")

def execute_RTYPEW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .ADDW => (rs1_val + rs2_val)
    | .SUBW => (rs1_val - rs2_val)
    | .SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | .SLT =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .SLTU =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | .OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | .XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | .SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | .SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex503612_ : Bool -/
def execute_REMW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex503621_ : Bool -/
def execute_REM (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (to_bits_truncate (l := 64) remainder))
  (pure RETIRE_SUCCESS)

def execute_MULW (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int := (BitVec.toInt rs1_bits)
  let rs2_int := (BitVec.toInt rs2_bits)
  let result32 : (BitVec 32) := (to_bits_truncate (l := 32) (rs1_int *i rs2_int))
  (wX_bits rd (sign_extend (m := 64) result32))
  (pure RETIRE_SUCCESS)

def execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd
    (mult_to_bits_half (l := xlen) mul_op.signed_rs1 mul_op.signed_rs2 rs1_bits rs2_bits
      mul_op.result_part))
  (pure RETIRE_SUCCESS)

def execute_MRET (_ : Unit) : SailM ExecutionResult := do
  if ((bne (← readReg cur_privilege) Machine) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Machine)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          let prev_priv ← do readReg cur_privilege
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3
            (_get_Mstatus_MPIE (← readReg mstatus)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7 1#1)
          writeReg cur_privilege (← (privLevel_bits_forwards
              ((_get_Mstatus_MPP (← readReg mstatus)), 0#1)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
            (privLevel_to_bits
              (← do
                if ((← (currentlyEnabled Ext_U)) : Bool)
                then (pure User)
                else (pure Machine))))
          if ((bne (← readReg cur_privilege) Machine) : Bool)
          then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
          else (pure ())
          if ((hartSupports Ext_Zicfilp) : Bool)
          then (zicfilp_restore_elp_on_xret mRET (← readReg cur_privilege))
          else (pure ())
          (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
          if ((get_config_print_exception ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "ret-ing from "
                  (HAppend.hAppend (← (privLevel_to_str prev_priv))
                    (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
          else (pure ())
          (set_next_pc (← (prepare_xret_target Machine)))
          let _ : Unit := (xret_callback true)
          (pure RETIRE_SUCCESS)))

def execute_LPAD (lpl : (BitVec 20)) : SailM ExecutionResult := do
  if ((← (is_landing_pad_expected ())) : Bool)
  then
    (do
      let unaligned_pc ← do (pure ((Sail.BitVec.extractLsb (← (get_arch_pc ())) 1 0) != 0b00#2))
      let label_mismatch ← do
        (pure (((Sail.BitVec.extractLsb (← (rX (Regno 7))) 31 12) != lpl) && (lpl != (zeros
                (n := 20)))))
      if ((unaligned_pc || label_mismatch) : Bool)
      then (trap (make_landing_pad_exception ()))
      else
        (do
          (reset_elp ())
          (pure RETIRE_SUCCESS)))
  else (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, k_ex503655_ : Bool, width ∈ {1, 2, 4, 8} -/
def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  assert (width ≤b xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29"
  match (← (vmem_read rs1 offset width (Load Data) false false false)) with
  | .Ok data =>
    (do
      (wX_bits rd (extend_value is_unsigned data))
      (pure RETIRE_SUCCESS))
  | .Err e => (pure e)

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (update_elp_state rs1)
  let link_address ← do (get_next_pc ())
  let target ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  match (← (jump_to (BitVec.update target 0 0#1))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : xlenbits := (sign_extend (m := 64) imm)
  (wX_bits rd
    (← do
      match op with
      | .ADDI => (pure ((← (rX_bits rs1)) + immext))
      | .SLTI => (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) immext))))
      | .SLTIU =>
        (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) immext))))
      | .ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | .ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | .XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)

def execute_ILLEGAL (_s : (BitVec 32)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_FENCE_TSO (_ : Unit) : SailM ExecutionResult := do
  (sail_barrier Barrier_RISCV_tso)
  (pure RETIRE_SUCCESS)

def execute_FENCE (_fm : (BitVec 4)) (pred : (BitVec 4)) (succ : (BitVec 4)) (_rs : regidx) (_rd : regidx) : SailM ExecutionResult := do
  let fiom ← do (is_fiom_active ())
  let pred := (effective_fence_set pred fiom)
  let succ := (effective_fence_set succ fiom)
  match ((Sail.BitVec.extractLsb pred 1 0), (Sail.BitVec.extractLsb succ 1 0)) with
  | (0b11, 0b11) => (sail_barrier Barrier_RISCV_rw_rw)
  | (0b10, 0b11) => (sail_barrier Barrier_RISCV_r_rw)
  | (0b10, 0b10) => (sail_barrier Barrier_RISCV_r_r)
  | (0b11, 0b01) => (sail_barrier Barrier_RISCV_rw_w)
  | (0b01, 0b01) => (sail_barrier Barrier_RISCV_w_w)
  | (0b01, 0b11) => (sail_barrier Barrier_RISCV_w_rw)
  | (0b11, 0b10) => (sail_barrier Barrier_RISCV_rw_r)
  | (0b10, 0b01) => (sail_barrier Barrier_RISCV_r_w)
  | (0b01, 0b10) => (sail_barrier Barrier_RISCV_w_r)
  | (_, 0b00) => (pure ())
  | (_, _) => (pure ())
  (pure RETIRE_SUCCESS)

def execute_ECALL (_ : Unit) : SailM ExecutionResult := do
  let exc_type ← (( do
    match (← readReg cur_privilege) with
    | .User => (pure (E_U_EnvCall ()))
    | .Supervisor => (pure (E_S_EnvCall ()))
    | .Machine => (pure (E_M_EnvCall ()))
    | .VirtualUser =>
      (internal_error "extensions/I/base_insts.sail" 546 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 547 "Hypervisor extension not supported") ) :
    SailM ExceptionType )
  let t : sync_exception :=
    { trap := exc_type
      excinfo := none
      ext := none }
  (trap t)

def execute_EBREAK (_ : Unit) : SailM ExecutionResult := do
  (trap (make_sync_exception (E_Breakpoint Brk_Software) (← readReg PC)))

/-- Type quantifiers: k_ex503662_ : Bool -/
def execute_DIVW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
    then (Neg.neg (2 ^i 31))
    else quotient
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex503671_ : Bool -/
def execute_DIV (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((not is_unsigned) && (quotient ≥b (2 ^i (xlen -i 1)))) : Bool)
    then (Neg.neg (2 ^i (xlen -i 1)))
    else quotient
  (wX_bits rd (to_bits_truncate (l := 64) quotient))
  (pure RETIRE_SUCCESS)

def execute_C_ILLEGAL (_s : (BitVec 16)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_CSRReg (csr : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := (csr_access_type op (rd == zreg) (rs1 == zreg))
  (doCSR csr (← (rX_bits rs1)) rd op access_type)

def execute_CSRImm (csr : (BitVec 12)) (imm : (BitVec 5)) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := (csr_access_type op (rd == zreg) (imm == (zeros (n := 5))))
  (doCSR csr (zero_extend (m := 64) imm) rd op access_type)

def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | .BEQ => (pure ((← (rX_bits rs1)) == (← (rX_bits rs2))))
    | .BNE => (pure ((← (rX_bits rs1)) != (← (rX_bits rs2))))
    | .BLT => (pure (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGE => (pure (zopz0zKzJ_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BLTU => (pure (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGEU => (pure (zopz0zKzJ_u (← (rX_bits rs1)) (← (rX_bits rs2)))) ) : SailM Bool )
  if (taken : Bool)
  then (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))
  else (pure RETIRE_SUCCESS)

def execute_ADDIW (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let result ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)))
  (pure RETIRE_SUCCESS)

def execute (merge_var : instruction) : SailM ExecutionResult := do
  match merge_var with
  | .LPAD lpl => (execute_LPAD lpl)
  | .UTYPE (imm, rd, op) => (execute_UTYPE imm rd op)
  | .JAL (imm, rd) => (execute_JAL imm rd)
  | .BTYPE (imm, rs2, rs1, op) => (execute_BTYPE imm rs2 rs1 op)
  | .ITYPE (imm, rs1, rd, op) => (execute_ITYPE imm rs1 rd op)
  | .SHIFTIOP (shamt, rs1, rd, op) => (execute_SHIFTIOP shamt rs1 rd op)
  | .RTYPE (rs2, rs1, rd, op) => (execute_RTYPE rs2 rs1 rd op)
  | .LOAD (imm, rs1, rd, is_unsigned, width) => (execute_LOAD imm rs1 rd is_unsigned width)
  | .STORE (imm, rs2, rs1, width) => (execute_STORE imm rs2 rs1 width)
  | .ADDIW (imm, rs1, rd) => (execute_ADDIW imm rs1 rd)
  | .RTYPEW (rs2, rs1, rd, op) => (execute_RTYPEW rs2 rs1 rd op)
  | .SHIFTIWOP (shamt, rs1, rd, op) => (execute_SHIFTIWOP shamt rs1 rd op)
  | .FENCE_TSO arg0 => (execute_FENCE_TSO arg0)
  | .FENCE (_fm, pred, succ, _rs, _rd) => (execute_FENCE _fm pred succ _rs _rd)
  | .ECALL arg0 => (execute_ECALL arg0)
  | .MRET arg0 => (execute_MRET arg0)
  | .SRET arg0 => (execute_SRET arg0)
  | .EBREAK arg0 => (execute_EBREAK arg0)
  | .WFI arg0 => (execute_WFI arg0)
  | .SFENCE_VMA (rs1, rs2) => (execute_SFENCE_VMA rs1 rs2)
  | .JALR (imm, rs1, rd) => (execute_JALR imm rs1 rd)
  | .MUL (rs2, rs1, rd, mul_op) => (execute_MUL rs2 rs1 rd mul_op)
  | .DIV (rs2, rs1, rd, is_unsigned) => (execute_DIV rs2 rs1 rd is_unsigned)
  | .REM (rs2, rs1, rd, is_unsigned) => (execute_REM rs2 rs1 rd is_unsigned)
  | .MULW (rs2, rs1, rd) => (execute_MULW rs2 rs1 rd)
  | .DIVW (rs2, rs1, rd, is_unsigned) => (execute_DIVW rs2 rs1 rd is_unsigned)
  | .REMW (rs2, rs1, rd, is_unsigned) => (execute_REMW rs2 rs1 rd is_unsigned)
  | .CSRReg (csr, rs1, rd, op) => (execute_CSRReg csr rs1 rd op)
  | .CSRImm (csr, imm, rd, op) => (execute_CSRImm csr imm rd op)
  | .ILLEGAL _s => (pure (execute_ILLEGAL _s))
  | .C_ILLEGAL _s => (pure (execute_C_ILLEGAL _s))

def assembly_backwards (arg_ : String) : SailM instruction := do
  match arg_ with
  | _ => throw Error.Exit

def assembly_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

