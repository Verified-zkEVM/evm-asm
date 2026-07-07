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

noncomputable def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__186 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__186 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then
      (let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__186 31 12)
      let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__186 31 12)
      (pure (some (LPAD lpl))))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__186 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__186 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__186 31 12)
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__186 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__186 11 7)
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__186 31 12)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__184 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__184 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__184 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__184 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__184 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__184 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__184 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__184 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__184 20 20)
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
            let v__181 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__181 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__181 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__181 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__181 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__181 31 20)
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__181 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__181 19 15)
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__181 31 20)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some (JALR (imm, rs1, rd)))))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__179 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__179 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__179 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__179 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__179 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__179 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__179 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__179 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__179 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__179 7 7)
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
                    let v__177 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__177 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__177 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__177 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__177 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__177 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__177 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__177 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__177 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__177 31 20)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__173 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__173 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__173 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__173 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__173 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 19 15)
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
                            let v__169 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__169 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__169 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__169 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__169 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__169 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__169 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 19 15)
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
                                let v__165 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__165 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__165 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__165 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__165 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__165 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__165 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__165 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__165 19 15)
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
                                    let v__161 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__161 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__161 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__161 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__161 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__161 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__161 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__161 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__161 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__161 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) =>
                                          (pure (some (RTYPE (rs2, rs1, rd, ADD)))))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__157 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__157 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__157 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__157 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__157 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__157 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__157 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__157 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__157 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__157 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) =>
                                              (pure (some (RTYPE (rs2, rs1, rd, SLT)))))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__153 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__153 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__153 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__153 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__153 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__153 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__153 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__153 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__153 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__153 24 20)
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
                                                let v__149 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__149 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__149 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__149 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__149 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__149 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__149 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__149 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__149 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__149 24 20)
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
                                                    let v__145 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__145 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__145 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__145 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__145 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__145 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__145 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__145 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__145 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__145 24 20)
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
                                                        let v__141 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__141 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__141 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__141 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__141 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__141 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__141 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__141 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__141 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__141 24 20)
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
                                                            let v__137 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__137 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__137 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__137 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__137 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__137 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__137 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__137 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__137 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__137 24
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
                                                                let v__133 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__133 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__133 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__133 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__133 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__133 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__133 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__133
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__133
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__133
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
                                                                    let v__129 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__129 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__129 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__129 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__129 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__129 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__129 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__129 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__129 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__129 24 20)
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
                                                                        let v__125 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__125 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__125 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__125 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__125 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__125 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__125 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__125 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__125 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__125 24 20)
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
                                                                            let v__123 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__123 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__123 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__123 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__123 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__123 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__123 31 20)
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__123 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__123 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__123 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__123 19 15)
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__123 31 20)
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
                                                                                let v__120 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__120 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__120 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__120 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__120 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__120 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__120 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__120 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__120 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__120 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__120 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__120 31 25)
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
                                                                                    let v__117 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__117
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__117
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__117
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__117
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__117
                                                                                            31 20)
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__117
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__117
                                                                                            19 15)
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__117
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
                                                                                        let v__113 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__113
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__113
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__113
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__113
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__113
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__113
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__113
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__113
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__113
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
                                                                                            let v__109 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__109
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__109
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__109
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__109
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__109
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__109
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__109
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__109
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__109
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
                                                                                                let v__105 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__105
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__105
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__105
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__105
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__105
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__105
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__105
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__105
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__105
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
                                                                                                    let v__101 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__101
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__101
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__101
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__101
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__101
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__101
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__101
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__101
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__101
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
                                                                                                        let v__97 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__97
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__97
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__97
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__97
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__97
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__97
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__97
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__97
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__97
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
                                                                                                            let v__93 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__93
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__93
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__93
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__93
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__93
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let shamt : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__93
                                                                                                                    24
                                                                                                                    20)
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__93
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__93
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
                                                                                                                let v__89 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__89
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__89
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__89
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__89
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__89
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let shamt : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__89
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__89
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__89
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
                                                                                                                    let v__85 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__85
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__85
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__85
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__85
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__85
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let shamt : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__85
                                                                                                                            24
                                                                                                                            20)
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__85
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__85
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
                                                                                                                        let v__74 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__74 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (FENCE_TSO
                                                                                                                                ())))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__74
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__74
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__74
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__74
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__74
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                let succ : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__74
                                                                                                                                    23
                                                                                                                                    20)
                                                                                                                                let pred : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__74
                                                                                                                                    27
                                                                                                                                    24)
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__74
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__74
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__74
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
                                                                                                                            let v__37 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__37 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  (ECALL
                                                                                                                                    ())))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__37 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (MRET
                                                                                                                                        ())))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__37 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          (SRET
                                                                                                                                            ())))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__37 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (EBREAK
                                                                                                                                                ())))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__37 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (WFI
                                                                                                                                                    ())))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__37
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__37
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__37
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__37
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__37
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__37
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
                                                                                                                                let v__34 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping84_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__34
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping83_ : (BitVec 3) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__34
                                                                                                                                         14
                                                                                                                                         12)
                                                                                                                                     let mapping82_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__34
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__34
                                                                                                                                         24
                                                                                                                                         20)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_reg_backwards_matches
                                                                                                                                           mapping82_) && ((encdec_mul_op_backwards_matches
                                                                                                                                             mapping83_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping84_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__34
                                                                                                                                           31
                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__34
                                                                                                                                           6
                                                                                                                                           0) == (0b0110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping84_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__34
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping83_ : (BitVec 3) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__34
                                                                                                                                        14
                                                                                                                                        12)
                                                                                                                                    let mapping82_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__34
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__34
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
                                                                                                                                    let v__30 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping88_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__30
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping87_ : (BitVec 1) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__30
                                                                                                                                             12
                                                                                                                                             12)
                                                                                                                                         let mapping86_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__30
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__30
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping85_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping86_) && ((bool_bit_backwards_matches
                                                                                                                                                 mapping87_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping88_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__30
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                 v__30
                                                                                                                                                 14
                                                                                                                                                 13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__30
                                                                                                                                                 6
                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping88_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__30
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping87_ : (BitVec 1) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__30
                                                                                                                                            12
                                                                                                                                            12)
                                                                                                                                        let mapping86_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__30
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__30
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
                                                                                                                                        let v__26 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping92_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__26
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping91_ : (BitVec 1) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__26
                                                                                                                                                 12
                                                                                                                                                 12)
                                                                                                                                             let mapping90_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__26
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping89_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__26
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping89_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping90_) && ((bool_bit_backwards_matches
                                                                                                                                                     mapping91_) && (encdec_reg_backwards_matches
                                                                                                                                                     mapping92_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__26
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__26
                                                                                                                                                     14
                                                                                                                                                     13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__26
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping92_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__26
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping91_ : (BitVec 1) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__26
                                                                                                                                                12
                                                                                                                                                12)
                                                                                                                                            let mapping90_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__26
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping89_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__26
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
                                                                                                                                            let v__22 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping95_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__22
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__22
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping93_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__22
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping93_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping94_) && (encdec_reg_backwards_matches
                                                                                                                                                       mapping95_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__22
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__22
                                                                                                                                                         14
                                                                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__22
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping95_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__22
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__22
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping93_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__22
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
                                                                                                                                                let v__18 :=
                                                                                                                                                  head_exp_
                                                                                                                                                if (((let mapping99_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__18
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping98_ : (BitVec 1) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__18
                                                                                                                                                         12
                                                                                                                                                         12)
                                                                                                                                                     let mapping97_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__18
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping96_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__18
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping96_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping97_) && ((bool_bit_backwards_matches
                                                                                                                                                             mapping98_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping99_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__18
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__18
                                                                                                                                                             14
                                                                                                                                                             13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__18
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping99_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__18
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping98_ : (BitVec 1) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__18
                                                                                                                                                        12
                                                                                                                                                        12)
                                                                                                                                                    let mapping97_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__18
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping96_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__18
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
                                                                                                                                                    let v__14 :=
                                                                                                                                                      head_exp_
                                                                                                                                                    if (((let mapping103_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__14
                                                                                                                                                             11
                                                                                                                                                             7)
                                                                                                                                                         let mapping102_ : (BitVec 1) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__14
                                                                                                                                                             12
                                                                                                                                                             12)
                                                                                                                                                         let mapping101_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__14
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping100_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__14
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping100_) && ((encdec_reg_backwards_matches
                                                                                                                                                               mapping101_) && ((bool_bit_backwards_matches
                                                                                                                                                                 mapping102_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping103_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__14
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                 v__14
                                                                                                                                                                 14
                                                                                                                                                                 13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                 v__14
                                                                                                                                                                 6
                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping103_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__14
                                                                                                                                                            11
                                                                                                                                                            7)
                                                                                                                                                        let mapping102_ : (BitVec 1) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__14
                                                                                                                                                            12
                                                                                                                                                            12)
                                                                                                                                                        let mapping101_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__14
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping100_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__14
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
                                                                                                                                                    (match head_exp_ with
                                                                                                                                                    | s =>
                                                                                                                                                      (pure (ILLEGAL
                                                                                                                                                          s)))))))))))))))))))))))))))))))))))))))

noncomputable def encdec_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure true)
      else (pure false))
  | .UTYPE (imm, rd, op) => (pure true)
  | .JAL (v__190, rd) =>
    (if (((Sail.BitVec.extractLsb v__190 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .JALR (imm, rs1, rd) => (pure true)
  | .BTYPE (v__192, rs2, rs1, op) =>
    (if (((Sail.BitVec.extractLsb v__192 0 0) == (0#1 : (BitVec 1))) : Bool)
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
  | .ILLEGAL s => (pure true)
  | _ => (pure false)

noncomputable def encdec_backwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__366 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__366 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then (pure (some true))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__366 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__366 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__366 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__366 11 7)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__364 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__364 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__364 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__364 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__364 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__364 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__364 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__364 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__364 20 20)
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
            let v__361 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__361 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__361 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__361 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__361 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__361 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__361 19 15)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some true)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__359 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__359 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__359 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__359 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__359 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__359 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__359 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__359 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__359 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__359 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__359 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__359 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__359 7 7)
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
                    let v__357 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__357 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__357 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__357 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__357 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__357 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__357 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__357 11 7)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some true)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__353 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__353 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__353 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__353 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__353 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__353 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__353 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__353 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__353 19 15)
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
                            let v__349 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__349 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__349 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__349 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__349 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__349 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__349 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__349 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__349 19 15)
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
                                let v__345 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__345 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__345 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__345 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__345 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__345 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__345 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__345 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__345 19 15)
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
                                    let v__341 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__341 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__341 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__341 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__341 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__341 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__341 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__341 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__341 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__341 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) => (pure (some true)))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__337 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__337 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__337 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__337 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__337 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__337 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__337 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__337 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__337 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__337 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) => (pure (some true)))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__333 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__333 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__333 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__333 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__333 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__333 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__333 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__333 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__333 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__333 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) => (pure (some true)))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__329 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__329 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__329 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__329 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__329 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__329 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__329 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__329 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__329 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__329 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) => (pure (some true)))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__325 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__325 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__325 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__325 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__325 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__325 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__325 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__325 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__325 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__325 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) => (pure (some true)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__321 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__321 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__321 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__321 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__321 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__321 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__321 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__321 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__321 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__321 24 20)
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
                                                            let v__317 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__317 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__317 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__317 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__317 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__317 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__317 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__317 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__317 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__317 24
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
                                                                let v__313 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__313 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__313 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__313 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__313 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__313 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__313 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__313
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__313
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__313
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
                                                                    let v__309 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__309 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__309 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__309 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__309 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__309 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__309 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__309 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__309 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__309 24 20)
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
                                                                        let v__305 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__305 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__305 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__305 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__305 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__305 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__305 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__305 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__305 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__305 24 20)
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
                                                                            let v__303 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__303 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__303 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__303 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__303 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__303 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__303 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__303 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__303 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__303 19 15)
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
                                                                                let v__300 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__300 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__300 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__300 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__300 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__300 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__300 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__300 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__300 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__300 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__300 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__300 31 25)
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
                                                                                    let v__297 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__297
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__297
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__297
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__297
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__297
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__297
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
                                                                                        let v__293 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__293
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__293
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__293
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__293
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__293
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__293
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__293
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__293
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__293
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
                                                                                            let v__289 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__289
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__289
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__289
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__289
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__289
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__289
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__289
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__289
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__289
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
                                                                                                let v__285 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__285
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__285
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__285
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__285
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__285
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__285
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__285
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__285
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__285
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
                                                                                                    let v__281 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__281
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__281
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__281
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__281
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__281
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__281
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__281
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__281
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__281
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
                                                                                                        let v__277 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__277
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__277
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__277
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__277
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__277
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__277
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__277
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__277
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__277
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
                                                                                                            let v__273 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__273
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__273
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__273
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__273
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__273
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__273
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__273
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
                                                                                                                let v__269 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__269
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__269
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__269
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__269
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__269
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__269
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__269
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
                                                                                                                    let v__265 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__265
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__265
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__265
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__265
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__265
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__265
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__265
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
                                                                                                                        let v__254 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__254 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__254
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__254
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__254
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__254
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__254
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__254
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
                                                                                                                            let v__217 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__217 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  true))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__217 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      true))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__217 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          true))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__217 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__217 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__217
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__217
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__217
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__217
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__217
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__217
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
                                                                                                                                let v__214 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping84_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__214
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping83_ : (BitVec 3) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__214
                                                                                                                                         14
                                                                                                                                         12)
                                                                                                                                     let mapping82_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__214
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__214
                                                                                                                                         24
                                                                                                                                         20)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_reg_backwards_matches
                                                                                                                                           mapping82_) && ((encdec_mul_op_backwards_matches
                                                                                                                                             mapping83_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping84_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__214
                                                                                                                                           31
                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__214
                                                                                                                                           6
                                                                                                                                           0) == (0b0110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping84_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__214
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping83_ : (BitVec 3) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__214
                                                                                                                                        14
                                                                                                                                        12)
                                                                                                                                    let mapping82_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__214
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__214
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
                                                                                                                                    let v__210 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping88_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__210
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping87_ : (BitVec 1) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__210
                                                                                                                                             12
                                                                                                                                             12)
                                                                                                                                         let mapping86_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__210
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__210
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping85_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping86_) && ((bool_bit_backwards_matches
                                                                                                                                                 mapping87_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping88_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__210
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                 v__210
                                                                                                                                                 14
                                                                                                                                                 13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__210
                                                                                                                                                 6
                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping88_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__210
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping87_ : (BitVec 1) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__210
                                                                                                                                            12
                                                                                                                                            12)
                                                                                                                                        let mapping86_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__210
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__210
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
                                                                                                                                        let v__206 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping92_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__206
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping91_ : (BitVec 1) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__206
                                                                                                                                                 12
                                                                                                                                                 12)
                                                                                                                                             let mapping90_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__206
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping89_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__206
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping89_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping90_) && ((bool_bit_backwards_matches
                                                                                                                                                     mapping91_) && (encdec_reg_backwards_matches
                                                                                                                                                     mapping92_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__206
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__206
                                                                                                                                                     14
                                                                                                                                                     13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__206
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping92_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__206
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping91_ : (BitVec 1) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__206
                                                                                                                                                12
                                                                                                                                                12)
                                                                                                                                            let mapping90_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__206
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping89_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__206
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
                                                                                                                                            let v__202 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping95_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__202
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__202
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping93_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__202
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping93_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping94_) && (encdec_reg_backwards_matches
                                                                                                                                                       mapping95_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__202
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__202
                                                                                                                                                         14
                                                                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__202
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping95_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__202
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__202
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping93_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__202
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
                                                                                                                                                let v__198 :=
                                                                                                                                                  head_exp_
                                                                                                                                                if (((let mapping99_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__198
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping98_ : (BitVec 1) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__198
                                                                                                                                                         12
                                                                                                                                                         12)
                                                                                                                                                     let mapping97_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__198
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping96_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__198
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping96_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping97_) && ((bool_bit_backwards_matches
                                                                                                                                                             mapping98_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping99_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__198
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__198
                                                                                                                                                             14
                                                                                                                                                             13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__198
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping99_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__198
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping98_ : (BitVec 1) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__198
                                                                                                                                                        12
                                                                                                                                                        12)
                                                                                                                                                    let mapping97_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__198
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping96_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__198
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
                                                                                                                                                    let v__194 :=
                                                                                                                                                      head_exp_
                                                                                                                                                    if (((let mapping103_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__194
                                                                                                                                                             11
                                                                                                                                                             7)
                                                                                                                                                         let mapping102_ : (BitVec 1) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__194
                                                                                                                                                             12
                                                                                                                                                             12)
                                                                                                                                                         let mapping101_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__194
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping100_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__194
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping100_) && ((encdec_reg_backwards_matches
                                                                                                                                                               mapping101_) && ((bool_bit_backwards_matches
                                                                                                                                                                 mapping102_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping103_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__194
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                 v__194
                                                                                                                                                                 14
                                                                                                                                                                 13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                 v__194
                                                                                                                                                                 6
                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping103_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__194
                                                                                                                                                            11
                                                                                                                                                            7)
                                                                                                                                                        let mapping102_ : (BitVec 1) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__194
                                                                                                                                                            12
                                                                                                                                                            12)
                                                                                                                                                        let mapping101_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__194
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping100_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__194
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
                                                                                                                                                    (match head_exp_ with
                                                                                                                                                    | s =>
                                                                                                                                                      (pure true))))))))))))))))))))))))))))))))))))))

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
    (internal_error "extensions/I/base_insts.sail" 661 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "extensions/I/base_insts.sail" 662 "Hypervisor extension not supported")

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
      (internal_error "extensions/I/base_insts.sail" 603 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 604 "Hypervisor extension not supported") ) :
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
    (internal_error "extensions/I/base_insts.sail" 688 "Hypervisor extension not supported")

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

/-- Type quantifiers: k_ex262644_ : Bool -/
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

/-- Type quantifiers: k_ex262653_ : Bool -/
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

/-- Type quantifiers: width : Nat, k_ex262687_ : Bool, width ∈ {1, 2, 4, 8} -/
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
      (internal_error "extensions/I/base_insts.sail" 542 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 543 "Hypervisor extension not supported") ) :
    SailM ExceptionType )
  let t : sync_exception :=
    { trap := exc_type
      excinfo := none
      ext := none }
  (trap t)

def execute_EBREAK (_ : Unit) : SailM ExecutionResult := do
  (trap (make_sync_exception (E_Breakpoint Brk_Software) (← readReg PC)))

/-- Type quantifiers: k_ex262694_ : Bool -/
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

/-- Type quantifiers: k_ex262703_ : Bool -/
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
  | .ILLEGAL _s => (pure (execute_ILLEGAL _s))
  | .C_ILLEGAL _s => (pure (execute_C_ILLEGAL _s))

def assembly_backwards (arg_ : String) : SailM instruction := do
  match arg_ with
  | _ => throw Error.Exit

def assembly_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

