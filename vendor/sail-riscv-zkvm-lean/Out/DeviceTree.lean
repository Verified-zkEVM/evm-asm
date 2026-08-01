import Out.Flow
import Out.Prelude
import Out.Xlen
import Out.PlatformConfig
import Out.Extensions
import Out.Pma

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

def mmu_type (_ : Unit) : SailM String := do
  assert (xlen == 64) "postlude/device_tree.sail:14.21-14.22"
  if ((hartSupports Ext_Sv57) : Bool)
  then (pure "sv57")
  else
    (if ((hartSupports Ext_Sv48) : Bool)
    then (pure "sv48")
    else
      (if ((hartSupports Ext_Sv39) : Bool)
      then (pure "sv39")
      else (pure "none")))

def generate_isa_base (_ : Unit) : String :=
  (HAppend.hAppend "rv" (HAppend.hAppend (Int.repr xlen) "i"))

def undefined_ISA_Format (_ : Unit) : SailM ISA_Format := do
  (internal_pick [Canonical_Lowercase, DeviceTree_ISA_Extensions])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def ISA_Format_of_num (arg_ : Nat) : ISA_Format :=
  match arg_ with
  | 0 => Canonical_Lowercase
  | _ => DeviceTree_ISA_Extensions

def num_of_ISA_Format (arg_ : ISA_Format) : Int :=
  match arg_ with
  | .Canonical_Lowercase => 0
  | .DeviceTree_ISA_Extensions => 1

def ext_wrap (ext : extension) (fmt : ISA_Format) : String :=
  if ((not (hartSupports ext)) : Bool)
  then ""
  else
    (let s := (extensionName_forwards ext)
    match fmt with
    | .Canonical_Lowercase =>
      (if (((String.length s) == 1) : Bool)
      then s
      else (HAppend.hAppend "_" s))
    | .DeviceTree_ISA_Extensions => (HAppend.hAppend ", \"" (HAppend.hAppend s "\"")))

def generate_isa_string (fmt : ISA_Format) : String := Id.run do
  let isa_string : String :=
    match fmt with
    | .Canonical_Lowercase => (HAppend.hAppend "rv" (HAppend.hAppend (Int.repr xlen) "i"))
    | .DeviceTree_ISA_Extensions => "\"i\""
  let loop_i_lower := 0
  let loop_i_upper := ((Vector.length extensions_ordered_for_isa_string) -i 1)
  let mut loop_vars := isa_string
  for i in [loop_i_upper:loop_i_lower:-1]i do
    let isa_string := loop_vars
    loop_vars :=
      (HAppend.hAppend isa_string
        (ext_wrap (GetElem?.getElem! extensions_ordered_for_isa_string i) fmt))
  (pure loop_vars)

def generate_dts_memories (pmas : (List PMA_Region)) : String :=
  match pmas with
  | [] => ""
  | (pma :: rest) =>
    (if (pma.include_in_device_tree : Bool)
    then
      (let base_hi := (BitVec.toNatInt (pma.base >>> 32))
      let base_lo := (BitVec.toNatInt (Sail.BitVec.extractLsb pma.base 31 0))
      let size_hi := (BitVec.toNatInt (pma.size >>> 32))
      let size_lo := (BitVec.toNatInt (Sail.BitVec.extractLsb pma.size 31 0))
      (HAppend.hAppend "  memory@"
        (HAppend.hAppend (String.dropStr (Int.toHex (BitVec.toNatInt pma.base)) 2)
          (HAppend.hAppend " {
"
            (HAppend.hAppend "    device_type = \"memory\";
"
              (HAppend.hAppend "    reg = <"
                (HAppend.hAppend (Int.toHex base_hi)
                  (HAppend.hAppend " "
                    (HAppend.hAppend (Int.toHex base_lo)
                      (HAppend.hAppend " "
                        (HAppend.hAppend (Int.toHex size_hi)
                          (HAppend.hAppend " "
                            (HAppend.hAppend (Int.toHex size_lo)
                              (HAppend.hAppend ">;
"
                                (HAppend.hAppend "  };
" (generate_dts_memories rest))))))))))))))))
    else (generate_dts_memories rest))

def generate_cbo_block_size (prefix : String) (ext : extension) : String :=
  if ((hartSupports ext) : Bool)
  then
    (HAppend.hAppend "      riscv,"
      (HAppend.hAppend prefix
        (HAppend.hAppend "-block-size = <"
          (HAppend.hAppend (Int.repr (2 ^i plat_cache_block_size_exp)) ">;
"))))
  else ""

def generate_dts (_ : Unit) : SailM String := do
  let clock_freq : Nat := 1000000000
  let clint_base_hi := (BitVec.toNatInt (plat_clint_base >>> 32))
  let clint_base_lo := (BitVec.toNatInt (Sail.BitVec.extractLsb plat_clint_base 31 0))
  let clint_size_hi := (BitVec.toNatInt (plat_clint_size >>> 32))
  let clint_size_lo := (BitVec.toNatInt (Sail.BitVec.extractLsb plat_clint_size 31 0))
  (pure (HAppend.hAppend "/dts-v1/;
"
      (HAppend.hAppend "
"
        (HAppend.hAppend "/ {
"
          (HAppend.hAppend "  #address-cells = <2>;
"
            (HAppend.hAppend "  #size-cells = <2>;
"
              (HAppend.hAppend "  compatible = \"ucbbar,spike-bare-dev\";
"
                (HAppend.hAppend "  model = \"ucbbar,spike-bare\";
"
                  (HAppend.hAppend "  chosen {
"
                    (HAppend.hAppend "    bootargs = \"console=hvc0 earlycon=sbi\";
"
                      (HAppend.hAppend "  };
"
                        (HAppend.hAppend "  cpus {
"
                          (HAppend.hAppend "    #address-cells = <1>;
"
                            (HAppend.hAppend "    #size-cells = <0>;
"
                              (HAppend.hAppend "    timebase-frequency = <"
                                (HAppend.hAppend
                                  (Int.repr (Int.tdiv clock_freq plat_insns_per_tick))
                                  (HAppend.hAppend ">;
"
                                    (HAppend.hAppend "    CPU0: cpu@0 {
"
                                      (HAppend.hAppend "      device_type = \"cpu\";
"
                                        (HAppend.hAppend "      reg = <0>;
"
                                          (HAppend.hAppend "      status = \"okay\";
"
                                            (HAppend.hAppend "      compatible = \"riscv\";
"
                                              (HAppend.hAppend "      riscv,isa-base = \""
                                                (HAppend.hAppend (generate_isa_base ())
                                                  (HAppend.hAppend "\";
"
                                                    (HAppend.hAppend "      riscv,isa = \""
                                                      (HAppend.hAppend
                                                        (generate_isa_string Canonical_Lowercase)
                                                        (HAppend.hAppend "\";
"
                                                          (HAppend.hAppend
                                                            "      riscv,isa-extensions = "
                                                            (HAppend.hAppend
                                                              (generate_isa_string
                                                                DeviceTree_ISA_Extensions)
                                                              (HAppend.hAppend ";
"
                                                                (HAppend.hAppend
                                                                  "      mmu-type = \"riscv,"
                                                                  (HAppend.hAppend
                                                                    (← (mmu_type ()))
                                                                    (HAppend.hAppend "\";
"
                                                                      (HAppend.hAppend
                                                                        (generate_cbo_block_size
                                                                          "cbom" Ext_Zicbom)
                                                                        (HAppend.hAppend
                                                                          (generate_cbo_block_size
                                                                            "cboz" Ext_Zicboz)
                                                                          (HAppend.hAppend
                                                                            (generate_cbo_block_size
                                                                              "cbop" Ext_Zicbop)
                                                                            (HAppend.hAppend
                                                                              "      clock-frequency = <"
                                                                              (HAppend.hAppend
                                                                                (Int.repr clock_freq)
                                                                                (HAppend.hAppend
                                                                                  ">;
"
                                                                                  (HAppend.hAppend
                                                                                    "      CPU0_intc: interrupt-controller {
"
                                                                                    (HAppend.hAppend
                                                                                      "        #address-cells = <2>;
"
                                                                                      (HAppend.hAppend
                                                                                        "        #interrupt-cells = <1>;
"
                                                                                        (HAppend.hAppend
                                                                                          "        interrupt-controller;
"
                                                                                          (HAppend.hAppend
                                                                                            "        compatible = \"riscv,cpu-intc\";
"
                                                                                            (HAppend.hAppend
                                                                                              "      };
"
                                                                                              (HAppend.hAppend
                                                                                                "    };
"
                                                                                                (HAppend.hAppend
                                                                                                  "  };
"
                                                                                                  (HAppend.hAppend
                                                                                                    (generate_dts_memories
                                                                                                      (← readReg pma_regions))
                                                                                                    (HAppend.hAppend
                                                                                                      "  soc {
"
                                                                                                      (HAppend.hAppend
                                                                                                        "    #address-cells = <2>;
"
                                                                                                        (HAppend.hAppend
                                                                                                          "    #size-cells = <2>;
"
                                                                                                          (HAppend.hAppend
                                                                                                            "    compatible = \"ucbbar,spike-bare-soc\", \"simple-bus\";
"
                                                                                                            (HAppend.hAppend
                                                                                                              "    ranges;
"
                                                                                                              (HAppend.hAppend
                                                                                                                "    clint@"
                                                                                                                (HAppend.hAppend
                                                                                                                  (String.dropStr
                                                                                                                    (Int.toHex
                                                                                                                      (BitVec.toNatInt
                                                                                                                        plat_clint_base))
                                                                                                                    2)
                                                                                                                  (HAppend.hAppend
                                                                                                                    " {
"
                                                                                                                    (HAppend.hAppend
                                                                                                                      "      compatible = \"riscv,clint0\";
"
                                                                                                                      (HAppend.hAppend
                                                                                                                        "      interrupts-extended = <&CPU0_intc 3 &CPU0_intc 7>;
"
                                                                                                                        (HAppend.hAppend
                                                                                                                          "      reg = <"
                                                                                                                          (HAppend.hAppend
                                                                                                                            (Int.toHex
                                                                                                                              clint_base_hi)
                                                                                                                            (HAppend.hAppend
                                                                                                                              " "
                                                                                                                              (HAppend.hAppend
                                                                                                                                (Int.toHex
                                                                                                                                  clint_base_lo)
                                                                                                                                (HAppend.hAppend
                                                                                                                                  " "
                                                                                                                                  (HAppend.hAppend
                                                                                                                                    (Int.toHex
                                                                                                                                      clint_size_hi)
                                                                                                                                    (HAppend.hAppend
                                                                                                                                      " "
                                                                                                                                      (HAppend.hAppend
                                                                                                                                        (Int.toHex
                                                                                                                                          clint_size_lo)
                                                                                                                                        (HAppend.hAppend
                                                                                                                                          ">;
"
                                                                                                                                          (HAppend.hAppend
                                                                                                                                            "    };
"
                                                                                                                                            (HAppend.hAppend
                                                                                                                                              "  };
"
                                                                                                                                              (HAppend.hAppend
                                                                                                                                                "  htif {
"
                                                                                                                                                (HAppend.hAppend
                                                                                                                                                  "    compatible = \"ucb,htif0\";
"
                                                                                                                                                  (HAppend.hAppend
                                                                                                                                                    "  };
"
                                                                                                                                                    "};
")))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def generate_canonical_isa_string (_ : Unit) : String :=
  (generate_isa_string Canonical_Lowercase)

