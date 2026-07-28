/-
  Diagnostic-only probe for #10763's reject-side authorization-chain-id cases.

  A valid EEST blockchain fixture cannot express a malformed authorization
  scalar: it is rejected while decoding the transaction.  This probe is the
  FA-direction control for the widening repair.  It drives the same K20 field
  selection followed by K35's strict U256-content decoder on (1) a
  non-canonical zero encoding and (2) canonical content longer than 32 bytes.
  Both output status words must be nonzero on the fixed ELF. This directly
  measures the FA-adjacent direction: the acceptance-widening repair must not
  admit malformed scalars. A parent run would only re-measure the FR direction,
  which the repair's paired EEST A/B already covers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

def authChainIdEncodingProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, acip_noncanonical; li a1, 3; li a2, 0; la a3, acip_off; la a4, acip_len; jal ra, rlp_list_nth_item\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  la a0, acip_oversize; li a1, 35; li a2, 0; la a3, acip_off; la a4, acip_len; jal ra, rlp_list_nth_item; bnez a0, .Lacip_store_oversize\n" ++
  "  la t1, acip_off; ld t1, 0(t1); la a0, acip_oversize; add a0, a0, t1; la t1, acip_len; ld a1, 0(t1); la a2, acip_scratch; jal ra, rlp_content_to_u256_be\n" ++
  ".Lacip_store_oversize:\n" ++
  "  li t0, 0xa0010000; sd a0, 8(t0); j .Lacip_done\n" ++
  rlpListNthItemFunction ++ "\n" ++ rlpContentToU256BeFunction ++ "\n" ++
  ".Lacip_done:"

def authChainIdEncodingProbeData : String :=
  ".section .data\n.balign 8\n" ++
  "acip_noncanonical:\n  .byte 0xc2, 0x81, 0x00\n" ++
  "acip_oversize:\n  .byte 0xe2, 0xa1\n  .rept 33\n  .byte 0x01\n  .endr\n" ++
  ".balign 8\nacip_off:\n  .zero 8\nacip_len:\n  .zero 8\nacip_scratch:\n  .zero 32"

def ziskAuthChainIdEncodingProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := authChainIdEncodingProbePrologue
  dataAsm := authChainIdEncodingProbeData
}

end EvmAsm.Codegen
