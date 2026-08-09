/-
  EvmAsm.Codegen.Programs.DepositDerivationE2E

  `zisk_deposit_derivation_e2e` (bead evm-asm-8uld3.1.3, EIP-6110) — the END-TO-END
  deposit-request derivation chain, composing the three standalone pieces:

    M26 descriptor + evm_log_data full-data (8uld3.1a #8674)
      -> materialize_log_records (8uld3.1b #8678): canonical BE log-record array
      -> parse_deposit_requests (#8657) -> extract_deposit_data (#8580): 192-byte body

  This is the integration check that materialize's OUTPUT record format (addr@0,
  topic_count@32, topic0@40, data_len@72, data@80) exactly agrees with what
  parse_deposit_requests CONSUMES — a risk the unit probes can't see.

  The probe synthesizes one packed block-log descriptor for a real DepositEvent:
  the address (+8) is stored canonical-BE and topic0 (+32) is stored in stack-word
  order by reversing `pdr_deposit_sig`, so materialize copies the address and
  reverses topic0 back to BE before parse_deposit_requests's filters. The 576-byte
  DepositEvent ABI payload is supplied via the ziskemu input and placed in the probe's
  evm_log_data buffer at offset 0; meta[0] = (0, 576).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.AssembleExecutionRequests

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `zisk_deposit_derivation_e2e`: end-to-end probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8.. : the 576-byte DepositEvent ABI payload (one deposit log's data)
    Output (at 0xa0010000):
      +0   c1_dstatus-style parse status (0 ok / 1 malformed deposit)
      +8   c1_dlen-style total deposit-request bytes written (expect 192)
      +16  the 192-byte deposit body (pubkey48 || wc32 || amount8 || sig96 || index8)
      +208 c1_erh_status-style verify(zero header hash) (expect 1 mismatch)
      +216 c1_erh_status-style verify(correct derived hash) (expect 0 match)
      +224 c1_erh_status-style verify(corrupted header hash) (expect 1 mismatch). -/
def ziskDepositDerivationE2EPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  -- copy the 576-byte DepositEvent payload (input+8) into dde_data (evm_log_data) @ off 0
  "  addi t0, a6, 8\n  la t1, dde_data\n  li t2, 576\n" ++
  ".Ldde_cpdata:\n" ++
  "  beqz t2, .Ldde_cpdata_d\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Ldde_cpdata\n" ++
  ".Ldde_cpdata_d:\n" ++
  -- PACK: descriptor 0 at dde_descs: topic_count=1 @+0; topic0 @+32 = reverse(pdr_deposit_sig);
  -- address @+8 (packed header) = pdr_deposit_addr BE. (dde_descs is .zero.)
  "  la s0, dde_descs\n" ++
  "  li t0, 1\n  sd t0, 0(s0)\n" ++                       -- topic_count = 1
  -- topic0: dde_descs+32+k = pdr_deposit_sig[31-k]  (LE)
  "  la t0, pdr_deposit_sig\n  addi t0, t0, 31\n  addi t1, s0, 32\n  li t2, 32\n" ++
  ".Ldde_sig:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Ldde_sig\n" ++
  -- address: dde_descs+8+k = pdr_deposit_addr[k] (canonical BE) at the packed header +8
  "  la t0, pdr_deposit_addr\n  addi t1, s0, 8\n  li t2, 20\n" ++
  ".Ldde_addr:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Ldde_addr\n" ++
  -- meta[0] = (offset 0, len 576)
  "  la t0, dde_meta\n  sd zero, 0(t0)\n  li t1, 576\n  sd t1, 8(t0)\n" ++
  -- materialize_log_records(descs, 1, data, meta, records)
  "  la a0, dde_descs\n  li a1, 1\n  la a2, dde_data\n  la a3, dde_meta\n  la a4, dde_records\n" ++
  "  jal ra, materialize_log_records\n" ++
  -- parse_deposit_requests(records, 1, body, status)
  "  la a0, dde_records\n  li a1, 1\n  la a2, dde_body\n  la a3, dde_status\n" ++
  "  jal ra, parse_deposit_requests\n" ++
  "  la t0, dde_len; sd a0, 0(t0)\n" ++
  -- output: status, total bytes, then the 192-byte body
  "  li t0, 0xa0010000\n" ++
  "  la t1, dde_status; ld t2, 0(t1); sd t2, 0(t0)\n" ++
  "  sd a0, 8(t0)\n" ++
  "  la t1, dde_body; addi t3, t0, 16; li t4, 192\n" ++
  ".Ldde_dump:\n" ++
  "  beqz t4, .Ldde_dd\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t3); addi t1, t1, 1; addi t3, t3, 1; addi t4, t4, -1; j .Ldde_dump\n" ++
  ".Ldde_dd:\n" ++
  -- Verify the execution-derived deposit body against a matching and forged header.requests_hash.
  -- This mirrors BlockVerdictReceiptsTail's c1_dbody/c1_dlen -> requests_hash_verify flow.
  "  la t0, dde_hash; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la a0, dde_body; la t0, dde_len; ld a1, 0(t0); li a2, 0; li a3, 0; li a4, 0; li a5, 0\n" ++
  "  la a6, dde_hash; la a7, dde_section\n" ++
  "  jal ra, requests_hash_verify\n" ++
  "  li t0, 0xa0010000; sd a0, 208(t0)\n" ++
  "  la t1, rhv_hash; la t2, dde_hash; li t3, 32\n" ++
  ".Ldde_hash_cp:\n" ++
  "  beqz t3, .Ldde_hash_cpd\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Ldde_hash_cp\n" ++
  ".Ldde_hash_cpd:\n" ++
  "  la a0, dde_body; la t0, dde_len; ld a1, 0(t0); li a2, 0; li a3, 0; li a4, 0; li a5, 0\n" ++
  "  la a6, dde_hash; la a7, dde_section\n" ++
  "  jal ra, requests_hash_verify\n" ++
  "  li t0, 0xa0010000; sd a0, 216(t0)\n" ++
  "  la t0, dde_hash; lbu t1, 0(t0); xori t1, t1, 0xff; sb t1, 0(t0)\n" ++
  "  la a0, dde_body; la t0, dde_len; ld a1, 0(t0); li a2, 0; li a3, 0; li a4, 0; li a5, 0\n" ++
  "  la a6, dde_hash; la a7, dde_section\n" ++
  "  jal ra, requests_hash_verify\n" ++
  "  li t0, 0xa0010000; sd a0, 224(t0)\n" ++
  "  j .Ldde_done\n" ++
  materializeLogRecordsFunction ++ "\n" ++
  parseDepositRequestsFunction ++ "\n" ++
  extractDepositDataFunction ++ "\n" ++
  requestsHashVerifyFunction ++ "\n" ++
  assembleExecutionRequestsFunction ++ "\n" ++
  executionRequestsHashFunctions ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Ldde_done:"

def ziskDepositDerivationE2EDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "pdr_deposit_addr:\n" ++   -- DEPOSIT_CONTRACT_ADDRESS (20 bytes BE)
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40\n" ++
  "  .byte 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30\n" ++
  "  .byte 0x3d, 0x77, 0x05, 0xfa\n" ++
  ".balign 8\n" ++
  "pdr_deposit_sig:\n" ++    -- DEPOSIT_EVENT_SIGNATURE_HASH (32 bytes BE)
  "  .byte 0x64, 0x9b, 0xbc, 0x62, 0xd0, 0xe3, 0x13, 0x42\n" ++
  "  .byte 0xaf, 0xea, 0x4e, 0x5c, 0xd8, 0x2d, 0x40, 0x49\n" ++
  "  .byte 0xe7, 0xe1, 0xee, 0x91, 0x2f, 0xc0, 0x88, 0x9a\n" ++
  "  .byte 0xa7, 0x90, 0x80, 0x3b, 0xe3, 0x90, 0x38, 0xc5\n" ++
  ".balign 8\n" ++
  "dde_descs:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "dde_data:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "dde_meta:\n  .zero 16\n" ++
  ".balign 8\n" ++
  "dde_records:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "dde_body:\n  .zero 256\n" ++
  "aer_bd_ptr:\n  .zero 8\naer_bd_len:\n  .zero 8\n" ++
  "aer_be_ptr:\n  .zero 8\naer_be_len:\n  .zero 8\n" ++
  "dde_status:\n  .zero 8\n" ++
  "dde_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "dde_hash:\n  .zero 32\n" ++
  "rhv_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "dde_section:\n  .zero 1024\n" ++
  executionRequestsHashShaDataSection ++ "\n" ++
  executionRequestsHashDataSection

def ziskDepositDerivationE2EProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskDepositDerivationE2EPrologue
  dataAsm     := ziskDepositDerivationE2EDataSection
}

end EvmAsm.Codegen
