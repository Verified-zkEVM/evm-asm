/-
  EvmAsm.Codegen.Programs.PrecompileBackendProbes

  Standalone backend probes for zkvm accelerator wrappers used by EVM
  precompile runtime bodies.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.ModexpBackend
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Linkable bare-RV64 wrapper for `zkvm_bls12_g1_add(p1, p2, result)`.
    The installed ziskemu currently does not complete ECALL selector 0x10b from
    bare codegen ELFs. Keep the ABI linkable and deterministic by returning
    EFAIL (-1) without touching the result buffer. Runtime callers can therefore
    exercise the BLS12 G1 ADD dispatch path without crashing guest execution;
    replacing this shim with the real ECALL route is tracked separately once the
    backend/replay path is available. -/
def zkvmBls12G1AddSafeFailWrapper : String :=
  ".globl zkvm_bls12_g1_add\n" ++
  "zkvm_bls12_g1_add:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for `zkvm_bls12_g1_msm(pairs, count, result)`.
    See `zkvmBls12G1AddSafeFailWrapper`: runtime callers need deterministic
    EFAIL until the success-producing backend/replay path is available. -/
def zkvmBls12G1MsmSafeFailWrapper : String :=
  ".globl zkvm_bls12_g1_msm\n" ++
  "zkvm_bls12_g1_msm:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for `zkvm_bn254_g1_add(p1, p2, result)`.
    Current runtime tests use deterministic EFAIL until the success-producing
    BN254 accelerator path is available from bare codegen ELFs. -/
def zkvmBn254G1AddSafeFailWrapper : String :=
  ".globl zkvm_bn254_g1_add\n" ++
  "zkvm_bn254_g1_add:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for `zkvm_bn254_g1_mul(point, scalar, result)`.
    See `zkvmBn254G1AddSafeFailWrapper`: runtime callers need deterministic
    EFAIL while still exercising dispatch, gas, and framing. -/
def zkvmBn254G1MulSafeFailWrapper : String :=
  ".globl zkvm_bn254_g1_mul\n" ++
  "zkvm_bn254_g1_mul:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for
    `zkvm_bn254_pairing(pairs, num_pairs, verified)`. Current runtime tests use
    deterministic EFAIL while still exercising dispatch, gas, and framing. -/
def zkvmBn254PairingSafeFailWrapper : String :=
  ".globl zkvm_bn254_pairing\n" ++
  "zkvm_bn254_pairing:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for
    `zkvm_blake2f(rounds, h, m, t, f)`. Current runtime tests use
    deterministic EFAIL until the BLAKE2F accelerator path is available from
    bare codegen ELFs. -/
def zkvmBlake2fSafeFailWrapper : String :=
  ".globl zkvm_blake2f\n" ++
  "zkvm_blake2f:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for
    `zkvm_kzg_point_eval(commitment, z, y, proof, verified)`. Current runtime
    tests use deterministic EFAIL while still exercising dispatch, length,
    gas, and framing. -/
def zkvmKzgPointEvalSafeFailWrapper : String :=
  ".globl zkvm_kzg_point_eval\n" ++
  "zkvm_kzg_point_eval:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for
    `zkvm_secp256r1_verify(msg, sig, pubkey, verified)`. Current runtime tests
    use deterministic EFAIL while still exercising P256VERIFY dispatch, gas,
    length, and framing. -/
def zkvmSecp256r1VerifySafeFailWrapper : String :=
  ".globl zkvm_secp256r1_verify\n" ++
  "zkvm_secp256r1_verify:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Probe driver for the BLS12 G1 ADD wrapper. It initializes two 96-byte
    zero point buffers and a 96-byte result buffer, calls the wrapper, then
    writes a compact record at OUTPUT_ADDR:

      OUTPUT+0   : returned zkvm_status as u64
      OUTPUT+8   : first 8 bytes of result buffer
      OUTPUT+16  : second 8 bytes of result buffer

    The shell harness classifies `0` (EOK) and `-1` (EFAIL) as a linked
    backend return. On the current host this probe uses the deterministic
    safe-fail shim above, so it should complete with EFAIL instead of crashing
    on the unsupported ECALL route. -/
def ziskBls12G1AddBackendProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, bls12_g1_add_result\n" ++
  "  li t1, 12\n" ++
  "  li t2, -6148914691236517206\n" ++ -- 0xaaaaaaaaaaaaaaaa
  ".Lbls12_g1_add_fill_result:\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lbls12_g1_add_fill_result\n" ++
  "  la a0, bls12_g1_add_p1\n" ++
  "  la a1, bls12_g1_add_p2\n" ++
  "  la a2, bls12_g1_add_result\n" ++
  "  jal ra, zkvm_bls12_g1_add\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, bls12_g1_add_result\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  ld t2, 8(t1)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  j .Lbls12_g1_add_done\n" ++
  zkvmBls12G1AddSafeFailWrapper ++ "\n" ++
  ".Lbls12_g1_add_done:"

def ziskBls12G1AddBackendProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bls12_g1_add_p1:\n" ++
  "  .zero 96\n" ++
  "bls12_g1_add_p2:\n" ++
  "  .zero 96\n" ++
  "bls12_g1_add_result:\n" ++
  "  .zero 96"


/-- Linkable bare-RV64 safe-fail wrapper for a BLS12 accelerator selector.
    Current ziskemu does not complete the BLS12 accelerator ECALL selectors from
    bare codegen ELFs. Keep each ABI symbol linkable and deterministic by
    returning EFAIL (-1) without touching the result buffer. -/
def bls12SafeFailWrapper (symbol : String) (_selectorHex : String) : String :=
  ".globl " ++ symbol ++ "\n" ++
  symbol ++ ":\n" ++
  "  li a0, -1\n" ++
  "  ret"

private def fillPatternAsm (label : String) (buffer : String) (bytes : Nat) : String :=
  "  la t0, " ++ buffer ++ "\n" ++
  "  li t1, " ++ toString (bytes / 8) ++ "\n" ++
  "  li t2, -6148914691236517206\n" ++
  "." ++ label ++ "_fill:\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, ." ++ label ++ "_fill\n"

private def copyProbeOutputAsm (resultLabel : String) : String :=
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, " ++ resultLabel ++ "\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  ld t2, 8(t1)\n" ++
  "  sd t2, 16(t0)\n"

/-- Linkable bare-RV64 wrapper for
    `zkvm_secp256k1_ecrecover(msg, sig, recid, output)`.
    The installed ziskemu does not currently expose a success-producing
    recovery route from bare codegen ELFs. Keep the ABI linkable and
    deterministic by returning EFAIL (-1) without touching the pubkey buffer;
    replacing this shim with a real recovery backend is tracked by the
    ECRECOVER backend bead. -/
def zkvmSecp256k1EcrecoverSafeFailWrapper : String :=
  ".globl zkvm_secp256k1_ecrecover\n" ++
  "zkvm_secp256k1_ecrecover:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Linkable bare-RV64 wrapper for
    `zkvm_modexp(base, base_len, exp, exp_len, modulus, mod_len, output)`.
    The current runtime harness does not expose a success-producing MODEXP
    backend, so this deterministic shim reports EFAIL while preserving the ABI
    call surface for the dispatcher path. -/
def zkvmModexpSafeFailWrapper : String :=
  ".globl zkvm_modexp\n" ++
  "zkvm_modexp:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Probe driver for the ECRECOVER backend ABI. It passes valid_signature_1
    from docs/eest-precompile-frontier.md to the linkable wrapper and writes:

      OUTPUT+0   : returned zkvm_status as u64
      OUTPUT+8   : first 8 bytes of recovered-pubkey buffer
      OUTPUT+16  : second 8 bytes of recovered-pubkey buffer

    On the current host the deterministic safe-fail wrapper returns EFAIL and
    leaves the poison-filled output buffer unchanged. -/
def ziskSecp256k1EcrecoverBackendProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  fillPatternAsm "Lsecp256k1_ecrecover" "secp256k1_ecrecover_output" 64 ++
  "  la a0, secp256k1_ecrecover_msg\n" ++
  "  la a1, secp256k1_ecrecover_sig\n" ++
  "  li a2, 1\n" ++
  "  la a3, secp256k1_ecrecover_output\n" ++
  "  jal ra, zkvm_secp256k1_ecrecover\n" ++
  copyProbeOutputAsm "secp256k1_ecrecover_output" ++
  "  j .Lsecp256k1_ecrecover_done\n" ++
  zkvmSecp256k1EcrecoverSafeFailWrapper ++ "\n" ++
  ".Lsecp256k1_ecrecover_done:"

def ziskSecp256k1EcrecoverBackendProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "secp256k1_ecrecover_msg:\n" ++
  "  .byte 0x18,0xc5,0x47,0xe4,0xf7,0xb0,0xf3,0x25\n" ++
  "  .byte 0xad,0x1e,0x56,0xf5,0x7e,0x26,0xc7,0x45\n" ++
  "  .byte 0xb0,0x9a,0x3e,0x50,0x3d,0x86,0xe0,0x0e\n" ++
  "  .byte 0x52,0x55,0xff,0x7f,0x71,0x5d,0x3d,0x1c\n" ++
  "secp256k1_ecrecover_sig:\n" ++
  "  .byte 0x73,0xb1,0x69,0x38,0x92,0x21,0x9d,0x73\n" ++
  "  .byte 0x6c,0xab,0xa5,0x5b,0xdb,0x67,0x21,0x6e\n" ++
  "  .byte 0x48,0x55,0x57,0xea,0x6b,0x6a,0xf7,0x5f\n" ++
  "  .byte 0x37,0x09,0x6c,0x9a,0xa6,0xa5,0xa7,0x5f\n" ++
  "  .byte 0xee,0xb9,0x40,0xb1,0xd0,0x3b,0x21,0xe3\n" ++
  "  .byte 0x6b,0x0e,0x47,0xe7,0x97,0x69,0xf0,0x95\n" ++
  "  .byte 0xfe,0x2a,0xb8,0x55,0xbd,0x91,0xe3,0xa3\n" ++
  "  .byte 0x87,0x56,0xb7,0xd7,0x5a,0x9c,0x45,0x49\n" ++
  "secp256k1_ecrecover_output:\n" ++
  "  .zero 64"


/-- Probe driver for the real linked ECRECOVER backend ABI.

    Unlike `ziskSecp256k1EcrecoverBackendProbePrologue`, this program does not
    append `zkvmSecp256k1EcrecoverSafeFailWrapper`. If the current toolchain
    cannot resolve `zkvm_secp256k1_ecrecover`, the companion script classifies
    that link failure as backend-not-ready instead of silently exercising the
    deterministic shim.

    Input at `0x40000000`:

      +0    32-byte message hash
      +32   64-byte signature (`r || s`)
      +96   8-byte recovery id word (low byte consumed by the backend)

    Output at `0xa0010000`:

      +0    returned zkvm_status as u64
      +8    64-byte recovered public key buffer
-/
def ziskSecp256k1EcrecoverRealBackendProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  addi s2, s1, 8\n" ++
  "  li t0, 8\n" ++
  "  mv t1, s2\n" ++
  "  li t2, -6148914691236517206\n" ++
  ".Lsecp256k1_ecrecover_real_fill:\n" ++
  "  sd t2, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, -1\n" ++
  "  bnez t0, .Lsecp256k1_ecrecover_real_fill\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, s0, 32\n" ++
  "  ld a2, 96(s0)\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, zkvm_secp256k1_ecrecover\n" ++
  "  sd a0, 0(s1)\n"


/-- Probe driver for the MODEXP backend ABI. It passes 2^5 mod 13 with
    one-byte components and records the returned status plus the first two
    output words. The safe-fail shim leaves the poison output unchanged. -/
def ziskModexpBackendProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  fillPatternAsm "Lmodexp_backend" "modexp_backend_output" 16 ++
  "  la a0, modexp_backend_base\n" ++
  "  li a1, 1\n" ++
  "  la a2, modexp_backend_exp\n" ++
  "  li a3, 1\n" ++
  "  la a4, modexp_backend_modulus\n" ++
  "  li a5, 1\n" ++
  "  la a6, modexp_backend_output\n" ++
  "  jal ra, zkvm_modexp\n" ++
  copyProbeOutputAsm "modexp_backend_output" ++
  "  j .Lmodexp_backend_done\n" ++
  zkvmModexpSafeFailWrapper ++ "\n" ++
  ".Lmodexp_backend_done:"

def ziskModexpBackendProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "modexp_backend_base:\n" ++
  "  .byte 0x02\n" ++
  "modexp_backend_exp:\n" ++
  "  .byte 0x05\n" ++
  "modexp_backend_modulus:\n" ++
  "  .byte 0x0d\n" ++
  ".balign 8\n" ++
  "modexp_backend_output:\n" ++
  "  .zero 16"


/-- One MODEXP real-backend probe vector. Zeroes the shared 8-byte output word,
    calls the *real* linked `zkvm_modexp` with the given operand buffers and
    byte-lengths, then records at `0xa0010000 + 16*recordIdx`:

      +0  returned zkvm_status as u64
      +8  first output word (LE-loaded from the BE output buffer)

    Callers pick operands so the low output word is a compact regression witness
    (e.g. `exp==0, mod==1` must yield 0, not the raw result=1). -/
private def modexpRealProbeVector
    (baseLabel expLabel modLabel : String)
    (blen elen mlen recordIdx : Nat) : String :=
  "  la t0, modexp_real_output\n" ++ "  sd zero, 0(t0)\n" ++
  "  la a0, " ++ baseLabel ++ "\n" ++ "  li a1, " ++ toString blen ++ "\n" ++
  "  la a2, " ++ expLabel ++ "\n" ++ "  li a3, " ++ toString elen ++ "\n" ++
  "  la a4, " ++ modLabel ++ "\n" ++ "  li a5, " ++ toString mlen ++ "\n" ++
  "  la a6, modexp_real_output\n" ++
  "  jal ra, zkvm_modexp\n" ++
  "  li t0, " ++ toString (0xa0010000 + 16 * recordIdx) ++ "\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, modexp_real_output\n" ++ "  ld t2, 0(t1)\n" ++ "  sd t2, 8(t0)\n"

/-- Probe driver for the *real* linked MODEXP backend (`zkvmModexpBackendImpl`),
    with no deterministic safe-fail shim. Unlike `ziskModexpBackendProbeUnit`,
    this exercises the actual bignum square-and-multiply and records four
    regression vectors (each routed to the bignum path via base_len=5):

      record 0 : exp==0, mod==1   → 0    (the 4ch8f.11.5 divergence witness)
      record 1 : exp==0, mod==13  → 1
      record 2 : exp==0, mod==0   → zeros
      record 3 : 2^5 mod 13       → 6    (unchanged happy path)

    On pre-fix code record 0's output word is 1 (raw, unreduced); the fix
    reduces it to 0. -/
def ziskModexpBackendRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  modexpRealProbeVector "modexp_real_base" "modexp_real_exp0" "modexp_real_mod1" 5 1 5 0 ++
  modexpRealProbeVector "modexp_real_base" "modexp_real_exp0" "modexp_real_mod13" 5 1 5 1 ++
  modexpRealProbeVector "modexp_real_base" "modexp_real_exp0" "modexp_real_mod0" 5 1 5 2 ++
  modexpRealProbeVector "modexp_real_base" "modexp_real_exp5" "modexp_real_mod13" 5 1 5 3 ++
  "  j .Lmodexp_real_done\n" ++
  zkvmModexpBackendImpl ++ "\n" ++
  ".Lmodexp_real_done:"

def ziskModexpBackendRealProbeDataSection : String :=
  ".section .data\n" ++
  emitModexpBnScratchData ++
  ".balign 8\n" ++
  "modexp_real_base:\n" ++ "  .byte 0x00,0x00,0x00,0x00,0x02\n" ++
  "modexp_real_exp0:\n" ++ "  .byte 0x00\n" ++
  "modexp_real_exp5:\n" ++ "  .byte 0x05\n" ++
  "modexp_real_mod1:\n" ++ "  .byte 0x00,0x00,0x00,0x00,0x01\n" ++
  "modexp_real_mod13:\n" ++ "  .byte 0x00,0x00,0x00,0x00,0x0d\n" ++
  "modexp_real_mod0:\n" ++ "  .byte 0x00,0x00,0x00,0x00,0x00\n" ++
  ".balign 8\n" ++
  "modexp_real_output:\n" ++ "  .zero 16"


private def bls12BackendProbePrologue
    (label symbol selectorHex resultLabel setupArgs : String)
    (resultBytes : Nat) : String :=
  "  li sp, 0xa0050000\n" ++
  fillPatternAsm label resultLabel resultBytes ++
  setupArgs ++
  "  jal ra, " ++ symbol ++ "\n" ++
  copyProbeOutputAsm resultLabel ++
  "  j ." ++ label ++ "_done\n" ++
  bls12SafeFailWrapper symbol selectorHex ++ "\n" ++
  "." ++ label ++ "_done:"

private def bls12ProbeDataSection (items : List (String × Nat)) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  String.intercalate "" (items.map fun (name, bytes) =>
    name ++ ":\n" ++
    "  .zero " ++ toString bytes ++ "\n")

def ziskBls12G1MsmBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_g1_msm" "zkvm_bls12_g1_msm" "0x10c" "bls12_g1_msm_result"
    ("  la a0, bls12_g1_msm_pairs\n" ++
     "  li a1, 1\n" ++
     "  la a2, bls12_g1_msm_result\n")
    96

def ziskBls12G1MsmBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_g1_msm_pairs", 128), ("bls12_g1_msm_result", 96)]


def ziskBls12G2AddBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_g2_add" "zkvm_bls12_g2_add" "0x10d" "bls12_g2_add_result"
    ("  la a0, bls12_g2_add_p1\n" ++
     "  la a1, bls12_g2_add_p2\n" ++
     "  la a2, bls12_g2_add_result\n")
    192

def ziskBls12G2AddBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_g2_add_p1", 192), ("bls12_g2_add_p2", 192),
     ("bls12_g2_add_result", 192)]


def ziskBls12G2MsmBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_g2_msm" "zkvm_bls12_g2_msm" "0x10e" "bls12_g2_msm_result"
    ("  la a0, bls12_g2_msm_pairs\n" ++
     "  li a1, 1\n" ++
     "  la a2, bls12_g2_msm_result\n")
    192

def ziskBls12G2MsmBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_g2_msm_pairs", 224), ("bls12_g2_msm_result", 192)]


def ziskBls12PairingBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_pairing" "zkvm_bls12_pairing" "0x10f" "bls12_pairing_verified"
    ("  la a0, bls12_pairing_pairs\n" ++
     "  li a1, 1\n" ++
     "  la a2, bls12_pairing_verified\n")
    16

def ziskBls12PairingBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_pairing_pairs", 288), ("bls12_pairing_verified", 16)]


def ziskBls12MapFpToG1BackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_map_fp_to_g1" "zkvm_bls12_map_fp_to_g1" "0x110" "bls12_map_fp_to_g1_result"
    ("  la a0, bls12_map_fp_to_g1_input\n" ++
     "  la a1, bls12_map_fp_to_g1_result\n")
    96

def ziskBls12MapFpToG1BackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_map_fp_to_g1_input", 48), ("bls12_map_fp_to_g1_result", 96)]


def ziskBls12MapFp2ToG2BackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_map_fp2_to_g2" "zkvm_bls12_map_fp2_to_g2" "0x111" "bls12_map_fp2_to_g2_result"
    ("  la a0, bls12_map_fp2_to_g2_input\n" ++
     "  la a1, bls12_map_fp2_to_g2_result\n")
    192

def ziskBls12MapFp2ToG2BackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_map_fp2_to_g2_input", 96), ("bls12_map_fp2_to_g2_result", 192)]


end EvmAsm.Codegen
