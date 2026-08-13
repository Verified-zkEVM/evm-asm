/-
  EvmAsm.Codegen.Programs.AddressFromPubkeySpec

  Verification support for `address_from_pubkey` (PR-K99), the ECRECOVER
  trailing step:

      address = keccak256(pubkey_x ‖ pubkey_y)[12:32]      (20 bytes)

  This module lands the FIRST increment of the whole-routine triple asked
  for by GH #12224: the ABI-frame decomposition.  `addressFromPubkey_prog`
  is byte-identically a standard leaf frame, so `abiFrame_spec_own`
  supplies the prologue, the epilogue, the `sp` round-trip and the `jalr`
  return without any per-instruction reasoning; what remains for the
  triple is the 18-instruction body.

  ⚠️ Deliberately NOT proved here (see #12224 for the analysis):

  * the body triple, whose keccak leg would be the FIRST consumer of
    `zkvm_keccak256_spec_within` anywhere in the repo, and
  * the 20-iteration digest→output copy loop, which is top-tested and
    counts UP against a LIMIT REGISTER (`beq x6, x7`) and therefore
    matches none of the existing loop combinators (`countdownLoop_spec`
    hard-codes `beq ctr, x0`; `upLoop_spec` hard-codes `bgeu`).
  * ⚠️ `zkvm_keccak256_spec_within` fixes its output buffer to
    `List.replicate 32 0`, and this routine never zeroes `afp_digest` —
    so that becomes a precondition of the eventual whole-routine triple
    unless the keccak contract is first generalised over `out0`.
-/

import EvmAsm.Codegen.Programs.Address
import EvmAsm.Rv64.SAsm.AbiFrame

namespace EvmAsm.Codegen.AddressFromPubkeySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

/-- The saved-register frame of `address_from_pubkey`: `ra` at `0(sp)` and
    `s0` at `8(sp)`, in a 16-byte frame.  `s0` holds the caller's 20-byte
    output pointer across the `zkvm_keccak256` call. -/
def afpFrame : FrameDesc := [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12))]

/-- The body of `address_from_pubkey`: everything between the frame
    prologue and the frame epilogue — instructions 3..20 of
    `addressFromPubkey_prog`.

    Reading order: stash the output pointer in `s0`, set up the
    `zkvm_keccak256(a0 = pubkey, a1 = 64, a2 = afp_digest)` call, call it,
    then copy the 20 bytes at `afp_digest + 12` to the output, and set
    `a0 = 0`. -/
def afpBody : List Instr :=
  [ .MV .x8 .x11,
    .LI .x11 (64 : Word),
    .AUIPC .x12 (laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)),
    .ADDI .x12 .x12 (laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_from_pubkey + 28)),
    .AUIPC .x5 (laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)),
    .LI .x6 (0 : Word),
    .LI .x7 (20 : Word),
    .BEQ .x6 .x7 (32 : BitVec 13),
    .ADDI .x28 .x5 (12 : BitVec 12),
    .ADD .x28 .x28 .x6,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x28 .x8 .x6,
    .SB .x28 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word) ]

/-- **The frame decomposition.**  `addressFromPubkey_prog` is byte-identically
    the standard leaf ABI frame `abiFrameProg (-16) 16 afpFrame afpBody`:

    * `addi sp, sp, -16`,
    * `sd ra, 0(sp)` / `sd s0, 8(sp)`,
    * the 18-instruction body,
    * `ld ra, 0(sp)` / `ld s0, 8(sp)`, `addi sp, sp, 16`,
    * `jalr x0, ra, 0`.

    This is what lets `abiFrame_spec_own` (`Rv64/SAsm/AbiFrameOwn.lean`)
    discharge the prologue and epilogue of the eventual whole-routine
    triple, leaving only `afpBody` to prove.  Kernel-checked by `rfl`, so
    it is a genuine byte-level identity and not a re-statement: if the
    emitted program drifts (a changed frame size, an extra saved
    register, a reordered prologue), this stops compiling. -/
theorem addressFromPubkey_prog_eq_abiFrame :
    addressFromPubkey_prog = abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) afpFrame afpBody :=
  rfl

/-- The body is 18 instructions, so the frame arithmetic
    `1 + frame.length + bodySteps + frame.length + 1 + 1` that
    `abiFrame_spec_own` reports is instantiated at `frame.length = 2`. -/
theorem afpBody_length : afpBody.length = 18 := by decide

theorem afpFrame_length : afpFrame.length = 2 := by decide

/-- Total program length, re-derived through the decomposition rather than
    copied: `1 + 2 + 18 + 2 + 1 + 1 = 25`, agreeing with the `#guard` on
    `addressFromPubkey_prog` in `Programs/Address.lean`. -/
theorem addressFromPubkey_prog_length : addressFromPubkey_prog.length = 25 := by decide

/-- `abiFrame_spec_own`'s `hframe` side condition: the frame saves `ra`
    first.  Discharged here so the eventual triple can cite it by name. -/
theorem afpFrame_cons : afpFrame = (.x1, (0 : BitVec 12)) :: [(.x8, (8 : BitVec 12))] := rfl

/-- `abiFrame_spec_own`'s `hne` side condition: no frame slot saves `x0`. -/
theorem afpFrame_ne_zero : ∀ p ∈ afpFrame, p.1 ≠ .x0 := by decide

/-- `abiFrame_spec_own`'s `hframeRestore` side condition: the `-16` of the
    prologue and the `+16` of the epilogue round-trip `sp` exactly, for
    every starting `sp0`.  Proved over all 2^64 stack pointers by
    bitvector reasoning, not by `decide`. -/
theorem afpFrame_restore (sp0 : Word) :
    (sp0 + signExtend12 (-16 : BitVec 12)) + signExtend12 (16 : BitVec 12) = sp0 := by
  have h : signExtend12 (-16 : BitVec 12) + signExtend12 (16 : BitVec 12) = (0 : Word) := by
    decide
  rw [BitVec.add_assoc, h]
  simp

end EvmAsm.Codegen.AddressFromPubkeySpec
