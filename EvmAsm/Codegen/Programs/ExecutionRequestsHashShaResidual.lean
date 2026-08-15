/-
  ExecutionRequestsHashShaResidual — unproven-callee residual for `zkvm_sha256`.

  Coord rule (#12011 option B, 2026-08-11): `h_sha` is an UNPROVEN-CALLEE
  RESIDUAL = DEPENDENCY, not an input-domain gate.
  - Register in Progress.Obligations as a dependency.
  - Do NOT absorb into the conditional gate list (mono/gates/h_align/…).
  - Grade must say: conditional on unproven callee `zkvm_sha256`.
  - Retires when `zkvm_sha256_spec_within` lands — **#12018** (codex owns;
    keccak #11985 template). Hole with a named owner, not an indefinite residual.

  Shape mirrors `MptWalkResiduals.wlCallWithinShape`: a callWithin hyp at one
  JAL site, instantiated by compose lemmas rather than building the machine.
  Callee-saved x8/x9/x18-x21 pass through F (sha frame saves/restores them).
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashShaResidual

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Stateless.SpecRef

/-- GuestAddrs of the residual callee. -/
abbrev ShaB : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256

/-- Nominal fuel budget for one residual `zkvm_sha256` callWithin.
    Concrete once the machine lands; compose uses this as an opaque upper bound. -/
def shaResidualFuel : Nat := 500

/-- Call-site entry ambient for `zkvm_sha256` (ABI matches keccak wrapper):
    a0=input, a1=len, a2=output; stack free ≥ 6 dwords (sha frame sp-48). -/
def shaCallEntry (sp0 inPtr lenW outPtr : Word)
    (inBytes outOld : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 6 **
  (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inPtr inBytes ** bytesRegion outPtr outOld

/-- Call-site return after residual `zkvm_sha256`.
    Input preserved; output holds `sha256 inBytes` (pure SpecRef post).
    Owns ABI args x10-12 only. Non-callee-saved temps x5-7/x28-31 pass through
    F as owns (caller peels concrete values before the residual). Callee-saved
    x8/x9/x18-x21 restored by sha frame live in F.
    `regOwn .x0` (not `x0 ↦ 0`): matches `shaCallerPost` from the machine triple. -/
def shaCallReturn (sp0 inPtr outPtr : Word)
    (inBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 6 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x0 **
  bytesRegion inPtr inBytes **
  bytesRegion outPtr (sha256 inBytes)

/-- Shape a residual `h_sha` must satisfy at one callWithin site.
    Compose lemmas take `h_sha` of this shape (instantiated at the site's
    callerPC / F / bytes) rather than building the machine.
    Discharge owner: #12018 `zkvm_sha256_spec_within`. -/
def shaCallWithinShape (cr : CodeReq) (callerPC vOld sp0 inPtr lenW outPtr : Word)
    (inBytes outOld : List (BitVec 8))
    (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  F.pcFree ∧
  (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = ShaB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
    cr a = some i) ∧
  lenW.toNat = inBytes.length ∧
  outOld.length = 32 ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) ** shaCallEntry sp0 inPtr lenW outPtr inBytes outOld) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) ** shaCallReturn sp0 inPtr outPtr inBytes) ** F)

/-- Obligation retirement note. -/
def zkvmSha256ResidualNote : String :=
  "machine triple `zkvm_sha256_spec_within` (#12018, codex owns; keccak #11985 \
template) at GuestAddrs.zkvm_sha256, registered in Routines + Correspondence; \
erh_hash_one / execution_requests_hash hash-half then discharge via callWithin \
against that triple (shaCallWithinShape). Until then: UNPROVEN-CALLEE residual \
DEPENDENCY — not an input-domain gate; grade names zkvm_sha256; hole has owner \
#12018."

end EvmAsm.Codegen.ExecutionRequestsHashShaResidual
