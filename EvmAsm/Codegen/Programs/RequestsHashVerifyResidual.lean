/-
  EvmAsm.Codegen.Programs.RequestsHashVerifyResidual

  The named callee residual for `requests_hash_verify`'s second call site
  (#12206 item 2): the `jal ra, execution_requests_hash` at index 12
  (0x8005437c).

  WHY THIS IS A RESIDUAL AND NOT A COMPOSITION.  `execution_requests_hash` IS
  rowed in the registry, but as `.conditional` covering only its
  VALIDATION-ACCEPT PREFIX: `execution_requests_hash_validation_accept` is a
  triple from `B` to `B + 300` at fuel 135, and that row's own notes say "Hash
  half residual." A prefix triple that stops 300 bytes into the callee does not
  return to its caller, so there is NO caller-visible contract to compose here
  today — not a weaker one, none at all. Stating this call under a named,
  satisfiable residual is therefore the honest posture, per the house rule that
  an unproven-callee residual is a DEPENDENCY, not an input-domain gate.

  WHAT THE RESIDUAL DELIBERATELY DOES NOT SAY.  `erhCallReturn` says the callee
  writes SOME 32 bytes into the output buffer and returns SOME status word. It
  does NOT say those bytes are `SpecRef`'s `requests_hash` of the section. That
  missing equation is exactly the inherited "Hash half residual", whose own
  discharge sits under `shaCallWithinShape` with owner #12018
  (`zkvm_sha256_spec_within`). Keeping the digest abstract is what makes the
  `requests_hash_verify` contract provable AND honest: the routine is proved to
  compare whatever digest the callee produced against the header's expected
  hash and to report `0`/`1`/`2` accordingly, which is the whole of its own
  behaviour.

  Discharge owners, in order: #12018 `zkvm_sha256_spec_within` (the hash half),
  then the return-path half of `execution_requests_hash` itself.
-/

import EvmAsm.Codegen.Programs.RequestsHashVerifyBase
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.RequestsHashVerifyResidual

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RequestsHashVerifyBase

/-- Free stack the callee carves its own frame from. `execution_requests_hash`
    opens with `sp -= 96` (registry row: "prologue sp-96"), i.e. 12 dwords. -/
def erhStackDwords : Nat := 12

/-- Nominal step budget for the residual call. Not load-bearing: the whole
    routine's step count is stated as a function of this parameter, so a
    discharge at any fuel instantiates it. -/
def erhResidualFuel : Nat := 4000

/-- Every caller-saved register the callee may clobber, held as OWNED and
    named in the residual's FOOTPRINT rather than left to the universal frame.

    This is deliberate and load-bearing. `cpsTripleWithin` quantifies over all
    frames `R`, so a caller may instantiate `R := r ↦ᵣ v` for any register `r`
    the footprint does not mention; if the callee then writes `r`, the triple is
    FALSE. Every register the callee may clobber must therefore appear in `P`
    and `Q`, which is what naming them here guarantees.

    ⚠️ What this argument does NOT say: that carrying a clobbered temp through a
    parameterised frame `F` is unsound. `F` is part of both `P` and `Q`, so a
    register held there as `regOwn` IS in the footprint, and `regOwn r` is
    `∃ v, regIs r v h` (`Rv64/SepLogic.lean`) — an existential over the value,
    so pre and post may be witnessed by different values and a clobber is fine.
    `shaCallWithinShape`'s `x5`–`x7`/`x28`–`x31` treatment is sound on exactly
    that reading. The real hazard is a frame carrying a CONCRETE `r ↦ᵣ v` on
    both sides for an `r` the callee writes — a different mistake, and one that
    has to be checked against the callee's measured clobber set rather than
    assumed. (GuestAddrs.zkvm_sha256 = 0x800018c0 saves and restores all of
    `s0`–`s5` and writes only `a0`/`t0`–`t5`, so the concrete
    `x13`/`x14`/`x24`/`x26` in `erh_hash_one`'s `F` are genuinely preserved.)

    `x8`/`x9` are NOT here: they are callee-saved, so a correct
    `execution_requests_hash` restores them and they may safely live in `F`.
    `requests_hash_verify` depends on exactly that — it reads `s0` at index 16
    (0x8005438c `mv t1, s0`), after this call returns. -/
def erhScratchOwn : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
  regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem erhScratchOwn_pcFree : erhScratchOwn.pcFree := by
  unfold erhScratchOwn
  repeat first | apply pcFree_sepConj | exact pcFree_regOwn

/-- Call-site entry ambient for `execution_requests_hash`:
    `a0` = SSZ section pointer, `a1` = section length, `a2` = 32-byte output. -/
def erhCallEntry (sp0 secPtr secLenW outPtr : Word)
    (sec outOld : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 erhStackDwords **
  (.x10 ↦ᵣ secPtr) ** (.x11 ↦ᵣ secLenW) ** (.x12 ↦ᵣ outPtr) **
  (.x0 ↦ᵣ (0 : Word)) ** erhScratchOwn **
  bytesRegion secPtr sec ** bytesRegion outPtr outOld

/-- Call-site return: the section is unchanged, the output buffer holds SOME
    32 bytes `dig`, and `a0` holds SOME status word `st`.

    Both are universally quantified by the shape's user, so nothing about the
    digest's VALUE is assumed here — see the module docstring. -/
def erhCallReturn (sp0 secPtr outPtr st : Word)
    (sec dig : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 erhStackDwords **
  (.x10 ↦ᵣ st) ** regOwn .x11 ** regOwn .x12 **
  (.x0 ↦ᵣ (0 : Word)) ** erhScratchOwn **
  bytesRegion secPtr sec ** bytesRegion outPtr dig

/-- The NON-TRIPLE side conditions of the residual, split out so that they can
    be discharged concretely at the real call site — this is where a vacuity
    hole would hide. `erhCallSite_ok` (RequestsHashVerifyTop) closes all of
    them against the emitted image. -/
def ErhCallSiteOk (cr : CodeReq) (callerPC : Word)
    (outOld dig : List (BitVec 8))
    (offset : BitVec 21) (F : Assertion) : Prop :=
  F.pcFree ∧
  ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = ErhB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
    cr a = some i) ∧
  outOld.length = 32 ∧ dig.length = 32

/-- Shape the residual `h_erh` must satisfy at the call site at index 12. -/
def ErhCallShape (cr : CodeReq)
    (callerPC vOld sp0 secPtr secLenW outPtr st : Word)
    (sec outOld dig : List (BitVec 8))
    (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  ErhCallSiteOk cr callerPC outOld dig offset F ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) **
      erhCallEntry sp0 secPtr secLenW outPtr sec outOld) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) **
      erhCallReturn sp0 secPtr outPtr st sec dig) ** F)

/-- Obligation-retirement note, rendered into `Progress.Obligations`. -/
def erhReturnResidualNote : String :=
  "requests_hash_verify's `jal execution_requests_hash` (index 12, \
0x8005437c) stands under `ErhCallShape`. The registry's \
`execution_requests_hash` row is `.conditional` over the VALIDATION-ACCEPT \
PREFIX only (B → B+300, fuel 135) and its notes say `Hash half residual`, so \
that prefix does not return to the caller and cannot be composed here. \
UNPROVEN-CALLEE residual DEPENDENCY, not an input-domain gate. Discharge \
owners: #12018 `zkvm_sha256_spec_within` for the hash half (via \
`shaCallWithinShape`), then the return path of `execution_requests_hash` \
itself. The residual leaves the digest ABSTRACT on purpose: \
requests_hash_verify's own behaviour (compare 32 bytes, report 0/1/2) is \
proved in full against an arbitrary digest."

end EvmAsm.Codegen.RequestsHashVerifyResidual
