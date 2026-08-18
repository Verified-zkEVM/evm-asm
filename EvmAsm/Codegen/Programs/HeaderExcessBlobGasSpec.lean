/-
  EvmAsm.Codegen.Programs.HeaderExcessBlobGasSpec

  Whole-routine spec for `header_validate_excess_blob_gas` (GH #12346
  critical path): the machine's three-way status corresponds to
  `SpecRef.calculate_excess_blob_gas` —

    x10 = 0  ↔  spec succeeds and equals the caller-supplied excess (`a0`)
    x10 = 2  ↔  spec succeeds and differs from `a0`
    x10 = 1  ↔  spec raises (`OverflowError` envelope)

  Both directions ride the same disjunction: each status pins exactly one
  spec outcome, and each spec outcome pins exactly one status (the
  arithmetic decisions inside the routine are deterministic in the spec
  values).

  The first external callee (`amsterdam_blob_gas_price_u256`) has no
  whole-routine spec yet (maintainer work in flight,
  `AmsterdamBlobGasPriceU256Sat.lean` witnesses); it enters the top
  theorem as ONE named hypothesis.  Registry row lands at `.conditional`
  with that gate named; the axiom-witness entry rides in the same PR.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.U256LtBeSAsm
import EvmAsm.Codegen.Programs.U256MulU64Be.WholeInPlace
import EvmAsm.Stateless.SpecRef.Gas

namespace EvmAsm.Codegen.HeaderExcessBlobGasSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.U256MulU64Be

/-- Routine entry. -/
abbrev H : Word := (GuestAddrs.header_validate_excess_blob_gas : Word)

/-- The routine program. -/
abbrev hvebgProg : Program := EvmAsm.Codegen.headerValidateExcessBlobGas_prog

theorem hvebg_length : hvebgProg.length = 71 := by decide

/-- The routine's own code. -/
abbrev hvebgCode : CodeReq := CodeReq.ofProg H hvebgProg

/-- `u256_lt_be` entry address (local abbrev so disjointness arithmetic
    keeps a rewriteable left-hand side). -/
abbrev ltBase : Word := GuestAddrs.u256_lt_be

/-- `u256_lt_be` code. -/
abbrev ltCode : CodeReq := CodeReq.ofProg ltBase u256LtBe_prog

/-- `u256_mul_u64_be` code. -/
abbrev mulCode : CodeReq := U256MulU64Be.mulCR

/-- Full code: the routine plus its two proven callees.  The price helper's
    code is supplied by the (conditional) price-spec hypothesis at use
    sites, so it is not unioned here. -/
abbrev fullCode : CodeReq := (hvebgCode.union mulCode).union ltCode

/-- Disjointness: routine vs `u256_lt_be` (ranges are far apart). -/
theorem hvebg_lt_disjoint : hvebgCode.Disjoint ltCode :=
  CodeReq.ofProg_disjoint_range_len (H : Word) hvebgProg 71
    ltBase u256LtBe_prog 19 hvebg_length (by rfl)
    (fun k1 k2 hk1 hk2 h => by
      have hS : (H : Word).toNat = GuestAddrs.header_validate_excess_blob_gas := by
        decide
      have hV : ltBase.toNat = GuestAddrs.u256_lt_be := by
        decide
      simp only [GuestAddrs.header_validate_excess_blob_gas,
        GuestAddrs.u256_lt_be] at hS hV
      have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hS, hV] at h1
      omega)

/-- Disjointness: routine vs `u256_mul_u64_be`. -/
theorem hvebg_mul_disjoint : hvebgCode.Disjoint mulCode :=
  CodeReq.ofProg_disjoint_range_len (H : Word) hvebgProg 71
    U256MulU64Be.mulBase mulProg 88 hvebg_length (by rfl)
    (fun k1 k2 hk1 hk2 h => by
      have hS : (H : Word).toNat = GuestAddrs.header_validate_excess_blob_gas := by
        decide
      have hV : (U256MulU64Be.mulBase).toNat =
          GuestAddrs.u256_mul_u64_be := by decide
      simp only [GuestAddrs.header_validate_excess_blob_gas,
        GuestAddrs.u256_mul_u64_be] at hS hV
      have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hS, hV] at h1
      omega)

/-- Frame layout: return address + six callee-saved registers, slots at
    `sp0 − 64 + 8k`, matching `ValidateHeaderGasCorrespondence.excessFrame`. -/
def hvebgFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48)]

/-- Saved-register sub-frame (the subset restored as pinned values). -/
def hvebgSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48)]

/-- Frame values with the return-address slot set to `ret`. -/
def hvebgFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

/-- Whole-routine precondition at `H`, mirroring
    `ValidateHeaderGasCorrespondence.excessEntryRest` (`x2 = sp0`, frame
    slots owned at `spC`, saved registers pinned at `vals`, ABI in
    `x10..x13`).  `scratch` covers the shared `.data` scratch cells
    (`hvebg_threshold`, `u256m_acc`). -/
def hvebgPre (sp0 spC : Word) (vals : Reg → Word) (a0 a1 a2 a3 : Word)
    (scratch : Assertion) : Assertion :=
  (regIs .x2 sp0) **
    frameSlotsOwn hvebgFrame spC **
    regsAt hvebgSavedFrame vals **
    (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) ** (regIs .x13 a3) **
    regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
    (regIs .x0 (0 : Word)) ** scratch

/-- Common return state shared by all three status outcomes: frame restored
    (`x2 = sp0`, saved slots), `x1 = raIn`, scratch registers owned. -/
def hvebgCommonRet (sp0 spC raIn : Word) (vals : Reg → Word)
    (scratch : Assertion) : Assertion :=
  (regIs .x2 sp0) ** (regIs .x1 raIn) **
    frameSlotsSaved hvebgFrame spC (hvebgFrameVals raIn vals) **
    regsAt hvebgSavedFrame vals **
    regOwns [.x5, .x6, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
    (regIs .x0 (0 : Word)) ** scratch

/-- Outcome 1 (`x10 = 0`): the spec succeeds and its value equals the
    caller-supplied `this.excess_blob_gas` (`a0`). -/
def hvebgSuccess (parent : EvmAsm.Stateless.SpecRef.Header) (a0 : Word)
    (sp0 spC raIn : Word) (vals : Reg → Word)
    (scratch : Assertion) : Assertion :=
  ⌜∃ v, EvmAsm.Stateless.SpecRef.calculate_excess_blob_gas parent = .ok v ∧
    v = a0.toNat⌝ ** (regIs .x10 (0 : Word)) **
    hvebgCommonRet sp0 spC raIn vals scratch

/-- Outcome 2 (`x10 = 2`): the spec succeeds and its value differs from
    `a0` — the header's excess-blob-gas field is wrong. -/
def hvebgMismatch (parent : EvmAsm.Stateless.SpecRef.Header) (a0 : Word)
    (sp0 spC raIn : Word) (vals : Reg → Word)
    (scratch : Assertion) : Assertion :=
  ⌜∃ v, EvmAsm.Stateless.SpecRef.calculate_excess_blob_gas parent = .ok v ∧
    v ≠ a0.toNat⌝ ** (regIs .x10 (2 : Word)) **
    hvebgCommonRet sp0 spC raIn vals scratch

/-- Outcome 3 (`x10 = 1`): the spec raises (u64 envelope overflow on the
    parent blob-gas sum or the schedule-path multiply). -/
def hvebgError (parent : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn : Word) (vals : Reg → Word)
    (scratch : Assertion) : Assertion :=
  ⌜∃ e, EvmAsm.Stateless.SpecRef.calculate_excess_blob_gas parent = .error e⌝ **
    (regIs .x10 (1 : Word)) ** hvebgCommonRet sp0 spC raIn vals scratch

/-- Unified postcondition: exactly one disjunct holds, and each disjunct
    pins one spec outcome — this is the both-directions correspondence at
    the routine boundary. -/
def hvebgPost (parent : EvmAsm.Stateless.SpecRef.Header) (a0 : Word)
    (sp0 spC raIn : Word) (vals : Reg → Word)
    (scratch : Assertion) : Assertion := fun h =>
  hvebgSuccess parent a0 sp0 spC raIn vals scratch h ∨
    hvebgMismatch parent a0 sp0 spC raIn vals scratch h ∨
    hvebgError parent sp0 spC raIn vals scratch h

end EvmAsm.Codegen.HeaderExcessBlobGasSpec
