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

/-! ## Staged theorems -/

/-- Prologue: 12 instructions — stack frame (`x2 −= 64`), seven saves
    (`x1, x8, x9, x18, x19, x20, x21`), four argument moves
    (`x8 ← a0`, `x9 ← a1`, `x18 ← a2`, `x19 ← a3`).  From the whole-routine
    entry pre (with `x1 = raIn` pinned) to the body-entry state at
    `H + 48`. -/
theorem hvebgPrologue_spec (sp0 spC raIn : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 : Word)
    (scratch : Assertion) (hscratch : scratch.pcFree)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 12 H (H + 48) hvebgCode
      ((regIs .x1 raIn) ** (regIs .x2 sp0) **
        memOwn (spC + signExtend12 (0 : BitVec 12)) **
        memOwn (spC + signExtend12 (8 : BitVec 12)) **
        memOwn (spC + signExtend12 (16 : BitVec 12)) **
        memOwn (spC + signExtend12 (24 : BitVec 12)) **
        memOwn (spC + signExtend12 (32 : BitVec 12)) **
        memOwn (spC + signExtend12 (40 : BitVec 12)) **
        memOwn (spC + signExtend12 (48 : BitVec 12)) **
        (regIs .x8 (vals .x8)) ** (regIs .x9 (vals .x9)) **
        (regIs .x18 (vals .x18)) ** (regIs .x19 (vals .x19)) **
        (regIs .x20 (vals .x20)) ** (regIs .x21 (vals .x21)) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) **
        regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
        (regIs .x0 (0 : Word)) ** scratch)
      ((regIs .x2 spC) ** (regIs .x1 raIn) **
        (regIs .x8 a0) ** (regIs .x9 a1) ** (regIs .x18 a2) **
        (regIs .x19 a3) ** (regIs .x20 (vals .x20)) **
        (regIs .x21 (vals .x21)) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) **
        ((spC + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
        ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ (vals .x8)) **
        ((spC + signExtend12 (16 : BitVec 12)) ↦ₘ (vals .x9)) **
        ((spC + signExtend12 (24 : BitVec 12)) ↦ₘ (vals .x18)) **
        ((spC + signExtend12 (32 : BitVec 12)) ↦ₘ (vals .x19)) **
        ((spC + signExtend12 (40 : BitVec 12)) ↦ₘ (vals .x20)) **
        ((spC + signExtend12 (48 : BitVec 12)) ↦ₘ (vals .x21)) **
        regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
        (regIs .x0 (0 : Word)) ** scratch) := by
  subst hspC
  have s0 := addi_spec_gen_same_within .x2 sp0 (-64 : BitVec 12) H (by decide)
  have s1 := sd_spec_gen_own_within .x2 .x1 (sp0 + signExtend12 (-64 : BitVec 12)) raIn (0 : BitVec 12) (H + 4)
  have s2 := sd_spec_gen_own_within .x2 .x8 (sp0 + signExtend12 (-64 : BitVec 12)) (vals .x8) (8 : BitVec 12) (H + 8)
  have s3 := sd_spec_gen_own_within .x2 .x9 (sp0 + signExtend12 (-64 : BitVec 12)) (vals .x9) (16 : BitVec 12) (H + 12)
  have s4 := sd_spec_gen_own_within .x2 .x18 (sp0 + signExtend12 (-64 : BitVec 12)) (vals .x18) (24 : BitVec 12) (H + 16)
  have s5 := sd_spec_gen_own_within .x2 .x19 (sp0 + signExtend12 (-64 : BitVec 12)) (vals .x19) (32 : BitVec 12) (H + 20)
  have s6 := sd_spec_gen_own_within .x2 .x20 (sp0 + signExtend12 (-64 : BitVec 12)) (vals .x20) (40 : BitVec 12) (H + 24)
  have s7 := sd_spec_gen_own_within .x2 .x21 (sp0 + signExtend12 (-64 : BitVec 12)) (vals .x21) (48 : BitVec 12) (H + 28)
  have s8 := mv_spec_gen_within .x8 .x10 a0 (vals .x8) (H + 32) (by decide)
  have s9 := mv_spec_gen_within .x9 .x11 a1 (vals .x9) (H + 36) (by decide)
  have s10 := mv_spec_gen_within .x18 .x12 a2 (vals .x18) (H + 40) (by decide)
  have s11 := mv_spec_gen_within .x19 .x13 a3 (vals .x19) (H + 44) (by decide)
  have hblock : cpsTripleWithin 12 H (H + 48) hvebgCode
      ((regIs .x2 sp0) ** (regIs .x1 raIn) **
        (regIs .x8 (vals .x8)) ** (regIs .x9 (vals .x9)) **
        (regIs .x18 (vals .x18)) ** (regIs .x19 (vals .x19)) **
        (regIs .x20 (vals .x20)) ** (regIs .x21 (vals .x21)) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) **
        memOwn ((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) **
        memOwn ((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) **
        memOwn ((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) **
        memOwn ((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) **
        memOwn ((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) **
        memOwn ((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) **
        memOwn ((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (48 : BitVec 12)))
      ((regIs .x2 (sp0 + signExtend12 (-64 : BitVec 12))) ** (regIs .x1 raIn) **
        (regIs .x8 a0) ** (regIs .x9 a1) ** (regIs .x18 a2) **
        (regIs .x19 a3) ** (regIs .x20 (vals .x20)) **
        (regIs .x21 (vals .x21)) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) **
        (((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
        (((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ (vals .x8)) **
        (((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ (vals .x9)) **
        (((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ (vals .x18)) **
        (((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ (vals .x19)) **
        (((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ (vals .x20)) **
        (((sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (48 : BitVec 12)) ↦ₘ (vals .x21))) := by
    runBlock s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
  have hfr := cpsTripleWithin_frameR
    (regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (regIs .x0 (0 : Word)) **
      scratch)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hscratch))
    hblock
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hp => ?_) hfr
  · xperm_hyp hp
  · xperm_hyp hp

/-! ## Stage 2: parent-blob-gas sum + u64-overflow branch (GH #12346)

Instructions 12–13: `x20 := x18 + x9` (parent.excess + parent.used), then
`BLTU x20, x18` — taken means the u64 addition wrapped, i.e. the spec's
`U64.add` overflow error (status 1); not-taken continues to the target
comparison.  Both arms keep the full register frame; the pure guards
(`ult` / `¬ ult`) ride as the branch pures and are discharged by the
caller against the spec's `Except` outcome. -/

theorem hvebgSum_branch
    (sp0 spC raIn a0 a1 a2 a3 : Word) (vals : Reg → Word) (scratch : Assertion)
    (hscratch : scratch.pcFree)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsBranchWithin 2 (H + 48) hvebgCode
      ((regIs .x2 spC) ** (regIs .x1 raIn) **
        (regIs .x8 a0) ** (regIs .x9 a1) ** (regIs .x18 a2) **
        (regIs .x19 a3) ** (regIs .x20 (vals .x20)) **
        (regIs .x21 (vals .x21)) **
        (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
        (regIs .x13 a3) **
        ((spC + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
        ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ vals .x8) **
        ((spC + signExtend12 (16 : BitVec 12)) ↦ₘ vals .x9) **
        ((spC + signExtend12 (24 : BitVec 12)) ↦ₘ vals .x18) **
        ((spC + signExtend12 (32 : BitVec 12)) ↦ₘ vals .x19) **
        ((spC + signExtend12 (40 : BitVec 12)) ↦ₘ vals .x20) **
        ((spC + signExtend12 (48 : BitVec 12)) ↦ₘ vals .x21) **
        regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
        (regIs .x0 (0 : Word)) ** scratch)
      (H + 236)
      ((regIs .x18 a2) ** (regIs .x20 (a2 + a1)) **
        ⌜BitVec.ult (a2 + a1) a2⌝)
      (H + 56)
      ((regIs .x18 a2) ** (regIs .x20 (a2 + a1)) **
        ⌜¬ BitVec.ult (a2 + a1) a2⌝) := by
  subst hspC
  have s0 := add_spec_gen_within .x20 .x18 .x9 a2 a1 (vals .x20) (H + 48)
    (by decide)
  have s1 := bltu_spec_gen_within .x20 .x18 (184 : BitVec 13) (a2 + a1) a2
    (H + 52)
  rw [show signExtend13 (184 : BitVec 13) = (184 : Word) from by decide,
    show (H + 52) + (184 : Word) = H + 236 from by bv_omega,
    show (H + 52) + 4 = H + 56 from by bv_omega] at s1
  have s0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 48) hvebgProg 12
      (.ADD .x20 .x18 .x9) (by bv_omega) (by rw [hvebg_length]; decide) rfl
      (by rw [hvebg_length]; decide)) s0
  have s1C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 52) hvebgProg 13
      (.BLTU .x20 .x18 (184 : BitVec 13)) (by bv_omega)
      (by rw [hvebg_length]; decide) rfl (by rw [hvebg_length]; decide)) s1
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_same_cr s0C s1C
  have hfr := cpsTripleWithin_frameR
    ((regIs .x2 (sp0 + signExtend12 (-64 : BitVec 12))) ** (regIs .x1 raIn) **
      (regIs .x8 a0) ** (regIs .x19 a3) ** (regIs .x21 (vals .x21)) **
      (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
      (regIs .x13 a3) **
      (((sp0 + signExtend12 (-64 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      (((sp0 + signExtend12 (-64 : BitVec 12)) +
          signExtend12 (8 : BitVec 12)) ↦ₘ vals .x8) **
      (((sp0 + signExtend12 (-64 : BitVec 12)) +
          signExtend12 (16 : BitVec 12)) ↦ₘ vals .x9) **
      (((sp0 + signExtend12 (-64 : BitVec 12)) +
          signExtend12 (24 : BitVec 12)) ↦ₘ vals .x18) **
      (((sp0 + signExtend12 (-64 : BitVec 12)) +
          signExtend12 (32 : BitVec 12)) ↦ₘ vals .x19) **
      (((sp0 + signExtend12 (-64 : BitVec 12)) +
          signExtend12 (40 : BitVec 12)) ↦ₘ vals .x20) **
      (((sp0 + signExtend12 (-64 : BitVec 12)) +
          signExtend12 (48 : BitVec 12)) ↦ₘ vals .x21) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
      (regIs .x0 (0 : Word)) ** scratch)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hscratch)) hseq
  refine cpsBranchWithin_weaken (fun _ hp => ?_) (fun _ hp => ?_)
    (fun _ hp => ?_) hfr
  · xperm_hyp hp
  · xperm_hyp hp
  · xperm_hyp hp

end EvmAsm.Codegen.HeaderExcessBlobGasSpec
