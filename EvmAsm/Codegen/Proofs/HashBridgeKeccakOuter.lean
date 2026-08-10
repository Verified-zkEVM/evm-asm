/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakOuter

  Outer absorb loop for `zkvm_keccak256` over `signedCountdownLoop_reload_spec`
  (hdr = LI x29,136).

  Geometry (guest `zkvm_keccak256` @ 0x8000364c):
    LI  x29,136     @ 0x8000368c  (prog idx 16)  ← JAL target
    BLT x9,x29,+68  @ 0x80003690  (prog idx 17)
    body ... JAL -68 back to LI

  `signedCountdownLoop_spec` (BLT-header) does **not** apply: JAL target and
  BLT address differ by 4.  Body also clobbers lim (x29 ∈ keccakCsrsRest after
  CSRS); the reload LI re-establishes 136 each trip — captured by reload_spec's
  `regOwn lim` post on the body.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakAbsorb
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSpec
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Rate stride (bytes). -/
abbrev keccakAbsorbStep : Nat := 136

/-- BLT exit offset: from BLT at liHdr+4, +68 lands at rem-setup (liHdr+72). -/
abbrev keccakAbsorbExitOff : BitVec 13 := 68

/-- Body fuel = absorb body + back-edge JAL. -/
abbrev keccakAbsorbOuterBodyFuel : Nat := keccakAbsorbBodyFuel

/-- Pure: sponge after absorbing the first `k` full rate blocks of `input`. -/
def keccakAbsorbedPrefix (input : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => keccakZeroStateBytes
  | k + 1 =>
    let st := keccakAbsorbedPrefix input k
    let blk := (input.drop (keccakAbsorbStep * k)).take keccakAbsorbStep
    keccakPermuteAbsorbed st blk

theorem keccakAbsorbedPrefix_length (input : List (BitVec 8)) (k : Nat) :
    (keccakAbsorbedPrefix input k).length = 200 := by
  induction k with
  | zero =>
    simp only [keccakAbsorbedPrefix, keccakZeroStateBytes]
    decide
  | succ k ih =>
    simp only [keccakAbsorbedPrefix]
    exact keccakPermuteAbsorbed_length _ _ ih

theorem keccakAbsorbedPrefix_succ (input : List (BitVec 8)) (k : Nat) :
    keccakAbsorbedPrefix input (k + 1) =
      keccakPermuteAbsorbed (keccakAbsorbedPrefix input k)
        ((input.drop (keccakAbsorbStep * k)).take keccakAbsorbStep) := rfl

/-- Cursor after absorbing `k` blocks. -/
def keccakAbsorbCursor (inputBase : Word) (k : Nat) : Word :=
  inputBase + BitVec.ofNat 64 (keccakAbsorbStep * k)

theorem keccakAbsorbCursor_succ (inputBase : Word) (k : Nat)
    (hk : keccakAbsorbStep * (k + 1) < 2 ^ 64) :
    keccakAbsorbCursor inputBase (k + 1) =
      keccakAbsorbCursor inputBase k + BitVec.ofNat 64 keccakAbsorbStep := by
  simp only [keccakAbsorbCursor, keccakAbsorbStep] at hk ⊢
  have hmul : 136 * (k + 1) = 136 * k + 136 := by omega
  have hab : 136 * k + 136 < 2 ^ 64 := by omega
  have ha : 136 * k < 2 ^ 64 := by omega
  have hb : (136 : Nat) < 2 ^ 64 := by omega
  rw [hmul, BitVec.add_assoc]
  congr 1
  -- ofNat (a+b) = ofNat a + ofNat b
  apply BitVec.eq_of_toNat_eq
  have hL : (BitVec.ofNat 64 (136 * k + 136)).toNat = 136 * k + 136 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab]
  have hR1 : (BitVec.ofNat 64 (136 * k)).toNat = 136 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hR2 : (BitVec.ofNat 64 136).toNat = 136 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  rw [hL, BitVec.toNat_add, hR1, hR2, Nat.mod_eq_of_lt hab]

/-- Temps owned inside the outer inv (excludes lim x29 — that is the reload reg,
    tracked separately by `signedCountdownLoop_reload_spec`).  Matches body post
    `regOwns keccakCsrsRest` after peeling x29. -/
def keccakAbsorbOuterTemps : List Reg :=
  [.x5, .x6, .x7, .x28, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Stable ambient through the outer loop (no lim).
    Full input stays in ambient; body focuses a 136 B window via
    `bytesRegion_window_focus`. -/
def keccakAbsorbOuterCore (scratchBase inputBase : Word)
    (input : List (BitVec 8)) (inputCur : Word)
    (st : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
    -- `x10` is `regOwn` (not pinned to scratch): first entry after setup still
    -- holds ABI a0; body `MV x10,x8` establishes the CSRS pointer each trip.
    (regOwn .x10) **
    regOwns keccakAbsorbOuterTemps **
    bytesRegion scratchBase st ** bytesRegion inputBase input ** A

/-- Outer-loop inv at countdown index `n` (blocks still to absorb).
    State = prefix of `N-n` absorbed blocks; cursor advanced by that many. -/
def keccakAbsorbOuterInv (scratchBase inputBase : Word)
    (input : List (BitVec 8)) (N : Nat) (n : Nat) (A : Assertion) : Assertion :=
  keccakAbsorbOuterCore scratchBase inputBase input
    (keccakAbsorbCursor inputBase (N - n))
    (keccakAbsorbedPrefix input (N - n)) A

/-- pcFree for outer core. -/
theorem keccakAbsorbOuterCore_pcFree (scratchBase inputBase : Word)
    (input : List (BitVec 8)) (inputCur : Word)
    (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (keccakAbsorbOuterCore scratchBase inputBase input inputCur st A).pcFree :=
  pcFree_sepConj (by pcFree) <|
  pcFree_sepConj (by pcFree) <|
  pcFree_sepConj (by pcFree) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (pcFree_regOwns _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) hA

theorem keccakAbsorbOuterInv_pcFree (scratchBase inputBase : Word)
    (input : List (BitVec 8)) (N n : Nat) (A : Assertion) (hA : A.pcFree) :
    (keccakAbsorbOuterInv scratchBase inputBase input N n A).pcFree :=
  keccakAbsorbOuterCore_pcFree _ _ _ _ _ _ hA

/-- `regOwns keccakCsrsRest` implies `regOwn x29 ** regOwns outerTemps` (xperm). -/
theorem regOwns_csrsRest_to_x29_outerTemps (h : PartialState)
    (hp : regOwns keccakCsrsRest h) :
    ((regOwn .x29) ** regOwns keccakAbsorbOuterTemps) h := by
  have this : (
    (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) **
      (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) **
      (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
      (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion
    ) h := by
    simpa [regOwns, keccakCsrsRest, regOwn] using hp
  have goal : (
    (regOwn .x29) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
      (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
      (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
      (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion
    ) h := by
    xperm_hyp this
  simpa [regOwns, keccakAbsorbOuterTemps, regOwn] using goal

/-- Reverse: outerTemps + x29 → full csrsRest. -/
theorem regOwns_x29_outerTemps_to_csrsRest (h : PartialState)
    (hp : ((regOwn .x29) ** regOwns keccakAbsorbOuterTemps) h) :
    regOwns keccakCsrsRest h := by
  have this : (
    (regOwn .x29) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
      (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
      (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
      (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion
    ) h := by
    simpa [regOwns, keccakAbsorbOuterTemps, regOwn] using hp
  have goal : (
    (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) **
      (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) **
      (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
      (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion
    ) h := by
    xperm_hyp this
  simpa [regOwns, keccakCsrsRest, regOwn] using goal

/-- outerTemps owns + own x29 → body pre owns (x28/x30/x31 + dwordFrame + x5/x6). -/
theorem outerTemps_to_body_owns (h : PartialState)
    (hp : ((regOwn .x29) ** regOwns keccakAbsorbOuterTemps) h) :
    ((regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
      regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6)) h := by
  have this : (
    (regOwn .x29) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
      (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
      (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
      (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion
    ) h := by
    simpa [regOwns, keccakAbsorbOuterTemps, regOwn] using hp
  -- Match foldr nesting of `regOwns dwordFrame ** own x5 ** own x6`
  have goal : (
    (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
      ((regOwn .x7) ** (regOwn .x29) **
        (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
        (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion) **
      (regOwn .x5) ** (regOwn .x6)
    ) h := by
    xperm_hyp this
  simpa [regOwns, keccakDwordFrameOwns, regOwn] using goal

/-- Reload-header outer absorb loop (abstract body hyp). -/
theorem keccakAbsorbOuterLoop_reload (cr : CodeReq) (liHdr exitAddr : Word)
    (scratchBase inputBase : Word) (input : List (BitVec 8))
    (N rem : Nat) (A : Assertion) (_hA : A.pcFree)
    (hrem : rem < keccakAbsorbStep)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hexit : (liHdr + 4) + signExtend13 keccakAbsorbExitOff = exitAddr)
    (hliMem : ∀ a i,
      CodeReq.singleton liHdr (.LI .x29 (BitVec.ofNat 64 keccakAbsorbStep)) a = some i →
        cr a = some i)
    (hguardMem : ∀ a i,
      CodeReq.singleton (liHdr + 4) (.BLT .x9 .x29 keccakAbsorbExitOff) a = some i →
        cr a = some i)
    (hpcFree : ∀ n, (keccakAbsorbOuterInv scratchBase inputBase input N n A).pcFree)
    (hbody : ∀ n, n < N →
      cpsTripleWithin keccakAbsorbOuterBodyFuel (liHdr + 8) liHdr cr
        ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * (n + 1) + rem)) **
          (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
          keccakAbsorbOuterInv scratchBase inputBase input N (n + 1) A)
        ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * n + rem)) **
          (regOwn .x29) **
          keccakAbsorbOuterInv scratchBase inputBase input N n A)) :
    cpsTripleWithin (N * (keccakAbsorbOuterBodyFuel + 2) + 2) liHdr exitAddr cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (regOwn .x29) **
        keccakAbsorbOuterInv scratchBase inputBase input N N A)
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        keccakAbsorbOuterInv scratchBase inputBase input N 0 A) := by
  have hstepbound : keccakAbsorbStep < 2 ^ 63 := by
    simp only [keccakAbsorbStep]; omega
  exact signedCountdownLoop_reload_spec cr liHdr exitAddr .x9 .x29
    keccakAbsorbExitOff keccakAbsorbOuterBodyFuel keccakAbsorbStep N rem
    (fun n => keccakAbsorbOuterInv scratchBase inputBase input N n A)
    (by decide) (by decide) (by decide) hrem hstepbound hNbound hexit
    hpcFree hliMem hguardMem hbody
end EvmAsm.Codegen.Proofs
