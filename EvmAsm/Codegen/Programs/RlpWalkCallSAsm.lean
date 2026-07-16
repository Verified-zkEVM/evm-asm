/-
  Framed call and sequencing adapters for the strict cursor walkers.

  The leaf contracts in `RlpWalkInitFlatSAsm` and `RlpWalkNextFlatSAsm`
  describe the complete cursor/end/scratch register state.  These adapters
  preserve that state as an arbitrary caller assertion (`Prest`) while adding
  the direct JAL and the caller's larger code requirement.  A caller can use
  the two adapters repeatedly and compose the resulting triples with
  `walk_call_seq`; no cursor, end-pointer, or scratch fact is hidden or
  weakened.
-/

import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.WP.Call

namespace EvmAsm.Codegen.RlpWalkCallSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

#guard EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = 53
#guard EvmAsm.Rv64.RLP.rlp_walk_next_prog.length = 103

/-- Add a direct `jal ra, callee` to a complete caller code requirement. -/
theorem walk_call_within
    {cr calleeCode : CodeReq} {Prest Q : Assertion}
    {n : Nat} (callerPC calleeEntry oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint calleeCode)
    (hcode : ∀ a i,
      (CodeReq.singleton callerPC (.JAL .x1 offset)).union calleeCode a = some i →
        cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      calleeCode ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  exact cpsTripleWithin_extend_code hcode
    (WP.cpsCallWithin (vOld := oldRa) offset hoffset halign hpre hdisj hcallee)

/-- Specialized adapter for the strict `rlp_walk_init` leaf.  `Prest` is
    intentionally arbitrary: HeaderFields callers place cursor/end/scratch
    registers and the immutable input bytes in it, and the leaf's exact raw
    post remains visible in `Q`. -/
theorem rlp_walk_init_call_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (callerPC calleeEntry oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_init_code calleeEntry))
    (hcode : ∀ a i,
      (CodeReq.singleton callerPC (.JAL .x1 offset)).union
        (rlp_walk_init_code calleeEntry) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code calleeEntry)
      ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  exact walk_call_within callerPC calleeEntry oldRa offset hpre hoffset halign hdisj hcode hcallee

/-- Specialized adapter for one strict `rlp_walk_next` call. -/
theorem rlp_walk_next_call_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (callerPC calleeEntry oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_next_code calleeEntry))
    (hcode : ∀ a i,
      (CodeReq.singleton callerPC (.JAL .x1 offset)).union
        (rlp_walk_next_code calleeEntry) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code calleeEntry)
      ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  exact walk_call_within callerPC calleeEntry oldRa offset hpre hoffset halign hdisj hcode hcallee

/-- Compose two already-lifted walker calls.  The midpoint assertion is where
    the first walk's cursor/end/scratch post is supplied to the next call; the
    genuine caller proof supplies that relation explicitly. -/
theorem walk_call_seq
    {cr : CodeReq} {n₁ n₂ : Nat} {entry mid exit_ : Word}
    {P M Q : Assertion}
    (h₁ : cpsTripleWithin n₁ entry mid cr P M)
    (h₂ : cpsTripleWithin n₂ mid exit_ cr M Q) :
    cpsTripleWithin (n₁ + n₂) entry exit_ cr P Q := by
  exact cpsTripleWithin_seq_same_cr h₁ h₂

/-! ### Fixed-width caller corollary

    The migrated header callers use one initializer followed by a statically
    known number of `rlp_walk_next` calls.  Keeping the intermediate assertions
    explicit is intentional: each `Mᵢ` carries the walker's exact cursor/end,
    status, content-length, and scratch-register relation, so a caller proof
    cannot accidentally hide or weaken the state threaded from one call to the
    next.  The hypotheses are normally obtained from
    `rlp_walk_init_call_within` and `rlp_walk_next_call_within`; this theorem
    performs only the CPS sequencing needed after those call-site VCs have
    discharged. -/

theorem walk_init_next_4
    {cr : CodeReq} {n₀ n₁ n₂ n₃ n₄ : Nat}
    {entry m₀ m₁ m₂ m₃ exit_ : Word}
    {P M₀ M₁ M₂ M₃ Q : Assertion}
    (h_init : cpsTripleWithin n₀ entry m₀ cr P M₀)
    (h_next₁ : cpsTripleWithin n₁ m₀ m₁ cr M₀ M₁)
    (h_next₂ : cpsTripleWithin n₂ m₁ m₂ cr M₁ M₂)
    (h_next₃ : cpsTripleWithin n₃ m₂ m₃ cr M₂ M₃)
    (h_next₄ : cpsTripleWithin n₄ m₃ exit_ cr M₃ Q) :
    cpsTripleWithin (n₀ + n₁ + n₂ + n₃ + n₄) entry exit_ cr P Q := by
  have h₁ := cpsTripleWithin_seq_same_cr h_init h_next₁
  have h₂ := cpsTripleWithin_seq_same_cr h₁ h_next₂
  have h₃ := cpsTripleWithin_seq_same_cr h₂ h_next₃
  exact cpsTripleWithin_seq_same_cr h₃ h_next₄

theorem walk_init_next_6
    {cr : CodeReq} {n₀ n₁ n₂ n₃ n₄ n₅ n₆ : Nat}
    {entry m₀ m₁ m₂ m₃ m₄ m₅ exit_ : Word}
    {P M₀ M₁ M₂ M₃ M₄ M₅ Q : Assertion}
    (h_init : cpsTripleWithin n₀ entry m₀ cr P M₀)
    (h_next₁ : cpsTripleWithin n₁ m₀ m₁ cr M₀ M₁)
    (h_next₂ : cpsTripleWithin n₂ m₁ m₂ cr M₁ M₂)
    (h_next₃ : cpsTripleWithin n₃ m₂ m₃ cr M₂ M₃)
    (h_next₄ : cpsTripleWithin n₄ m₃ m₄ cr M₃ M₄)
    (h_next₅ : cpsTripleWithin n₅ m₄ m₅ cr M₄ M₅)
    (h_next₆ : cpsTripleWithin n₆ m₅ exit_ cr M₅ Q) :
    cpsTripleWithin (n₀ + n₁ + n₂ + n₃ + n₄ + n₅ + n₆) entry exit_ cr P Q := by
  have h₁ := cpsTripleWithin_seq_same_cr h_init h_next₁
  have h₂ := cpsTripleWithin_seq_same_cr h₁ h_next₂
  have h₃ := cpsTripleWithin_seq_same_cr h₂ h_next₃
  have h₄ := cpsTripleWithin_seq_same_cr h₃ h_next₄
  have h₅ := cpsTripleWithin_seq_same_cr h₄ h_next₅
  exact cpsTripleWithin_seq_same_cr h₅ h_next₆

theorem walk_init_next_17
    {cr : CodeReq}
    {n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ n₁₁ n₁₂ n₁₃ n₁₄ n₁₅ n₁₆ n₁₇ : Nat}
    {entry m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ m₁₆ exit_ : Word}
    {P M₀ M₁ M₂ M₃ M₄ M₅ M₆ M₇ M₈ M₉ M₁₀ M₁₁ M₁₂ M₁₃ M₁₄ M₁₅ M₁₆ Q : Assertion}
    (h_init : cpsTripleWithin n₀ entry m₀ cr P M₀)
    (h_next₁ : cpsTripleWithin n₁ m₀ m₁ cr M₀ M₁)
    (h_next₂ : cpsTripleWithin n₂ m₁ m₂ cr M₁ M₂)
    (h_next₃ : cpsTripleWithin n₃ m₂ m₃ cr M₂ M₃)
    (h_next₄ : cpsTripleWithin n₄ m₃ m₄ cr M₃ M₄)
    (h_next₅ : cpsTripleWithin n₅ m₄ m₅ cr M₄ M₅)
    (h_next₆ : cpsTripleWithin n₆ m₅ m₆ cr M₅ M₆)
    (h_next₇ : cpsTripleWithin n₇ m₆ m₇ cr M₆ M₇)
    (h_next₈ : cpsTripleWithin n₈ m₇ m₈ cr M₇ M₈)
    (h_next₉ : cpsTripleWithin n₉ m₈ m₉ cr M₈ M₉)
    (h_next₁₀ : cpsTripleWithin n₁₀ m₉ m₁₀ cr M₉ M₁₀)
    (h_next₁₁ : cpsTripleWithin n₁₁ m₁₀ m₁₁ cr M₁₀ M₁₁)
    (h_next₁₂ : cpsTripleWithin n₁₂ m₁₁ m₁₂ cr M₁₁ M₁₂)
    (h_next₁₃ : cpsTripleWithin n₁₃ m₁₂ m₁₃ cr M₁₂ M₁₃)
    (h_next₁₄ : cpsTripleWithin n₁₄ m₁₃ m₁₄ cr M₁₃ M₁₄)
    (h_next₁₅ : cpsTripleWithin n₁₅ m₁₄ m₁₅ cr M₁₄ M₁₅)
    (h_next₁₆ : cpsTripleWithin n₁₆ m₁₅ m₁₆ cr M₁₅ M₁₆)
    (h_next₁₇ : cpsTripleWithin n₁₇ m₁₆ exit_ cr M₁₆ Q) :
    cpsTripleWithin
      (n₀ + n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ + n₉ +
        n₁₀ + n₁₁ + n₁₂ + n₁₃ + n₁₄ + n₁₅ + n₁₆ + n₁₇)
      entry exit_ cr P Q := by
  have h₁ := cpsTripleWithin_seq_same_cr h_init h_next₁
  have h₂ := cpsTripleWithin_seq_same_cr h₁ h_next₂
  have h₃ := cpsTripleWithin_seq_same_cr h₂ h_next₃
  have h₄ := cpsTripleWithin_seq_same_cr h₃ h_next₄
  have h₅ := cpsTripleWithin_seq_same_cr h₄ h_next₅
  have h₆ := cpsTripleWithin_seq_same_cr h₅ h_next₆
  have h₇ := cpsTripleWithin_seq_same_cr h₆ h_next₇
  have h₈ := cpsTripleWithin_seq_same_cr h₇ h_next₈
  have h₉ := cpsTripleWithin_seq_same_cr h₈ h_next₉
  have h₁₀ := cpsTripleWithin_seq_same_cr h₉ h_next₁₀
  have h₁₁ := cpsTripleWithin_seq_same_cr h₁₀ h_next₁₁
  have h₁₂ := cpsTripleWithin_seq_same_cr h₁₁ h_next₁₂
  have h₁₃ := cpsTripleWithin_seq_same_cr h₁₂ h_next₁₃
  have h₁₄ := cpsTripleWithin_seq_same_cr h₁₃ h_next₁₄
  have h₁₅ := cpsTripleWithin_seq_same_cr h₁₄ h_next₁₅
  have h₁₆ := cpsTripleWithin_seq_same_cr h₁₅ h_next₁₆
  exact cpsTripleWithin_seq_same_cr h₁₆ h_next₁₇

theorem walk_init_next_13
    {cr : CodeReq}
    {n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ n₁₁ n₁₂ n₁₃ : Nat}
    {entry m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ exit_ : Word}
    {P M₀ M₁ M₂ M₃ M₄ M₅ M₆ M₇ M₈ M₉ M₁₀ M₁₁ M₁₂ Q : Assertion}
    (h_init : cpsTripleWithin n₀ entry m₀ cr P M₀)
    (h_next₁ : cpsTripleWithin n₁ m₀ m₁ cr M₀ M₁)
    (h_next₂ : cpsTripleWithin n₂ m₁ m₂ cr M₁ M₂)
    (h_next₃ : cpsTripleWithin n₃ m₂ m₃ cr M₂ M₃)
    (h_next₄ : cpsTripleWithin n₄ m₃ m₄ cr M₃ M₄)
    (h_next₅ : cpsTripleWithin n₅ m₄ m₅ cr M₄ M₅)
    (h_next₆ : cpsTripleWithin n₆ m₅ m₆ cr M₅ M₆)
    (h_next₇ : cpsTripleWithin n₇ m₆ m₇ cr M₆ M₇)
    (h_next₈ : cpsTripleWithin n₈ m₇ m₈ cr M₇ M₈)
    (h_next₉ : cpsTripleWithin n₉ m₈ m₉ cr M₈ M₉)
    (h_next₁₀ : cpsTripleWithin n₁₀ m₉ m₁₀ cr M₉ M₁₀)
    (h_next₁₁ : cpsTripleWithin n₁₁ m₁₀ m₁₁ cr M₁₀ M₁₁)
    (h_next₁₂ : cpsTripleWithin n₁₂ m₁₁ m₁₂ cr M₁₁ M₁₂)
    (h_next₁₃ : cpsTripleWithin n₁₃ m₁₂ exit_ cr M₁₂ Q)
    : cpsTripleWithin
        (n₀ + n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ + n₉ +
          n₁₀ + n₁₁ + n₁₂ + n₁₃)
        entry exit_ cr P Q := by
  have h₁ := cpsTripleWithin_seq_same_cr h_init h_next₁
  have h₂ := cpsTripleWithin_seq_same_cr h₁ h_next₂
  have h₃ := cpsTripleWithin_seq_same_cr h₂ h_next₃
  have h₄ := cpsTripleWithin_seq_same_cr h₃ h_next₄
  have h₅ := cpsTripleWithin_seq_same_cr h₄ h_next₅
  have h₆ := cpsTripleWithin_seq_same_cr h₅ h_next₆
  have h₇ := cpsTripleWithin_seq_same_cr h₆ h_next₇
  have h₈ := cpsTripleWithin_seq_same_cr h₇ h_next₈
  have h₉ := cpsTripleWithin_seq_same_cr h₈ h_next₉
  have h₁₀ := cpsTripleWithin_seq_same_cr h₉ h_next₁₀
  have h₁₁ := cpsTripleWithin_seq_same_cr h₁₀ h_next₁₁
  have h₁₂ := cpsTripleWithin_seq_same_cr h₁₁ h_next₁₂
  exact cpsTripleWithin_seq_same_cr h₁₂ h_next₁₃


end EvmAsm.Codegen.RlpWalkCallSAsm
