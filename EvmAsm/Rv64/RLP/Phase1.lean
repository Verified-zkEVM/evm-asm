/-
  EvmAsm.Rv64.RLP.Phase1

  EL.3 Phase 1: RLP prefix classifier.

  Given the first byte `p` of an RLP-encoded item in `x5`, dispatches to one
  of five exits based on the Yellow Paper Appendix B boundaries:

  | Range          | Category      |
  |----------------|---------------|
  | `p < 0x80`     | single byte   |
  | `0x80..0xB7`   | short string  |
  | `0xB8..0xBF`   | long string   |
  | `0xC0..0xF7`   | short list    |
  | `0xF8..0xFF`   | long list     |

  Implementation: a cascade of four `(ADDI x10, x0, K ; BLTU x5, x10, off)`
  steps on the thresholds `0x80, 0xB8, 0xC0, 0xF8`. Each BLTU taken branch is
  one of the first four exits; the final fall-through is the long-list exit.

  Register usage:
    x5  — input prefix byte (zero-extended, `toNat < 256` assumed by caller)
    x10 — scratch (clobbered; holds the last threshold constant on exit)
    x0  — zero register (unchanged)

  This file provides:
    * `rlp_phase1_step_prog` — the 2-instruction cascade-step program
    * `rlp_phase1_classifier_prog` — the full 8-instruction classifier
    * `rlp_phase1_step_code` — the matching `CodeReq`
    * `rlp_phase1_step_spec` — `cpsBranchWithin` spec preserving the dispatch fact
      (`BitVec.ult v5 kVal` on the taken side, `¬…` on the fall-through).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.EL.RLP.Prefix

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Program definitions
-- ============================================================================

/-- One cascade step: `ADDI x10, x0, k ; BLTU x5, x10, offset`.
    If `x5 <u k` (unsigned), take the branch; else fall through. -/
def rlp_phase1_step_prog (k : BitVec 12) (offset : BitVec 13) : Program :=
  [.ADDI .x10 .x0 k, .BLTU .x5 .x10 offset]

/-- Full Phase 1 classifier (8 instructions = 32 bytes).

    The four branch offsets are the relative targets of the four taken
    exits (single byte, short string, long string, short list). The
    fall-through at `base + 32` is the long-list exit. -/
def rlp_phase1_classifier_prog
    (off_single off_short_str off_long_str off_short_list : BitVec 13) : Program :=
  rlp_phase1_step_prog 0x80 off_single ++
  rlp_phase1_step_prog 0xB8 off_short_str ++
  rlp_phase1_step_prog 0xC0 off_long_str ++
  rlp_phase1_step_prog 0xF8 off_short_list

example (a b c d : BitVec 13) :
    (rlp_phase1_classifier_prog a b c d).length = 8 := rfl

-- ============================================================================
-- CodeReq for the cascade step
-- ============================================================================

/-- Code requirement for a single cascade step, as `ofProg`. -/
abbrev rlp_phase1_step_code
    (k : BitVec 12) (offset : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (rlp_phase1_step_prog k offset)

-- ============================================================================
-- Spec: cascade step
-- ============================================================================

/-- `cpsBranchWithin` spec for one cascade step.

    Taken (`x5 <u kVal`):     PC := target           (BLTU took the branch)
    Not taken (`¬ x5 <u kVal`): PC := base + 8       (fell through)

    Both postconditions preserve `⌜…⌝` so downstream compositions can case
    on the dispatch result. `kVal = (0 : Word) + signExtend12 k` matches
    the result of `ADDI x10, x0, k` starting from `x0 = 0`. For the RLP
    thresholds (0x80, 0xB8, 0xC0, 0xF8), `kVal.toNat = k.toNat` since all
    four fit in 11 bits (no sign extension). -/
theorem rlp_phase1_step_spec_within (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let kVal := (0 : Word) + signExtend12 k
    let code := rlp_phase1_step_code k offset base
    cpsBranchWithin 2 base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal) **
         ⌜BitVec.ult v5 kVal⌝)
      (base + 8)
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal) **
         ⌜¬ BitVec.ult v5 kVal⌝) := by
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_omega
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x10 .x0 k))
      (CodeReq.singleton (base + 4) (.BLTU .x5 .x10 offset)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  -- Step 1: ADDI x10, x0, k at base
  have s1 := addi_spec_gen_within .x10 .x0 v10 0 k base (by nofun)
  have s1' : cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.ADDI .x10 .x0 k))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x5 ↦ᵣ v5) (by pcFree) s1)
  -- Step 2: BLTU x5, x10, offset at base+4
  have s2_raw := bltu_spec_gen_within .x5 .x10 offset v5
    ((0 : Word) + signExtend12 k) (base + 4)
  rw [htarget, ha1] at s2_raw
  -- Frame with x0, rearrange pre/post
  have s2' : cpsBranchWithin 1 (base + 4)
      (CodeReq.singleton (base + 4) (.BLTU .x5 .x10 offset))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      target
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) **
         ⌜BitVec.ult v5 ((0 : Word) + signExtend12 k)⌝)
      (base + 8)
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) **
         ⌜¬ BitVec.ult v5 ((0 : Word) + signExtend12 k)⌝) :=
    cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) s2_raw)
  exact cpsTripleWithin_seq_cpsBranchWithin hd
    (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => hp) s1') s2'

theorem rlp_phase1_step_spec_plain_within (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let kVal := (0 : Word) + signExtend12 k
    let code := rlp_phase1_step_code k offset base
    cpsBranchWithin 2 base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal))
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal)) :=
  cpsBranchWithin_weaken
    (fun _ hp => hp)
    sepConj_strip_pure_end3
    sepConj_strip_pure_end3
    (rlp_phase1_step_spec_within v5 v10 k offset base target htarget)

theorem rlp_phase1_step_taken_spec_within (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hv5 : BitVec.ult v5 ((0 : Word) + signExtend12 k)) :
    let kVal := (0 : Word) + signExtend12 k
    let code := rlp_phase1_step_code k offset base
    cpsTripleWithin 2 base target code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal)) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    sepConj_strip_pure_end3
    (cpsBranchWithin_takenPath
      (rlp_phase1_step_spec_within v5 v10 k offset base target htarget)
      (fun _ hpost => by
        -- The not-taken post carries `⌜¬ BitVec.ult v5 kVal⌝`; the
        -- assumption `hv5` contradicts it.
        open EvmAsm.Rv64.Tactics in extract_pure hpost
        exact hpost.1 hv5))

theorem rlp_phase1_step_ntaken_spec_within (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hv5 : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 k)) :
    let kVal := (0 : Word) + signExtend12 k
    let code := rlp_phase1_step_code k offset base
    cpsTripleWithin 2 base (base + 8) code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal)) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    sepConj_strip_pure_end3
    (cpsBranchWithin_ntakenPath
      (rlp_phase1_step_spec_within v5 v10 k offset base target htarget)
      (fun _ hpost => by
        -- The taken post carries `⌜BitVec.ult v5 kVal⌝`; the assumption
        -- `hv5` (its negation) contradicts it.
        open EvmAsm.Rv64.Tactics in extract_pure hpost
        exact hv5 hpost.1))

abbrev rlp_phase1_classifier_code
    (off_single off_short_str off_long_str off_short_list : BitVec 13)
    (base : Word) : CodeReq :=
  (rlp_phase1_step_code 0x80 off_single base).union
  ((rlp_phase1_step_code 0xB8 off_short_str (base + 8)).union
  ((rlp_phase1_step_code 0xC0 off_long_str (base + 16)).union
  (rlp_phase1_step_code 0xF8 off_short_list (base + 24))))

-- ============================================================================
-- Spec: full 5-exit classifier
-- ============================================================================

/-- Two cascade-step `CodeReq`s whose bases are 8 bytes apart are disjoint.
    Helper for the classifier composition. -/
theorem step_code_Disjoint_8 (k1 k2 : BitVec 12) (off1 off2 : BitVec 13)
    (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 8)) :=
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))

/-- Cascade-step at `base` is disjoint from step at `base + 16`. -/
theorem step_code_Disjoint_16 (k1 k2 : BitVec 12) (off1 off2 : BitVec 13)
    (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 16)) :=
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))

/-- Cascade-step at `base` is disjoint from step at `base + 24`. -/
theorem step_code_Disjoint_24 (k1 k2 : BitVec 12) (off1 off2 : BitVec 13)
    (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 24)) :=
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))

/-- Address-normalized variant: step at `base + 8` disjoint from step at `base + 16`. -/
private theorem step_code_Disjoint_8_at_8
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 (base + 8)).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 16)) := by
  have h := step_code_Disjoint_8 k1 k2 off1 off2 (base + 8)
  rwa [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at h

/-- Address-normalized variant: step at `base + 8` disjoint from step at `base + 24`. -/
private theorem step_code_Disjoint_16_at_8
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 (base + 8)).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 24)) := by
  have h := step_code_Disjoint_16 k1 k2 off1 off2 (base + 8)
  rwa [show (base + 8 : Word) + 16 = base + 24 from by bv_omega] at h

/-- Address-normalized variant: step at `base + 16` disjoint from step at `base + 24`. -/
private theorem step_code_Disjoint_8_at_16
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 (base + 16)).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 24)) := by
  have h := step_code_Disjoint_8 k1 k2 off1 off2 (base + 16)
  rwa [show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at h

/-- Bundled exit postcondition for the Phase 1 classifier: the register-
    ownership triple with `x10` holding the threshold constant `k`.
    Wrapped in an `@[irreducible] def` to avoid leaking `let`-bound
    intermediates into theorem statements — see `AGENTS.md` ("Bundling
    Postconditions with `let` Bindings"). -/
@[irreducible]
def rlp_phase1_exit_post (v5 : Word) (k : BitVec 12) : Assertion :=
  let kVal := (0 : Word) + signExtend12 k
  (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal)

/-- Unfold lemma for `rlp_phase1_exit_post`. Use when a consumer needs the
    explicit register-ownership form. -/
theorem rlp_phase1_exit_post_unfold {v5 : Word} {k : BitVec 12} :
    rlp_phase1_exit_post v5 k =
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) := by
  delta rlp_phase1_exit_post; rfl

/-- Full 5-exit spec for the Phase 1 classifier.

    Given `x5` holding the prefix byte (arbitrary 64-bit value, no range
    constraint), `x0 = 0`, and `x10` arbitrary, the classifier reaches one
    of five exits determined by the cascade:

    | Exit PC  | When                                     | `x10` on exit |
    |----------|------------------------------------------|---------------|
    | `e1`     | first BLTU (k=0x80) taken                | 0x80          |
    | `e2`     | second BLTU (k=0xB8) taken (fell #1)     | 0xB8          |
    | `e3`     | third BLTU (k=0xC0) taken  (fell #1,#2)  | 0xC0          |
    | `e4`     | fourth BLTU (k=0xF8) taken (fell #1..#3) | 0xF8          |
    | `e5`     | fall-through after all four BLTUs        | 0xF8          |

    This plain variant drops the dispatch facts; downstream phases can
    recover them by re-reading the prefix byte or by using a pure-fact
    variant (`rlp_phase1_classifier_spec_pure`). -/
theorem rlp_phase1_classifier_spec_within (v5 v10 : Word) (base : Word)
    (off1 off2 off3 off4 : BitVec 13)
    (e1 e2 e3 e4 e5 : Word)
    (he1 : (base + 4) + signExtend13 off1 = e1)
    (he2 : (base + 12) + signExtend13 off2 = e2)
    (he3 : (base + 20) + signExtend13 off3 = e3)
    (he4 : (base + 28) + signExtend13 off4 = e4)
    (he5 : base + 32 = e5) :
    cpsNBranchWithin 8 base (rlp_phase1_classifier_code off1 off2 off3 off4 base)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e1, rlp_phase1_exit_post v5 0x80),
       (e2, rlp_phase1_exit_post v5 0xB8),
       (e3, rlp_phase1_exit_post v5 0xC0),
       (e4, rlp_phase1_exit_post v5 0xF8),
       (e5, rlp_phase1_exit_post v5 0xF8)] := by
  -- Step specs (one per cascade step), with per-step target-address witnesses.
  -- rlp_phase1_step_spec_plain gives us `cpsBranchWithin base_i (...) e_i (...) (base_i + 8) (...)`.
  have cs1 := rlp_phase1_step_spec_plain_within v5 v10 0x80 off1 base e1 he1
  have cs2 := rlp_phase1_step_spec_plain_within v5 ((0 : Word) + signExtend12 0x80)
    0xB8 off2 (base + 8) e2 (by
      rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega]; exact he2)
  have cs3 := rlp_phase1_step_spec_plain_within v5 ((0 : Word) + signExtend12 0xB8)
    0xC0 off3 (base + 16) e3 (by
      rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega]; exact he3)
  have cs4 := rlp_phase1_step_spec_plain_within v5 ((0 : Word) + signExtend12 0xC0)
    0xF8 off4 (base + 24) e4 (by
      rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega]; exact he4)
  -- Fallthrough after step 4 lands at base + 32 = e5.
  rw [show (base + 24 : Word) + 8 = e5 from by rw [← he5]; bv_omega] at cs4
  -- Align cs2/cs3 fallthrough PCs with the next step's base.
  rw [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at cs2
  rw [show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at cs3
  -- Disjointness between each step's CR and the union of remaining steps' CRs.
  let cr1 := rlp_phase1_step_code 0x80 off1 base
  let cr2 := rlp_phase1_step_code 0xB8 off2 (base + 8)
  let cr3 := rlp_phase1_step_code 0xC0 off3 (base + 16)
  let cr4 := rlp_phase1_step_code 0xF8 off4 (base + 24)
  have hd12 : cr1.Disjoint cr2 := step_code_Disjoint_8 _ _ _ _ _
  have hd13 : cr1.Disjoint cr3 := step_code_Disjoint_16 _ _ _ _ _
  have hd14 : cr1.Disjoint cr4 := step_code_Disjoint_24 _ _ _ _ _
  have hd23 : cr2.Disjoint cr3 := step_code_Disjoint_8_at_8 0xB8 0xC0 off2 off3 base
  have hd24 : cr2.Disjoint cr4 := step_code_Disjoint_16_at_8 0xB8 0xF8 off2 off4 base
  have hd34 : cr3.Disjoint cr4 := step_code_Disjoint_8_at_16 0xC0 0xF8 off3 off4 base
  -- Fallthrough cpsNBranchWithin at e5 (zero steps; refl).
  have ft : cpsNBranchWithin 0 e5 CodeReq.empty
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 0xF8)))
      [(e5, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 0xF8)))] :=
    cpsNBranchWithin_refl e5 _ _ (fun _ hp => hp)
  -- Chain step 4 + fallthrough → cpsNBranchWithin at base+24 with [e4, e5].
  have n4 := cpsBranchWithin_cons_cpsNBranchWithin (CodeReq.Disjoint.empty_right cr4) cs4 ft
  -- Chain step 3 + n4 → cpsNBranchWithin at base+16 with [e3, e4, e5].
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  have hd3_rest : cr3.Disjoint (cr4.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd34
  have n3 := cpsBranchWithin_cons_cpsNBranchWithin hd3_rest cs3 n4
  -- Chain step 2 + n3 → cpsNBranchWithin at base+8 with [e2, e3, e4, e5].
  have hd2_rest : cr2.Disjoint (cr3.union (cr4.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd23 hd24
  have n2 := cpsBranchWithin_cons_cpsNBranchWithin hd2_rest cs2 n3
  -- Chain step 1 + n2 → cpsNBranchWithin at base with [e1, e2, e3, e4, e5].
  have hd1_rest : cr1.Disjoint (cr2.union (cr3.union (cr4.union CodeReq.empty))) := by
    rw [hunion_empty]
    exact CodeReq.Disjoint.union_right hd12 (CodeReq.Disjoint.union_right hd13 hd14)
  have n1 := cpsBranchWithin_cons_cpsNBranchWithin hd1_rest cs1 n2
  -- The CR now is: cr1.union (cr2.union (cr3.union (cr4.union empty))).
  -- Simplify the trailing `empty` and match the goal's classifier_code.
  have hcr_eq : cr1.union (cr2.union (cr3.union (cr4.union CodeReq.empty))) =
      rlp_phase1_classifier_code off1 off2 off3 off4 base := by
    simp only [hunion_empty]; rfl
  -- Unfold the irreducible `rlp_phase1_exit_post` in the goal so n1's
  -- explicit register-ownership posts match.
  simp only [rlp_phase1_exit_post_unfold]
  exact hcr_eq ▸ n1

@[irreducible]
def rlp_phase1_exit_post_pure
    (v5 : Word) (k : BitVec 12) (fact : Prop) : Assertion :=
  let kVal := (0 : Word) + signExtend12 k
  (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal) ** ⌜fact⌝

/-- Unfold lemma for `rlp_phase1_exit_post_pure`. -/
theorem rlp_phase1_exit_post_pure_unfold
    (v5 : Word) (k : BitVec 12) (fact : Prop) :
    rlp_phase1_exit_post_pure v5 k fact =
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) ** ⌜fact⌝) := by
  delta rlp_phase1_exit_post_pure; rfl

/-- Pure-fact variant of `rlp_phase1_classifier_spec`: each exit post carries
    the `⌜BitVec.ult v5 k_i⌝` (or negation, for the fall-through) fact from
    the corresponding BLTU. Downstream handlers can combine these with the
    exit PC to discriminate the RLP categories.

    Note: this variant only carries the **current** step's dispatch fact at
    each exit, not the accumulated chain of prior negations. For full range
    identification (e.g., `0x80 ≤ p < 0xB8` at exit `e2`), a handler must
    either re-read the prefix byte or combine with a prior-negation chain
    that a future accumulated variant would provide. -/
theorem rlp_phase1_classifier_spec_pure_within (v5 v10 : Word) (base : Word)
    (off1 off2 off3 off4 : BitVec 13)
    (e1 e2 e3 e4 e5 : Word)
    (he1 : (base + 4) + signExtend13 off1 = e1)
    (he2 : (base + 12) + signExtend13 off2 = e2)
    (he3 : (base + 20) + signExtend13 off3 = e3)
    (he4 : (base + 28) + signExtend13 off4 = e4)
    (he5 : base + 32 = e5) :
    cpsNBranchWithin 8 base (rlp_phase1_classifier_code off1 off2 off3 off4 base)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e1, rlp_phase1_exit_post_pure v5 0x80
              (BitVec.ult v5 ((0 : Word) + signExtend12 0x80))),
       (e2, rlp_phase1_exit_post_pure v5 0xB8
              (BitVec.ult v5 ((0 : Word) + signExtend12 0xB8))),
       (e3, rlp_phase1_exit_post_pure v5 0xC0
              (BitVec.ult v5 ((0 : Word) + signExtend12 0xC0))),
       (e4, rlp_phase1_exit_post_pure v5 0xF8
              (BitVec.ult v5 ((0 : Word) + signExtend12 0xF8))),
       (e5, rlp_phase1_exit_post_pure v5 0xF8
              (¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xF8)))] := by
  -- Step specs WITH pure facts preserved.
  have cs1 := rlp_phase1_step_spec_within v5 v10 0x80 off1 base e1 he1
  have cs2 := rlp_phase1_step_spec_within v5 ((0 : Word) + signExtend12 0x80)
    0xB8 off2 (base + 8) e2 (by
      rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega]; exact he2)
  have cs3 := rlp_phase1_step_spec_within v5 ((0 : Word) + signExtend12 0xB8)
    0xC0 off3 (base + 16) e3 (by
      rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega]; exact he3)
  have cs4 := rlp_phase1_step_spec_within v5 ((0 : Word) + signExtend12 0xC0)
    0xF8 off4 (base + 24) e4 (by
      rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega]; exact he4)
  -- Align fall-through PCs.
  rw [show (base + 24 : Word) + 8 = e5 from by rw [← he5]; bv_omega] at cs4
  rw [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at cs2
  rw [show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at cs3
  -- Disjointness (same shape as the plain classifier spec).
  let cr1 := rlp_phase1_step_code 0x80 off1 base
  let cr2 := rlp_phase1_step_code 0xB8 off2 (base + 8)
  let cr3 := rlp_phase1_step_code 0xC0 off3 (base + 16)
  let cr4 := rlp_phase1_step_code 0xF8 off4 (base + 24)
  have hd12 : cr1.Disjoint cr2 := step_code_Disjoint_8 _ _ _ _ _
  have hd13 : cr1.Disjoint cr3 := step_code_Disjoint_16 _ _ _ _ _
  have hd14 : cr1.Disjoint cr4 := step_code_Disjoint_24 _ _ _ _ _
  have hd23 : cr2.Disjoint cr3 := step_code_Disjoint_8_at_8 0xB8 0xC0 off2 off3 base
  have hd24 : cr2.Disjoint cr4 := step_code_Disjoint_16_at_8 0xB8 0xF8 off2 off4 base
  have hd34 : cr3.Disjoint cr4 := step_code_Disjoint_8_at_16 0xC0 0xF8 off3 off4 base
  -- Fallthrough cpsNBranchWithin preserving step 4's pure fact.
  have ft : cpsNBranchWithin 0 e5 CodeReq.empty
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 0xF8)) **
       ⌜¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xF8)⌝)
      [(e5, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 0xF8)) **
            ⌜¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xF8)⌝)] :=
    cpsNBranchWithin_refl e5 _ _ (fun _ hp => hp)
  -- Chain step 4 + fallthrough (no perm: step4.fall = ft.pre).
  have n4 := cpsBranchWithin_cons_cpsNBranchWithin (CodeReq.Disjoint.empty_right cr4) cs4 ft
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  -- Chain step 3 + n4: strip `⌜¬ult v5 k3⌝` from step3.fall to match n4.pre.
  have hd3_rest : cr3.Disjoint (cr4.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd34
  have n3 := cpsBranchWithin_cons_cpsNBranchWithin_with_perm hd3_rest
    sepConj_strip_pure_end3 cs3 n4
  -- Chain step 2 + n3.
  have hd2_rest : cr2.Disjoint (cr3.union (cr4.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd23 hd24
  have n2 := cpsBranchWithin_cons_cpsNBranchWithin_with_perm hd2_rest
    sepConj_strip_pure_end3 cs2 n3
  -- Chain step 1 + n2.
  have hd1_rest : cr1.Disjoint (cr2.union (cr3.union (cr4.union CodeReq.empty))) := by
    rw [hunion_empty]
    exact CodeReq.Disjoint.union_right hd12 (CodeReq.Disjoint.union_right hd13 hd14)
  have n1 := cpsBranchWithin_cons_cpsNBranchWithin_with_perm hd1_rest
    sepConj_strip_pure_end3 cs1 n2
  -- Collapse the trailing `empty` and match the goal's classifier_code.
  have hcr_eq : cr1.union (cr2.union (cr3.union (cr4.union CodeReq.empty))) =
      rlp_phase1_classifier_code off1 off2 off3 off4 base := by
    simp only [hunion_empty]; rfl
  -- Unfold `rlp_phase1_exit_post_pure` so n1's explicit posts match.
  simp only [rlp_phase1_exit_post_pure_unfold]
  exact hcr_eq ▸ n1

theorem rlp_phase1_step_spec_acc_within (Acc : Prop) (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let kVal := (0 : Word) + signExtend12 k
    let code := rlp_phase1_step_code k offset base
    cpsBranchWithin 2 base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜Acc⌝)
      target
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal) **
         ⌜Acc ∧ BitVec.ult v5 kVal⌝)
      (base + 8)
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal) **
         ⌜Acc ∧ ¬ BitVec.ult v5 kVal⌝) := by
  have h := rlp_phase1_step_spec_within v5 v10 k offset base target htarget
  -- Frame `rlp_phase1_step_spec` with `⌜Acc⌝` on the right.
  have hf := cpsBranchWithin_frameR ⌜Acc⌝ pcFree_pure h
  -- hf has pre `(regs_3chain) ** ⌜Acc⌝`; target theorem has the 4-chain
  -- `regs ** ⌜Acc⌝`. Reshape via the associativity helper.
  exact cpsBranchWithin_weaken
    sepConj_chain_push_outer
    sepConj_merge_pure_and_end3
    sepConj_merge_pure_and_end3
    hf

@[irreducible]
def rlp_phase1_exit_post_acc
    (v5 : Word) (k : BitVec 12) (Acc : Prop) : Assertion :=
  let kVal := (0 : Word) + signExtend12 k
  (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal) ** ⌜Acc⌝

/-- Unfold lemma for `rlp_phase1_exit_post_acc`. -/
theorem rlp_phase1_exit_post_acc_unfold
    (v5 : Word) (k : BitVec 12) (Acc : Prop) :
    rlp_phase1_exit_post_acc v5 k Acc =
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) ** ⌜Acc⌝) := by
  delta rlp_phase1_exit_post_acc; rfl

/-- Accumulated-chain variant of `rlp_phase1_classifier_spec`. Each exit
    post carries the **full** conjunction of prior "not-taken" facts plus
    (for taken exits) the current "taken" fact, so downstream handlers can
    prove tight range bounds like `0x80 ≤ p < 0xB8` at exit `e2`.

    Reading the exit facts (with `k_i := (0 : Word) + signExtend12 K_i`):
    * `e1`: `ult v5 k1`                                    — i.e. `p < 0x80`
    * `e2`: `¬ ult v5 k1 ∧ ult v5 k2`                      — i.e. `0x80 ≤ p < 0xB8`
    * `e3`: `(¬ ult v5 k1 ∧ ¬ ult v5 k2) ∧ ult v5 k3`      — i.e. `0xB8 ≤ p < 0xC0`
    * `e4`: `((¬…k1 ∧ ¬…k2) ∧ ¬…k3) ∧ ult v5 k4`           — i.e. `0xC0 ≤ p < 0xF8`
    * `e5`: `((¬…k1 ∧ ¬…k2) ∧ ¬…k3) ∧ ¬ ult v5 k4`         — i.e. `0xF8 ≤ p`

    The nested `And` shape reflects the left-to-right accumulator build-up
    via `rlp_phase1_step_spec_acc`; consumers may reassociate with `And.assoc`. -/
theorem rlp_phase1_classifier_spec_acc_within (v5 v10 : Word) (base : Word)
    (off1 off2 off3 off4 : BitVec 13)
    (e1 e2 e3 e4 e5 : Word)
    (he1 : (base + 4) + signExtend13 off1 = e1)
    (he2 : (base + 12) + signExtend13 off2 = e2)
    (he3 : (base + 20) + signExtend13 off3 = e3)
    (he4 : (base + 28) + signExtend13 off4 = e4)
    (he5 : base + 32 = e5) :
    cpsNBranchWithin 8 base (rlp_phase1_classifier_code off1 off2 off3 off4 base)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e1, rlp_phase1_exit_post_acc v5 0x80
              (BitVec.ult v5 ((0 : Word) + signExtend12 0x80))),
       (e2, rlp_phase1_exit_post_acc v5 0xB8
              (¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
                 BitVec.ult v5 ((0 : Word) + signExtend12 0xB8))),
       (e3, rlp_phase1_exit_post_acc v5 0xC0
              ((¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
                ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xB8)) ∧
                 BitVec.ult v5 ((0 : Word) + signExtend12 0xC0))),
       (e4, rlp_phase1_exit_post_acc v5 0xF8
              (((¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
                 ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xB8)) ∧
                 ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xC0)) ∧
                 BitVec.ult v5 ((0 : Word) + signExtend12 0xF8))),
       (e5, rlp_phase1_exit_post_acc v5 0xF8
              (((¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
                 ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xB8)) ∧
                 ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xC0)) ∧
                 ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xF8)))] := by
  -- Step 1 has no prior accumulator, so use the plain step spec directly;
  -- its pre is just `regs` (no ⌜True⌝ prefix) and taken/fall posts already
  -- carry the dispatch fact as a single pure atom. Steps 2..4 then pick up
  -- the accumulator chain via `rlp_phase1_step_spec_acc`.
  have cs1 := rlp_phase1_step_spec_within v5 v10 0x80 off1 base e1 he1
  have cs2 := rlp_phase1_step_spec_acc_within
    (¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80))
    v5 ((0 : Word) + signExtend12 0x80)
    0xB8 off2 (base + 8) e2 (by
      rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega]; exact he2)
  have cs3 := rlp_phase1_step_spec_acc_within
    (¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
      ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xB8))
    v5 ((0 : Word) + signExtend12 0xB8)
    0xC0 off3 (base + 16) e3 (by
      rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega]; exact he3)
  have cs4 := rlp_phase1_step_spec_acc_within
    ((¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
       ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xB8)) ∧
       ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xC0))
    v5 ((0 : Word) + signExtend12 0xC0)
    0xF8 off4 (base + 24) e4 (by
      rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega]; exact he4)
  rw [show (base + 24 : Word) + 8 = e5 from by rw [← he5]; bv_omega] at cs4
  rw [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at cs2
  rw [show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at cs3
  -- Disjointness (same as plain spec).
  let cr1 := rlp_phase1_step_code 0x80 off1 base
  let cr2 := rlp_phase1_step_code 0xB8 off2 (base + 8)
  let cr3 := rlp_phase1_step_code 0xC0 off3 (base + 16)
  let cr4 := rlp_phase1_step_code 0xF8 off4 (base + 24)
  have hd12 : cr1.Disjoint cr2 := step_code_Disjoint_8 _ _ _ _ _
  have hd13 : cr1.Disjoint cr3 := step_code_Disjoint_16 _ _ _ _ _
  have hd14 : cr1.Disjoint cr4 := step_code_Disjoint_24 _ _ _ _ _
  have hd23 : cr2.Disjoint cr3 := step_code_Disjoint_8_at_8 0xB8 0xC0 off2 off3 base
  have hd24 : cr2.Disjoint cr4 := step_code_Disjoint_16_at_8 0xB8 0xF8 off2 off4 base
  have hd34 : cr3.Disjoint cr4 := step_code_Disjoint_8_at_16 0xC0 0xF8 off3 off4 base
  -- Fallthrough cpsNBranchWithin at e5, carrying cs4's fall-post accumulator.
  have ft : cpsNBranchWithin 0 e5 CodeReq.empty
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 0xF8)) **
       ⌜((¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
          ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xB8)) ∧
          ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xC0)) ∧
         ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xF8)⌝)
      [(e5, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 0xF8)) **
            ⌜((¬ BitVec.ult v5 ((0 : Word) + signExtend12 0x80) ∧
                ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xB8)) ∧
               ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xC0)) ∧
               ¬ BitVec.ult v5 ((0 : Word) + signExtend12 0xF8)⌝)] :=
    cpsNBranchWithin_refl e5 _ _ (fun _ hp => hp)
  -- Chain step 4 + ft (no perm needed: cs4.fall matches ft.pre).
  have n4 := cpsBranchWithin_cons_cpsNBranchWithin (CodeReq.Disjoint.empty_right cr4) cs4 ft
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  -- Chain remaining steps (no perm needed: each cs_i's fall matches cs_{i+1}'s pre).
  have hd3_rest : cr3.Disjoint (cr4.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd34
  have n3 := cpsBranchWithin_cons_cpsNBranchWithin hd3_rest cs3 n4
  have hd2_rest : cr2.Disjoint (cr3.union (cr4.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd23 hd24
  have n2 := cpsBranchWithin_cons_cpsNBranchWithin hd2_rest cs2 n3
  have hd1_rest : cr1.Disjoint (cr2.union (cr3.union (cr4.union CodeReq.empty))) := by
    rw [hunion_empty]
    exact CodeReq.Disjoint.union_right hd12 (CodeReq.Disjoint.union_right hd13 hd14)
  have n1 := cpsBranchWithin_cons_cpsNBranchWithin hd1_rest cs1 n2
  have hcr_eq : cr1.union (cr2.union (cr3.union (cr4.union CodeReq.empty))) =
      rlp_phase1_classifier_code off1 off2 off3 off4 base := by
    simp only [hunion_empty]; rfl
  -- n1's exits already match the goal's exit list structurally; just unfold
  -- the `@[irreducible]` exit-post def and rewrite the code requirement.
  simp only [rlp_phase1_exit_post_acc_unfold]
  exact hcr_eq ▸ n1

/-- The RISC-V phase-1 first-exit predicate implies the pure RLP prefix class.
    This is the bridge from the executable classifier's accumulated branch
    facts to `EvmAsm.EL.RLP.classifyPrefix`. -/
theorem rlp_phase1_acc_fact_classifyPrefix_singleByte
    (pfx : EvmAsm.EL.RLP.Byte)
    (h : BitVec.ult (BitVec.setWidth 64 pfx)
      ((0 : Word) + signExtend12 0x80)) :
    EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.singleByte := by
  rw [EvmAsm.EL.RLP.classifyPrefix_singleByte_iff]
  rw [BitVec.ult_eq_decide] at h
  simp only [BitVec.toNat_setWidth] at h
  have hmod : pfx.toNat % 18446744073709551616 = pfx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hk80 : (((0 : Word) + signExtend12 0x80).toNat = 0x80) := by native_decide
  rw [hmod, hk80] at h
  norm_num at h
  exact h

/-- The RISC-V phase-1 second-exit accumulated predicate implies the pure
    short-byte-string prefix class. -/
theorem rlp_phase1_acc_fact_classifyPrefix_shortBytes
    (pfx : EvmAsm.EL.RLP.Byte)
    (h : ¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0x80) ∧
         BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xB8)) :
    EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.shortBytes := by
  rw [EvmAsm.EL.RLP.classifyPrefix_shortBytes_iff]
  rw [BitVec.ult_eq_decide, BitVec.ult_eq_decide] at h
  simp only [BitVec.toNat_setWidth] at h
  have hmod : pfx.toNat % 18446744073709551616 = pfx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hk80 : (((0 : Word) + signExtend12 0x80).toNat = 0x80) := by native_decide
  have hkB8 : (((0 : Word) + signExtend12 0xB8).toNat = 0xB8) := by native_decide
  rw [hmod, hk80, hkB8] at h
  norm_num at h
  omega

/-- The RISC-V phase-1 third-exit accumulated predicate implies the pure
    long-byte-string prefix class. -/
theorem rlp_phase1_acc_fact_classifyPrefix_longBytes
    (pfx : EvmAsm.EL.RLP.Byte)
    (h : (¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0x80) ∧
          ¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xB8)) ∧
         BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xC0)) :
    EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.longBytes := by
  rw [EvmAsm.EL.RLP.classifyPrefix_longBytes_iff]
  rw [BitVec.ult_eq_decide, BitVec.ult_eq_decide, BitVec.ult_eq_decide] at h
  simp only [BitVec.toNat_setWidth] at h
  have hmod : pfx.toNat % 18446744073709551616 = pfx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hk80 : (((0 : Word) + signExtend12 0x80).toNat = 0x80) := by native_decide
  have hkB8 : (((0 : Word) + signExtend12 0xB8).toNat = 0xB8) := by native_decide
  have hkC0 : (((0 : Word) + signExtend12 0xC0).toNat = 0xC0) := by native_decide
  rw [hmod, hk80, hkB8, hkC0] at h
  norm_num at h
  omega

/-- The RISC-V phase-1 fourth-exit accumulated predicate implies the pure
    short-list prefix class. -/
theorem rlp_phase1_acc_fact_classifyPrefix_shortList
    (pfx : EvmAsm.EL.RLP.Byte)
    (h : ((¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0x80) ∧
           ¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xB8)) ∧
          ¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xC0)) ∧
         BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xF8)) :
    EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.shortList := by
  rw [EvmAsm.EL.RLP.classifyPrefix_shortList_iff]
  rw [BitVec.ult_eq_decide, BitVec.ult_eq_decide, BitVec.ult_eq_decide,
    BitVec.ult_eq_decide] at h
  simp only [BitVec.toNat_setWidth] at h
  have hmod : pfx.toNat % 18446744073709551616 = pfx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hk80 : (((0 : Word) + signExtend12 0x80).toNat = 0x80) := by native_decide
  have hkB8 : (((0 : Word) + signExtend12 0xB8).toNat = 0xB8) := by native_decide
  have hkC0 : (((0 : Word) + signExtend12 0xC0).toNat = 0xC0) := by native_decide
  have hkF8 : (((0 : Word) + signExtend12 0xF8).toNat = 0xF8) := by native_decide
  rw [hmod, hk80, hkB8, hkC0, hkF8] at h
  norm_num at h
  omega

/-- The RISC-V phase-1 fall-through accumulated predicate implies the pure
    long-list prefix class. -/
theorem rlp_phase1_acc_fact_classifyPrefix_longList
    (pfx : EvmAsm.EL.RLP.Byte)
    (h : ((¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0x80) ∧
           ¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xB8)) ∧
          ¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xC0)) ∧
         ¬ BitVec.ult (BitVec.setWidth 64 pfx)
            ((0 : Word) + signExtend12 0xF8)) :
    EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.longList := by
  rw [EvmAsm.EL.RLP.classifyPrefix_longList_iff]
  rw [BitVec.ult_eq_decide, BitVec.ult_eq_decide, BitVec.ult_eq_decide,
    BitVec.ult_eq_decide] at h
  simp only [BitVec.toNat_setWidth] at h
  have hmod : pfx.toNat % 18446744073709551616 = pfx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hk80 : (((0 : Word) + signExtend12 0x80).toNat = 0x80) := by native_decide
  have hkB8 : (((0 : Word) + signExtend12 0xB8).toNat = 0xB8) := by native_decide
  have hkC0 : (((0 : Word) + signExtend12 0xC0).toNat = 0xC0) := by native_decide
  have hkF8 : (((0 : Word) + signExtend12 0xF8).toNat = 0xF8) := by native_decide
  rw [hmod, hk80, hkB8, hkC0, hkF8] at h
  norm_num at h
  omega

/-- Weaken only the pure fact carried by an accumulated Phase 1 exit post. -/
theorem rlp_phase1_exit_post_acc_pure_mono
    {v5 : Word} {k : BitVec 12} {Acc Acc' : Prop}
    (hAcc : Acc → Acc') :
    ∀ h, rlp_phase1_exit_post_acc v5 k Acc h →
      rlp_phase1_exit_post_acc v5 k Acc' h := by
  intro h hp
  rw [rlp_phase1_exit_post_acc_unfold] at hp ⊢
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hp
  intro h' hp'
  rcases hp' with ⟨hempty, h_acc⟩
  exact ⟨hempty, hAcc h_acc⟩

/-- Phase 1 classifier spec whose exits directly identify the pure RLP prefix
    class for a zero-extended input prefix byte. This packages the executable
    classifier's accumulated branch facts into the semantic `classifyPrefix`
    view used by downstream decoder phases. -/
theorem rlp_phase1_classifier_spec_class_within
    (pfx : EvmAsm.EL.RLP.Byte) (v10 : Word) (base : Word)
    (off1 off2 off3 off4 : BitVec 13)
    (e1 e2 e3 e4 e5 : Word)
    (he1 : (base + 4) + signExtend13 off1 = e1)
    (he2 : (base + 12) + signExtend13 off2 = e2)
    (he3 : (base + 20) + signExtend13 off3 = e3)
    (he4 : (base + 28) + signExtend13 off4 = e4)
    (he5 : base + 32 = e5) :
    cpsNBranchWithin 8 base (rlp_phase1_classifier_code off1 off2 off3 off4 base)
      ((.x5 ↦ᵣ BitVec.setWidth 64 pfx) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e1, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0x80
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.singleByte)),
       (e2, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xB8
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.shortBytes)),
       (e3, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xC0
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.longBytes)),
       (e4, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.shortList)),
       (e5, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.longList))] := by
  have hacc := rlp_phase1_classifier_spec_acc_within (BitVec.setWidth 64 pfx)
    v10 base off1 off2 off3 off4 e1 e2 e3 e4 e5 he1 he2 he3 he4 he5
  refine cpsNBranchWithin_weaken_posts hacc ?_
  intro ex hex
  simp only [List.mem_cons, List.not_mem_nil] at hex
  rcases hex with h1 | h2 | h3 | h4 | h5
  · cases h1
    refine ⟨(e1, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0x80
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.singleByte)), by simp, rfl, ?_⟩
    exact rlp_phase1_exit_post_acc_pure_mono
      (fun h => rlp_phase1_acc_fact_classifyPrefix_singleByte pfx h)
  · cases h2
    refine ⟨(e2, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xB8
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.shortBytes)), by simp, rfl, ?_⟩
    exact rlp_phase1_exit_post_acc_pure_mono
      (fun h => rlp_phase1_acc_fact_classifyPrefix_shortBytes pfx h)
  · cases h3
    refine ⟨(e3, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xC0
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.longBytes)), by simp, rfl, ?_⟩
    exact rlp_phase1_exit_post_acc_pure_mono
      (fun h => rlp_phase1_acc_fact_classifyPrefix_longBytes pfx h)
  · cases h4
    refine ⟨(e4, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
              (EvmAsm.EL.RLP.classifyPrefix pfx =
                EvmAsm.EL.RLP.PrefixClass.shortList)), by simp, rfl, ?_⟩
    exact rlp_phase1_exit_post_acc_pure_mono
      (fun h => rlp_phase1_acc_fact_classifyPrefix_shortList pfx h)
  · rcases h5 with h5 | hfalse
    · cases h5
      refine ⟨(e5, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
                (EvmAsm.EL.RLP.classifyPrefix pfx =
                  EvmAsm.EL.RLP.PrefixClass.longList)), by simp, rfl, ?_⟩
      exact rlp_phase1_exit_post_acc_pure_mono
        (fun h => rlp_phase1_acc_fact_classifyPrefix_longList pfx h)
    · cases hfalse

end EvmAsm.Rv64.RLP
