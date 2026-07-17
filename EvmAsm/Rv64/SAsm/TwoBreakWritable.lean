/-
  EvmAsm.Rv64.SAsm.TwoBreakWritable

  The **return-terminating two-break combinator with writable-output tails**
  (bead evm-asm-i177q).

  `retWhileBreak` (structured layer) expresses ONE mid-loop return break;
  `while2BreakJoin` reconverges its two breaks at a JOIN.  Comparison
  routines like `u256_lt_be` need a third shape: a scan loop with TWO
  mid-loop break guards routing to TWO **return tails that each write a
  DISTINCT value to a writable output cell**, with loop exhaustion falling
  into one of them:

  ```
  hdr:  beq  ctr, x0, .tail0        -- exhaustion   → tail 0
        <load/compare prefix>
        bltu tA, tB, .tail1         -- break guard A → tail 1
        bltu tB, tA, .tail0         -- break guard B → tail 0
        <advance> ; jal x0, hdr
  .tail1: li rs, 1 ; sd rs, 0(out) ; li a0, 0 ; ret   -- writes 1
  .tail0:            sd x0, 0(out) ; li a0, 0 ; ret   -- writes 0
  ```

  Everything is at `cpsTripleWithin` level (additive; no `Ast`/`Vc`
  changes), register/offset/value-agnostic.  Three pieces:

  * `storeRetTail_spec` — the writable-output return tail
    `SD rb, rs, ofs ; LI rd, c ; ret`, proven ONCE per tail address:
    it stores the value held in `rs` into the OWNED output dword cell
    `[rb + ofs]` and returns; the two tails instantiate it at their two
    distinct stored values (`rs`-held `1` vs the hardwired `x0` zero).
    The `sharedRetTail_spec` analogue with a store.

  * `breakStation_spec` — one break-guard station: a conditional branch
    whose taken arm runs a RETURN TAIL (a `cpsTripleWithin` to the shared
    `ret` continuation, e.g. a `storeRetTail_spec` instance) and whose
    fall-through arm CONTINUES the iteration (a `cpsBranchWithin` that may
    still break at a later station or loop back to the header).  Chaining
    stations is nesting, exactly as in `retJoinStation_spec`; the decided
    branch fact arrives as a plain hypothesis on each arm.

  * `twoBreakRetLoop_spec` — the loop: from `inv 0` at the header, each
    iteration either RETURNS (some break fired and its tail completed, the
    final post `Q` holds) or comes back to the header with `inv (i+1)`;
    after `N` iterations the exhaustion path must return with `Q`.  The
    conclusion is a single-exit triple `hdr → ret` — return-terminating,
    ready to sequence after the routine's init block.

  Supporting glue (branch-level composition the CPSSpec module lacks):
  `cpsBranchWithin_pure_pre`, `cpsTripleWithin_as_cpsBranchWithin_left/
  _right`, `cpsBranchWithin_merge_branch_same_cr`.

  Consumer: `u256_lt_be` (`Codegen/Programs/U256LtBeSAsm.lean`) — two
  `BLTU` stations over a dual byte-walk, tails writing the `a < b` flag
  `1`/`0` to the `a2` output dword.
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  Branch-level composition glue
-- ============================================================================

/-- Discharge a pure-proposition conjunct in a branch precondition
    (branch analogue of `cpsTripleWithin_pure_pre`). -/
theorem cpsBranchWithin_pure_pre {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Prop} {H : Assertion} {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f : Assertion}
    (h : P → cpsBranchWithin n entry cr H exit_t Q_t exit_f Q_f) :
    cpsBranchWithin n entry cr (⌜P⌝ ** H) exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨h0, hcompat, hh⟩ := hPR
  rw [sepConj_assoc', sepConj_pure_left] at hh
  exact h hh.1 R hR s hcr ⟨h0, hcompat, hh.2⟩ hpc

/-- A single-exit triple viewed as a branch that always takes the FIRST
    exit.  The second exit is arbitrary. -/
theorem cpsTripleWithin_as_cpsBranchWithin_left {n : Nat} {entry e : Word}
    {cr : CodeReq} {P Q : Assertion} (f : Word) (Q_f : Assertion)
    (h : cpsTripleWithin n entry e cr P Q) :
    cpsBranchWithin n entry cr P e Q f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, Or.inl ⟨hpc', hQR⟩⟩

/-- A single-exit triple viewed as a branch that always takes the SECOND
    exit.  The first exit is arbitrary. -/
theorem cpsTripleWithin_as_cpsBranchWithin_right {n : Nat} {entry f : Word}
    {cr : CodeReq} {P Q : Assertion} (e : Word) (Q_t : Assertion)
    (h : cpsTripleWithin n entry f cr P Q) :
    cpsBranchWithin n entry cr P e Q_t f Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, Or.inr ⟨hpc', hQR⟩⟩

/-- Branch-to-branches composition (same CodeReq): a guard followed by a
    branchy continuation at each of its exits, both continuations sharing
    the same two final exits.  Bounds add, using the common continuation
    bound. -/
theorem cpsBranchWithin_merge_branch_same_cr {n m : Nat}
    {entry l_t l_f : Word} {cr : CodeReq}
    {P Q_t Q_f : Assertion} {e1 e2 : Word} {R1 R2 : Assertion}
    (hbr : cpsBranchWithin n entry cr P l_t Q_t l_f Q_f)
    (h_t : cpsBranchWithin m l_t cr Q_t e1 R1 e2 R2)
    (h_f : cpsBranchWithin m l_f cr Q_f e1 R1 e2 R2) :
    cpsBranchWithin (n + m) entry cr P e1 R1 e2 R2 := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, hk1, s1, hstep1, hbranch⟩ := hbr F hF s hcr hPF hpc
  have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
  rcases hbranch with ⟨hpc1, hQ⟩ | ⟨hpc1, hQ⟩
  · obtain ⟨k2, hk2, s2, hstep2, hcase⟩ := h_t F hF s1 hcr' hQ hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hcase⟩
  · obtain ⟨k2, hk2, s2, hstep2, hcase⟩ := h_f F hF s1 hcr' hQ hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hcase⟩

-- ============================================================================
-- §2  The break station
-- ============================================================================

/-- **One break-guard station.**  A conditional branch inside a loop
    iteration: the taken arm runs a RETURN TAIL (a triple to the shared
    `ret` continuation with the loop's final post `Q` — e.g. a
    `storeRetTail_spec` instance), the fall-through arm CONTINUES the
    iteration (still branchy: it may break at a later station, reaching
    `ret` with `Q`, or loop back to `hdr` with `I`).  The branch's own
    postconditions carry the decided fact as a pure conjunct (the shape
    every `*_spec_gen_within` branch spec produces); each arm consumes it
    as a hypothesis.  Chaining stations is nesting: an outer station's
    `hfall` IS the next station's conclusion. -/
theorem breakStation_spec {n m : Nat} {addr tgtT tgtF ret hdr : Word}
    {cr : CodeReq} {P Qt Qf PT PF Q I : Assertion} {cond : Prop}
    (hbr : cpsBranchWithin n addr cr P tgtT Qt tgtF Qf)
    (hentT : ∀ h, Qt h → (⌜cond⌝ ** PT) h)
    (hentF : ∀ h, Qf h → (⌜¬ cond⌝ ** PF) h)
    (hbreak : cond → cpsTripleWithin m tgtT ret cr PT Q)
    (hfall : ¬ cond → cpsBranchWithin m tgtF cr PF ret Q hdr I) :
    cpsBranchWithin (n + m) addr cr P ret Q hdr I := by
  have hT : cpsBranchWithin m tgtT cr Qt ret Q hdr I :=
    cpsBranchWithin_weaken hentT (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pure_pre (fun hc =>
        cpsTripleWithin_as_cpsBranchWithin_left hdr I (hbreak hc)))
  have hF : cpsBranchWithin m tgtF cr Qf ret Q hdr I :=
    cpsBranchWithin_weaken hentF (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pure_pre hfall)
  exact cpsBranchWithin_merge_branch_same_cr hbr hT hF

-- ============================================================================
-- §3  The writable-output return tail
-- ============================================================================

/-- **The writable-output return tail** `SD rb, rs, ofs ; LI rd, c ; ret`:
    stores the value held in `rs` into the OWNED output dword cell
    `[rb + ofs]`, loads the result register, and returns.  Proven ONCE per
    tail address against the routine's single `CodeReq`; register-, offset-
    and value-agnostic — the two tails of a two-break loop instantiate it
    at their two DISTINCT stored values.  The `sharedRetTail_spec` analogue
    with a store (the post pins the output cell to the stored value — no
    arbitrary write). -/
theorem storeRetTail_spec (cr : CodeReq) (addr ret : Word) (rb rs rd : Reg)
    (ofs : BitVec 12) (p v a0Old c : Word)
    (hrd : rd ≠ .x0)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hsd : ∀ a i, CodeReq.singleton addr (.SD rb rs ofs) a = some i →
      cr a = some i)
    (hli : ∀ a i, CodeReq.singleton (addr + 4) (.LI rd c) a = some i →
      cr a = some i)
    (hret : ∀ a i, CodeReq.singleton (addr + 8) (.JALR .x0 .x1 0) a = some i →
      cr a = some i) :
    cpsTripleWithin 3 addr ret cr
      ((rb ↦ᵣ p) ** (rs ↦ᵣ v) ** memOwn (p + signExtend12 ofs) **
        (rd ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
      ((rb ↦ᵣ p) ** (rs ↦ᵣ v) ** ((p + signExtend12 ofs) ↦ₘ v) **
        (rd ↦ᵣ c) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have hSd := cpsTripleWithin_extend_code (hmono := hsd)
    (h := sd_spec_gen_own_within rb rs p v ofs addr)
  have hLi := cpsTripleWithin_extend_code (hmono := hli)
    (h := li_spec_gen_within rd a0Old c (addr + 4) hrd)
  rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]
    at hLi
  have hRet := cpsTripleWithin_extend_code (hmono := hret)
    (h := EvmAsm.Evm64.ret_spec_within' (addr + 8) ret)
  rw [halign] at hRet
  have hSdF := cpsTripleWithin_frameR
    ((rd ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
    (pcFree_sepConj pcFree_regIs pcFree_regIs) hSd
  have hLiF := cpsTripleWithin_frameR
    ((rb ↦ᵣ p) ** (rs ↦ᵣ v) ** ((p + signExtend12 ofs) ↦ₘ v) **
      ((.x1 : Reg) ↦ᵣ ret))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs pcFree_regIs))) hLi
  have hRetF := cpsTripleWithin_frameR
    ((rb ↦ᵣ p) ** (rs ↦ᵣ v) ** ((p + signExtend12 ofs) ↦ₘ v) **
      (rd ↦ᵣ c))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs pcFree_regIs))) hRet
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hSdF hLiF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hRetF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc2

-- ============================================================================
-- §4  The return-terminating break loop
-- ============================================================================

/-- **The return-terminating break loop.**  From `inv 0` at the loop
    header, each of the `N` iterations either RETURNS — one of its break
    stations fired and the corresponding writable-output tail completed,
    so the shared continuation `ret` is reached with the FINAL post `Q` —
    or comes back to the header with the invariant advanced; the
    exhaustion path (`inv N` at the header, i.e. the loop guard fires)
    must also return with `Q`.  `m` bounds one full iteration INCLUDING
    its break tail; `e` bounds the exhaustion path including its tail.

    The per-iteration hypothesis is exactly what nesting
    `breakStation_spec` produces: a two-exit branch `hdr → {ret with Q,
    hdr with inv (i+1)}`. -/
theorem twoBreakRetLoop_spec {hdr ret : Word} {cr : CodeReq} {Q : Assertion}
    (N m e : Nat) (inv : Nat → Assertion)
    (hiter : ∀ i, i < N →
      cpsBranchWithin m hdr cr (inv i) ret Q hdr (inv (i + 1)))
    (hexh : cpsTripleWithin e hdr ret cr (inv N) Q) :
    cpsTripleWithin (N * m + e) hdr ret cr (inv 0) Q := by
  suffices h : ∀ M i, i + M = N →
      cpsTripleWithin (M * m + e) hdr ret cr (inv i) Q from
    h N 0 (by omega)
  intro M
  induction M with
  | zero =>
      intro i hi
      rw [show i = N from by omega]
      simpa using hexh
  | succ n ih =>
      intro i hi
      have hstay : cpsTripleWithin (n * m + e) ret ret cr Q Q := by
        intro R _hR s _hcr hQR hpc
        exact ⟨0, Nat.zero_le _, s, rfl, hpc, hQR⟩
      have hmerge := cpsBranchWithin_merge_same_cr
        (hiter i (by omega)) hstay (ih (i + 1) (by omega))
      rw [show (n + 1) * m + e = m + (n * m + e) from by
        rw [Nat.succ_mul]; omega]
      exact hmerge


end EvmAsm.Rv64.SAsm
