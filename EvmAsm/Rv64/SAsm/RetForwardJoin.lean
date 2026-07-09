/-
  EvmAsm.Rv64.SAsm.RetForwardJoin

  The **shared-return-tail forward join** (bead evm-asm-k2f1x).

  `retIf` expresses ONE guard with two disjoint return tails, but validation
  routines commonly have SEVERAL guards that converge on the SAME shared
  tails at the machine level:

  ```
        bltu t0, a1, .invalid     -- guard 1 (taken → shared invalid tail)
        beqz a1,     .valid       -- guard 2 (taken → shared valid tail)
        <byte check>
        beq  t1, t0, .invalid     -- guard 3 (taken → shared invalid tail)
  .valid:   li a0, 0 ; ret        -- ONE copy, reached from 2 points
  .invalid: li a0, 1 ; ret        -- ONE copy, reached from 2 points
  ```

  Duplicating a tail would change guest bytes (turning a byte-transparent
  port into a re-emit).  This module keeps the tails single at the machine
  level and single at the proof level:

  * `sharedRetTail_spec` — the `li rd, c ; ret` return arm, proven ONCE per
    tail address against the routine's single `CodeReq`, generic in the
    result register/value and in an arbitrary `pcFree` frame.  Each guard
    that targets the tail reuses the same lemma instance.

  * `retJoinStation_spec` — one guard station: a conditional branch whose
    taken/not-taken postconditions carry the branch fact as a pure conjunct
    (the shape every `*_spec_gen_within` branch spec produces).  The
    continuation proofs receive the fact as a plain HYPOTHESIS (`cond →
    …` / `¬ cond → …`), so each arm can reduce its `if`-post without the
    `sepConj_pure_left` destructuring dance.  Chaining stations is just
    nesting: an outer station's fall-through proof IS the next station's
    joined triple.

  Everything is at `cpsTripleWithin` level (additive; no `Ast`/`Vc`
  changes).  Consumer: `create_deployed_code_valid`
  (`Codegen/Programs/CreateDeployedCodeValidSAsm.lean`).
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-- One forward-join guard station.  The branch's own postconditions carry
    the decided fact as a pure conjunct; the two continuations — one of
    which is typically a SHARED return tail also targeted by other
    stations — consume it as a hypothesis.  `m` is the common step bound of
    the two continuations (`cpsTripleWithin_mono_nSteps` the shorter one
    up). -/
theorem retJoinStation_spec {n m : Nat} {addr tgtT tgtF ret : Word}
    {cr : CodeReq} {P Qt Qf PT PF Q : Assertion} {cond : Prop}
    (hbr : cpsBranchWithin n addr cr P tgtT Qt tgtF Qf)
    (hentT : ∀ h, Qt h → (⌜cond⌝ ** PT) h)
    (hentF : ∀ h, Qf h → (⌜¬ cond⌝ ** PF) h)
    (htaken : cond → cpsTripleWithin m tgtT ret cr PT Q)
    (hfall : ¬ cond → cpsTripleWithin m tgtF ret cr PF Q) :
    cpsTripleWithin (n + m) addr ret cr P Q := by
  have hT : cpsTripleWithin m tgtT ret cr Qt Q :=
    cpsTripleWithin_weaken hentT (fun _ hq => hq)
      (cpsTripleWithin_pure_pre htaken)
  have hF : cpsTripleWithin m tgtF ret cr Qf Q :=
    cpsTripleWithin_weaken hentF (fun _ hq => hq)
      (cpsTripleWithin_pure_pre hfall)
  exact cpsBranchWithin_merge_same_cr hbr hT hF

/-- The shared `li rd, c ; ret` return tail, proven ONCE per tail address
    against the routine's single `CodeReq` and reused by every guard station
    that targets it — the tail bytes exist exactly once. -/
theorem sharedRetTail_spec (cr : CodeReq) (addr ret : Word) (rd : Reg)
    (c vOld : Word) (P : Assertion) (hP : P.pcFree)
    (hrd : rd ≠ .x0)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hli : ∀ a i, CodeReq.singleton addr (.LI rd c) a = some i → cr a = some i)
    (hret : ∀ a i, CodeReq.singleton (addr + 4) (.JALR .x0 .x1 0) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 addr ret cr
      ((rd ↦ᵣ vOld) ** ((.x1 : Reg) ↦ᵣ ret) ** P)
      ((rd ↦ᵣ c) ** ((.x1 : Reg) ↦ᵣ ret) ** P) := by
  have hLi := cpsTripleWithin_extend_code (hmono := hli)
    (h := li_spec_gen_within rd vOld c addr hrd)
  have hRet0 := cpsTripleWithin_extend_code (hmono := hret)
    (h := EvmAsm.Evm64.ret_spec_within' (addr + 4) ret)
  rw [halign] at hRet0
  have hLiF := cpsTripleWithin_frameR (((.x1 : Reg) ↦ᵣ ret) ** P)
    (pcFree_sepConj pcFree_regIs hP) hLi
  have hRetF := cpsTripleWithin_frameR ((rd ↦ᵣ c) ** P)
    (pcFree_sepConj pcFree_regIs hP) hRet0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hLiF hRetF)

end EvmAsm.Rv64.SAsm
