/-
  EvmAsm.Rv64.WP.Core

  A small weakest-precondition style layer over the existing bounded CPS
  Hoare triples.  The layer is intentionally soundness-first: each calculator
  result exposes a precondition together with a proof that the existing
  `cpsTripleWithin`/`cpsNBranchWithin` contract follows.
-/

import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64
namespace WP

/-- Assertion entailment.  `Entails P Q` means every partial state satisfying
    `P` also satisfies `Q`. -/
def Entails (P Q : Assertion) : Prop :=
  ∀ h, P h → Q h

namespace Entails

theorem refl (P : Assertion) : Entails P P :=
  fun _ hp => hp

theorem trans {P Q R : Assertion} (hPQ : Entails P Q) (hQR : Entails Q R) :
    Entails P R :=
  fun h hp => hQR h (hPQ h hp)

end Entails

/-- A backward WP result for a single-exit region.

    The intended reading is: to establish `post` at `exit_`, it is sufficient
    to prove `pre` at `entry`; `sound` is the existing CPS triple that makes
    this kernel-checked. -/
structure Triple (entry exit_ : Word) (cr : CodeReq) (post : Assertion) where
  nSteps : Nat
  pre : Assertion
  sound : cpsTripleWithin nSteps entry exit_ cr pre post

namespace Triple

/-- The reduced precondition computed by the WP object. -/
def wp {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) : Assertion :=
  t.pre

/-- A same-address continuation: the WP of `post` at the current PC is `pre`
    when `pre` entails `post`. -/
def refl (addr : Word) (cr : CodeReq) {pre post : Assertion}
    (h : Entails pre post) : Triple addr addr cr post where
  nSteps := 0
  pre := pre
  sound := by
    intro R hR s _hcr hPR hpc
    exact ⟨0, Nat.le_refl 0, s, rfl, hpc, by
      obtain ⟨hp, hcompat, hpq⟩ := hPR
      exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

/-- A WP continuation for an unreachable state. If the computed precondition is
    contradictory, any exit/postcondition follows without executing code. This
    is useful when generated control-flow keeps syntactic exits whose path
    guards are inconsistent with the current input witness. -/
def unreachable (entry exit_ : Word) (cr : CodeReq) {pre post : Assertion}
    (hpre : ∀ h, pre h → False) : Triple entry exit_ cr post where
  nSteps := 0
  pre := pre
  sound := by
    intro R _hR s _hcr hPR _hpc
    obtain ⟨hp, _hcompat, hpq⟩ := hPR
    obtain ⟨hprePart, _hRPart, _hd, _hunion, hpreSat, _hRSat⟩ := hpq
    exact False.elim (hpre hprePart hpreSat)

/-- Lift an already-proved CPS triple into a WP result, weakening its
    postcondition to the requested continuation post. -/
def ofSpec {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post post' : Assertion}
    (hpost : Entails post post')
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    Triple entry exit_ cr post' where
  nSteps := nSteps
  pre := pre
  sound := cpsTripleWithin_weaken (fun _ hp => hp) hpost h

/-- Weaken the computed precondition. -/
def weakenPre {entry exit_ : Word} {cr : CodeReq} {post pre' : Assertion}
    (t : Triple entry exit_ cr post) (hpre : Entails pre' t.pre) :
    Triple entry exit_ cr post where
  nSteps := t.nSteps
  pre := pre'
  sound := cpsTripleWithin_weaken hpre (fun _ hp => hp) t.sound

/-- Weaken the continuation postcondition. -/
def weakenPost {entry exit_ : Word} {cr : CodeReq} {post post' : Assertion}
    (t : Triple entry exit_ cr post) (hpost : Entails post post') :
    Triple entry exit_ cr post' where
  nSteps := t.nSteps
  pre := t.pre
  sound := cpsTripleWithin_weaken (fun _ hp => hp) hpost t.sound

/-- Increase the step budget of a WP result. -/
def monoSteps {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) {nSteps' : Nat} (hle : t.nSteps ≤ nSteps') :
    Triple entry exit_ cr post where
  nSteps := nSteps'
  pre := t.pre
  sound := cpsTripleWithin_mono_nSteps hle t.sound

/-- Extend a WP result to a larger persistent code requirement. -/
def extendCode {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    Triple entry exit_ cr' post where
  nSteps := t.nSteps
  pre := t.pre
  sound := cpsTripleWithin_extend_code hmono t.sound

/-- Frame a single-exit WP result with a PC-free assertion. -/
def frameR {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (F : Assertion) (hF : F.pcFree) :
    Triple entry exit_ cr (post ** F) where
  nSteps := t.nSteps
  pre := t.pre ** F
  sound := cpsTripleWithin_frameR F hF t.sound

/-- Rewrite the entry address of a WP result. -/
def changeEntry {entry entry' exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (hentry : entry' = entry) :
    Triple entry' exit_ cr post where
  nSteps := t.nSteps
  pre := t.pre
  sound := by
    intro R hR s hcr hPR hpc
    exact t.sound R hR s hcr hPR (by simpa [hentry] using hpc)

/-- Rewrite the exit address of a WP result. -/
def changeExit {entry exit_ exit_' : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (hexit : exit_ = exit_') :
    Triple entry exit_' cr post where
  nSteps := t.nSteps
  pre := t.pre
  sound := by
    intro R hR s hcr hPR hpc
    obtain ⟨k, hk, s', hstep, hpc', hpost⟩ := t.sound R hR s hcr hPR hpc
    exact ⟨k, hk, s', hstep, by simpa [hexit] using hpc', hpost⟩

/-- Backward sequencing when both regions share the same persistent code
    requirement.  The precondition of the tail becomes the requested
    postcondition for the head. -/
def seq {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nSteps entry mid cr pre midPost)
    (tail : Triple mid exit_ cr post)
    (hlink : Entails midPost tail.pre) :
    Triple entry exit_ cr post where
  nSteps := nSteps + tail.nSteps
  pre := pre
  sound := cpsTripleWithin_seq_perm_same_cr hlink head tail.sound

/-- Backward sequencing for disjoint code requirements. -/
def seqDisjoint {nSteps : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nSteps entry mid cr1 pre midPost)
    (tail : Triple mid exit_ cr2 post)
    (hlink : Entails midPost tail.pre) :
    Triple entry exit_ (cr1.union cr2) post where
  nSteps := nSteps + tail.nSteps
  pre := pre
  sound := cpsTripleWithin_seq_with_perm hd hlink head tail.sound

/-- Projection lemmas used by WP link normalization. -/
theorem refl_pre (addr : Word) (cr : CodeReq) {pre post : Assertion}
    (h : Entails pre post) :
    (refl addr cr h).pre = pre :=
  rfl

theorem unreachable_pre (entry exit_ : Word) (cr : CodeReq) {pre post : Assertion}
    (hpre : ∀ h, pre h → False) :
    (@unreachable entry exit_ cr pre post hpre).pre = pre :=
  rfl

theorem ofSpec_pre {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post post' : Assertion}
    (hpost : Entails post post')
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    (ofSpec hpost h).pre = pre :=
  rfl

theorem weakenPre_pre {entry exit_ : Word} {cr : CodeReq} {post pre' : Assertion}
    (t : Triple entry exit_ cr post) (hpre : Entails pre' t.pre) :
    (weakenPre t hpre).pre = pre' :=
  rfl

theorem weakenPost_pre {entry exit_ : Word} {cr : CodeReq} {post post' : Assertion}
    (t : Triple entry exit_ cr post) (hpost : Entails post post') :
    (weakenPost t hpost).pre = t.pre :=
  rfl

theorem monoSteps_pre {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) {nSteps' : Nat} (hle : t.nSteps ≤ nSteps') :
    (monoSteps t hle).pre = t.pre :=
  rfl

theorem extendCode_pre {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    (extendCode t hmono).pre = t.pre :=
  rfl

theorem frameR_pre {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (F : Assertion) (hF : F.pcFree) :
    (frameR t F hF).pre = (t.pre ** F) :=
  rfl

theorem changeEntry_pre {entry entry' exit_ : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (hentry : entry' = entry) :
    (changeEntry t hentry).pre = t.pre :=
  rfl

theorem changeExit_pre {entry exit_ exit_' : Word} {cr : CodeReq} {post : Assertion}
    (t : Triple entry exit_ cr post) (hexit : exit_ = exit_') :
    (changeExit t hexit).pre = t.pre :=
  rfl

theorem seq_pre {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nSteps entry mid cr pre midPost)
    (tail : Triple mid exit_ cr post)
    (hlink : Entails midPost tail.pre) :
    (seq head tail hlink).pre = pre :=
  rfl

theorem seqDisjoint_pre {nSteps : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nSteps entry mid cr1 pre midPost)
    (tail : Triple mid exit_ cr2 post)
    (hlink : Entails midPost tail.pre) :
    (seqDisjoint hd head tail hlink).pre = pre :=
  rfl

end Triple

/-- A two-exit branch summary consumable by the WP join rule. -/
structure Branch (entry : Word) (cr : CodeReq) where
  nSteps : Nat
  pre : Assertion
  exit_t : Word
  post_t : Assertion
  exit_f : Word
  post_f : Assertion
  sound : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f

namespace Branch

def ofSpec {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exit_t : Word} {post_t : Assertion}
    {exit_f : Word} {post_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f) :
    Branch entry cr where
  nSteps := nSteps
  pre := pre
  exit_t := exit_t
  post_t := post_t
  exit_f := exit_f
  post_f := post_f
  sound := h

/-- Frame both exits of a branch with a PC-free assertion. -/
def frameR {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) : Branch entry cr where
  nSteps := br.nSteps
  pre := br.pre ** F
  exit_t := br.exit_t
  post_t := br.post_t ** F
  exit_f := br.exit_f
  post_f := br.post_f ** F
  sound := cpsBranchWithin_frameR F hF br.sound

/-- Join a branch by providing a continuation for each exit.  The branch's
    posts only need to entail the corresponding continuation preconditions. -/
def join {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : Branch entry cr)
    (t : Triple br.exit_t exit_ cr post)
    (f : Triple br.exit_f exit_ cr post)
    (ht : Entails br.post_t t.pre)
    (hf : Entails br.post_f f.pre) :
    Triple entry exit_ cr post where
  nSteps := br.nSteps + Nat.max t.nSteps f.nSteps
  pre := br.pre
  sound := by
    exact cpsBranchWithin_merge_same_cr
      (cpsBranchWithin_weaken (fun _ hp => hp) ht hf br.sound)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_left t.nSteps f.nSteps) t.sound)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right t.nSteps f.nSteps) f.sound)

/-- Continue only the taken exit of a branch with disjoint code, leaving the
    not-taken exit open.  This is useful for early failure/success endpoints in
    generated CFGs. -/
def seqTakenDisjoint {entry target : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Triple br.exit_t target cr2 post)
    (hlink : Entails br.post_t tail.pre) :
    Branch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exit_t := target
  post_t := post
  exit_f := br.exit_f
  post_f := br.post_f
  sound := cpsBranchWithin_seq_cpsTripleWithin_taken hd br.sound (tail.weakenPre hlink).sound

/-- Continue only the not-taken exit of a branch with disjoint code, leaving the
    taken exit open.  This is the usual shape for fall-through decoder logic. -/
def seqNotTakenDisjoint {entry target : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Triple br.exit_f target cr2 post)
    (hlink : Entails br.post_f tail.pre) :
    Branch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exit_t := br.exit_t
  post_t := br.post_t
  exit_f := target
  post_f := post
  sound := cpsBranchWithin_seq_cpsTripleWithin_notTaken hd br.sound (tail.weakenPre hlink).sound

/-- Continue the taken exit with another branch whose taken exit converges with
    the first branch fall exit as one shared failure case. The second branch fall
    exit becomes the success exit of the composed branch. -/
def seqTakenBranchConvergeDisjoint {entry : Word} {cr1 cr2 : CodeReq}
    {failPost : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Branch br.exit_t cr2)
    (hfail : tail.exit_t = br.exit_f)
    (hlink : Entails br.post_t tail.pre)
    (hf1 : Entails br.post_f failPost)
    (hf2 : Entails tail.post_t failPost) :
    Branch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exit_t := tail.exit_f
  post_t := tail.post_f
  exit_f := br.exit_f
  post_f := failPost
  sound := by
    have htail : cpsBranchWithin tail.nSteps br.exit_t cr2 tail.pre
        br.exit_f tail.post_t tail.exit_f tail.post_f := by
      simpa [hfail] using tail.sound
    exact cpsBranchWithin_seq_cpsBranchWithin_taken_converge hd br.sound
      (cpsBranchWithin_weaken hlink (fun _ hp => hp) (fun _ hp => hp) htail)
      hf1 hf2

/-- Projection lemmas used by WP link normalization. -/
theorem ofSpec_pre {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exit_t : Word} {post_t : Assertion}
    {exit_f : Word} {post_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f) :
    (ofSpec h).pre = pre :=
  rfl

theorem ofSpec_exit_t {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exit_t : Word} {post_t : Assertion}
    {exit_f : Word} {post_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f) :
    (ofSpec h).exit_t = exit_t :=
  rfl

theorem ofSpec_post_t {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exit_t : Word} {post_t : Assertion}
    {exit_f : Word} {post_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f) :
    (ofSpec h).post_t = post_t :=
  rfl

theorem ofSpec_exit_f {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exit_t : Word} {post_t : Assertion}
    {exit_f : Word} {post_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f) :
    (ofSpec h).exit_f = exit_f :=
  rfl

theorem ofSpec_post_f {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exit_t : Word} {post_t : Assertion}
    {exit_f : Word} {post_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr pre exit_t post_t exit_f post_f) :
    (ofSpec h).post_f = post_f :=
  rfl

theorem frameR_pre {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) :
    (frameR br F hF).pre = (br.pre ** F) :=
  rfl

theorem frameR_exit_t {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) :
    (frameR br F hF).exit_t = br.exit_t :=
  rfl

theorem frameR_post_t {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) :
    (frameR br F hF).post_t = (br.post_t ** F) :=
  rfl

theorem frameR_exit_f {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) :
    (frameR br F hF).exit_f = br.exit_f :=
  rfl

theorem frameR_post_f {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) :
    (frameR br F hF).post_f = (br.post_f ** F) :=
  rfl

theorem join_pre {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : Branch entry cr)
    (t : Triple br.exit_t exit_ cr post)
    (f : Triple br.exit_f exit_ cr post)
    (ht : Entails br.post_t t.pre)
    (hf : Entails br.post_f f.pre) :
    (join br t f ht hf).pre = br.pre :=
  rfl

theorem seqTakenDisjoint_pre {entry target : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Triple br.exit_t target cr2 post)
    (hlink : Entails br.post_t tail.pre) :
    (seqTakenDisjoint hd br tail hlink).pre = br.pre :=
  rfl

theorem seqNotTakenDisjoint_pre {entry target : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Triple br.exit_f target cr2 post)
    (hlink : Entails br.post_f tail.pre) :
    (seqNotTakenDisjoint hd br tail hlink).pre = br.pre :=
  rfl

theorem seqTakenBranchConvergeDisjoint_pre {entry : Word} {cr1 cr2 : CodeReq}
    {failPost : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Branch br.exit_t cr2)
    (hfail : tail.exit_t = br.exit_f)
    (hlink : Entails br.post_t tail.pre)
    (hf1 : Entails br.post_f failPost)
    (hf2 : Entails tail.post_t failPost) :
    (seqTakenBranchConvergeDisjoint hd br tail hfail hlink hf1 hf2).pre = br.pre :=
  rfl

end Branch

/-- A multi-exit branch summary. -/
structure NBranch (entry : Word) (cr : CodeReq) where
  nSteps : Nat
  pre : Assertion
  exits : List (Word × Assertion)
  sound : cpsNBranchWithin nSteps entry cr pre exits

namespace NBranch

def ofSpec {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {pre : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry cr pre exits) :
    NBranch entry cr where
  nSteps := nSteps
  pre := pre
  exits := exits
  sound := h

/-- View a single-exit WP triple as a singleton multi-exit branch. -/
def ofTriple {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Triple entry exit_ cr post) :
    NBranch entry cr :=
  ofSpec (cpsTripleWithin_as_cpsNBranchWithin cfg.sound)

theorem ofTriple_pre {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Triple entry exit_ cr post) :
    (ofTriple cfg).pre = cfg.pre := by
  rfl

theorem ofTriple_exits {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Triple entry exit_ cr post) :
    (ofTriple cfg).exits = [(exit_, post)] := by
  rfl

/-- View a two-exit branch as a multi-exit branch. -/
def ofBranch {entry : Word} {cr : CodeReq} (br : Branch entry cr) :
    NBranch entry cr where
  nSteps := br.nSteps
  pre := br.pre
  exits := [(br.exit_t, br.post_t), (br.exit_f, br.post_f)]
  sound := cpsBranchWithin_as_cpsNBranchWithin br.sound

/-- Weaken the computed precondition of an N-way branch. -/
def weakenPre {entry : Word} {cr : CodeReq} {pre' : Assertion}
    (br : NBranch entry cr) (hpre : Entails pre' br.pre) : NBranch entry cr where
  nSteps := br.nSteps
  pre := pre'
  exits := br.exits
  sound := cpsNBranchWithin_weaken_pre hpre br.sound

/-- Extend an N-way branch to a larger persistent code requirement. -/
def extendCode {entry : Word} {cr cr' : CodeReq}
    (br : NBranch entry cr)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    NBranch entry cr' where
  nSteps := br.nSteps
  pre := br.pre
  exits := br.exits
  sound := cpsNBranchWithin_extend_code hmono br.sound

/-- Frame every exit of an N-way branch with a PC-free assertion. -/
def frameR {entry : Word} {cr : CodeReq}
    (br : NBranch entry cr) (F : Assertion) (hF : F.pcFree) : NBranch entry cr where
  nSteps := br.nSteps
  pre := br.pre ** F
  exits := br.exits.map (fun ex => (ex.1, ex.2 ** F))
  sound := cpsNBranchWithin_frameR hF br.sound

/-- Weaken the postconditions of an N-way branch without changing its step
    bound or computed precondition. This is the WP-facing form of
    cpsNBranchWithin_weaken_posts, useful after symbolic control-flow
    construction has reduced the remaining work to per-exit semantic facts. -/
def weakenPosts {entry : Word} {cr : CodeReq}
    (br : NBranch entry cr) (exits' : List (Word × Assertion))
    (hmap : ∀ ex ∈ br.exits, ∃ ex' ∈ exits',
      ex'.1 = ex.1 ∧ Entails ex.2 ex'.2) :
    NBranch entry cr where
  nSteps := br.nSteps
  pre := br.pre
  exits := exits'
  sound := cpsNBranchWithin_weaken_posts br.sound hmap

/-- Weaken the head exit and optionally remap the tail exits of an N-way branch.
    This avoids rebuilding the low-level membership map when a generated proof
    consumes exits from left to right. -/
def weakenPostsCons {entry : Word} {cr : CodeReq}
    {l : Word} {Q Q' : Assertion} {others others' : List (Word × Assertion)}
    (br : NBranch entry cr) (hexits : br.exits = (l, Q) :: others)
    (hhead : Entails Q Q')
    (htail : ∀ ex ∈ others, ∃ ex' ∈ others',
      ex'.1 = ex.1 ∧ Entails ex.2 ex'.2) :
    NBranch entry cr :=
  br.weakenPosts ((l, Q') :: others') (by
    intro ex hmem
    have hmem' : ex ∈ (l, Q) :: others := by
      simpa [hexits] using hmem
    cases hmem' with
    | head =>
        exact ⟨(l, Q'), by simp, rfl, hhead⟩
    | tail _ htailmem =>
        obtain ⟨ex', hmemEx', heq, hent⟩ := htail ex htailmem
        exact ⟨ex', List.mem_cons_of_mem _ hmemEx', heq, hent⟩)

/-- Weaken only the head exit of an N-way branch, preserving every tail exit. -/
def weakenHeadPost {entry : Word} {cr : CodeReq}
    {l : Word} {Q Q' : Assertion} {others : List (Word × Assertion)}
    (br : NBranch entry cr) (hexits : br.exits = (l, Q) :: others)
    (hhead : Entails Q Q') :
    NBranch entry cr :=
  br.weakenPostsCons hexits hhead (fun ex hmem =>
    ⟨ex, hmem, rfl, Entails.refl ex.2⟩)

/-- Weaken exactly two known exits. This is a small-list frontend for
    `weakenPosts`, avoiding the recurring membership proof in generated CFG
    adapters. -/
def weakenPosts2 {entry : Word} {cr : CodeReq}
    {l1 l2 : Word} {Q1 Q2 Q1' Q2' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') :
    NBranch entry cr :=
  br.weakenPosts [(l1, Q1'), (l2, Q2')] (by
    intro ex hmem
    have hmem' : ex ∈ [(l1, Q1), (l2, Q2)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l1, Q1'), by simp, rfl, h1⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l2, Q2'), by simp, rfl, h2⟩)

/-- Weaken exactly three known exits. This is a small-list frontend for
    `weakenPosts`, avoiding the recurring membership proof in generated CFG
    adapters. -/
def weakenPosts3 {entry : Word} {cr : CodeReq}
    {l1 l2 l3 : Word} {Q1 Q2 Q3 Q1' Q2' Q3' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') (h3 : Entails Q3 Q3') :
    NBranch entry cr :=
  br.weakenPosts [(l1, Q1'), (l2, Q2'), (l3, Q3')] (by
    intro ex hmem
    have hmem' : ex ∈ [(l1, Q1), (l2, Q2), (l3, Q3)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l1, Q1'), by simp, rfl, h1⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l2, Q2'), by simp, rfl, h2⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l3, Q3'), by simp, rfl, h3⟩)

/-- Weaken exactly four known exits. This is the common endpoint for generated
    decoder classifiers: normalize the calculated exits once, then provide one
    semantic entailment per arm. -/
def weakenPosts4 {entry : Word} {cr : CodeReq}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 Q1' Q2' Q3' Q4' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') (h3 : Entails Q3 Q3')
    (h4 : Entails Q4 Q4') :
    NBranch entry cr :=
  br.weakenPosts [(l1, Q1'), (l2, Q2'), (l3, Q3'), (l4, Q4')] (by
    intro ex hmem
    have hmem' : ex ∈ [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase | hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l1, Q1'), by simp, rfl, h1⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l2, Q2'), by simp, rfl, h2⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l3, Q3'), by simp, rfl, h3⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l4, Q4'), by simp, rfl, h4⟩)

/-- Weaken exactly four known exits while merging the first two exits into one
    replacement exit. The first two original exits must share the same target. -/
def weakenPosts4MergeFirstTwo {entry : Word} {cr : CodeReq}
    {l l3 l4 : Word} {Q1 Q2 Q3 Q4 Q12 Q3' Q4' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l, Q1), (l, Q2), (l3, Q3), (l4, Q4)])
    (h1 : Entails Q1 Q12) (h2 : Entails Q2 Q12) (h3 : Entails Q3 Q3')
    (h4 : Entails Q4 Q4') :
    NBranch entry cr :=
  br.weakenPosts [(l, Q12), (l3, Q3'), (l4, Q4')] (by
    intro ex hmem
    have hmem' : ex ∈ [(l, Q1), (l, Q2), (l3, Q3), (l4, Q4)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase | hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l, Q12), by simp, rfl, h1⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l, Q12), by simp, rfl, h2⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l3, Q3'), by simp, rfl, h3⟩
    · rcases hcase with ⟨rfl, rfl⟩
      exact ⟨(l4, Q4'), by simp, rfl, h4⟩)

/-- Continue the head exit of an N-way branch with a single-exit continuation
    over the same code requirement. -/
def seqHead {entry l l' : Word} {cr : CodeReq}
    {Q R : Assertion} {others : List (Word × Assertion)}
    (br : NBranch entry cr)
    (hexits : br.exits = (l, Q) :: others)
    (tail : Triple l l' cr R)
    (hlink : Entails Q tail.pre) :
    NBranch entry cr where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exits := (l', R) :: others
  sound := by
    have hbr : cpsNBranchWithin br.nSteps entry cr br.pre ((l, Q) :: others) := by
      simpa [hexits] using br.sound
    exact cpsNBranchWithin_extend_head hbr (tail.weakenPre hlink).sound

/-- Continue the head exit of an N-way branch with a single-exit continuation
    over disjoint tail code. -/
def seqHeadDisjoint {entry l l' : Word} {cr1 cr2 : CodeReq}
    {Q R : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = (l, Q) :: others)
    (tail : Triple l l' cr2 R)
    (hlink : Entails Q tail.pre) :
    NBranch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exits := (l', R) :: others
  sound := by
    have hbr : cpsNBranchWithin br.nSteps entry cr1 br.pre ((l, Q) :: others) := by
      simpa [hexits] using br.sound
    exact cpsNBranchWithin_extend_head_disjoint hd hbr (tail.weakenPre hlink).sound

/-- Continue the head exit of an N-way branch with another N-way continuation
    over the same code requirement. -/
def seqHeadNBranch {entry l : Word} {cr : CodeReq}
    {Q : Assertion} {others : List (Word × Assertion)}
    (br : NBranch entry cr)
    (hexits : br.exits = (l, Q) :: others)
    (tail : NBranch l cr)
    (hlink : Entails Q tail.pre) :
    NBranch entry cr where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exits := tail.exits ++ others
  sound := by
    have hbr : cpsNBranchWithin br.nSteps entry cr br.pre ((l, Q) :: others) := by
      simpa [hexits] using br.sound
    exact cpsNBranchWithin_extend_head_nbranch hbr (tail.weakenPre hlink).sound

/-- Continue the head exit of an N-way branch with another N-way continuation
    over disjoint tail code. -/
def seqHeadNBranchDisjoint {entry l : Word} {cr1 cr2 : CodeReq}
    {Q : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = (l, Q) :: others)
    (tail : NBranch l cr2)
    (hlink : Entails Q tail.pre) :
    NBranch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exits := tail.exits ++ others
  sound := by
    have hbr : cpsNBranchWithin br.nSteps entry cr1 br.pre ((l, Q) :: others) := by
      simpa [hexits] using br.sound
    exact cpsNBranchWithin_extend_head_nbranch_disjoint hd hbr (tail.weakenPre hlink).sound

/-- Continue an arbitrary exit of an N-way branch with another N-way continuation
    over disjoint tail code, preserving the exits before and after it. -/
def seqExitNBranchDisjoint {entry l : Word} {cr1 cr2 : CodeReq}
    {Q : Assertion} {preExits others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = preExits ++ (l, Q) :: others)
    (tail : NBranch l cr2)
    (hlink : Entails Q tail.pre) :
    NBranch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exits := (preExits ++ tail.exits) ++ others
  sound := by
    have hbr : cpsNBranchWithin br.nSteps entry cr1 br.pre (preExits ++ (l, Q) :: others) := by
      simpa [hexits] using br.sound
    exact cpsNBranchWithin_extend_prefixed_nbranch_disjoint hd hbr (tail.weakenPre hlink).sound

/-- Preserve the first exit of an N-way branch and continue the second exit with
    another N-way continuation over disjoint tail code. -/
def seqSecondNBranchDisjoint {entry head l : Word} {cr1 cr2 : CodeReq}
    {H Q : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = (head, H) :: (l, Q) :: others)
    (tail : NBranch l cr2)
    (hlink : Entails Q tail.pre) :
    NBranch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exits := (head, H) :: (tail.exits ++ others)
  sound := by
    have hbr : cpsNBranchWithin br.nSteps entry cr1 br.pre ((head, H) :: (l, Q) :: others) := by
      simpa [hexits] using br.sound
    exact cpsNBranchWithin_extend_second_nbranch_disjoint hd hbr (tail.weakenPre hlink).sound

/-- Continue the third exit of a four-way N-branch with another N-way
    continuation over disjoint tail code, preserving the other three exits. -/
def seqThirdNBranchDisjoint {entry l1 l2 l3 l4 : Word} {cr1 cr2 : CodeReq}
    {Q1 Q2 Q3 Q4 : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (tail : NBranch l3 cr2)
    (hlink : Entails Q3 tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqExitNBranchDisjoint
    (preExits := [(l1, Q1), (l2, Q2)]) (others := [(l4, Q4)])
    hd (by simpa using hexits) tail hlink

/-- Continue the third exit of a four-way N-branch with a single-exit
    continuation over disjoint tail code. -/
def seqThirdCertDisjoint {entry l1 l2 l3 l4 l3' : Word} {cr1 cr2 : CodeReq}
    {Q1 Q2 Q3 Q4 R : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (tail : Triple l3 l3' cr2 R)
    (hlink : Entails Q3 tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqThirdNBranchDisjoint hd hexits (NBranch.ofTriple tail) hlink

/-- Join all exits with a uniform continuation bound. -/
def join {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : NBranch entry cr) (tailBound : Nat)
    (hall : ∀ ex ∈ br.exits, cpsTripleWithin tailBound ex.1 exit_ cr ex.2 post) :
    Triple entry exit_ cr post where
  nSteps := br.nSteps + tailBound
  pre := br.pre
  sound := cpsNBranchWithin_merge br.sound hall

/-- Join exactly two known exits when the first exit is the only reachable one.
    The second exit is closed by a contradictory precondition, and the first
    exit is treated as the continuation post. -/
def join2ResolveFirst {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 : Word} {Q1 Q2 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hlink1 : Entails Q1 post)
    (hdead2 : ∀ h, Q2 h → False) :
    Triple entry l1 cr post :=
  br.join 0 (by
    intro ex hmem
    have hmem' : ex ∈ [(l1, Q1), (l2, Q2)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact (Triple.refl l1 cr hlink1).sound
    · rcases hcase with ⟨rfl, rfl⟩
      exact (Triple.unreachable l2 l1 cr (pre := Q2) (post := post) hdead2).sound)

/-- Join exactly two known exits when the second exit is the only reachable one.
    The first exit is closed by a contradictory precondition, and the second
    exit is treated as the continuation post. -/
def join2ResolveSecond {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 : Word} {Q1 Q2 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : Entails Q2 post) :
    Triple entry l2 cr post :=
  br.join 0 (by
    intro ex hmem
    have hmem' : ex ∈ [(l1, Q1), (l2, Q2)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact (Triple.unreachable l1 l2 cr (pre := Q1) (post := post) hdead1).sound
    · rcases hcase with ⟨rfl, rfl⟩
      exact (Triple.refl l2 cr hlink2).sound)

/-- Join exactly three known exits when the second exit is the only reachable one.
    The first and third exits are closed by contradictory preconditions, and the
    second exit is treated as the continuation post. -/
def join3ResolveSecond {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 : Word} {Q1 Q2 Q3 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : Entails Q2 post)
    (hdead3 : ∀ h, Q3 h → False) :
    Triple entry l2 cr post :=
  br.join 0 (by
    intro ex hmem
    have hmem' : ex ∈ [(l1, Q1), (l2, Q2), (l3, Q3)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact (Triple.unreachable l1 l2 cr (pre := Q1) (post := post) hdead1).sound
    · rcases hcase with ⟨rfl, rfl⟩
      exact (Triple.refl l2 cr hlink2).sound
    · rcases hcase with ⟨rfl, rfl⟩
      exact (Triple.unreachable l3 l2 cr (pre := Q3) (post := post) hdead3).sound)

/-- Join exactly four known exits with single-exit continuations. This is the
    fixed-arity frontend generated CFG proofs use after normalizing an N-branch
    exit list. -/
def join4 {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (tailBound : Nat)
    (t1 : Triple l1 exit_ cr post) (t2 : Triple l2 exit_ cr post)
    (t3 : Triple l3 exit_ cr post) (t4 : Triple l4 exit_ cr post)
    (hlink1 : Entails Q1 t1.pre) (hlink2 : Entails Q2 t2.pre)
    (hlink3 : Entails Q3 t3.pre) (hlink4 : Entails Q4 t4.pre)
    (h1 : t1.nSteps ≤ tailBound) (h2 : t2.nSteps ≤ tailBound)
    (h3 : t3.nSteps ≤ tailBound) (h4 : t4.nSteps ≤ tailBound) :
    Triple entry exit_ cr post :=
  br.join tailBound (by
    intro ex hmem
    have hmem' : ex ∈ [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)] := by
      simpa [hexits] using hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hcase | hcase | hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      exact ((t1.weakenPre hlink1).monoSteps h1).sound
    · rcases hcase with ⟨rfl, rfl⟩
      exact ((t2.weakenPre hlink2).monoSteps h2).sound
    · rcases hcase with ⟨rfl, rfl⟩
      exact ((t3.weakenPre hlink3).monoSteps h3).sound
    · rcases hcase with ⟨rfl, rfl⟩
      exact ((t4.weakenPre hlink4).monoSteps h4).sound)

/-- Join exactly four known exits, computing the common continuation bound from
    the supplied continuation certificates. -/
def join4Max {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (t1 : Triple l1 exit_ cr post) (t2 : Triple l2 exit_ cr post)
    (t3 : Triple l3 exit_ cr post) (t4 : Triple l4 exit_ cr post)
    (hlink1 : Entails Q1 t1.pre) (hlink2 : Entails Q2 t2.pre)
    (hlink3 : Entails Q3 t3.pre) (hlink4 : Entails Q4 t4.pre) :
    Triple entry exit_ cr post :=
  br.join4 hexits (Nat.max (Nat.max t1.nSteps t2.nSteps) (Nat.max t3.nSteps t4.nSteps))
    t1 t2 t3 t4 hlink1 hlink2 hlink3 hlink4
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- Join exactly four known exits when the third exit is the only reachable one.
    The other exits are closed by contradictory preconditions, and the third
    exit is treated as the continuation post. -/
def join4ResolveThird {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (hdead1 : ∀ h, Q1 h → False)
    (hdead2 : ∀ h, Q2 h → False)
    (hlink3 : Entails Q3 post)
    (hdead4 : ∀ h, Q4 h → False) :
    Triple entry l3 cr post :=
  br.join4 hexits 0
    (Triple.unreachable l1 l3 cr (pre := Q1) (post := post) hdead1)
    (Triple.unreachable l2 l3 cr (pre := Q2) (post := post) hdead2)
    (Triple.refl l3 cr hlink3)
    (Triple.unreachable l4 l3 cr (pre := Q4) (post := post) hdead4)
    (Entails.refl _) (Entails.refl _) (Entails.refl _) (Entails.refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

end NBranch

namespace Branch

/-- Continue the taken exit of a branch and expose the result as a multi-exit
    branch. This is the endpoint shape for generated decoders: close one failure
    arm while keeping the fall-through arm open for later CFG construction. -/
def seqTakenAsNBranchDisjoint {entry target : Word} {cr1 cr2 : CodeReq}
    {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Triple br.exit_t target cr2 post)
    (hlink : Entails br.post_t tail.pre) :
    NBranch entry (cr1.union cr2) :=
  NBranch.ofBranch (br.seqTakenDisjoint hd tail hlink)

/-- Continue the not-taken exit of a branch with a multi-exit CFG over disjoint
    code. The taken exit is preserved as the first open exit, followed by the
    tail's exits. This is the standard shape for generated decoders that peel
    off one failure branch and keep walking the fall-through CFG. -/
def seqNotTakenNBranchDisjoint {entry : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : NBranch br.exit_f cr2)
    (hlink : Entails br.post_f tail.pre) :
    NBranch entry (cr1.union cr2) where
  nSteps := br.nSteps + tail.nSteps
  pre := br.pre
  exits := (br.exit_t, br.post_t) :: tail.exits
  sound := cpsBranchWithin_cons_cpsNBranchWithin_with_perm hd hlink br.sound tail.sound

end Branch

end WP
end EvmAsm.Rv64
