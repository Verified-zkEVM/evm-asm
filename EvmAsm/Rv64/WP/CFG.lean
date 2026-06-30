/-
  EvmAsm.Rv64.WP.CFG

  User-facing constructors for structured control-flow certificates.  The
  certificate itself is a `WP.Triple`; this file gives stable names for the
  CFG operations that a proof-producing agent should emit.
-/

import EvmAsm.Rv64.WP.Loop

namespace EvmAsm.Rv64
namespace WP
namespace CFG

/-- A structured single-exit CFG certificate. -/
abbrev Cert (entry exit_ : Word) (cr : CodeReq) (post : Assertion) :=
  Triple entry exit_ cr post

/-- The precondition computed by a CFG certificate. -/
def pre {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) : Assertion :=
  cfg.pre

/-- Empty CFG at a join point. -/
def exit (addr : Word) (cr : CodeReq) {pre post : Assertion}
    (h : Entails pre post) : Cert addr addr cr post :=
  Triple.refl addr cr h

/-- Empty CFG at a join point when the precondition already is the
    postcondition. -/
def exitRefl (addr : Word) (cr : CodeReq) (post : Assertion) :
    Cert addr addr cr post :=
  exit addr cr (Entails.refl post)

/-- A CFG certificate for an unreachable precondition. -/
def unreachable (entry exit_ : Word) (cr : CodeReq) {pre post : Assertion}
    (hpre : ∀ h, pre h → False) : Cert entry exit_ cr post :=
  Triple.unreachable entry exit_ cr hpre

/-- A leaf block whose CPS spec is already available. -/
def block {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post post' : Assertion}
    (hpost : Entails post post')
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    Cert entry exit_ cr post' :=
  Triple.ofSpec hpost h

/-- A leaf block whose CPS postcondition already matches the
    certificate postcondition. -/
def leaf {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    Cert entry exit_ cr post :=
  block (Entails.refl _) h

/-- Frame a single-exit CFG certificate with a PC-free assertion. -/
def frameR {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) (F : Assertion) (hF : F.pcFree) :
    Cert entry exit_ cr (post ** F) :=
  cfg.frameR F hF

/-- Weaken the computed precondition of a single-exit CFG certificate. -/
def weakenPre {entry exit_ : Word} {cr : CodeReq} {post pre' : Assertion}
    (cfg : Cert entry exit_ cr post) (hpre : Entails pre' cfg.pre) :
    Cert entry exit_ cr post :=
  cfg.weakenPre hpre

/-- Weaken the continuation postcondition of a single-exit CFG certificate. -/
def weakenPost {entry exit_ : Word} {cr : CodeReq} {post post' : Assertion}
    (cfg : Cert entry exit_ cr post) (hpost : Entails post post') :
    Cert entry exit_ cr post' :=
  cfg.weakenPost hpost

/-- Increase the step budget of a single-exit CFG certificate. -/
def monoSteps {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) {nSteps' : Nat} (hle : cfg.nSteps ≤ nSteps') :
    Cert entry exit_ cr post :=
  cfg.monoSteps hle

/-- Extend a single-exit CFG certificate to a larger persistent code requirement. -/
def extendCode {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    Cert entry exit_ cr' post :=
  cfg.extendCode hmono

/-- Rewrite the entry address of a single-exit CFG certificate. -/
def changeEntry {entry entry' exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) (hentry : entry' = entry) :
    Cert entry' exit_ cr post :=
  cfg.changeEntry hentry

/-- Rewrite the exit address of a single-exit CFG certificate. -/
def changeExit {entry exit_ exit_' : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) (hexit : exit_ = exit_') :
    Cert entry exit_' cr post :=
  cfg.changeExit hexit

/-- `exitRefl` exposes exactly the supplied postcondition as its precondition. -/
theorem exitRefl_pre (addr : Word) (cr : CodeReq) (post : Assertion) :
    (exitRefl addr cr post).pre = post :=
  rfl

/-- `block` exposes exactly the source precondition of the CPS proof. -/
theorem block_pre {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post post' : Assertion}
    (hpost : Entails post post')
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    (block hpost h).pre = pre :=
  rfl

/-- `leaf` exposes exactly the source precondition of the CPS proof. -/
theorem leaf_pre {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    (leaf h).pre = pre :=
  rfl

/-- `frameR` appends exactly the supplied frame to the generated precondition. -/
theorem frameR_pre {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) (F : Assertion) (hF : F.pcFree) :
    (frameR cfg F hF).pre = (cfg.pre ** F) :=
  rfl

/-- `weakenPre` exposes exactly the supplied precondition. -/
theorem weakenPre_pre {entry exit_ : Word} {cr : CodeReq} {post pre' : Assertion}
    (cfg : Cert entry exit_ cr post) (hpre : Entails pre' cfg.pre) :
    (weakenPre cfg hpre).pre = pre' :=
  rfl

/-- `weakenPost` preserves the computed precondition. -/
theorem weakenPost_pre {entry exit_ : Word} {cr : CodeReq} {post post' : Assertion}
    (cfg : Cert entry exit_ cr post) (hpost : Entails post post') :
    (weakenPost cfg hpost).pre = cfg.pre :=
  rfl

/-- `monoSteps` preserves the computed precondition. -/
theorem monoSteps_pre {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) {nSteps' : Nat} (hle : cfg.nSteps ≤ nSteps') :
    (monoSteps cfg hle).pre = cfg.pre :=
  rfl

/-- `extendCode` preserves the computed precondition. -/
theorem extendCode_pre {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    (extendCode cfg hmono).pre = cfg.pre :=
  rfl

/-- `changeEntry` preserves the computed precondition. -/
theorem changeEntry_pre {entry entry' exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) (hentry : entry' = entry) :
    (changeEntry cfg hentry).pre = cfg.pre :=
  rfl

/-- `changeExit` preserves the computed precondition. -/
theorem changeExit_pre {entry exit_ exit_' : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) (hexit : exit_ = exit_') :
    (changeExit cfg hexit).pre = cfg.pre :=
  rfl

example {entry exit_ : Word} {cr : CodeReq} {post post' : Assertion}
    (cfg : Cert entry exit_ cr post) (hpost : Entails post post') :
    Cert entry exit_ cr post' :=
  weakenPost cfg hpost

example {entry exit_ : Word} {cr cr' : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    (extendCode cfg hmono).pre = cfg.pre :=
  extendCode_pre cfg hmono

/-- Sequential composition with one shared persistent code requirement. -/
def seq {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nSteps entry mid cr pre midPost)
    (tail : Cert mid exit_ cr post)
    (hlink : Entails midPost tail.pre) :
    Cert entry exit_ cr post :=
  Triple.seq head tail hlink

/-- Sequential composition when the head postcondition is exactly the
    tail precondition. -/
def seqExact {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre post : Assertion}
    (tail : Cert mid exit_ cr post)
    (head : cpsTripleWithin nSteps entry mid cr pre tail.pre) :
    Cert entry exit_ cr post :=
  seq head tail (Entails.refl _)

/-- Sequential composition for disjoint code requirements. -/
def seqDisjoint {nSteps : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nSteps entry mid cr1 pre midPost)
    (tail : Cert mid exit_ cr2 post)
    (hlink : Entails midPost tail.pre) :
    Cert entry exit_ (cr1.union cr2) post :=
  Triple.seqDisjoint hd head tail hlink

/-- Disjoint-code sequencing when the head postcondition is exactly the
    tail precondition. -/
def seqDisjointExact {nSteps : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (tail : Cert mid exit_ cr2 post)
    (head : cpsTripleWithin nSteps entry mid cr1 pre tail.pre) :
    Cert entry exit_ (cr1.union cr2) post :=
  seqDisjoint hd head tail (Entails.refl _)

/-- Sequential composition where both adjacent regions are already available as
    CPS triples over one shared persistent code requirement. -/
def seqBlock {nHead nTail : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost tailPre post : Assertion}
    (head : cpsTripleWithin nHead entry mid cr pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr tailPre post)
    (hlink : Entails midPost tailPre) :
    Cert entry exit_ cr post :=
  seq head (leaf tail) hlink

/-- Same-code block sequencing when the first postcondition exactly
    matches the second precondition. -/
def seqBlockExact {nHead nTail : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nHead entry mid cr pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr midPost post) :
    Cert entry exit_ cr post :=
  seqBlock head tail (Entails.refl _)

/-- Sequential composition where both adjacent regions are already available as
    CPS triples over disjoint code requirements. -/
def seqBlockDisjoint {nHead nTail : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost tailPre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr2 tailPre post)
    (hlink : Entails midPost tailPre) :
    Cert entry exit_ (cr1.union cr2) post :=
  seqDisjoint hd head (leaf tail) hlink

/-- Disjoint-code block sequencing when the first postcondition exactly
    matches the second precondition. -/
def seqBlockDisjointExact {nHead nTail : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr2 midPost post) :
    Cert entry exit_ (cr1.union cr2) post :=
  seqBlockDisjoint hd head tail (Entails.refl _)

/-- Sequential composition from a CPS block into an N-way CFG over disjoint code. -/
def seqBlockNBranchDisjoint {nHead : Nat} {entry mid : Word} {cr1 cr2 : CodeReq}
    {pre midPost : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost)
    (tail : NBranch mid cr2)
    (hlink : Entails midPost tail.pre) :
    NBranch entry (cr1.union cr2) where
  nSteps := nHead + tail.nSteps
  pre := pre
  exits := tail.exits
  sound := cpsTripleWithin_seq_cpsNBranchWithin hd
    (cpsTripleWithin_weaken (fun _ hp => hp) hlink head) tail.sound

/-- Frame both exits of a branch with a PC-free assertion. -/
def branchFrameR {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) (F : Assertion) (hF : F.pcFree) : Branch entry cr :=
  br.frameR F hF

/-- Join a two-way branch with a continuation for each exit. -/
def branch {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : Branch entry cr)
    (taken : Cert br.exit_t exit_ cr post)
    (notTaken : Cert br.exit_f exit_ cr post)
    (ht : Entails br.post_t taken.pre)
    (hf : Entails br.post_f notTaken.pre) :
    Cert entry exit_ cr post :=
  br.join taken notTaken ht hf

/-- Continue only the taken exit of a branch with disjoint code, leaving the
    not-taken exit open. -/
def branchSeqTakenDisjoint {entry target : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Cert br.exit_t target cr2 post)
    (hlink : Entails br.post_t tail.pre) :
    Branch entry (cr1.union cr2) :=
  br.seqTakenDisjoint hd tail hlink

/-- Continue only the taken exit of a branch with a CPS leaf over disjoint code. -/
def branchSeqTakenBlockDisjoint {nTail : Nat} {entry target : Word}
    {cr1 cr2 : CodeReq} {tailPre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_t target cr2 tailPre post)
    (hlink : Entails br.post_t tailPre) :
    Branch entry (cr1.union cr2) :=
  branchSeqTakenDisjoint hd br (block (Entails.refl _) tail) hlink

/-- Continue the taken exit with another branch and merge both failure exits into
    one failure post. This is the WP form of a decoder parse followed by a
    validation branch. -/
def branchSeqTakenBranchConvergeDisjoint {entry : Word} {cr1 cr2 : CodeReq}
    {failPost : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Branch br.exit_t cr2)
    (hfail : tail.exit_t = br.exit_f)
    (hlink : Entails br.post_t tail.pre)
    (hf1 : Entails br.post_f failPost)
    (hf2 : Entails tail.post_t failPost) :
    Branch entry (cr1.union cr2) :=
  br.seqTakenBranchConvergeDisjoint hd tail hfail hlink hf1 hf2

/-- Continue only the not-taken exit of a branch with disjoint code, leaving the
    taken exit open. -/
def branchSeqNotTakenDisjoint {entry target : Word} {cr1 cr2 : CodeReq} {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Cert br.exit_f target cr2 post)
    (hlink : Entails br.post_f tail.pre) :
    Branch entry (cr1.union cr2) :=
  br.seqNotTakenDisjoint hd tail hlink

/-- Continue only the not-taken exit of a branch with a CPS leaf over disjoint code. -/
def branchSeqNotTakenBlockDisjoint {nTail : Nat} {entry target : Word}
    {cr1 cr2 : CodeReq} {tailPre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_f target cr2 tailPre post)
    (hlink : Entails br.post_f tailPre) :
    Branch entry (cr1.union cr2) :=
  branchSeqNotTakenDisjoint hd br (block (Entails.refl _) tail) hlink

/-- Continue only the taken exit of a branch with disjoint code and expose the
    resulting two exits as an N-way branch. -/
def branchSeqTakenNBranchDisjoint {entry target : Word} {cr1 cr2 : CodeReq}
    {post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : Cert br.exit_t target cr2 post)
    (hlink : Entails br.post_t tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqTakenAsNBranchDisjoint hd tail hlink

/-- Continue only the taken exit of a branch with a CPS leaf over disjoint code
    and expose the resulting two exits as an N-way branch. -/
def branchSeqTakenBlockNBranchDisjoint {nTail : Nat} {entry target : Word}
    {cr1 cr2 : CodeReq} {tailPre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : cpsTripleWithin nTail br.exit_t target cr2 tailPre post)
    (hlink : Entails br.post_t tailPre) :
    NBranch entry (cr1.union cr2) :=
  branchSeqTakenNBranchDisjoint hd br (block (Entails.refl _) tail) hlink

/-- View a two-way branch as an N-way branch. -/
def nbranchOfBranch {entry : Word} {cr : CodeReq} (br : Branch entry cr) :
    NBranch entry cr :=
  NBranch.ofBranch br

/-- Frame every exit of an N-way CFG with a PC-free assertion. -/
def nbranchFrameR {entry : Word} {cr : CodeReq}
    (br : NBranch entry cr) (F : Assertion) (hF : F.pcFree) :
    NBranch entry cr :=
  br.frameR F hF

/-- Weaken the exit postconditions of an N-way CFG. -/
def nbranchWeakenPosts {entry : Word} {cr : CodeReq}
    (br : NBranch entry cr) (exits' : List (Word × Assertion))
    (hmap : ∀ ex ∈ br.exits, ∃ ex' ∈ exits',
      ex'.1 = ex.1 ∧ Entails ex.2 ex'.2) :
    NBranch entry cr :=
  br.weakenPosts exits' hmap

/-- Weaken the head exit of an N-way CFG, preserving the tail exits. -/
def nbranchWeakenHeadPost {entry : Word} {cr : CodeReq}
    {l : Word} {headPost headPost' : Assertion} {others : List (Word × Assertion)}
    (br : NBranch entry cr)
    (hexits : br.exits = (l, headPost) :: others)
    (hhead : Entails headPost headPost') :
    NBranch entry cr :=
  br.weakenHeadPost hexits hhead

/-- Weaken the head exit and remap the tail exits of an N-way CFG. -/
def nbranchWeakenPostsCons {entry : Word} {cr : CodeReq}
    {l : Word} {headPost headPost' : Assertion}
    {others others' : List (Word × Assertion)}
    (br : NBranch entry cr)
    (hexits : br.exits = (l, headPost) :: others)
    (hhead : Entails headPost headPost')
    (htail : ∀ ex ∈ others, ∃ ex' ∈ others',
      ex'.1 = ex.1 ∧ Entails ex.2 ex'.2) :
    NBranch entry cr :=
  br.weakenPostsCons hexits hhead htail

/-- Weaken exactly two known exits of an N-way CFG. -/
def nbranchWeakenPosts2 {entry : Word} {cr : CodeReq}
    {l1 l2 : Word} {Q1 Q2 Q1' Q2' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') :
    NBranch entry cr :=
  br.weakenPosts2 hexits h1 h2

/-- Weaken exactly three known exits of an N-way CFG. -/
def nbranchWeakenPosts3 {entry : Word} {cr : CodeReq}
    {l1 l2 l3 : Word} {Q1 Q2 Q3 Q1' Q2' Q3' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') (h3 : Entails Q3 Q3') :
    NBranch entry cr :=
  br.weakenPosts3 hexits h1 h2 h3

/-- Weaken exactly four known exits of an N-way CFG. -/
def nbranchWeakenPosts4 {entry : Word} {cr : CodeReq}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 Q1' Q2' Q3' Q4' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') (h3 : Entails Q3 Q3')
    (h4 : Entails Q4 Q4') :
    NBranch entry cr :=
  br.weakenPosts4 hexits h1 h2 h3 h4

/-- Weaken four exits into three by mapping the first two same-target exits to
    one replacement post. -/
def nbranchWeakenPosts4MergeFirstTwo {entry : Word} {cr : CodeReq}
    {l l3 l4 : Word} {Q1 Q2 Q3 Q4 Q12 Q3' Q4' : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l, Q1), (l, Q2), (l3, Q3), (l4, Q4)])
    (h1 : Entails Q1 Q12) (h2 : Entails Q2 Q12) (h3 : Entails Q3 Q3')
    (h4 : Entails Q4 Q4') :
    NBranch entry cr :=
  br.weakenPosts4MergeFirstTwo hexits h1 h2 h3 h4

/-- Continue a branch's not-taken exit with an N-way CFG over disjoint code,
    preserving the taken exit as the first open exit. -/
def branchSeqNotTakenNBranchDisjoint {entry : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    (br : Branch entry cr1)
    (tail : NBranch br.exit_f cr2)
    (hlink : Entails br.post_f tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqNotTakenNBranchDisjoint hd tail hlink

/-- Continue the head exit of an N-way CFG over the same code requirement. -/
def nbranchSeqHead {entry l l' : Word} {cr : CodeReq}
    {headPost post : Assertion} {others : List (Word × Assertion)}
    (br : NBranch entry cr)
    (hexits : br.exits = (l, headPost) :: others)
    (tail : Cert l l' cr post)
    (hlink : Entails headPost tail.pre) :
    NBranch entry cr :=
  br.seqHead hexits tail hlink

/-- Continue the head exit of an N-way CFG with a CPS leaf over the same code
    requirement. -/
def nbranchSeqHeadBlock {nTail : Nat} {entry l l' : Word} {cr : CodeReq}
    {headPost tailPre post : Assertion} {others : List (Word × Assertion)}
    (br : NBranch entry cr)
    (hexits : br.exits = (l, headPost) :: others)
    (tail : cpsTripleWithin nTail l l' cr tailPre post)
    (hlink : Entails headPost tailPre) :
    NBranch entry cr :=
  nbranchSeqHead br hexits (block (Entails.refl _) tail) hlink

/-- Continue the head exit of an N-way CFG over disjoint tail code. -/
def nbranchSeqHeadDisjoint {entry l l' : Word} {cr1 cr2 : CodeReq}
    {headPost post : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = (l, headPost) :: others)
    (tail : Cert l l' cr2 post)
    (hlink : Entails headPost tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqHeadDisjoint hd hexits tail hlink

/-- Continue the head exit of an N-way CFG with a CPS leaf over disjoint tail code. -/
def nbranchSeqHeadBlockDisjoint {nTail : Nat} {entry l l' : Word}
    {cr1 cr2 : CodeReq} {headPost tailPre post : Assertion}
    {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = (l, headPost) :: others)
    (tail : cpsTripleWithin nTail l l' cr2 tailPre post)
    (hlink : Entails headPost tailPre) :
    NBranch entry (cr1.union cr2) :=
  nbranchSeqHeadDisjoint hd br hexits (block (Entails.refl _) tail) hlink

/-- Continue the head exit of an N-way CFG with another N-way CFG over the same
    code requirement. -/
def nbranchSeqHeadNBranch {entry l : Word} {cr : CodeReq}
    {headPost : Assertion} {others : List (Word × Assertion)}
    (br : NBranch entry cr)
    (hexits : br.exits = (l, headPost) :: others)
    (tail : NBranch l cr)
    (hlink : Entails headPost tail.pre) :
    NBranch entry cr :=
  br.seqHeadNBranch hexits tail hlink

/-- Continue the head exit of an N-way CFG with another N-way CFG over disjoint
    tail code. -/
def nbranchSeqHeadNBranchDisjoint {entry l : Word} {cr1 cr2 : CodeReq}
    {headPost : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = (l, headPost) :: others)
    (tail : NBranch l cr2)
    (hlink : Entails headPost tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqHeadNBranchDisjoint hd hexits tail hlink

/-- Continue an arbitrary exit of an N-way CFG with another N-way CFG over disjoint
    tail code, preserving the exits before and after it. -/
def nbranchSeqExitNBranchDisjoint {entry l : Word} {cr1 cr2 : CodeReq}
    {exitPost : Assertion} {preExits others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = preExits ++ (l, exitPost) :: others)
    (tail : NBranch l cr2)
    (hlink : Entails exitPost tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqExitNBranchDisjoint hd hexits tail hlink

/-- Continue an arbitrary exit of an N-way CFG with a single-exit certificate
    over disjoint tail code, preserving the exits before and after it. -/
def nbranchSeqExitCertDisjoint {entry l l' : Word} {cr1 cr2 : CodeReq}
    {exitPost post : Assertion} {preExits others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = preExits ++ (l, exitPost) :: others)
    (tail : Cert l l' cr2 post)
    (hlink : Entails exitPost tail.pre) :
    NBranch entry (cr1.union cr2) :=
  nbranchSeqExitNBranchDisjoint hd br hexits (NBranch.ofTriple tail) hlink

/-- Preserve the first exit and continue the second exit with another N-way CFG
    over disjoint tail code. -/
def nbranchSeqSecondNBranchDisjoint {entry head l : Word} {cr1 cr2 : CodeReq}
    {headPost secondPost : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = (head, headPost) :: (l, secondPost) :: others)
    (tail : NBranch l cr2)
    (hlink : Entails secondPost tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqSecondNBranchDisjoint hd hexits tail hlink

/-- Continue the third exit of a four-way N-branch with another N-way CFG over
    disjoint tail code. -/
def nbranchSeqThirdNBranchDisjoint {entry l1 l2 l3 l4 : Word} {cr1 cr2 : CodeReq}
    {Q1 Q2 Q3 Q4 : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (tail : NBranch l3 cr2)
    (hlink : Entails Q3 tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqThirdNBranchDisjoint hd hexits tail hlink

/-- Continue the third exit of a four-way N-branch with a single-exit CFG over
    disjoint tail code. -/
def nbranchSeqThirdCertDisjoint {entry l1 l2 l3 l4 l3' : Word} {cr1 cr2 : CodeReq}
    {Q1 Q2 Q3 Q4 R : Assertion}
    (hd : cr1.Disjoint cr2)
    (br : NBranch entry cr1)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (tail : Cert l3 l3' cr2 R)
    (hlink : Entails Q3 tail.pre) :
    NBranch entry (cr1.union cr2) :=
  br.seqThirdCertDisjoint hd hexits tail hlink

/-- Join an N-way branch with a uniform continuation bound. -/
def nbranch {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : NBranch entry cr) (tailBound : Nat)
    (hall : ∀ ex ∈ br.exits, cpsTripleWithin tailBound ex.1 exit_ cr ex.2 post) :
    Cert entry exit_ cr post :=
  br.join tailBound hall

/-- Join exactly two known exits when the first exit is the only reachable one. -/
def nbranchJoin2ResolveFirst {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 : Word} {Q1 Q2 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hlink1 : Entails Q1 post)
    (hdead2 : ∀ h, Q2 h → False) :
    Cert entry l1 cr post :=
  br.join2ResolveFirst hexits hlink1 hdead2

/-- Join exactly two known exits when the second exit is the only reachable one. -/
def nbranchJoin2ResolveSecond {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 : Word} {Q1 Q2 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : Entails Q2 post) :
    Cert entry l2 cr post :=
  br.join2ResolveSecond hexits hdead1 hlink2

/-- Join exactly three known exits when the second exit is the only reachable one. -/
def nbranchJoin3ResolveSecond {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 : Word} {Q1 Q2 Q3 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : Entails Q2 post)
    (hdead3 : ∀ h, Q3 h → False) :
    Cert entry l2 cr post :=
  br.join3ResolveSecond hexits hdead1 hlink2 hdead3

/-- Join exactly four known exits with single-exit continuations. -/
def nbranchJoin4 {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (tailBound : Nat)
    (t1 : Cert l1 exit_ cr post) (t2 : Cert l2 exit_ cr post)
    (t3 : Cert l3 exit_ cr post) (t4 : Cert l4 exit_ cr post)
    (hlink1 : Entails Q1 t1.pre) (hlink2 : Entails Q2 t2.pre)
    (hlink3 : Entails Q3 t3.pre) (hlink4 : Entails Q4 t4.pre)
    (h1 : t1.nSteps ≤ tailBound) (h2 : t2.nSteps ≤ tailBound)
    (h3 : t3.nSteps ≤ tailBound) (h4 : t4.nSteps ≤ tailBound) :
    Cert entry exit_ cr post :=
  br.join4 hexits tailBound t1 t2 t3 t4 hlink1 hlink2 hlink3 hlink4 h1 h2 h3 h4

/-- Join exactly four known exits, computing the common continuation bound from
    the supplied continuation certificates. -/
def nbranchJoin4Max {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (t1 : Cert l1 exit_ cr post) (t2 : Cert l2 exit_ cr post)
    (t3 : Cert l3 exit_ cr post) (t4 : Cert l4 exit_ cr post)
    (hlink1 : Entails Q1 t1.pre) (hlink2 : Entails Q2 t2.pre)
    (hlink3 : Entails Q3 t3.pre) (hlink4 : Entails Q4 t4.pre) :
    Cert entry exit_ cr post :=
  br.join4Max hexits t1 t2 t3 t4 hlink1 hlink2 hlink3 hlink4

/-- Join exactly four known exits when the third exit is the only reachable one. -/
def nbranchJoin4ResolveThird {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 : Assertion}
    (br : NBranch entry cr)
    (hexits : br.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (hdead1 : ∀ h, Q1 h → False)
    (hdead2 : ∀ h, Q2 h → False)
    (hlink3 : Entails Q3 post)
    (hdead4 : ∀ h, Q4 h → False) :
    Cert entry l3 cr post :=
  br.join4ResolveThird hexits hdead1 hdead2 hlink3 hdead4

/-- Package an indexed invariant/variant loop as a CFG certificate. -/
def loopNat {nHeader nBody nExit : Nat}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {inv bodyPre exitPost : Nat → Assertion} {post : Assertion}
    {fuel : Nat}
    (hcert : loopNatCert nHeader nBody nExit header bodyEntry exit_ cr
      inv bodyPre exitPost post 0 fuel) :
    Cert header exit_ cr post :=
  Triple.ofLoopNatCert hcert

end CFG
end WP
end EvmAsm.Rv64
