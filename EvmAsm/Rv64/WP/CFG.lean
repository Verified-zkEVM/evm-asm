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

/-- A leaf block whose CPS spec is already available. -/
def block {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre post post' : Assertion}
    (hpost : Entails post post')
    (h : cpsTripleWithin nSteps entry exit_ cr pre post) :
    Cert entry exit_ cr post' :=
  Triple.ofSpec hpost h

/-- Frame a single-exit CFG certificate with a PC-free assertion. -/
def frameR {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : Cert entry exit_ cr post) (F : Assertion) (hF : F.pcFree) :
    Cert entry exit_ cr (post ** F) :=
  cfg.frameR F hF

/-- Sequential composition with one shared persistent code requirement. -/
def seq {nSteps : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost post : Assertion}
    (head : cpsTripleWithin nSteps entry mid cr pre midPost)
    (tail : Cert mid exit_ cr post)
    (hlink : Entails midPost tail.pre) :
    Cert entry exit_ cr post :=
  Triple.seq head tail hlink

/-- Sequential composition for disjoint code requirements. -/
def seqDisjoint {nSteps : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nSteps entry mid cr1 pre midPost)
    (tail : Cert mid exit_ cr2 post)
    (hlink : Entails midPost tail.pre) :
    Cert entry exit_ (cr1.union cr2) post :=
  Triple.seqDisjoint hd head tail hlink

/-- Sequential composition where both adjacent regions are already available as
    CPS triples over one shared persistent code requirement. -/
def seqBlock {nHead nTail : Nat} {entry mid exit_ : Word} {cr : CodeReq}
    {pre midPost tailPre post : Assertion}
    (head : cpsTripleWithin nHead entry mid cr pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr tailPre post)
    (hlink : Entails midPost tailPre) :
    Cert entry exit_ cr post :=
  seq head (block (Entails.refl _) tail) hlink

/-- Sequential composition where both adjacent regions are already available as
    CPS triples over disjoint code requirements. -/
def seqBlockDisjoint {nHead nTail : Nat} {entry mid exit_ : Word} {cr1 cr2 : CodeReq}
    {pre midPost tailPre post : Assertion}
    (hd : cr1.Disjoint cr2)
    (head : cpsTripleWithin nHead entry mid cr1 pre midPost)
    (tail : cpsTripleWithin nTail mid exit_ cr2 tailPre post)
    (hlink : Entails midPost tailPre) :
    Cert entry exit_ (cr1.union cr2) post :=
  seqDisjoint hd head (block (Entails.refl _) tail) hlink

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

/-- Join an N-way branch with a uniform continuation bound. -/
def nbranch {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : NBranch entry cr) (tailBound : Nat)
    (hall : ∀ ex ∈ br.exits, cpsTripleWithin tailBound ex.1 exit_ cr ex.2 post) :
    Cert entry exit_ cr post :=
  br.join tailBound hall

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
