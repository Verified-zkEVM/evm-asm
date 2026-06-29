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

/-- Join a two-way branch with a continuation for each exit. -/
def branch {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (br : Branch entry cr)
    (taken : Cert br.exit_t exit_ cr post)
    (notTaken : Cert br.exit_f exit_ cr post)
    (ht : Entails br.post_t taken.pre)
    (hf : Entails br.post_f notTaken.pre) :
    Cert entry exit_ cr post :=
  br.join taken notTaken ht hf

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
