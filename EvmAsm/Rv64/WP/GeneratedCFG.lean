/-
  EvmAsm.Rv64.WP.GeneratedCFG

  Typed shape helpers for generated control-flow proofs. The generator supplies
  labels and local postconditions as an explicit exit list; these helpers keep
  that list attached to the underlying WP.NBranch certificate while composing
  or joining exits.
-/

import EvmAsm.Rv64.WP.CFG

namespace EvmAsm.Rv64
namespace WP
namespace GeneratedCFG

/-- One generated CFG exit as supplied by a control-flow description.  This is
    intentionally just a label plus the local postcondition at that label; it
    does not carry decoded runtime result values. -/
structure ExitSpec where
  label : Word
  post : Assertion

/-- A generated two-way branch summary.  `taken` and `fallthrough` are the
    expected successors and local posts; runtime success/failure information
    belongs in those posts, not in this shape. -/
structure Branch2Spec where
  taken : ExitSpec
  fallthrough : ExitSpec

/-- A generated bounded natural-number loop summary.

    The generated shape records labels, step budgets, fuel, and the assertion
    names used by the loop rule.  Runtime success/failure data still belongs in
    `post`, `exitPost`, or the invariant assertions, not in the shape fields as
    decoded values. -/
structure LoopNatSpec where
  header : Word
  bodyEntry : Word
  exitLabel : Word
  nHeader : Nat
  nBody : Nat
  nExit : Nat
  fuel : Nat
  inv : Nat → Assertion
  bodyPre : Nat → Assertion
  exitPost : Nat → Assertion
  post : Assertion

namespace Branch2Spec

/-- Exit list represented by a generated two-way branch summary. -/
def exits (spec : Branch2Spec) : List (Word × Assertion) :=
  [(spec.taken.label, spec.taken.post),
    (spec.fallthrough.label, spec.fallthrough.post)]

/-- The kernel branch agrees with the generated two-exit shape. -/
def Matches {entry : Word} {cr : CodeReq}
    (spec : Branch2Spec) (br : Branch entry cr) : Prop :=
  br.exit_t = spec.taken.label ∧ br.post_t = spec.taken.post ∧
    br.exit_f = spec.fallthrough.label ∧ br.post_f = spec.fallthrough.post

theorem exits_eq_of_matches {entry : Word} {cr : CodeReq}
    {spec : Branch2Spec} {br : Branch entry cr}
    (hshape : spec.Matches br) :
    [(br.exit_t, br.post_t), (br.exit_f, br.post_f)] = spec.exits := by
  rcases hshape with ⟨h_taken_label, h_taken_post, h_fall_label, h_fall_post⟩
  simp [exits, h_taken_label, h_taken_post, h_fall_label, h_fall_post]

end Branch2Spec

/-- A generated multi-exit CFG with the expected exit list kept as data.

    `cfg` is the kernel-checked certificate. `exits` is the generated
    control-flow summary: labels paired with local postconditions. `exits_eq`
    ties the two together, so later skeleton steps can refer to the generated
    list instead of unfolding `cfg.exits` by hand. -/
structure OpenCFG (entry : Word) (cr : CodeReq) where
  cfg : NBranch entry cr
  exits : List (Word × Assertion)
  exits_eq : cfg.exits = exits

namespace OpenCFG

/-- The WP-computed precondition of a generated CFG. -/
def pre {entry : Word} {cr : CodeReq} (g : OpenCFG entry cr) : Assertion :=
  g.cfg.pre

/-- The step bound of the underlying N-way certificate. -/
def nSteps {entry : Word} {cr : CodeReq} (g : OpenCFG entry cr) : Nat :=
  g.cfg.nSteps

/-- The low-level soundness theorem for the underlying N-way certificate. -/
def sound {entry : Word} {cr : CodeReq} (g : OpenCFG entry cr) :
    cpsNBranchWithin g.nSteps entry cr g.pre g.exits := by
  simpa [nSteps, pre, g.exits_eq] using g.cfg.sound

/-- Labels exposed by a generated CFG. -/
def labels {entry : Word} {cr : CodeReq} (g : OpenCFG entry cr) : List Word :=
  g.exits.map Prod.fst

/-- Wrap an existing N-way branch and use its computed exit list as the shape. -/
def ofNBranch {entry : Word} {cr : CodeReq} (cfg : NBranch entry cr) :
    OpenCFG entry cr where
  cfg := cfg
  exits := cfg.exits
  exits_eq := rfl

/-- View a single-exit CFG certificate as a generated CFG shape. -/
def ofCert {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : CFG.Cert entry exit_ cr post) : OpenCFG entry cr where
  cfg := NBranch.ofTriple cfg
  exits := [(exit_, post)]
  exits_eq := rfl

/-- View a two-way branch as a generated CFG shape. -/
def ofBranch {entry : Word} {cr : CodeReq} (br : Branch entry cr) :
    OpenCFG entry cr where
  cfg := NBranch.ofBranch br
  exits := [(br.exit_t, br.post_t), (br.exit_f, br.post_f)]
  exits_eq := rfl

/-- View a two-way branch through a generated two-exit shape.  The proof only
    checks that the kernel branch labels/posts match the generated shape; the
    shape itself carries no decoded result values. -/
def ofBranchSpec {entry : Word} {cr : CodeReq}
    (spec : Branch2Spec) (br : Branch entry cr)
    (hshape : spec.Matches br) : OpenCFG entry cr where
  cfg := NBranch.ofBranch br
  exits := spec.exits
  exits_eq := by
    exact Branch2Spec.exits_eq_of_matches hshape

@[simp] theorem ofCert_exits {entry exit_ : Word} {cr : CodeReq}
    {post : Assertion} (cfg : CFG.Cert entry exit_ cr post) :
    (ofCert cfg).exits = [(exit_, post)] :=
  rfl

@[simp] theorem ofBranch_exits {entry : Word} {cr : CodeReq}
    (br : Branch entry cr) :
    (ofBranch br).exits = [(br.exit_t, br.post_t), (br.exit_f, br.post_f)] :=
  rfl

@[simp] theorem ofNBranch_exits {entry : Word} {cr : CodeReq}
    (cfg : NBranch entry cr) :
    (ofNBranch cfg).exits = cfg.exits :=
  rfl

/-- Weaken all generated exit posts while preserving the generated shape. -/
def weakenPosts {entry : Word} {cr : CodeReq}
    (g : OpenCFG entry cr) (exits' : List (Word × Assertion))
    (hmap : ∀ ex ∈ g.exits, ∃ ex' ∈ exits',
      ex'.1 = ex.1 ∧ Entails ex.2 ex'.2) :
    OpenCFG entry cr where
  cfg := CFG.nbranchWeakenPosts g.cfg exits' (by
    intro ex hmem
    exact hmap ex (by simpa [g.exits_eq] using hmem))
  exits := exits'
  exits_eq := rfl

/-- Weaken exactly two generated exits. -/
def weakenPosts2 {entry : Word} {cr : CodeReq}
    {l1 l2 : Word} {Q1 Q2 Q1' Q2' : Assertion}
    (g : OpenCFG entry cr)
    (hexits : g.exits = [(l1, Q1), (l2, Q2)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') :
    OpenCFG entry cr where
  cfg := CFG.nbranchWeakenPosts2 (l1 := l1) (l2 := l2)
    (Q1 := Q1) (Q2 := Q2) g.cfg (by simp [g.exits_eq, hexits]) h1 h2
  exits := [(l1, Q1'), (l2, Q2')]
  exits_eq := rfl

/-- Weaken exactly three generated exits. -/
def weakenPosts3 {entry : Word} {cr : CodeReq}
    {l1 l2 l3 : Word} {Q1 Q2 Q3 Q1' Q2' Q3' : Assertion}
    (g : OpenCFG entry cr)
    (hexits : g.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') (h3 : Entails Q3 Q3') :
    OpenCFG entry cr where
  cfg := CFG.nbranchWeakenPosts3 (l1 := l1) (l2 := l2) (l3 := l3)
    (Q1 := Q1) (Q2 := Q2) (Q3 := Q3) g.cfg
    (by simp [g.exits_eq, hexits]) h1 h2 h3
  exits := [(l1, Q1'), (l2, Q2'), (l3, Q3')]
  exits_eq := rfl

/-- Weaken exactly four generated exits. -/
def weakenPosts4 {entry : Word} {cr : CodeReq}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 Q1' Q2' Q3' Q4' : Assertion}
    (g : OpenCFG entry cr)
    (hexits : g.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (h1 : Entails Q1 Q1') (h2 : Entails Q2 Q2') (h3 : Entails Q3 Q3')
    (h4 : Entails Q4 Q4') :
    OpenCFG entry cr where
  cfg := CFG.nbranchWeakenPosts4 (l1 := l1) (l2 := l2) (l3 := l3) (l4 := l4)
    (Q1 := Q1) (Q2 := Q2) (Q3 := Q3) (Q4 := Q4) g.cfg
    (by simp [g.exits_eq, hexits]) h1 h2 h3 h4
  exits := [(l1, Q1'), (l2, Q2'), (l3, Q3'), (l4, Q4')]
  exits_eq := rfl

/-- Continue the head generated exit with another generated N-way CFG over
    disjoint code. -/
def seqHeadNBranchDisjoint {entry l : Word} {cr1 cr2 : CodeReq}
    {headPost : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (g : OpenCFG entry cr1)
    (hexits : g.exits = (l, headPost) :: others)
    (tail : OpenCFG l cr2)
    (hlink : Entails headPost tail.pre) :
    OpenCFG entry (cr1.union cr2) where
  cfg := CFG.nbranchSeqHeadNBranchDisjoint (l := l) (headPost := headPost)
    (others := others) hd g.cfg (by simp [g.exits_eq, hexits]) tail.cfg hlink
  exits := tail.exits ++ others
  exits_eq := by
    simp [CFG.nbranchSeqHeadNBranchDisjoint, NBranch.seqHeadNBranchDisjoint,
      tail.exits_eq]

/-- Continue the head generated exit with a single-exit CFG over disjoint code. -/
def seqHeadCertDisjoint {entry l l' : Word} {cr1 cr2 : CodeReq}
    {headPost post : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (g : OpenCFG entry cr1)
    (hexits : g.exits = (l, headPost) :: others)
    (tail : CFG.Cert l l' cr2 post)
    (hlink : Entails headPost tail.pre) :
    OpenCFG entry (cr1.union cr2) where
  cfg := CFG.nbranchSeqHeadDisjoint (l := l) (l' := l')
    (headPost := headPost) (others := others) hd g.cfg
    (by simp [g.exits_eq, hexits]) tail hlink
  exits := (l', post) :: others
  exits_eq := rfl

/-- Continue an arbitrary generated exit with another generated N-way CFG over
    disjoint code, preserving exits before and after it. -/
def seqExitNBranchDisjoint {entry l : Word} {cr1 cr2 : CodeReq}
    {exitPost : Assertion} {preExits others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (g : OpenCFG entry cr1)
    (hexits : g.exits = preExits ++ (l, exitPost) :: others)
    (tail : OpenCFG l cr2)
    (hlink : Entails exitPost tail.pre) :
    OpenCFG entry (cr1.union cr2) where
  cfg := CFG.nbranchSeqExitNBranchDisjoint (l := l) (exitPost := exitPost)
    (preExits := preExits) (others := others) hd g.cfg
    (by simp [g.exits_eq, hexits]) tail.cfg hlink
  exits := (preExits ++ tail.exits) ++ others
  exits_eq := by
    simp [CFG.nbranchSeqExitNBranchDisjoint, NBranch.seqExitNBranchDisjoint,
      tail.exits_eq]

/-- Continue an arbitrary generated exit with a single-exit CFG over disjoint
    code, preserving exits before and after it. -/
def seqExitCertDisjoint {entry l l' : Word} {cr1 cr2 : CodeReq}
    {exitPost post : Assertion} {preExits others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (g : OpenCFG entry cr1)
    (hexits : g.exits = preExits ++ (l, exitPost) :: others)
    (tail : CFG.Cert l l' cr2 post)
    (hlink : Entails exitPost tail.pre) :
    OpenCFG entry (cr1.union cr2) where
  cfg := CFG.nbranchSeqExitCertDisjoint (l := l) (l' := l')
    (exitPost := exitPost) (preExits := preExits) (others := others) hd g.cfg
    (by simp [g.exits_eq, hexits]) tail hlink
  exits := (preExits ++ [(l', post)]) ++ others
  exits_eq := rfl

/-- Join all generated exits with a uniform continuation bound. -/
def join {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (g : OpenCFG entry cr) (tailBound : Nat)
    (hall : ∀ ex ∈ g.exits,
      cpsTripleWithin tailBound ex.1 exit_ cr ex.2 post) :
    CFG.Cert entry exit_ cr post :=
  CFG.nbranch g.cfg tailBound (by
    intro ex hmem
    exact hall ex (by simpa [g.exits_eq] using hmem))

/-- Join exactly two generated exits when the first exit is the only reachable
    one. -/
def join2ResolveFirst {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 : Word} {Q1 Q2 : Assertion}
    (g : OpenCFG entry cr)
    (hexits : g.exits = [(l1, Q1), (l2, Q2)])
    (hlink1 : Entails Q1 post)
    (hdead2 : ∀ h, Q2 h → False) :
    CFG.Cert entry l1 cr post :=
  CFG.nbranchJoin2ResolveFirst (l1 := l1) (l2 := l2)
    (Q1 := Q1) (Q2 := Q2) g.cfg (by simp [g.exits_eq, hexits])
    hlink1 hdead2

/-- Join exactly two generated exits when the second exit is the only reachable
    one. -/
def join2ResolveSecond {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 : Word} {Q1 Q2 : Assertion}
    (g : OpenCFG entry cr)
    (hexits : g.exits = [(l1, Q1), (l2, Q2)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : Entails Q2 post) :
    CFG.Cert entry l2 cr post :=
  CFG.nbranchJoin2ResolveSecond (l1 := l1) (l2 := l2)
    (Q1 := Q1) (Q2 := Q2) g.cfg (by simp [g.exits_eq, hexits])
    hdead1 hlink2

/-- Join exactly three generated exits when the second exit is the only
    reachable one. -/
def join3ResolveSecond {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 : Word} {Q1 Q2 Q3 : Assertion}
    (g : OpenCFG entry cr)
    (hexits : g.exits = [(l1, Q1), (l2, Q2), (l3, Q3)])
    (hdead1 : ∀ h, Q1 h → False)
    (hlink2 : Entails Q2 post)
    (hdead3 : ∀ h, Q3 h → False) :
    CFG.Cert entry l2 cr post :=
  CFG.nbranchJoin3ResolveSecond (l1 := l1) (l2 := l2) (l3 := l3)
    (Q1 := Q1) (Q2 := Q2) (Q3 := Q3) g.cfg
    (by simp [g.exits_eq, hexits]) hdead1 hlink2 hdead3

/-- Join exactly four generated exits when the third exit is the only reachable
    one. -/
def join4ResolveThird {entry : Word} {cr : CodeReq} {post : Assertion}
    {l1 l2 l3 l4 : Word} {Q1 Q2 Q3 Q4 : Assertion}
    (g : OpenCFG entry cr)
    (hexits : g.exits = [(l1, Q1), (l2, Q2), (l3, Q3), (l4, Q4)])
    (hdead1 : ∀ h, Q1 h → False)
    (hdead2 : ∀ h, Q2 h → False)
    (hlink3 : Entails Q3 post)
    (hdead4 : ∀ h, Q4 h → False) :
    CFG.Cert entry l3 cr post :=
  CFG.nbranchJoin4ResolveThird (l1 := l1) (l2 := l2) (l3 := l3) (l4 := l4)
    (Q1 := Q1) (Q2 := Q2) (Q3 := Q3) (Q4 := Q4) g.cfg
    (by simp [g.exits_eq, hexits]) hdead1 hdead2 hlink3 hdead4

end OpenCFG

namespace LoopNatSpec

/-- The generated precondition of a bounded loop shape. -/
def pre (spec : LoopNatSpec) : Assertion :=
  spec.inv 0

/-- The generated step bound of a bounded loop shape. -/
def bound (spec : LoopNatSpec) : Nat :=
  loopBound spec.nHeader spec.nBody spec.nExit spec.fuel

/-- Package a generated loop shape and the kernel-checked loop obligations as a
    single-exit CFG certificate. -/
def toCert (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    CFG.Cert spec.header spec.exitLabel cr spec.post :=
  CFG.loopNat hcert

/-- View a generated loop shape as an `OpenCFG` with one generated exit. -/
def toOpenCFG (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    OpenCFG spec.header cr :=
  OpenCFG.ofCert (spec.toCert hcert)

@[simp] theorem toCert_pre (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    (spec.toCert hcert).pre = spec.pre :=
  rfl

@[simp] theorem toCert_nSteps (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    (spec.toCert hcert).nSteps = spec.bound :=
  rfl

@[simp] theorem toOpenCFG_exits (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    (spec.toOpenCFG hcert).exits = [(spec.exitLabel, spec.post)] :=
  rfl

end LoopNatSpec

namespace Branch2Spec

/-- Build an `OpenCFG` branch skeleton from a generated two-exit shape and a
    kernel-checked branch certificate. -/
def toOpenCFG {entry : Word} {cr : CodeReq}
    (spec : Branch2Spec) (br : Branch entry cr)
    (hshape : spec.Matches br) : OpenCFG entry cr :=
  OpenCFG.ofBranchSpec spec br hshape

/-- Resolve a generated two-way branch when the taken exit is the reachable
    join case. -/
def joinTaken {entry : Word} {cr : CodeReq} {post : Assertion}
    (spec : Branch2Spec) (br : Branch entry cr)
    (hshape : spec.Matches br)
    (hlink : Entails spec.taken.post post)
    (hdead : ∀ h, spec.fallthrough.post h → False) :
    CFG.Cert entry spec.taken.label cr post :=
  (spec.toOpenCFG br hshape).join2ResolveFirst rfl hlink hdead

/-- Resolve a generated two-way branch when the fall-through exit is the
    reachable join case. -/
def joinFallthrough {entry : Word} {cr : CodeReq} {post : Assertion}
    (spec : Branch2Spec) (br : Branch entry cr)
    (hshape : spec.Matches br)
    (hdead : ∀ h, spec.taken.post h → False)
    (hlink : Entails spec.fallthrough.post post) :
    CFG.Cert entry spec.fallthrough.label cr post :=
  (spec.toOpenCFG br hshape).join2ResolveSecond rfl hdead hlink

end Branch2Spec

namespace OpenCFG

example {entry : Word} {cr : CodeReq} (br : Branch entry cr) :
    (OpenCFG.ofBranch br).labels = [br.exit_t, br.exit_f] :=
  rfl

example {entry : Word} {cr : CodeReq} {post : Assertion}
    (br : Branch entry cr)
    (hlink : Entails br.post_t post)
    (hdead : ∀ h, br.post_f h → False) :
    CFG.Cert entry br.exit_t cr post :=
  (OpenCFG.ofBranch br).join2ResolveFirst rfl hlink hdead

example {entry : Word} {cr : CodeReq} {post : Assertion}
    (spec : Branch2Spec) (br : Branch entry cr)
    (hshape : spec.Matches br)
    (hlink : Entails spec.taken.post post)
    (hdead : ∀ h, spec.fallthrough.post h → False) :
    CFG.Cert entry spec.taken.label cr post :=
  spec.joinTaken br hshape hlink hdead

example {entry : Word} {cr : CodeReq} {post : Assertion}
    (spec : Branch2Spec) (br : Branch entry cr)
    (hshape : spec.Matches br)
    (hdead : ∀ h, spec.taken.post h → False)
    (hlink : Entails spec.fallthrough.post post) :
    CFG.Cert entry spec.fallthrough.label cr post :=
  spec.joinFallthrough br hshape hdead hlink

example {entry l : Word} {cr1 cr2 : CodeReq}
    {headPost : Assertion} {others : List (Word × Assertion)}
    (hd : cr1.Disjoint cr2)
    (g : OpenCFG entry cr1)
    (hexits : g.exits = (l, headPost) :: others)
    (tail : OpenCFG l cr2)
    (hlink : Entails headPost tail.pre) :
    ((g.seqHeadNBranchDisjoint hd hexits tail hlink).exits =
      tail.exits ++ others) :=
  rfl

example (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    (spec.toCert hcert).pre = spec.pre :=
  rfl

example (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    (spec.toCert hcert).nSteps = spec.bound :=
  rfl

example (spec : LoopNatSpec) {cr : CodeReq}
    (hcert : loopNatCert spec.nHeader spec.nBody spec.nExit
      spec.header spec.bodyEntry spec.exitLabel cr
      spec.inv spec.bodyPre spec.exitPost spec.post 0 spec.fuel) :
    (spec.toOpenCFG hcert).exits = [(spec.exitLabel, spec.post)] :=
  rfl

end OpenCFG
end GeneratedCFG
end WP
end EvmAsm.Rv64
