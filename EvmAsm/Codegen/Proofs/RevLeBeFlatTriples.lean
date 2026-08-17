/-
  EvmAsm.Codegen.Proofs.RevLeBeFlatTriples

  Guest-image anchored FLAT triples for the byte-reversing copy routine, at
  BOTH guest addresses it is deployed to (#12244).

  ## What this closes

  `swrRevLeBeFn_spec` was a real, fully proven contract, but stated in the
  `Fn`/`Reach` vocabulary over a free `base` — what the `--shape` classifier
  calls "model-only".  A registry row must name a whole-routine
  `cpsTripleWithin` whose entry AND `CodeReq` are anchored at the routine's
  `GuestAddrs` entry, so that the claim is about the DEPLOYED image rather
  than about a model.  `Fn.retSpecFlat` closes that gap now that the `Fn`'s
  post pins its ambient.

  ## ⭐ One proof, two guest addresses

  `bhrRevLeBe_prog` is byte-identical to `swrRevLeBe_prog` — the same routine
  emitted under two labels — and `bhrRevLeBeFn` is a *definitional alias* of
  `swrRevLeBeFn`.  Rather than duplicate the lift, `revLeBeFlat_at` below is
  parameterized over the base address and the program, with the pairing
  supplied as `hprog`.  The two public theorems instantiate it at
  `GuestAddrs.swr_rev_le_be`/`swrRevLeBe_prog` and
  `GuestAddrs.bhr_rev_le_be`/`bhrRevLeBe_prog`, each `hprog` discharged by
  `rfl`.  That the SAME lemma accepts both instantiations is itself the
  byte-identity witness: the body's `flatten` is base-independent
  (`SwrRevLeBeSAsm`'s `#guard` pins `flatten 0 = flatten 0x80000000`), so the
  emitted code at the two addresses is the same list of instructions.

  ## ⚠️ Three pinned registers, and why `hdisj` is load-bearing

  This routine pins THREE ABI registers (`a0`=src, `a1`=len, `a2`=dst), so the
  register-file split is the three-way `exposedRegs_split_rev`; the pattern is
  ported from `U256BeFlat.exposedRegs_split_add`, which splits the same
  fifteen exposed registers around the same three.

  The contract is NOT total over its argument types: beyond the length and
  no-overflow hypotheses it needs `hdj` — source and destination DISJOINT.
  That is a genuine domain restriction, not framing convenience: the block
  engine's `inRw` routing test is ARITHMETIC, so without disjointness an `LBU`
  aimed at the source could be routed into the writable window and read a
  PARTIALLY REVERSED byte.  An overlapping caller cannot satisfy this
  contract, which matches the routine's real contract (reverse-copy into a
  separate buffer).

  Both contracts pin the source region INTACT in the post, so a routine that
  scribbled on its input could not satisfy them.
-/

import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Codegen.Programs.SwrRevLeBeSAsm
import EvmAsm.Codegen.Programs.BhrRevLeBeSAsm

namespace EvmAsm.Codegen.RevLeBeFlat

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- The exposed registers the reverse-copy may clobber, excluding its three
    ABI registers `a0`/`a1`/`a2` (`x10`/`x11`/`x12`).  Same fifteen-minus-three
    split as the u256 big-endian family. -/
def revScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]

/-- Split the exposed register file around the routine's three ABI registers. -/
private theorem exposedRegs_split_rev (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf revScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [revScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_revScratch : (.x10 : Reg) ∉ revScratch := by decide
private theorem x11_notin_revScratch : (.x11 : Reg) ∉ revScratch := by decide
private theorem x12_notin_revScratch : (.x12 : Reg) ∉ revScratch := by decide

/-- **The reverse-copy routine's whole-routine flat triple, at an arbitrary
    deployed base.**

    Reverses the first `len` bytes of the read-only region at `a0` into the
    `len`-byte writable window at `a2`, leaving the source INTACT:
    `dst = (bs.take len).reverse`.

    `hprog` is the deployment pairing — `programRet base` IS the program
    recorded for `base` in `GuestImageEntries` — so an instantiation of this
    lemma is a statement about the deployed image.  See the module header for
    why `hdj` is load-bearing. -/
private theorem revLeBeFlat_at (base : Word) (prog : Program)
    (hprog : (SwrRevLeBeSAsm.swrRevLeBeFn 0 0 0 [] []).programRet base = prog)
    (ret src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩)
    (hol : orig.length = len) (hlb : len ≤ bs.length)
    (hsb : src.toNat + len < 2 ^ 64) (hdb : dst.toNat + len < 2 ^ 64)
    (hdj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig).body.steps + 1)
      base ret (CodeReq.ofProg base prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x12 : Reg) ↦ᵣ dst) **
        regOwns revScratch ** bytesRegion dst orig ** bytesRegion src bs)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst ((bs.take len).reverse) ** bytesRegion src bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns revScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x12 : Reg) ↦ᵣ dst) **
        bytesRegion dst orig ** bytesRegion src bs)
      (fun vf => ?_))
  -- ⚠️ The if-valuation is written INLINE, not bound with `set`: a `set` here
  -- puts the routine's arguments into the expected type of the `Fn.retSpecFlat`
  -- application and elaboration rejects it ("expected type must not contain
  -- free variables").
  have hpre : (SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig).pre
      (fun r => if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
        else if r = .x12 then dst else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, ?_, rfl, hol, hlb, hsb, hdb, hdj, rfl⟩
    · show RegFile.get _ .x10 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = BitVec.ofNat 64 len
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0),
        if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlat (SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig) base
    (SwrRevLeBeSAsm.swrRevLeBeFn_spec src dst len bs orig hwf hrww base)
    -- 10 = the flattened body length pinned by `SwrRevLeBeSAsm`'s `#guard`.
    (by show 4 * (10 + 1) ≤ 2 ^ 64; decide)
    ret halign
    (fun r => if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
      else if r = .x12 then dst else vf r)
    orig (by exact hol) hpre
    (Q := regOwns exposedRegs ** bytesRegion dst ((bs.take len).reverse))
    -- `hpostEmp`: the ambient is pinned by the `Fn` post's second conjunct.
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hws, -⟩ := hpost
      subst hws
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  -- Anchor the `CodeReq` at the deployed program.  `programRet` is independent
  -- of the `Fn`'s value arguments (the body's instruction blocks are
  -- constants), which is what lets `hprog` be stated at `0 0 0 [] []`.
  rw [show (SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig).programRet base
      = prog from hprog] at had
  rw [show (SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig).region.base = src from rfl,
      show (SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig).region.bytes = bs from rfl,
      show (SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig).rw.base = dst from rfl] at had
  -- Re-express the lift's `regFileIs` (at our if-valuation) as the three ABI
  -- atoms plus `regAtomsOf vf revScratch`, which is what the peeled goal has.
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_rev,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then BitVec.ofNat 64 len else
        if (Reg.x10 : Reg) = .x12 then dst else vf .x10) = src from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then BitVec.ofNat 64 len else
        if (Reg.x11 : Reg) = .x12 then dst else vf .x11)
      = BitVec.ofNat 64 len from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    show (if (Reg.x12 : Reg) = .x10 then src else
        if (Reg.x12 : Reg) = .x11 then BitVec.ofNat 64 len else
        if (Reg.x12 : Reg) = .x12 then dst else vf .x12) = dst from by
      rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
        else if r = .x12 then dst else vf r)
      vf revScratch
      (fun r hr => by
        show (if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
          else if r = .x12 then dst else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_revScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_revScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x12) => x12_notin_revScratch (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

/-- **`swr_rev_le_be`, whole-routine flat triple at the guest entry.**

    Anchored at `GuestAddrs.swr_rev_le_be` over
    `CodeReq.ofProg … swrRevLeBe_prog` — the pairing recorded in
    `GuestImageEntries.lean` — so this is a statement about the deployed
    image.  See the module header for the `hdj` domain restriction. -/
theorem swrRevLeBeFlat_spec (ret src dst : Word) (len : Nat)
    (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩)
    (hol : orig.length = len) (hlb : len ≤ bs.length)
    (hsb : src.toNat + len < 2 ^ 64) (hdb : dst.toNat + len < 2 ^ 64)
    (hdj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((SwrRevLeBeSAsm.swrRevLeBeFn src dst len bs orig).body.steps + 1)
      (GuestAddrs.swr_rev_le_be : Word) ret
      (CodeReq.ofProg (GuestAddrs.swr_rev_le_be : Word) swrRevLeBe_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x12 : Reg) ↦ᵣ dst) **
        regOwns revScratch ** bytesRegion dst orig ** bytesRegion src bs)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst ((bs.take len).reverse) ** bytesRegion src bs) :=
  revLeBeFlat_at (GuestAddrs.swr_rev_le_be : Word) swrRevLeBe_prog rfl
    ret src dst len bs orig hwf hrww hol hlb hsb hdb hdj halign

/-- **`bhr_rev_le_be`, whole-routine flat triple at the guest entry.**

    The SAME routine as `swr_rev_le_be`, deployed at a second address:
    `bhrRevLeBe_prog` is byte-identical to `swrRevLeBe_prog` and
    `bhrRevLeBeFn` is a definitional alias.  Anchored at
    `GuestAddrs.bhr_rev_le_be` over `CodeReq.ofProg … bhrRevLeBe_prog`, the
    pairing recorded in `GuestImageEntries.lean`. -/
theorem bhrRevLeBeFlat_spec (ret src dst : Word) (len : Nat)
    (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩)
    (hol : orig.length = len) (hlb : len ≤ bs.length)
    (hsb : src.toNat + len < 2 ^ 64) (hdb : dst.toNat + len < 2 ^ 64)
    (hdj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((BhrRevLeBeSAsm.bhrRevLeBeFn src dst len bs orig).body.steps + 1)
      (GuestAddrs.bhr_rev_le_be : Word) ret
      (CodeReq.ofProg (GuestAddrs.bhr_rev_le_be : Word) bhrRevLeBe_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x12 : Reg) ↦ᵣ dst) **
        regOwns revScratch ** bytesRegion dst orig ** bytesRegion src bs)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst ((bs.take len).reverse) ** bytesRegion src bs) :=
  revLeBeFlat_at (GuestAddrs.bhr_rev_le_be : Word) bhrRevLeBe_prog rfl
    ret src dst len bs orig hwf hrww hol hlb hsb hdb hdj halign

end EvmAsm.Codegen.RevLeBeFlat
