/-
  EvmAsm.Codegen.Proofs.U256BeFlatTriples

  Guest-image anchored FLAT triples for the u256 big-endian helper family
  (#12244, harvesting #12225's triage).

  ## Why this module exists

  Each routine in this family already had a *structured* SAsm contract of the
  form `(u256…Fn args).Spec base` — a real, fully proven triple, but stated in
  the `Fn`/`Reach` vocabulary with a free `base`.  The proof registry cannot
  cite such a theorem as a row: a row must name a whole-routine
  `cpsTripleWithin` whose entry AND `CodeReq` are both anchored at the
  routine's `GuestAddrs` entry, so that the contract is about the DEPLOYED
  image rather than about a model.  The `--shape` classifier from #12240 calls
  that gap "model-only".

  The lift that closes the gap is `Fn.retSpecFlatAmbient`
  (`EvmAsm/Rv64/SAsm/FnFlat.lean`): it turns `f.Spec base` into a flat
  `cpsTripleWithin (f.body.steps + 1) base ret (CodeReq.ofProg base
  (f.programRet base))`, carrying a FIXED pc-free ambient `A` across the call
  so that read-only operand regions may live in the ambient (which the
  ambient-free `Fn.retSpecFlat` rejects).  `u256SubBeFlat_spec`
  (`Secp256k1FieldReduceOnceSAsmSupport.lean`, rowed `.proven` in #12231) is
  the worked precedent; this module follows it, with two deliberate
  differences noted below.

  ## Two deliberate departures from the `u256_sub_be` precedent

  1. **`CodeReq.ofProg`, not a stage union.**  `u256SubBeFlat_spec` was
     produced as support for `secf_reduce_once`, so it ends with a `liftCode`
     into the caller's shared `secfReduceOnceCr` and its row carries a caveat
     about that.  Nothing here needs a caller's stage, so the contract keeps
     the minimal, self-describing `CodeReq.ofProg (GuestAddrs.u256_add_be)
     u256AddBe_prog`.  A caller that wants it inside a stage union can
     `liftCode` at the call site; the reverse direction is not available.
  2. **The result register is EXPOSED, not forgotten.**  The `sub` precedent
     collapses the whole post-state register file to `regOwns exposedRegs`,
     discarding the borrow it computed.  `u256AddBePost` pins `a0` to
     `u256AddBeCarry`, so this contract publishes it: the carry-out IS the
     256-bit overflow flag, and a caller settling a balance or a gas product
     needs exactly that bit.  `a1`/`a2` are likewise republished as the
     untouched operand/output pointers.

  Both routines keep BOTH 32-byte input regions pinned INTACT in the post, so a
  routine that scribbled on its operands could not satisfy these contracts.
-/

import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Codegen.Programs.U256AddBeSAsm
import EvmAsm.Codegen.Programs.U256FromU64BeSAsm
import EvmAsm.Crypto.PowLadder
import EvmAsm.Crypto.BeBytesArith
import EvmAsm.Codegen.Programs.U256
import Mathlib.Tactic.Ring

namespace EvmAsm.Codegen.U256BeFlat

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- The exposed registers `u256_add_be` may clobber, excluding its ABI
    registers `a0`/`a1`/`a2` (`x10`/`x11`/`x12`).  Identical as a list to the
    `subScratch` used by the `u256_sub_be` precedent — the two routines share
    a register discipline — but re-declared here so this module does not
    depend on a `private` definition inside a secp256k1 support file. -/
def addScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]

/-- Split the exposed register file around `u256_add_be`'s three ABI
    registers. -/
private theorem exposedRegs_split_add (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf addScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [addScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_addScratch : (.x10 : Reg) ∉ addScratch := by decide
private theorem x11_notin_addScratch : (.x11 : Reg) ∉ addScratch := by decide
private theorem x12_notin_addScratch : (.x12 : Reg) ∉ addScratch := by decide

/-- **`u256_add_be`, whole-routine flat triple at the guest entry.**

    Adds the two 32-byte big-endian operands at `a0`/`a1` into the 32-byte
    output window at `a2` and returns the carry-out in `a0`.  Anchored at
    `GuestAddrs.u256_add_be` over `CodeReq.ofProg … u256AddBe_prog` — the
    pairing recorded in `EvmAsm/Codegen/Proofs/GuestImageEntries.lean` — so
    this is a statement about the deployed image.

    Domain: ABI hypotheses only (32-byte operand/output lengths,
    region well-formedness, no address-space wraparound, and each operand
    range disjoint from the output range).  Both input regions are pinned
    INTACT in the post. -/
theorem u256AddBeFlat_spec (ret aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenA : aBytes.length = 32) (hlenB : bBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjA : aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ bPtr.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((U256AddBeSAsm.u256AddBeFn aPtr bPtr outPtr aBytes bBytes orig).body.steps + 1)
      (GuestAddrs.u256_add_be : Word) ret
      (CodeReq.ofProg (GuestAddrs.u256_add_be : Word) u256AddBe_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns addScratch ** bytesRegion outPtr orig **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry aBytes bBytes orig) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns addScratch **
        bytesRegion outPtr (U256AddBeSAsm.u256AddBeBytes aBytes bBytes orig) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns addScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        bytesRegion outPtr orig ** bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (fun vf => ?_))
  -- The concrete post-call valuation of the three ABI registers.
  have hpre : U256AddBeSAsm.u256AddBePre aPtr bPtr outPtr aBytes bBytes orig
      (fun r => if r = .x10 then aPtr else if r = .x11 then bPtr
        else if r = .x12 then outPtr else vf r)
      orig (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
    refine ⟨?_, ?_, ?_, rfl, hlenA, hlenB, hlenOrig, hovA, hovB, hovOut,
      hdisjA, hdisjB, rfl⟩
    · show RegFile.get _ .x10 = aPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = bPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = outPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (U256AddBeSAsm.u256AddBeFn aPtr bPtr outPtr aBytes bBytes orig)
    (GuestAddrs.u256_add_be : Word)
    (U256AddBeSAsm.u256AddBe_spec aPtr bPtr outPtr aBytes bBytes orig hrw hroA hroB
      (GuestAddrs.u256_add_be : Word))
    (by show 4 * (16 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then aPtr else if r = .x11 then bPtr
      else if r = .x12 then outPtr else vf r)
    orig (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
    (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
    (by exact hlenOrig) hpre
    (Q := ((((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry aBytes bBytes orig) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns addScratch) **
        bytesRegion outPtr (U256AddBeSAsm.u256AddBeBytes aBytes bBytes orig)) **
      (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes))
    -- `hpostAmb`: the ambient is pinned by the `Fn` post's last conjunct.
    (fun _ _ _ hpost => hpost.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hc10, hc11, hc12, hws, _hA⟩ := hpost
      subst ws'
      -- Turn the post-state register file into the three named ABI atoms plus
      -- ownership of the scratch set, then substitute the values the `Fn` post
      -- pins.  `RegFile.get r = rf' r` for each ABI register (none is `x0`).
      have g10 : rf' .x10 = U256AddBeSAsm.u256AddBeCarry aBytes bBytes orig := by
        rw [← hc10, RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have g11 : rf' .x11 = bPtr := by
        rw [← hc11, RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      have g12 : rf' .x12 = outPtr := by
        rw [← hc12, RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_add, g10, g11, g12] at hh
      refine sepConj_mono_left (sepConj_mono_left ?_) hp hh
      exact fun h hx => by
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hx
        exact regAtomsOf_to_regOwns (fun r => rf' r) addScratch)
  -- Anchor the `CodeReq`: the lift's `f.programRet base` IS the deployed
  -- `u256AddBe_prog` at this base (definitional — the body never bakes in a
  -- layout value, see `U256AddBeSAsm.u256AddBeBody_flatten`).
  rw [show (U256AddBeSAsm.u256AddBeFn aPtr bPtr outPtr aBytes bBytes orig).programRet
      (GuestAddrs.u256_add_be : Word) = u256AddBe_prog from rfl] at had
  -- `region = Region.empty`, so the region conjunct is `emp`.
  rw [show (U256AddBeSAsm.u256AddBeFn aPtr bPtr outPtr aBytes bBytes orig).region
        = Region.empty from rfl,
      show (U256AddBeSAsm.u256AddBeFn aPtr bPtr outPtr aBytes bBytes orig).rw.base
        = outPtr from rfl,
      show Region.empty.base = (0 : Word) from rfl,
      show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil] at had
  -- Re-express the lift's `regFileIs rf` (at our if-valuation) as the three ABI
  -- atoms plus `regAtomsOf vf addScratch`, which is what the peeled goal has.
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_add,
    show (if (Reg.x10 : Reg) = .x10 then aPtr else
        if (Reg.x10 : Reg) = .x11 then bPtr else
        if (Reg.x10 : Reg) = .x12 then outPtr else vf .x10) = aPtr from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then aPtr else
        if (Reg.x11 : Reg) = .x11 then bPtr else
        if (Reg.x11 : Reg) = .x12 then outPtr else vf .x11) = bPtr from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    show (if (Reg.x12 : Reg) = .x10 then aPtr else
        if (Reg.x12 : Reg) = .x11 then bPtr else
        if (Reg.x12 : Reg) = .x12 then outPtr else vf .x12) = outPtr from by
      rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then aPtr else if r = .x11 then bPtr
        else if r = .x12 then outPtr else vf r)
      vf addScratch
      (fun r hr => by
        show (if r = .x10 then aPtr else if r = .x11 then bPtr
          else if r = .x12 then outPtr else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_addScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_addScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x12) => x12_notin_addScratch (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by
      rw [sepConj_emp_right'] at hq
      xperm_hyp hq) had

/-! ## `u256_from_u64_be`

  This one needed a change to the leaf's own contract before any adapter could
  reach it.  `u256FromU64BeFn`'s post used to be `fun _ ws _ => ws =
  u256FromU64Bytes v` — ambient-AGNOSTIC — so neither `Fn.retSpecFlat`'s
  `hpostEmp` nor `Fn.retSpecFlatAmbient`'s `hpostAmb` was dischargeable: both
  require the post to PIN the ambient, because that is the only way the fact
  survives out of the existentially-quantified `asrtOf` in `Fn.retSpec`'s
  conclusion.  The ambient is now pinned to `empAssertion` in the leaf's pre and
  post (see the note on `u256FromU64BeFn`), which is the honest ambient for a
  routine with NO read-only input region, and the plain ambient-free
  `Fn.retSpecFlat` applies. -/

/-- The exposed registers `u256_from_u64_be` may clobber, excluding its ABI
    registers `a0`/`a1` (`x10`/`x11`). -/
def fromU64Scratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Split the exposed register file around `u256_from_u64_be`'s ABI registers. -/
private theorem exposedRegs_split_fromU64 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          regAtomsOf vf fromU64Scratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [fromU64Scratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_fromU64Scratch : (.x10 : Reg) ∉ fromU64Scratch := by decide
private theorem x11_notin_fromU64Scratch : (.x11 : Reg) ∉ fromU64Scratch := by decide

/-- **`u256_from_u64_be`, whole-routine flat triple at the guest entry.**

    Zero-extends the 64-bit value in `a0` into the 32-byte big-endian window at
    `a1`.  Anchored at `GuestAddrs.u256_from_u64_be` over
    `CodeReq.ofProg … u256FromU64Be_prog` — the pairing recorded in
    `GuestImageEntries.lean`.  Domain: ABI hypotheses only (output region
    well-formed, 32 original bytes, aligned `ra`), so this is TOTAL over the
    64-bit input: there is no input-domain side condition. -/
theorem u256FromU64BeFlat_spec (ret v dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 32⟩) (hlenOrig : orig.length = 32)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((U256FromU64BeSAsm.u256FromU64BeFn v dst orig).body.steps + 1)
      (GuestAddrs.u256_from_u64_be : Word) ret
      (CodeReq.ofProg (GuestAddrs.u256_from_u64_be : Word) u256FromU64Be_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ dst) **
        regOwns fromU64Scratch ** bytesRegion dst orig)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst (U256FromU64BeSAsm.u256FromU64Bytes v)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns fromU64Scratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ v) **
        ((.x11 : Reg) ↦ᵣ dst) ** bytesRegion dst orig)
      (fun vf => ?_))
  have hpre : (U256FromU64BeSAsm.u256FromU64BeFn v dst orig).pre
      (fun r => if r = .x10 then v else if r = .x11 then dst else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, rfl, hlenOrig, rfl⟩
    · show RegFile.get _ .x10 = v
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlat
    (U256FromU64BeSAsm.u256FromU64BeFn v dst orig)
    (GuestAddrs.u256_from_u64_be : Word)
    (U256FromU64BeSAsm.u256FromU64BeFn_spec v dst orig hwf
      (GuestAddrs.u256_from_u64_be : Word))
    (by show 4 * (18 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then v else if r = .x11 then dst else vf r)
    orig (by exact hlenOrig) hpre
    (Q := regOwns exposedRegs **
      bytesRegion dst (U256FromU64BeSAsm.u256FromU64Bytes v))
    -- `hpostEmp`: dischargeable exactly because the post now pins the ambient.
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hws, -⟩ := hpost
      subst ws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (U256FromU64BeSAsm.u256FromU64BeFn v dst orig).programRet
      (GuestAddrs.u256_from_u64_be : Word) = u256FromU64Be_prog from rfl] at had
  rw [show (U256FromU64BeSAsm.u256FromU64BeFn v dst orig).region
        = Region.empty from rfl,
      show (U256FromU64BeSAsm.u256FromU64BeFn v dst orig).rw.base = dst from rfl,
      show Region.empty.base = (0 : Word) from rfl,
      show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_fromU64,
    show (if (Reg.x10 : Reg) = .x10 then v else
        if (Reg.x10 : Reg) = .x11 then dst else vf .x10) = v from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then v else
        if (Reg.x11 : Reg) = .x11 then dst else vf .x11) = dst from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then v else if r = .x11 then dst else vf r)
      vf fromU64Scratch
      (fun r hr => by
        show (if r = .x10 then v else if r = .x11 then dst else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_fromU64Scratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_fromU64Scratch (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by
      rw [sepConj_emp_right'] at hq
      xperm_hyp hq) had


/-! ## Arithmetic meaning of the encoder (#12225)

    The flat triples above state their posts OPERATIONALLY — `u256FromU64Bytes v`
    for the encoder, `u256AddBeBytes a b orig` for the adder — which pins the exact
    bytes but says nothing numeric.  #12225 asked for these legs to be tied to
    `Nat` arithmetic through the BE-bytes abstraction; `u256_lt_be` was already the
    only member of the family whose post carried numeric meaning
    (`if beBytesToNat as < beBytesToNat bs then 1 else 0`).

    This is that tie for the encoder; the ADDER's tie is the next section. The
    encoder's is a literal unfolding, while the adder needs a carry-chain
    induction, because its post is a 32-step per-byte fold
    (`(addCarryState a b orig 32).1`) rather than an explicit list. -/

set_option maxRecDepth 8000 in
/-- **`u256_from_u64_be` computes the big-endian encoding of its u64 argument.**

    Together with `u256FromU64BeFlat_spec` — whose post is
    `bytesRegion dst (u256FromU64Bytes v)` — this gives the routine a numeric
    contract: the 32-byte window at `a1` decodes back to exactly `v.toNat`, so the
    high 24 bytes are genuinely zero rather than merely "whatever the model says".

    The proof is a literal unfolding: `u256FromU64Bytes` is an explicit 32-element
    list (24 zeros then `beByte v 0 … beByte v 7`), so the big-endian `foldl`
    reduces to a closed bitvector identity that `bv_omega` discharges. -/
theorem beBytesToNat_u256FromU64Bytes (v : Word) :
    EvmAsm.Crypto.beBytesToNat (U256FromU64BeSAsm.u256FromU64Bytes v) = v.toNat := by
  simp only [EvmAsm.Crypto.beBytesToNat, U256FromU64BeSAsm.u256FromU64Bytes,
    U256FromU64BeSAsm.beByte, List.foldl_cons, List.foldl_nil]
  bv_omega

-- Non-vacuity: a real numeric identity, not a definitional unfolding that would
-- hold for any encoder. Includes the bound the 24 zero bytes are there to give.
#guard EvmAsm.Crypto.beBytesToNat
    (U256FromU64BeSAsm.u256FromU64Bytes 0x0102030405060708) = 0x0102030405060708
#guard EvmAsm.Crypto.beBytesToNat
    (U256FromU64BeSAsm.u256FromU64Bytes 0xffffffffffffffff) = 18446744073709551615
#guard EvmAsm.Crypto.beBytesToNat
    (U256FromU64BeSAsm.u256FromU64Bytes 0xffffffffffffffff) < 2 ^ 64


/-! ## Arithmetic meaning of the adder (#12225)

    `u256AddBeFlat_spec`'s post is operational: the 32-byte window at `a2` holds
    `u256AddBeBytes a b orig` and `a0` holds `u256AddBeCarry a b orig`, both
    projections of a 32-step per-byte fold that walks index 31 down to 0. This
    section gives that fold its numeric meaning — the routine computes the
    256-bit truncated sum and reports the overflow bit — which is what lets it
    serve the money path (balance debits, gas settlement: #11145) without every
    caller having to reason about carries.

    ### Why the induction is stated over `drop`

    The obvious formulation ("the low `k` bytes hold the low `k` bytes of the
    sum") needs a positional digit sum and then a reindexing lemma to connect it
    to `beBytesToNat` at `k = 32`. Stating the invariant over the SUFFIX
    `l.drop (32 - k)` avoids that entirely: `drop 0 = l`, so the `k = 32` instance
    IS the whole-buffer statement, and each step peels exactly one digit off the
    front of the suffix (`beBytesToNat_drop_succ`). The carry bound
    `carry.toNat ≤ 1` has to travel WITH the equation — it is what makes the next
    byte column non-wrapping — so the invariant is a conjunction. -/

/-- **One byte column is exact.** The emitted digit plus 256× the carry-out
    accounts for both input bytes and the carry-in, and the carry-out is again a
    single bit. The `carry.toNat ≤ 1` hypothesis is what rules out 64-bit wrap:
    the column sum is at most `255 + 255 + 1 = 511`. -/
private theorem addCarryByte_digit (a b : BitVec 8) (carry : Word)
    (hc : carry.toNat ≤ 1) :
    (U256AddBeSAsm.addCarryByte a b carry).1.toNat
        + 256 * (U256AddBeSAsm.addCarryByte a b carry).2.toNat
        = a.toNat + b.toNat + carry.toNat
      ∧ (U256AddBeSAsm.addCarryByte a b carry).2.toNat ≤ 1 := by
  unfold U256AddBeSAsm.addCarryByte
  exact ⟨by bv_omega, by bv_omega⟩

/-- Writing at index `n` and then dropping the first `n` elements exposes the
    written value at the head, with the untouched tail behind it. -/
private theorem drop_set_self {α : Type _} (l : List α) (n : Nat) (v : α)
    (hn : n < l.length) : (l.set n v).drop n = v :: l.drop (n + 1) := by
  have hn' : n < (l.set n v).length := by rw [List.length_set]; exact hn
  rw [List.drop_eq_getElem_cons hn', List.getElem_set_self hn', List.drop_set]
  simp

/-- **The carry-chain invariant.** After `k` columns the processed suffix holds
    the low `k` bytes of the sum, with `carry` the carry out of those columns:

    `value(out.drop (32-k)) + 256^k * carry = value(a.drop (32-k)) + value(b.drop (32-k))`

    The second conjunct (`carry.toNat ≤ 1`) is not decoration: it is the
    hypothesis the next column needs, so the two facts must be proved
    simultaneously. -/
private theorem addCarryState_be (a b orig : List (BitVec 8))
    (hla : a.length = 32) (hlb : b.length = 32) (hlo : orig.length = 32) (k : Nat)
    (hk : k ≤ 32) :
    EvmAsm.Crypto.beBytesToNat ((U256AddBeSAsm.addCarryState a b orig k).1.drop (32 - k))
        + 256 ^ k * (U256AddBeSAsm.addCarryState a b orig k).2.toNat
      = EvmAsm.Crypto.beBytesToNat (a.drop (32 - k))
        + EvmAsm.Crypto.beBytesToNat (b.drop (32 - k))
    ∧ (U256AddBeSAsm.addCarryState a b orig k).2.toNat ≤ 1 := by
  induction k with
  | zero =>
    have h0 : ∀ l : List (BitVec 8), l.length = 32 → l.drop 32 = [] :=
      fun l hl => List.drop_eq_nil_of_le (by omega)
    have hst : (U256AddBeSAsm.addCarryState a b orig 0) = (orig, 0) := rfl
    rw [hst]
    simp [h0 a hla, h0 b hlb, h0 orig hlo, EvmAsm.Crypto.beBytesToNat]
  | succ k ih =>
    obtain ⟨ihEq, ihC⟩ := ih (by omega)
    have hstlen : (U256AddBeSAsm.addCarryState a b orig k).1.length = 32 := by
      rw [U256AddBeSAsm.addCarryState_length]; exact hlo
    have hstep : U256AddBeSAsm.addCarryState a b orig (k + 1) =
        ((U256AddBeSAsm.addCarryState a b orig k).1.set (31 - k)
            (U256AddBeSAsm.addCarryByte (a.getD (31 - k) 0) (b.getD (31 - k) 0)
              (U256AddBeSAsm.addCarryState a b orig k).2).1,
          (U256AddBeSAsm.addCarryByte (a.getD (31 - k) 0) (b.getD (31 - k) 0)
            (U256AddBeSAsm.addCarryState a b orig k).2).2) := rfl
    obtain ⟨hdig, hcar⟩ :=
      addCarryByte_digit (a.getD (31 - k) 0) (b.getD (31 - k) 0)
        (U256AddBeSAsm.addCarryState a b orig k).2 ihC
    rw [hstep]
    refine ⟨?_, hcar⟩
    have hidx : 32 - (k + 1) = 31 - k := by omega
    rw [hidx]
    rw [drop_set_self _ _ _
      (by omega : 31 - k < (U256AddBeSAsm.addCarryState a b orig k).1.length)]
    rw [EvmAsm.Crypto.beBytesToNat_cons, List.length_drop, hstlen]
    rw [EvmAsm.Crypto.beBytesToNat_drop_succ a (31 - k) (by omega),
      EvmAsm.Crypto.beBytesToNat_drop_succ b (31 - k) (by omega), hla, hlb]
    have hsucc : 31 - k + 1 = 32 - k := by omega
    have hexp : 32 - (32 - k) = k := by omega
    have hexp2 : 32 - (31 - k) - 1 = k := by omega
    rw [hsucc, hexp, hexp2, Nat.pow_succ]
    calc (U256AddBeSAsm.addCarryByte (a.getD (31 - k) 0) (b.getD (31 - k) 0)
              (U256AddBeSAsm.addCarryState a b orig k).2).1.toNat * 256 ^ k
            + EvmAsm.Crypto.beBytesToNat
                (List.drop (32 - k) (U256AddBeSAsm.addCarryState a b orig k).1)
            + 256 ^ k * 256 * (U256AddBeSAsm.addCarryByte (a.getD (31 - k) 0)
                (b.getD (31 - k) 0) (U256AddBeSAsm.addCarryState a b orig k).2).2.toNat
        = 256 ^ k * ((U256AddBeSAsm.addCarryByte (a.getD (31 - k) 0) (b.getD (31 - k) 0)
              (U256AddBeSAsm.addCarryState a b orig k).2).1.toNat
            + 256 * (U256AddBeSAsm.addCarryByte (a.getD (31 - k) 0) (b.getD (31 - k) 0)
              (U256AddBeSAsm.addCarryState a b orig k).2).2.toNat)
            + EvmAsm.Crypto.beBytesToNat
                (List.drop (32 - k) (U256AddBeSAsm.addCarryState a b orig k).1) := by ring
      _ = 256 ^ k * ((a.getD (31 - k) 0).toNat + (b.getD (31 - k) 0).toNat
              + (U256AddBeSAsm.addCarryState a b orig k).2.toNat)
            + EvmAsm.Crypto.beBytesToNat
                (List.drop (32 - k) (U256AddBeSAsm.addCarryState a b orig k).1) := by
          rw [hdig]
      _ = (a.getD (31 - k) 0).toNat * 256 ^ k + (b.getD (31 - k) 0).toNat * 256 ^ k
            + (EvmAsm.Crypto.beBytesToNat
                (List.drop (32 - k) (U256AddBeSAsm.addCarryState a b orig k).1)
              + 256 ^ k * (U256AddBeSAsm.addCarryState a b orig k).2.toNat) := by ring
      _ = (a.getD (31 - k) 0).toNat * 256 ^ k + (b.getD (31 - k) 0).toNat * 256 ^ k
            + (EvmAsm.Crypto.beBytesToNat (List.drop (32 - k) a)
              + EvmAsm.Crypto.beBytesToNat (List.drop (32 - k) b)) := by rw [ihEq]
      _ = _ := by ring

private theorem be32_eq : (256 : Nat) ^ 32 = 2 ^ 256 := by decide

/-- The output buffer keeps its 32-byte width. -/
theorem u256AddBeBytes_length (a b orig : List (BitVec 8)) (hlo : orig.length = 32) :
    (U256AddBeSAsm.u256AddBeBytes a b orig).length = 32 := by
  rw [U256AddBeSAsm.u256AddBeBytes, U256AddBeSAsm.addCarryState_length]; exact hlo

/-- **`u256_add_be` adds, exactly.** The 32-byte result together with the returned
    carry accounts for the full 257-bit sum of the two inputs.

    Together with `u256AddBeFlat_spec` this gives the routine a numeric contract:
    the window at `a2` and the flag in `a0` are the truncated sum and its overflow
    bit, with no residual dependence on `orig` — every byte is overwritten. -/
theorem beBytesToNat_u256AddBeBytes (a b orig : List (BitVec 8))
    (hla : a.length = 32) (hlb : b.length = 32) (hlo : orig.length = 32) :
    EvmAsm.Crypto.beBytesToNat (U256AddBeSAsm.u256AddBeBytes a b orig)
        + 2 ^ 256 * (U256AddBeSAsm.u256AddBeCarry a b orig).toNat
      = EvmAsm.Crypto.beBytesToNat a + EvmAsm.Crypto.beBytesToNat b := by
  obtain ⟨hEq, _⟩ := addCarryState_be a b orig hla hlb hlo 32 (Nat.le_refl _)
  rw [U256AddBeSAsm.u256AddBeBytes, U256AddBeSAsm.u256AddBeCarry, ← be32_eq]
  simpa using hEq

/-- The same fact in the form a caller wants: the result is the sum reduced mod
    `2 ^ 256`, and the carry is exactly the overflow predicate. -/
theorem u256AddBe_mod_and_carry (a b orig : List (BitVec 8))
    (hla : a.length = 32) (hlb : b.length = 32) (hlo : orig.length = 32) :
    EvmAsm.Crypto.beBytesToNat (U256AddBeSAsm.u256AddBeBytes a b orig)
        = (EvmAsm.Crypto.beBytesToNat a + EvmAsm.Crypto.beBytesToNat b) % 2 ^ 256
    ∧ (U256AddBeSAsm.u256AddBeCarry a b orig).toNat
        = if 2 ^ 256 ≤ EvmAsm.Crypto.beBytesToNat a + EvmAsm.Crypto.beBytesToNat b
          then 1 else 0 := by
  have hmain := beBytesToNat_u256AddBeBytes a b orig hla hlb hlo
  obtain ⟨_, hc⟩ := addCarryState_be a b orig hla hlb hlo 32 (Nat.le_refl _)
  have hcar : (U256AddBeSAsm.u256AddBeCarry a b orig).toNat ≤ 1 := hc
  have hlt : EvmAsm.Crypto.beBytesToNat (U256AddBeSAsm.u256AddBeBytes a b orig)
      < 2 ^ 256 := by
    have h := EvmAsm.Crypto.beBytesToNat_lt (U256AddBeSAsm.u256AddBeBytes a b orig)
    rw [u256AddBeBytes_length a b orig hlo] at h
    simpa using h
  interval_cases h : (U256AddBeSAsm.u256AddBeCarry a b orig).toNat
  · simp only [Nat.mul_zero, Nat.add_zero] at hmain
    rw [← hmain]
    refine ⟨(Nat.mod_eq_of_lt hlt).symm, ?_⟩
    rw [if_neg (by omega)]
  · rw [Nat.mul_one] at hmain
    have hge : 2 ^ 256 ≤ EvmAsm.Crypto.beBytesToNat a + EvmAsm.Crypto.beBytesToNat b := by
      omega
    refine ⟨?_, by rw [if_pos hge]⟩
    have hsplit : EvmAsm.Crypto.beBytesToNat a + EvmAsm.Crypto.beBytesToNat b
        = EvmAsm.Crypto.beBytesToNat (U256AddBeSAsm.u256AddBeBytes a b orig)
          + 2 ^ 256 := by omega
    rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

-- Non-vacuity for the adder: the WRAP case is the one an operational post cannot
-- express, so it is checked concretely. `orig` is fully overwritten, so starting
-- from the all-zero buffer is not special.
private def zeros32 : List (BitVec 8) := List.replicate 32 (0 : BitVec 8)
private def ones32 : List (BitVec 8) := List.replicate 32 (0xff : BitVec 8)
private def one32 : List (BitVec 8) := List.replicate 31 (0 : BitVec 8) ++ [(1 : BitVec 8)]
private def two32 : List (BitVec 8) := List.replicate 31 (0 : BitVec 8) ++ [(2 : BitVec 8)]

#guard EvmAsm.Crypto.beBytesToNat ones32 = 2 ^ 256 - 1
#guard EvmAsm.Crypto.beBytesToNat (U256AddBeSAsm.u256AddBeBytes ones32 one32 zeros32) = 0
#guard (U256AddBeSAsm.u256AddBeCarry ones32 one32 zeros32).toNat = 1
#guard EvmAsm.Crypto.beBytesToNat (U256AddBeSAsm.u256AddBeBytes one32 two32 zeros32) = 3
#guard (U256AddBeSAsm.u256AddBeCarry one32 two32 zeros32).toNat = 0
#guard EvmAsm.Crypto.beBytesToNat (U256AddBeSAsm.u256AddBeBytes ones32 ones32 zeros32)
    = 2 ^ 256 - 2

end EvmAsm.Codegen.U256BeFlat
