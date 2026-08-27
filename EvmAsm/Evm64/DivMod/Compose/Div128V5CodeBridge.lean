/-
  EvmAsm.Evm64.DivMod.Compose.Div128V5CodeBridge

  Code-subsumption bridges for the v5 div128 composition: the full step-1
  and step-2 block CodeReqs (unions of per-instruction singletons) are
  included in `ofProg (base + div128Off) divK_div128_v5`.

  These are the `hmono` witnesses needed by `div128_v5_spec` (Div128V5.lean)
  to extend each block spec — stated over its own block code at an offset —
  to the single `ofProg`-of-the-whole-program code requirement.

  Mirror of the per-instruction `d128_v4_sub` peeling in
  `Compose/Div128V4.lean` (lines 213-238, 276-280), but bridging the
  union-of-blocks v5 step codes rather than v4's `ofProg` sub-programs.

  Bead `evm-asm-wbc4i.6.14.1` / `evm-asm-wbc4i.6.14.2` (V5.6.15a/b).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.Base
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1FullV5
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2FullV5

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Singleton at index `k` of `divK_div128_v5` ⊆ `ofProg`-based v5 cr.
    Mirrors `d128_v4_sub` but uses `divK_div128_v5`. -/
theorem d128_v5_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128_v5.length)
    (h_addr : addr = (base + div128Off) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128_v5.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (CodeReq.ofProg (base + div128Off) divK_div128_v5) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => CodeReq.singleton_mono
    (CodeReq.ofProg_lookup (base + div128Off) divK_div128_v5 k hk (by decide)) a i h

/-- The full v5 step-1 block code (instrs [10..40], placed at
    `base + div128Off + 40`) is included in `ofProg divK_div128_v5`. -/
theorem step1FullV5Code_sub_v5 {base : Word} :
    ∀ a i, divKDiv128Step1FullV5Code (base + div128Off + 40) a = some i →
      (CodeReq.ofProg (base + div128Off) divK_div128_v5) a = some i := by
  simp only [divKDiv128Step1FullV5Code, divKDiv128Step1InitCapGuardV5Code,
    divKDiv128Step1InitCapV5Code, divKDiv128Phase1bBodyV5Code,
    divKDiv128Prodcheck1bMergedCode]
  -- FullV5 = InitCapGuard ∪ Phase1bBody
  apply CodeReq.union_sub
  · -- InitCapGuard = InitCapV5 [10..20] ∪ guard [21,22]
    apply CodeReq.union_sub
    · -- InitCapV5 [10..20]
      apply CodeReq.union_sub; · exact d128_v5_sub 10 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 11 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 12 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 13 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 14 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 15 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 16 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 17 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 18 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 19 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 20 _ _ (by decide) (by bv_addr) (by decide)
    · -- guard [21,22]
      apply CodeReq.union_sub; · exact d128_v5_sub 21 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 22 _ _ (by decide) (by bv_addr) (by decide)
  · -- Phase1bBody = leading8 [23..30] ∪ merged [31..40]
    apply CodeReq.union_sub
    · -- leading8 [23..30]
      apply CodeReq.union_sub; · exact d128_v5_sub 23 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 24 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 25 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 26 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 27 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 28 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 29 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 30 _ _ (by decide) (by bv_addr) (by decide)
    · -- merged [31..40]
      apply CodeReq.union_sub; · exact d128_v5_sub 31 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 32 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 33 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 34 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 35 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 36 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 37 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 38 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 39 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 40 _ _ (by decide) (by bv_addr) (by decide)

/-- The full v5 step-2 block code (instrs [46..80], placed at
    `base + div128Off + 184`) is included in `ofProg divK_div128_v5`. -/
theorem step2FullV5Code_sub_v5 {base : Word} :
    ∀ a i, divKDiv128Step2FullV5Code (base + div128Off + 184) a = some i →
      (CodeReq.ofProg (base + div128Off) divK_div128_v5) a = some i := by
  simp only [divKDiv128Step2FullV5Code, divKDiv128Step2InitCapGuardV5Code,
    divKDiv128Step2InitCapV5Code, divKDiv128Phase2bBodyV5Code,
    divKDiv128Prodcheck2bV5MergedCode]
  -- FullV5 = InitCapGuard ∪ Phase2bBody
  apply CodeReq.union_sub
  · -- InitCapGuard = InitCapV5 [46..56] ∪ guard [57,58]
    apply CodeReq.union_sub
    · -- InitCapV5 [46..56]
      apply CodeReq.union_sub; · exact d128_v5_sub 46 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 47 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 48 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 49 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 50 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 51 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 52 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 53 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 54 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 55 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 56 _ _ (by decide) (by bv_addr) (by decide)
    · -- guard [57,58]
      apply CodeReq.union_sub; · exact d128_v5_sub 57 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 58 _ _ (by decide) (by bv_addr) (by decide)
  · -- Phase2bBody = spill [59..70] ∪ merged [71..80]
    apply CodeReq.union_sub
    · -- spill [59..70]
      apply CodeReq.union_sub; · exact d128_v5_sub 59 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 60 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 61 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 62 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 63 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 64 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 65 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 66 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 67 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 68 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 69 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 70 _ _ (by decide) (by bv_addr) (by decide)
    · -- merged [71..80]
      apply CodeReq.union_sub; · exact d128_v5_sub 71 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 72 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 73 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 74 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 75 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 76 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 77 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 78 _ _ (by decide) (by bv_addr) (by decide)
      apply CodeReq.union_sub; · exact d128_v5_sub 79 _ _ (by decide) (by bv_addr) (by decide)
      exact d128_v5_sub 80 _ _ (by decide) (by bv_addr) (by decide)

end EvmAsm.Evm64
