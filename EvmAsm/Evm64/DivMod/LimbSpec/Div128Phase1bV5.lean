/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase1bV5

  v5 div128 Phase-1b body: the two D3 corrections (1st then guarded 2nd),
  executed when the Phase-1b leading guard falls through (`rhatc < 2^32`).
  Instrs [23]-[40] of `divK_div128_v5`:
    * prodcheck1 (1st D3) — [23..30]
    * prodcheck1b (2nd D3, guarded) — [31..40]

  Composed via the disjoint-union sequencing lemma
  (`cpsTripleWithin_seq_cpsBranchWithin_with_perm`) so no flat-CR
  subsumption is needed — `crDisjoint` discharges the disjointness of the
  two singleton-union code requirements.

  Output `q1''`/`rhat''` match the `div128Quot_v5` Phase-1 result in the
  `rhatc < 2^32` regime. Bead `evm-asm-wbc4i.6` (V5.6); a building block
  of the full `step1_v5` spec.
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1b

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Code requirement for the v5 div128 Phase-1b body (instrs [23]-[40]):
    the 8 prodcheck1 singletons unioned with the prodcheck1b merged code. -/
def divKDiv128Phase1bBodyV5Code (base : Word) : CodeReq :=
  (CodeReq.union (CodeReq.singleton base (.LD .x9 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x9))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x9 .x7 32))
  (CodeReq.union (CodeReq.singleton (base + 12) (.OR .x9 .x9 .x11))
  (CodeReq.union (CodeReq.singleton (base + 16) (.BLTU .x9 .x5 8))
  (CodeReq.union (CodeReq.singleton (base + 20) (.JAL .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 24) (.ADDI .x10 .x10 4095))
   (CodeReq.singleton (base + 28) (.ADD .x7 .x7 .x6))))))))).union
  (divKDiv128Prodcheck1bMergedCode (base + 32))

/-- v5 div128 Phase-1b body (instrs [23]-[40]): prodcheck1 then prodcheck1b.
    `cpsBranchWithin` on the 2nd-D3 guard `rhat' >> 32`; both legs exit at
    base+72. Composed via disjoint-union sequencing. -/
theorem divK_div128_phase1b_body_v5_spec_within
    (sp q1c rhatc dHi un1 v9Old v5Old dlo : Word) (base : Word) :
    let qDlo1 := q1c * dlo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
    cpsBranchWithin 18 base (divKDiv128Phase1bBodyV5Code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5Old) ** (.x9 ↦ᵣ v9Old) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (base + 72)
        (divKDiv128Prodcheck1bMergedTakenPost sp q1' rhat' dHi un1 qDlo1 dlo)
      (base + 72)
        (divKDiv128Prodcheck1bMergedFTPost sp q1' rhat' dHi un1 dlo) := by
  intro qDlo1 rhatUn1 q1' rhat'
  unfold divKDiv128Phase1bBodyV5Code
  -- Block 1: prodcheck1 (1st D3) [23..30], framed with x0.
  have h1_raw := divK_div128_prodcheck1_merged_spec_within sp q1c rhatc dHi un1 v9Old v5Old dlo base
  have h1f := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) h1_raw
  -- Block 2: prodcheck1b (2nd D3) [31..40] at base+32.
  have h2_raw := divK_div128_prodcheck1b_merged_spec_within sp q1' rhat' dHi un1
    rhatUn1 qDlo1 dlo (base + 32)
  have he : (base + 32 : Word) + 40 = base + 72 := by bv_addr
  rw [he] at h2_raw
  unfold divKDiv128Prodcheck1bMergedPre at h2_raw
  have composed := cpsTripleWithin_seq_cpsBranchWithin_with_perm
    (by unfold divKDiv128Prodcheck1bMergedCode; crDisjoint)
    (fun h hp => by xperm_hyp hp) h1f h2_raw
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => hp)
    (fun h hp => hp)
    composed

end EvmAsm.Evm64
