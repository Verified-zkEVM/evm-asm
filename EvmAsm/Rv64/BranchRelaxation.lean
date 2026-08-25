/-
  EvmAsm.Rv64.BranchRelaxation

  Semantics of the **assembler's branch relaxation**, for the handler lane
  (GH #12204 decision 1).

  ## Why this exists

  A conditional branch to a far target does not survive assembly as one
  instruction. B-type reach is ±4 KiB, and every dispatcher handler branches to
  the dispatcher-owned `.exit_outofgas` roughly 65 KB away, so GNU-as **relaxes**
  each site into a two-instruction pair with the *inverted* condition skipping
  over an unconditional jump:

  ```
    beq  rs1, rs2, .exit_outofgas        -- source
  ⇒ bne  rs1, rs2, .+8                   -- relaxed: skip the jump when NOT equal
    j    .exit_outofgas
  ```

  The linked image therefore contains the **pair**, so any `Program` faithful to
  the image contains the pair too — which is what makes the instruction count a
  function of the link layout rather than the source text (the #12128
  measurement, and the reason `AsmSym.br` exists in `Codegen/Emit.lean`).

  ## What the lemmas below buy

  Without them, every handler triple that crosses one of these ~130 sites has to
  case-split on a two-instruction dance and reason about an intermediate PC that
  corresponds to nothing in the source. These lemmas collapse the pair back to
  the single conditional branch the author wrote:

  * **taken** ⇒ two steps land at the far target;
  * **not taken** ⇒ one step lands at `pc + 8`.

  ⚠️ Note the fall-through is `pc + 8`, **not** `pc + 4`: the pair occupies eight
  bytes, so "the instruction after the branch" is two words along. That offset is
  the whole reason a hand-written triple over a relaxed site is easy to get wrong,
  and it is why these are stated as lemmas rather than left to `simp`.

  ## Coverage

  Complete for the conditions that actually occur at far-branch sites in
  `EvmAsm/Codegen/`, measured by grepping branches targeting `.exit_outofgas`:
  `bltu` (65 sites), `bnez` (55), `bgeu` (5), `beq` (5). Those close under
  inversion into two pairs — {`BEQ`, `BNE`} and {`BLTU`, `BGEU`} — and all four
  relaxations are proved here. `bnez rs` is `BNE rs x0`, so it is the `BNE` case
  with `rs2 := .x0` and needs nothing extra.

  `BLT`/`BGE` do not occur at far-branch sites today; if one appears, add its
  pair here rather than inlining the reasoning at the use site.

  ## Trust

  These lemmas are about the **Lean `step` semantics of the relaxed pair**. That
  GNU-as produces exactly this pair for a far branch is an assembler fact, not a
  Lean theorem — it is checked by the byte-identity gate (`cmp` against the
  linked image), not here. Keep the two claims distinct when citing this file.
-/

module

public import EvmAsm.Rv64.Execution

@[expose] public section

namespace EvmAsm.Rv64
namespace BranchRelaxation

/-! ## The jump leg

`j target` is `JAL x0`, and `setReg .x0` is definitionally the identity
(`Basic.lean:275`), so the jump leg is a pure PC change — it does not clobber a
link register the way a `jal ra` would. Isolating that here keeps it out of each
relaxation proof. -/

/-- The `j` leg of a relaxed pair moves the PC and touches nothing else. -/
theorem step_j (s : MachineState) (joff : BitVec 21)
    (hcode : s.code s.pc = some (.JAL .x0 joff)) :
    step s = some (s.setPC (s.pc + signExtend21 joff)) := by
  unfold step
  rw [hcode]
  rfl

/-! ## Relaxation of `beq` (inverted skip is `bne`)

The source branch is `beq rs1, rs2, target`; the image holds
`bne rs1, rs2, .+8` followed by `j target`. -/

/-- `beq` relaxed, **taken** leg: equal operands fall through the inverted `bne`
    into the jump, so two steps reach the far target. -/
theorem beq_relaxed_taken (s : MachineState) (rs1 rs2 : Reg) (joff : BitVec 21)
    (hbr : s.code s.pc = some (.BNE rs1 rs2 8))
    (hj : s.code (s.pc + 4) = some (.JAL .x0 joff))
    (heq : s.getReg rs1 = s.getReg rs2) :
    stepN 2 s = some (s.setPC ((s.pc + 4) + signExtend21 joff)) := by
  have hfirst : step s = some (s.setPC (s.pc + 4)) := by
    unfold step
    rw [hbr]
    simp [execInstrBr, heq]
  have hpc : (s.setPC (s.pc + 4)).pc = s.pc + 4 := rfl
  have hcode' : (s.setPC (s.pc + 4)).code (s.setPC (s.pc + 4)).pc
      = some (.JAL .x0 joff) := by
    rw [hpc]; exact hj
  have hsecond := step_j (s.setPC (s.pc + 4)) joff hcode'
  rw [hpc] at hsecond
  simp only [stepN, hfirst]
  show (step (s.setPC (s.pc + 4))).bind (fun x => some x) = _
  rw [hsecond]
  rfl

/-- `beq` relaxed, **not-taken** leg: unequal operands take the inverted `bne`
    over the jump, landing at `pc + 8` — the instruction after the *pair*. -/
theorem beq_relaxed_not_taken (s : MachineState) (rs1 rs2 : Reg)
    (hbr : s.code s.pc = some (.BNE rs1 rs2 8))
    (hne : s.getReg rs1 ≠ s.getReg rs2) :
    step s = some (s.setPC (s.pc + 8)) := by
  unfold step
  rw [hbr]
  simp [execInstrBr, hne, signExtend13]

/-! ## Relaxation of `bne` (inverted skip is `beq`)

This is the `bnez` case too: `bnez rs` is `BNE rs x0`. -/

/-- `bne` relaxed, **taken** leg. -/
theorem bne_relaxed_taken (s : MachineState) (rs1 rs2 : Reg) (joff : BitVec 21)
    (hbr : s.code s.pc = some (.BEQ rs1 rs2 8))
    (hj : s.code (s.pc + 4) = some (.JAL .x0 joff))
    (hne : s.getReg rs1 ≠ s.getReg rs2) :
    stepN 2 s = some (s.setPC ((s.pc + 4) + signExtend21 joff)) := by
  have hfirst : step s = some (s.setPC (s.pc + 4)) := by
    unfold step
    rw [hbr]
    simp [execInstrBr, hne]
  have hpc : (s.setPC (s.pc + 4)).pc = s.pc + 4 := rfl
  have hcode' : (s.setPC (s.pc + 4)).code (s.setPC (s.pc + 4)).pc
      = some (.JAL .x0 joff) := by
    rw [hpc]; exact hj
  have hsecond := step_j (s.setPC (s.pc + 4)) joff hcode'
  rw [hpc] at hsecond
  simp only [stepN, hfirst]
  show (step (s.setPC (s.pc + 4))).bind (fun x => some x) = _
  rw [hsecond]
  rfl

/-- `bne` relaxed, **not-taken** leg. -/
theorem bne_relaxed_not_taken (s : MachineState) (rs1 rs2 : Reg)
    (hbr : s.code s.pc = some (.BEQ rs1 rs2 8))
    (heq : s.getReg rs1 = s.getReg rs2) :
    step s = some (s.setPC (s.pc + 8)) := by
  unfold step
  rw [hbr]
  simp [execInstrBr, heq, signExtend13]

/-! ## Relaxation of `bltu` (inverted skip is `bgeu`) -/

/-- `bltu` relaxed, **taken** leg. -/
theorem bltu_relaxed_taken (s : MachineState) (rs1 rs2 : Reg) (joff : BitVec 21)
    (hbr : s.code s.pc = some (.BGEU rs1 rs2 8))
    (hj : s.code (s.pc + 4) = some (.JAL .x0 joff))
    (hlt : BitVec.ult (s.getReg rs1) (s.getReg rs2)) :
    stepN 2 s = some (s.setPC ((s.pc + 4) + signExtend21 joff)) := by
  have hfirst : step s = some (s.setPC (s.pc + 4)) := by
    unfold step
    rw [hbr]
    simp [execInstrBr, hlt]
  have hpc : (s.setPC (s.pc + 4)).pc = s.pc + 4 := rfl
  have hcode' : (s.setPC (s.pc + 4)).code (s.setPC (s.pc + 4)).pc
      = some (.JAL .x0 joff) := by
    rw [hpc]; exact hj
  have hsecond := step_j (s.setPC (s.pc + 4)) joff hcode'
  rw [hpc] at hsecond
  simp only [stepN, hfirst]
  show (step (s.setPC (s.pc + 4))).bind (fun x => some x) = _
  rw [hsecond]
  rfl

/-- `bltu` relaxed, **not-taken** leg. -/
theorem bltu_relaxed_not_taken (s : MachineState) (rs1 rs2 : Reg)
    (hbr : s.code s.pc = some (.BGEU rs1 rs2 8))
    (hge : ¬ BitVec.ult (s.getReg rs1) (s.getReg rs2)) :
    step s = some (s.setPC (s.pc + 8)) := by
  unfold step
  rw [hbr]
  simp [execInstrBr, hge, signExtend13]

/-! ## Relaxation of `bgeu` (inverted skip is `bltu`) -/

/-- `bgeu` relaxed, **taken** leg. -/
theorem bgeu_relaxed_taken (s : MachineState) (rs1 rs2 : Reg) (joff : BitVec 21)
    (hbr : s.code s.pc = some (.BLTU rs1 rs2 8))
    (hj : s.code (s.pc + 4) = some (.JAL .x0 joff))
    (hge : ¬ BitVec.ult (s.getReg rs1) (s.getReg rs2)) :
    stepN 2 s = some (s.setPC ((s.pc + 4) + signExtend21 joff)) := by
  have hfirst : step s = some (s.setPC (s.pc + 4)) := by
    unfold step
    rw [hbr]
    simp [execInstrBr, hge]
  have hpc : (s.setPC (s.pc + 4)).pc = s.pc + 4 := rfl
  have hcode' : (s.setPC (s.pc + 4)).code (s.setPC (s.pc + 4)).pc
      = some (.JAL .x0 joff) := by
    rw [hpc]; exact hj
  have hsecond := step_j (s.setPC (s.pc + 4)) joff hcode'
  rw [hpc] at hsecond
  simp only [stepN, hfirst]
  show (step (s.setPC (s.pc + 4))).bind (fun x => some x) = _
  rw [hsecond]
  rfl

/-- `bgeu` relaxed, **not-taken** leg. -/
theorem bgeu_relaxed_not_taken (s : MachineState) (rs1 rs2 : Reg)
    (hbr : s.code s.pc = some (.BLTU rs1 rs2 8))
    (hlt : BitVec.ult (s.getReg rs1) (s.getReg rs2)) :
    step s = some (s.setPC (s.pc + 8)) := by
  unfold step
  rw [hbr]
  simp [execInstrBr, hlt, signExtend13]

/-! ## Non-vacuity

Every lemma above is conditioned on a `s.code` fact plus a register comparison,
so none is vacuous for want of a satisfiable hypothesis — but "the hypotheses are
satisfiable" is worth exhibiting rather than asserting, since a `code` function
that cannot hold two specific instructions at adjacent addresses would make the
whole file empty.

The witness below is deliberately *both* legs of one site: the same code function
serves the taken and not-taken lemmas, differing only in the register values. -/

/-- A code function holding a relaxed `beq` pair at `0x80000000`. -/
def witnessCode (joff : BitVec 21) : Word → Option Instr := fun a =>
  if a = 0x80000000#64 then some (.BNE .x5 .x6 8)
  else if a = 0x80000004#64 then some (.JAL .x0 joff)
  else none

theorem witnessCode_br (joff : BitVec 21) :
    witnessCode joff 0x80000000#64 = some (.BNE .x5 .x6 8) := by
  simp [witnessCode]

theorem witnessCode_j (joff : BitVec 21) :
    witnessCode joff (0x80000000#64 + 4) = some (.JAL .x0 joff) := by
  have h : (0x80000000#64 : Word) + 4 = 0x80000004#64 := by decide
  rw [h]
  simp [witnessCode]

end BranchRelaxation
end EvmAsm.Rv64
