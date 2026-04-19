/-
  EvmAsm.Evm64.DivMod.LimbSpec.CLZ

  CPS specs for the count-leading-zeros subcircuit used by the Knuth
  Algorithm D shift computation:
    * `divK_clz_init_spec` — single ADDI x6 x0 0 that zeros the counter.
    * `divK_clz_stage_prog` / `_code` — 4-instruction SRLI+BNE+SLLI+ADDI
      stage, parameterized by the per-stage shamt (K/M_s) and count
      increment (M_a).
    * `divK_clz_stage_{taken,ntaken}_spec` — deterministic per-path specs
      obtained by `cpsBranch_elim_{taken,ntaken}` from the single branch.
    * `divK_clz_last_prog` / `_code` — 3-instruction SRLI+BNE(8)+ADDI
      final stage (no SLLI, BNE offset 8).
    * `divK_clz_last_{taken,ntaken}_spec` — corresponding deterministic
      specs for the last stage.

  Thirteenth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees all
  five specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.AddrNorm
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se13_8 se13_12)
open EvmAsm.Evm64.DivMod.AddrNorm (bv6_toNat_63)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CLZ init: set x6 = 0 (count register). -/
theorem divK_clz_init_spec (v6 : Word) (base : Word) :
    let cr := CodeReq.singleton base (.ADDI .x6 .x0 0)
    cpsTriple base (base + 4) cr
      ((.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ signExtend12 (0 : BitVec 12)) **
       (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := addi_x0_spec_gen .x6 v6 0 base (by nofun)
  runBlock I0

def divK_clz_stage_prog (K M_s : BitVec 6) (M_a : BitVec 12) : List Instr :=
  [.SRLI .x7 .x5 K, .BNE .x7 .x0 12, .SLLI .x5 .x5 M_s, .ADDI .x6 .x6 M_a]

abbrev divK_clz_stage_code (K M_s : BitVec 6) (M_a : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_clz_stage_prog K M_s M_a)

/-- CLZ stage, taken branch: val >>> K ≠ 0, skip SLLI+ADDI.
    x5 = val (unchanged), x6 = count (unchanged), x7 = val >>> K. -/
theorem divK_clz_stage_taken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Word)
    (hne : val >>> K.toNat ≠ 0) :
    let cr := divK_clz_stage_code K M_s M_a base
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [se13_12]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frameR
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 16)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_stage_code K M_s M_a base (base + 4) = _
        simp only [divK_clz_stage_code, divK_clz_stage_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  have taken := cpsBranch_takenPath composed (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := taken R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp') hp hpq⟩⟩

/-- CLZ stage, not-taken branch: val >>> K = 0, execute SLLI+ADDI.
    x5 = val <<< M, x6 = count + signExtend12 M, x7 = 0. -/
theorem divK_clz_stage_ntaken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Word)
    (heq : val >>> K.toNat = 0) :
    let cr := divK_clz_stage_code K M_s M_a base
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a)) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [se13_12]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frameR
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 16)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_stage_code K M_s M_a base (base + 4) = _
        simp only [divK_clz_stage_code, divK_clz_stage_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  have ntaken := cpsBranch_ntakenPath composed (fun hp hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  have I1 := slli_spec_gen_same .x5 val M_s (base + 8) (by nofun)
  have I2 := addi_spec_gen_same .x6 count M_a (base + 12) (by nofun)
  have hslli_addi : cpsTriple (base + 8) (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
      ((.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a))) := by
    runBlock I1 I2
  have hframed := cpsTriple_frameR
    ((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hslli_addi
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp')
    ntaken hframed
  exact cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => by rw [heq] at hp; xperm_hyp hp)
    full

def divK_clz_last_prog : List Instr :=
  [.SRLI .x7 .x5 63, .BNE .x7 .x0 8, .ADDI .x6 .x6 1]

abbrev divK_clz_last_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_clz_last_prog

/-- CLZ last stage, taken: val >>> 63 ≠ 0 (MSB is 1), skip ADDI.
    x5 unchanged, x6 unchanged, x7 = val >>> 63. -/
theorem divK_clz_last_taken_spec (val count v7 : Word) (base : Word)
    (hne : val >>> 63 ≠ 0) :
    let cr := divK_clz_last_code base
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 := bv6_toNat_63
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig := se13_8
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frameR
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 12)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_last_code base (base + 4) = _
        simp only [divK_clz_last_code, divK_clz_last_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  have taken := cpsBranch_takenPath composed (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := taken R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp') hp hpq⟩⟩

/-- CLZ last stage, ntaken: val >>> 63 = 0, execute ADDI.
    x5 unchanged, x6 = count + 1, x7 = 0. -/
theorem divK_clz_last_ntaken_spec (val count v7 : Word) (base : Word)
    (heq : val >>> 63 = 0) :
    let cr := divK_clz_last_code base
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ (count + signExtend12 (1 : BitVec 12))) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 := bv6_toNat_63
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig := se13_8
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frameR
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 12)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_last_code base (base + 4) = _
        simp only [divK_clz_last_code, divK_clz_last_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  have ntaken := cpsBranch_ntakenPath composed (fun hp hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  have I2 := addi_spec_gen_same .x6 count 1 (base + 8) (by nofun)
  have haddi : cpsTriple (base + 8) (base + 12) cr
      (.x6 ↦ᵣ count)
      (.x6 ↦ᵣ (count + signExtend12 (1 : BitVec 12))) := by
    runBlock I2
  have hframed := cpsTriple_frameR
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) haddi
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp')
    ntaken hframed
  exact cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => by rw [heq] at hp; xperm_hyp hp)
    full

end EvmAsm.Evm64
