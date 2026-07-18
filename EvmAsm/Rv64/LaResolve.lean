/-
  EvmAsm.Rv64.LaResolve

  **The `la` (AUIPC/ADDI address-materialization) resolution model**
  (bead evm-asm-85699; subsumes the arithmetic half of 4ch8f.59.1.1).

  The emitter materializes a global `.data` address with the standard
  RISC-V `la` idiom

  ```
    auipc rd, %pcrel_hi(sym)     -- rd := pc + sext32→64(hi << 12)
    addi  rd, rd, %pcrel_lo(sym) -- rd := rd + sext12(lo)
  ```

  Until now the terminating `.conditional` specs (RETURN / REVERT /
  SELFDESTRUCT and the guarded-handler family) carried the resolution as
  ASSUMED hypotheses (`hla1`/`hla2`/…):

  ```
    pc + ((hi.zeroExtend 32) <<< 12).signExtend 64 + signExtend12 lo = sym
  ```

  This module PROVES that arithmetic instead:

  * `laHi`/`laLo` — the psABI `%pcrel_hi`/`%pcrel_lo` immediates as
    functions of the AUIPC pc and the target (`hi = trunc20((Δ + 0x800)
    >>> 12)`, `lo = trunc12 Δ`, `Δ = target − pc`);
  * `la_resolve` — the round-trip: whenever the displacement is
    representable (`laInRange`: signed Δ ∈ (−2³¹, 2³¹ − 2¹¹)), the
    materialized address IS the target.  Fully generic, kernel-checked
    (per-bit-free: `toNat` decomposition + `omega`);
  * `la_materialize_within` — the two-instruction `cpsTripleWithin`:
    executing the emitted pair at `pc` yields `rd ↦ᵣ target`.

  Consumers instantiate `hi := laHi pc sym`, `lo := laLo pc sym`, discharge
  `laInRange` (decidable — for linked layouts Δ is a few MB), and the former
  `hla*` hypotheses become `la_resolve` facts
  (`Terminating/ReturnHaltResolved.lean` retires RETURN's).
-/

import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Rv64

/-- `%pcrel_lo`: the low 12 bits of the displacement. -/
def laLo (pc target : Word) : BitVec 12 := (target - pc).truncate 12

/-- `%pcrel_hi`: the high 20 bits of the displacement, rounded so the
    sign-extended low part corrects exactly (`+ 0x800` carries the low
    half's sign bit into the upper immediate). -/
def laHi (pc target : Word) : BitVec 20 :=
  (((target - pc) + 0x800) >>> 12).truncate 20

/-- Representability of the displacement: signed `target − pc` in
    `(−2³¹, 2³¹ − 2¹¹)` — the `auipc`+`addi` reach.  Decidable; concrete
    linked layouts discharge it by `decide`. -/
def laInRange (pc target : Word) : Prop :=
  (target - pc).toNat < 2 ^ 31 - 2 ^ 11 ∨ 2 ^ 64 - 2 ^ 31 ≤ (target - pc).toNat

instance (pc target : Word) : Decidable (laInRange pc target) := by
  unfold laInRange
  infer_instance

/-- **The `la` round-trip**: the psABI immediates materialize exactly the
    target.  This is the arithmetic the `hla*` reconstruction hypotheses
    of the terminating specs assumed — now proven, for every in-range
    displacement. -/
theorem la_resolve (pc target : Word) (h : laInRange pc target) :
    pc + (((laHi pc target).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
      + signExtend12 (laLo pc target) = target := by
  unfold laInRange at h
  apply BitVec.eq_of_toNat_eq
  have hpc : pc.toNat < 2 ^ 64 := pc.isLt
  have htg : target.toNat < 2 ^ 64 := target.isLt
  have hdN : (target - pc).toNat = (2 ^ 64 - pc.toNat + target.toNat) % 2 ^ 64 :=
    BitVec.toNat_sub target pc
  have hhiLt : (laHi pc target).toNat < 2 ^ 20 := (laHi pc target).isLt
  -- lo
  have hlo : (laLo pc target).toNat = (target - pc).toNat % 2 ^ 12 := by
    show (BitVec.setWidth 12 (target - pc)).toNat = _
    rw [BitVec.toNat_setWidth]
  have hloMsb : (laLo pc target).msb = decide (2 ^ 11 ≤ (laLo pc target).toNat) := by
    rw [BitVec.msb_eq_decide]
  -- hi
  have hhi : (laHi pc target).toNat
      = (((target - pc).toNat + 2048) % 2 ^ 64) / 2 ^ 12 % 2 ^ 20 := by
    show (BitVec.setWidth 20 (((target - pc) + 0x800) >>> 12)).toNat = _
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add,
      Nat.shiftRight_eq_div_pow]
    rfl
  -- zeroExtend + shift
  have hz : ((laHi pc target).zeroExtend 32).toNat = (laHi pc target).toNat := by
    show (BitVec.setWidth 32 (laHi pc target)).toNat = _
    rw [BitVec.toNat_setWidth]
    omega
  have hs : (((laHi pc target).zeroExtend 32 : BitVec 32) <<< 12).toNat
      = (laHi pc target).toNat * 4096 := by
    rw [BitVec.toNat_shiftLeft, hz, Nat.shiftLeft_eq]
    have : (laHi pc target).toNat * 2 ^ 12 < 2 ^ 32 := by omega
    omega
  have hsMsb : ((((laHi pc target).zeroExtend 32 : BitVec 32) <<< 12)).msb
      = decide (2 ^ 31 ≤ (((laHi pc target).zeroExtend 32 : BitVec 32) <<< 12).toNat) := by
    rw [BitVec.msb_eq_decide]
  -- the two sign extensions, as `toNat` case splits
  have hX : ((((laHi pc target).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64).toNat
      = (laHi pc target).toNat * 4096
        + (if 2 ^ 31 ≤ (laHi pc target).toNat * 4096 then 2 ^ 64 - 2 ^ 32 else 0) := by
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, hsMsb, hs]
    have hmod : ((laHi pc target).toNat * 4096) % 2 ^ 64
        = (laHi pc target).toNat * 4096 := by omega
    rw [hmod]
    by_cases hc : 2 ^ 31 ≤ (laHi pc target).toNat * 4096
    · simp [hc]
    · simp [hc]
  have hY : (signExtend12 (laLo pc target)).toNat
      = (target - pc).toNat % 2 ^ 12
        + (if 2 ^ 11 ≤ (target - pc).toNat % 2 ^ 12 then 2 ^ 64 - 2 ^ 12 else 0) := by
    unfold signExtend12
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, hloMsb, hlo]
    have hmod : (target - pc).toNat % 2 ^ 12 % 2 ^ 64
        = (target - pc).toNat % 2 ^ 12 := by omega
    rw [hmod]
    by_cases hc : 2 ^ 11 ≤ (target - pc).toNat % 2 ^ 12
    · simp
    · simp
  rw [BitVec.toNat_add, BitVec.toNat_add, hX, hY, hhi]
  by_cases h1 : 2 ^ 31 ≤ (((target - pc).toNat + 2048) % 2 ^ 64) / 2 ^ 12 % 2 ^ 20 * 4096 <;>
    by_cases h2 : 2 ^ 11 ≤ (target - pc).toNat % 2 ^ 12 <;>
      simp only [h1, h2, if_true, if_false] <;>
        omega

/-- **`la` as a two-instruction triple**: the emitted
    `auipc rd, laHi ; addi rd, rd, laLo` at `pc` materializes the target
    address in `rd` — the address PROVEN, not assumed.  Code membership is
    hypothesis-shaped so consumers lift into their routine's single
    `CodeReq` (e.g. via the `code_mem` tactic). -/
theorem la_materialize_within (rd : Reg) (vOld pc target : Word) {cr : CodeReq}
    (hrd : rd ≠ .x0) (hrange : laInRange pc target)
    (hau : ∀ a i, CodeReq.singleton pc (.AUIPC rd (laHi pc target)) a = some i →
      cr a = some i)
    (had : ∀ a i, CodeReq.singleton (pc + 4) (.ADDI rd rd (laLo pc target)) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 pc (pc + 8) cr (rd ↦ᵣ vOld) (rd ↦ᵣ target) := by
  have h1 := cpsTripleWithin_extend_code hau
    (auipc_spec_within rd vOld (laHi pc target) pc hrd)
  have h2 := cpsTripleWithin_extend_code had
    (addi_spec_same_within rd
      (pc + (((laHi pc target).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)
      (laLo pc target) (pc + 4) hrd)
  rw [la_resolve pc target hrange,
    show (pc + 4 : Word) + 4 = pc + 8 from by bv_omega] at h2
  exact cpsTripleWithin_seq_same_cr h1 h2

end EvmAsm.Rv64
