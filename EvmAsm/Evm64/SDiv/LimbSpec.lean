/-
  EvmAsm.Evm64.SDiv.LimbSpec

  Per-block / per-limb cpsTriple specs for SDIV sub-blocks (sign
  extraction, abs negation, callable-divide JAL, sign-correction).

  Per `OPCODE_TEMPLATE.md`, each sub-block gets exactly one cpsTriple
  lemma; later Compose slices chain them.
-/

module

public import EvmAsm.Evm64.SDiv.Program
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.XSimp
public import EvmAsm.Rv64.Tactics.RunBlock

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64.Tactics

/-- CodeReq for `evm_sdiv_sign_bit_block` at byte offset `base`. -/
abbrev evm_sdiv_sign_bit_block_code
    (addrReg signReg : EvmAsm.Rv64.Reg) (topLimbOff : BitVec 12)
    (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_sign_bit_block addrReg signReg topLimbOff)

/-- 2-instruction leaf spec: load `topLimbOff(addrReg)` into `signReg`,
    then shift right logically by 63 to expose the top bit. The
    post-state's `signReg` holds `topLimbVal >>> 63` (i.e. `0` for
    non-negative inputs and `1` for negative inputs).

    Requires `signReg ≠ x0`; separation of `(addrReg ↦ᵣ _)` and
    `(signReg ↦ᵣ _)` in the precondition implicitly forces
    `addrReg ≠ signReg`. -/
theorem evm_sdiv_sign_bit_block_spec_within
    (addrReg signReg : EvmAsm.Rv64.Reg) (topLimbOff : BitVec 12)
    (vAddr sOld topLimbVal : Word) (base : Word)
    (hsign_ne_x0 : signReg ≠ .x0) :
    let code := evm_sdiv_sign_bit_block_code addrReg signReg topLimbOff base
    EvmAsm.Rv64.cpsTripleWithin 2 base (base + 8) code
      ((addrReg ↦ᵣ vAddr) ** (signReg ↦ᵣ sOld) **
       ((vAddr + EvmAsm.Rv64.signExtend12 topLimbOff) ↦ₘ topLimbVal))
      ((addrReg ↦ᵣ vAddr) ** (signReg ↦ᵣ (topLimbVal >>> (63 : BitVec 6).toNat)) **
       ((vAddr + EvmAsm.Rv64.signExtend12 topLimbOff) ↦ₘ topLimbVal)) := by
  have L := EvmAsm.Rv64.ld_spec_gen_within signReg addrReg vAddr sOld topLimbVal
              topLimbOff base hsign_ne_x0
  have S := EvmAsm.Rv64.srli_spec_gen_same_within signReg topLimbVal (63 : BitVec 6)
              (base + 4) hsign_ne_x0
  runBlock L S

/-- CodeReq for one conditional-negation limb step at byte offset `base`. -/
abbrev evm_sdiv_cond_negate_limb_step_code
    (addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limbOff : BitVec 12) (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base
    (evm_sdiv_cond_negate_limb_step addrReg carryInReg maskReg valueReg carryReg
      limbOff)

/-- Precondition for the SDIV conditional-negation limb step. Wrapped
    `@[irreducible]` so downstream proofs do not re-reduce the sepConj
    atoms at each use site. -/
@[irreducible]
def condNegateLimbStepPre
    (addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limbOff : BitVec 12)
    (vAddr carryIn mask valueOld carryOld limbVal : Word) : EvmAsm.Rv64.Assertion :=
  (addrReg ↦ᵣ vAddr) ** (carryInReg ↦ᵣ carryIn) **
  (maskReg ↦ᵣ mask) ** (valueReg ↦ᵣ valueOld) **
  (carryReg ↦ᵣ carryOld) ** ((vAddr + EvmAsm.Rv64.signExtend12 limbOff) ↦ₘ limbVal)

theorem condNegateLimbStepPre_unfold
    {addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg}
    {limbOff : BitVec 12}
    {vAddr carryIn mask valueOld carryOld limbVal : Word} :
    condNegateLimbStepPre addrReg carryInReg maskReg valueReg carryReg
        limbOff vAddr carryIn mask valueOld carryOld limbVal =
      ((addrReg ↦ᵣ vAddr) ** (carryInReg ↦ᵣ carryIn) **
       (maskReg ↦ᵣ mask) ** (valueReg ↦ᵣ valueOld) **
       (carryReg ↦ᵣ carryOld) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limbOff) ↦ₘ limbVal)) := by
  delta condNegateLimbStepPre
  rfl

/-- Postcondition for the SDIV conditional-negation limb step: XOR the
    limb with `mask`, add the incoming carry, and write back. Wrapped
    `@[irreducible]` to hide the 3-step let chain from consumers. -/
@[irreducible]
def condNegateLimbStepPost
    (addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limbOff : BitVec 12)
    (vAddr carryIn mask limbVal : Word) : EvmAsm.Rv64.Assertion :=
  let sum := (limbVal ^^^ mask) + carryIn
  let carryOut := if BitVec.ult sum carryIn then (1 : Word) else 0
  (addrReg ↦ᵣ vAddr) ** (carryInReg ↦ᵣ carryIn) **
  (maskReg ↦ᵣ mask) ** (valueReg ↦ᵣ sum) **
  (carryReg ↦ᵣ carryOut) ** ((vAddr + EvmAsm.Rv64.signExtend12 limbOff) ↦ₘ sum)

theorem condNegateLimbStepPost_unfold
    {addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg}
    {limbOff : BitVec 12}
    {vAddr carryIn mask limbVal : Word} :
    condNegateLimbStepPost addrReg carryInReg maskReg valueReg carryReg
        limbOff vAddr carryIn mask limbVal =
      (let sum := (limbVal ^^^ mask) + carryIn
       let carryOut := if BitVec.ult sum carryIn then (1 : Word) else 0
       (addrReg ↦ᵣ vAddr) ** (carryInReg ↦ᵣ carryIn) **
       (maskReg ↦ᵣ mask) ** (valueReg ↦ᵣ sum) **
       (carryReg ↦ᵣ carryOut) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limbOff) ↦ₘ sum)) := by
  delta condNegateLimbStepPost
  rfl

/-- Postcondition for the self-carry variant: carry-in register is the same
    as carry-out, so no separate carryInReg ownership atom appears. -/
@[irreducible]
def condNegateLimbStepSelfCarryPost
    (addrReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limbOff : BitVec 12)
    (vAddr carryIn mask limbVal : Word) : EvmAsm.Rv64.Assertion :=
  let sum := (limbVal ^^^ mask) + carryIn
  let carryOut := if BitVec.ult sum carryIn then (1 : Word) else 0
  (addrReg ↦ᵣ vAddr) ** (maskReg ↦ᵣ mask) **
  (valueReg ↦ᵣ sum) ** (carryReg ↦ᵣ carryOut) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limbOff) ↦ₘ sum)

theorem condNegateLimbStepSelfCarryPost_unfold
    {addrReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg}
    {limbOff : BitVec 12}
    {vAddr carryIn mask limbVal : Word} :
    condNegateLimbStepSelfCarryPost addrReg maskReg valueReg carryReg
        limbOff vAddr carryIn mask limbVal =
      (let sum := (limbVal ^^^ mask) + carryIn
       let carryOut := if BitVec.ult sum carryIn then (1 : Word) else 0
       (addrReg ↦ᵣ vAddr) ** (maskReg ↦ᵣ mask) **
       (valueReg ↦ᵣ sum) ** (carryReg ↦ᵣ carryOut) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limbOff) ↦ₘ sum)) := by
  delta condNegateLimbStepSelfCarryPost
  rfl

/-- 5-instruction conditional-negation limb step with the incoming carry
    held in a separate register: `LD; XOR; ADD; SLTU; SD`. This is the
    leaf used for limb 0 of the 256-bit SDIV conditional-negation block,
    where `carryInReg` is the sign register. -/
theorem evm_sdiv_cond_negate_limb_step_spec_within
    (addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limbOff : BitVec 12)
    (vAddr carryIn mask valueOld carryOld limbVal : Word) (base : Word)
    (hvalue_ne_x0 : valueReg ≠ .x0) (hcarry_ne_x0 : carryReg ≠ .x0) :
    let code :=
      evm_sdiv_cond_negate_limb_step_code addrReg carryInReg maskReg valueReg
        carryReg limbOff base
    EvmAsm.Rv64.cpsTripleWithin 5 base (base + 20) code
      (condNegateLimbStepPre addrReg carryInReg maskReg valueReg carryReg
        limbOff vAddr carryIn mask valueOld carryOld limbVal)
      (condNegateLimbStepPost addrReg carryInReg maskReg valueReg carryReg
        limbOff vAddr carryIn mask limbVal) := by
  intro code
  rw [condNegateLimbStepPre_unfold, condNegateLimbStepPost_unfold]
  let mem := vAddr + EvmAsm.Rv64.signExtend12 limbOff
  let xored := limbVal ^^^ mask
  let sum := xored + carryIn
  let carryOut := if BitVec.ult sum carryIn then (1 : Word) else 0
  have L := EvmAsm.Rv64.ld_spec_gen_within valueReg addrReg vAddr valueOld limbVal
    limbOff base hvalue_ne_x0
  have X := EvmAsm.Rv64.xor_spec_gen_rd_eq_rs1_within valueReg maskReg limbVal mask
    (base + 4) hvalue_ne_x0
  have A := EvmAsm.Rv64.add_spec_gen_rd_eq_rs1_within valueReg carryInReg xored carryIn
    (base + 8) hvalue_ne_x0
  have C := EvmAsm.Rv64.sltu_spec_gen_within carryReg valueReg carryInReg carryOld sum carryIn
    (base + 12) hcarry_ne_x0
  have S := EvmAsm.Rv64.sd_spec_gen_within addrReg valueReg vAddr sum limbVal limbOff
    (base + 16)
  runBlock L X A C S

/-- 5-instruction conditional-negation limb step for limbs 1..3, where the
    carry register is both the incoming carry source and the outgoing carry
    destination. -/
theorem evm_sdiv_cond_negate_limb_step_self_carry_spec_within
    (addrReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg) (limbOff : BitVec 12)
    (vAddr mask valueOld carryIn limbVal : Word) (base : Word)
    (hvalue_ne_x0 : valueReg ≠ .x0) (hcarry_ne_x0 : carryReg ≠ .x0) :
    let code :=
      evm_sdiv_cond_negate_limb_step_code addrReg carryReg maskReg valueReg
        carryReg limbOff base
    EvmAsm.Rv64.cpsTripleWithin 5 base (base + 20) code
      ((addrReg ↦ᵣ vAddr) ** (maskReg ↦ᵣ mask) **
       (valueReg ↦ᵣ valueOld) ** (carryReg ↦ᵣ carryIn) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limbOff) ↦ₘ limbVal))
      (condNegateLimbStepSelfCarryPost addrReg maskReg valueReg carryReg
        limbOff vAddr carryIn mask limbVal) := by
  intro code
  rw [condNegateLimbStepSelfCarryPost_unfold]
  let mem := vAddr + EvmAsm.Rv64.signExtend12 limbOff
  let xored := limbVal ^^^ mask
  let sum := xored + carryIn
  let carryOut := if BitVec.ult sum carryIn then (1 : Word) else 0
  have L := EvmAsm.Rv64.ld_spec_gen_within valueReg addrReg vAddr valueOld limbVal
    limbOff base hvalue_ne_x0
  have X := EvmAsm.Rv64.xor_spec_gen_rd_eq_rs1_within valueReg maskReg limbVal mask
    (base + 4) hvalue_ne_x0
  have A := EvmAsm.Rv64.add_spec_gen_rd_eq_rs1_within valueReg carryReg xored carryIn
    (base + 8) hvalue_ne_x0
  have C := EvmAsm.Rv64.sltu_spec_gen_rd_eq_rs2_within carryReg valueReg sum carryIn
    (base + 12) hcarry_ne_x0
  have S := EvmAsm.Rv64.sd_spec_gen_within addrReg valueReg vAddr sum limbVal limbOff
    (base + 16)
  runBlock L X A C S

/-- CodeReq for `evm_sdiv_cond_negate_256_block` at byte offset `base`. -/
abbrev evm_sdiv_cond_negate_256_block_code
    (addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12) (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base
    (evm_sdiv_cond_negate_256_block addrReg signReg maskReg valueReg carryReg
      limb0Off limb1Off limb2Off limb3Off)

/-- Precondition for the 21-instruction SDIV conditional-negation block.
    Wrapped `@[irreducible]` so downstream consumers do not re-reduce the
    sepConj atoms at each use site. -/
@[irreducible]
def condNegate256BlockPre
    (addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12)
    (vAddr sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (addrReg ↦ᵣ vAddr) **
  (signReg ↦ᵣ sign) ** (maskReg ↦ᵣ maskOld) **
  (valueReg ↦ᵣ valueOld) ** (carryReg ↦ᵣ carryOld) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb0Off) ↦ₘ limb0) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb1Off) ↦ₘ limb1) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb2Off) ↦ₘ limb2) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb3Off) ↦ₘ limb3)

theorem condNegate256BlockPre_unfold
    {addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg}
    {limb0Off limb1Off limb2Off limb3Off : BitVec 12}
    {vAddr sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    condNegate256BlockPre addrReg signReg maskReg valueReg carryReg
        limb0Off limb1Off limb2Off limb3Off
        vAddr sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (addrReg ↦ᵣ vAddr) **
       (signReg ↦ᵣ sign) ** (maskReg ↦ᵣ maskOld) **
       (valueReg ↦ᵣ valueOld) ** (carryReg ↦ᵣ carryOld) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb0Off) ↦ₘ limb0) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb1Off) ↦ₘ limb1) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb2Off) ↦ₘ limb2) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb3Off) ↦ₘ limb3)) := by
  delta condNegate256BlockPre
  rfl

/-- Postcondition for the 21-instruction SDIV conditional-negation block:
    materialize `mask = -sign` and propagate the ripple-carry add across
    four limbs. Wrapped `@[irreducible]` to hide the 16-step let chain. -/
@[irreducible]
def condNegate256BlockPost
    (addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12)
    (vAddr sign limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (addrReg ↦ᵣ vAddr) **
  (signReg ↦ᵣ sign) ** (maskReg ↦ᵣ mask) **
  (valueReg ↦ᵣ sum3) ** (carryReg ↦ᵣ carry3) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb0Off) ↦ₘ sum0) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb1Off) ↦ₘ sum1) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb2Off) ↦ₘ sum2) **
  ((vAddr + EvmAsm.Rv64.signExtend12 limb3Off) ↦ₘ sum3)

theorem condNegate256BlockPost_unfold
    {addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg}
    {limb0Off limb1Off limb2Off limb3Off : BitVec 12}
    {vAddr sign limb0 limb1 limb2 limb3 : Word} :
    condNegate256BlockPost addrReg signReg maskReg valueReg carryReg
        limb0Off limb1Off limb2Off limb3Off
        vAddr sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (addrReg ↦ᵣ vAddr) **
       (signReg ↦ᵣ sign) ** (maskReg ↦ᵣ mask) **
       (valueReg ↦ᵣ sum3) ** (carryReg ↦ᵣ carry3) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb0Off) ↦ₘ sum0) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb1Off) ↦ₘ sum1) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb2Off) ↦ₘ sum2) **
       ((vAddr + EvmAsm.Rv64.signExtend12 limb3Off) ↦ₘ sum3)) := by
  delta condNegate256BlockPost
  rfl

/-- 21-instruction conditional-negation block spec: materialize the mask
    `0 - sign`, then apply the four limb-step updates in place. -/
theorem evm_sdiv_cond_negate_256_block_spec_within
    (addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12)
    (vAddr sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word)
    (hmask_ne_x0 : maskReg ≠ .x0)
    (hvalue_ne_x0 : valueReg ≠ .x0)
    (hcarry_ne_x0 : carryReg ≠ .x0) :
    let code :=
      evm_sdiv_cond_negate_256_block_code addrReg signReg maskReg valueReg
        carryReg limb0Off limb1Off limb2Off limb3Off base
    EvmAsm.Rv64.cpsTripleWithin 21 base (base + 84) code
      (condNegate256BlockPre addrReg signReg maskReg valueReg carryReg
        limb0Off limb1Off limb2Off limb3Off
        vAddr sign maskOld valueOld carryOld limb0 limb1 limb2 limb3)
      (condNegate256BlockPost addrReg signReg maskReg valueReg carryReg
        limb0Off limb1Off limb2Off limb3Off
        vAddr sign limb0 limb1 limb2 limb3) := by
  intro code
  rw [condNegate256BlockPre_unfold, condNegate256BlockPost_unfold]
  let mem0 := vAddr + EvmAsm.Rv64.signExtend12 limb0Off
  let mem1 := vAddr + EvmAsm.Rv64.signExtend12 limb1Off
  let mem2 := vAddr + EvmAsm.Rv64.signExtend12 limb2Off
  let mem3 := vAddr + EvmAsm.Rv64.signExtend12 limb3Off
  let mask := (0 : Word) - sign
  let xored0 := limb0 ^^^ mask
  let sum0 := xored0 + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let xored1 := limb1 ^^^ mask
  let sum1 := xored1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let xored2 := limb2 ^^^ mask
  let sum2 := xored2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let xored3 := limb3 ^^^ mask
  let sum3 := xored3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  have M := EvmAsm.Rv64.sub_spec_gen_within maskReg .x0 signReg
    (0 : Word) sign maskOld
    base hmask_ne_x0
  have L0 := EvmAsm.Rv64.ld_spec_gen_within valueReg addrReg vAddr valueOld limb0
    limb0Off (base + 4) hvalue_ne_x0
  have X0 := EvmAsm.Rv64.xor_spec_gen_rd_eq_rs1_within valueReg maskReg limb0 mask
    (base + 8) hvalue_ne_x0
  have A0 := EvmAsm.Rv64.add_spec_gen_rd_eq_rs1_within valueReg signReg xored0 sign
    (base + 12) hvalue_ne_x0
  have C0 := EvmAsm.Rv64.sltu_spec_gen_within carryReg valueReg signReg carryOld sum0 sign
    (base + 16) hcarry_ne_x0
  have S0 := EvmAsm.Rv64.sd_spec_gen_within addrReg valueReg vAddr sum0 limb0 limb0Off
    (base + 20)
  have L1 := EvmAsm.Rv64.ld_spec_gen_within valueReg addrReg vAddr sum0 limb1
    limb1Off (base + 24) hvalue_ne_x0
  have X1 := EvmAsm.Rv64.xor_spec_gen_rd_eq_rs1_within valueReg maskReg limb1 mask
    (base + 28) hvalue_ne_x0
  have A1 := EvmAsm.Rv64.add_spec_gen_rd_eq_rs1_within valueReg carryReg xored1 carry0
    (base + 32) hvalue_ne_x0
  have C1 := EvmAsm.Rv64.sltu_spec_gen_rd_eq_rs2_within carryReg valueReg sum1 carry0
    (base + 36) hcarry_ne_x0
  have S1 := EvmAsm.Rv64.sd_spec_gen_within addrReg valueReg vAddr sum1 limb1 limb1Off
    (base + 40)
  have L2 := EvmAsm.Rv64.ld_spec_gen_within valueReg addrReg vAddr sum1 limb2
    limb2Off (base + 44) hvalue_ne_x0
  have X2 := EvmAsm.Rv64.xor_spec_gen_rd_eq_rs1_within valueReg maskReg limb2 mask
    (base + 48) hvalue_ne_x0
  have A2 := EvmAsm.Rv64.add_spec_gen_rd_eq_rs1_within valueReg carryReg xored2 carry1
    (base + 52) hvalue_ne_x0
  have C2 := EvmAsm.Rv64.sltu_spec_gen_rd_eq_rs2_within carryReg valueReg sum2 carry1
    (base + 56) hcarry_ne_x0
  have S2 := EvmAsm.Rv64.sd_spec_gen_within addrReg valueReg vAddr sum2 limb2 limb2Off
    (base + 60)
  have L3 := EvmAsm.Rv64.ld_spec_gen_within valueReg addrReg vAddr sum2 limb3
    limb3Off (base + 64) hvalue_ne_x0
  have X3 := EvmAsm.Rv64.xor_spec_gen_rd_eq_rs1_within valueReg maskReg limb3 mask
    (base + 68) hvalue_ne_x0
  have A3 := EvmAsm.Rv64.add_spec_gen_rd_eq_rs1_within valueReg carryReg xored3 carry2
    (base + 72) hvalue_ne_x0
  have C3 := EvmAsm.Rv64.sltu_spec_gen_rd_eq_rs2_within carryReg valueReg sum3 carry2
    (base + 76) hcarry_ne_x0
  have S3 := EvmAsm.Rv64.sd_spec_gen_within addrReg valueReg vAddr sum3 limb3 limb3Off
    (base + 80)
  runBlock M L0 X0 A0 C0 S0 L1 X1 A1 C1 S1 L2 X2 A2 C2 S2 L3 X3 A3 C3 S3

/-- CodeReq for `evm_sdiv_save_ra_block` at byte offset `base`. -/
abbrev evm_sdiv_save_ra_block_code
    (savedRaReg : EvmAsm.Rv64.Reg) (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_save_ra_block savedRaReg)

/-- 1-instruction leaf spec: `ADDI savedRaReg, x1, 0` copies the current
    `x1` (return address) into a preserved scratch register. The block is
    used to save `ra` across a nested `JAL` to `evm_div_callable` (which
    clobbers `x1`). Mirrors `evm_sdiv_div_call_block_spec_within`. -/
theorem evm_sdiv_save_ra_block_spec_within
    (savedRaReg : EvmAsm.Rv64.Reg) (vRa vSavedOld : Word) (base : Word)
    (hsaved_ne_x0 : savedRaReg ≠ .x0) :
    let code := evm_sdiv_save_ra_block_code savedRaReg base
    EvmAsm.Rv64.cpsTripleWithin 1 base (base + 4) code
      ((.x1 ↦ᵣ vRa) ** (savedRaReg ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) **
       (savedRaReg ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  show EvmAsm.Rv64.cpsTripleWithin 1 base (base + 4)
    (EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_save_ra_block savedRaReg)) _ _
  rw [show EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_save_ra_block savedRaReg) =
      EvmAsm.Rv64.CodeReq.singleton base (.ADDI savedRaReg .x1 0) from
      EvmAsm.Rv64.CodeReq.ofProg_singleton]
  exact EvmAsm.Rv64.addi_spec_within savedRaReg .x1 vRa vSavedOld 0 base hsaved_ne_x0

/-- CodeReq for `evm_sdiv_saved_ra_ret_block` at byte offset `base`. -/
abbrev evm_sdiv_saved_ra_ret_block_code
    (savedRaReg : EvmAsm.Rv64.Reg) (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_saved_ra_ret_block savedRaReg)

/-- 1-instruction leaf spec: `JALR x0, savedRaReg, 0` returns to the
    address saved by `evm_sdiv_save_ra_block`. Exit pc is
    `(vSavedRa + 0) &&& ~~~1` per the standard `JALR x0` semantics. The
    `savedRaReg` value is preserved. Mirrors `ret_spec_within`. -/
theorem evm_sdiv_saved_ra_ret_block_spec_within
    (savedRaReg : EvmAsm.Rv64.Reg) (vSavedRa : Word) (base : Word) :
    let code := evm_sdiv_saved_ra_ret_block_code savedRaReg base
    EvmAsm.Rv64.cpsTripleWithin 1 base
        ((vSavedRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~1) code
      (savedRaReg ↦ᵣ vSavedRa)
      (savedRaReg ↦ᵣ vSavedRa) := by
  show EvmAsm.Rv64.cpsTripleWithin 1 base _
    (EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_saved_ra_ret_block savedRaReg)) _ _
  rw [show EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_saved_ra_ret_block savedRaReg) =
      EvmAsm.Rv64.CodeReq.singleton base (.JALR .x0 savedRaReg 0) from
      EvmAsm.Rv64.CodeReq.ofProg_singleton]
  exact EvmAsm.Rv64.jalr_x0_spec_gen_within savedRaReg vSavedRa 0 base

/-- CodeReq for `evm_sdiv_div_call_block` at byte offset `base`. -/
abbrev evm_sdiv_div_call_block_code
    (divOff : BitVec 21) (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_div_call_block divOff)

/-- 1-instruction leaf spec: near-`JAL` from SDIV into the unsigned
    `evm_div_callable` shim. Control transfers to
    `base + signExtend21 divOff` and `.x1` is updated with the return
    address `base + 4`. Argument-marshalling (placing both operands in
    the LP64 a-slots) is handled by the surrounding scaffold and is not
    part of this leaf cpsTriple. Mirrors `exp_square_block_spec_within`
    (`Evm64/Exp/LimbSpec.lean`). -/
theorem evm_sdiv_div_call_block_spec_within
    (divOff : BitVec 21) (vOld : Word) (base : Word) :
    let code := evm_sdiv_div_call_block_code divOff base
    EvmAsm.Rv64.cpsTripleWithin 1 base (base + EvmAsm.Rv64.signExtend21 divOff) code
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 4)) := by
  show EvmAsm.Rv64.cpsTripleWithin 1 base (base + EvmAsm.Rv64.signExtend21 divOff)
    (EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_div_call_block divOff)) _ _
  rw [show EvmAsm.Rv64.CodeReq.ofProg base (evm_sdiv_div_call_block divOff) =
      EvmAsm.Rv64.CodeReq.singleton base (.JAL .x1 divOff) from
      EvmAsm.Rv64.CodeReq.ofProg_singleton]
  exact EvmAsm.Rv64.jal_spec_within .x1 vOld divOff base (by nofun)

end EvmAsm.Evm64
