/-
  EvmAsm.Evm64.DivMod.Compose.V5Code

  Shared DIV/MOD code surfaces for the v5 div128 migration.

  Mirror of the v5-relevant shared surfaces from
  `EvmAsm.Evm64.DivMod.Compose.Base` (`sharedDivModCode_v4`) and
  `EvmAsm.Evm64.DivMod.Compose.V4NoNop` (`sharedDivModCodeNoNop_v4`),
  swapping in `divK_div128_v5` — the capped Knuth Algorithm D variant that
  repairs v4's two buggy ULTs by clamping `q1c`/`q0c` at `2^32 - 1`.

  These surfaces are the code requirements for the shared variants of
  `div128_v5_spec` (`div128_v5_spec_shared` / `div128_v5_spec_shared_noNop`).
  Kept in a dedicated file rather than appended to `Base.lean`, which is at
  its size cap. See bead evm-asm-wbc4i.6 (V5.6 val256 lift).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.Base

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 mirror of `sharedDivModCode_v4` — uses `divK_div128_v5` at block 12.
    Blocks 0-11 are identical to `sharedDivModCode_v4`; only block 12 swaps
    in the longer `divK_div128_v5` program. -/
abbrev sharedDivModCode_v5 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 10
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),       -- block 11
    CodeReq.ofProg (base + div128Off)     divK_div128_v5          -- block 12 (v5)
  ]

/-- v5 mirror of `shared_b12_div128_v4_sub`: block 12 (`divK_div128_v5`)
    is included in `sharedDivModCode_v5 base`. Used by `div128_v5_spec_shared`
    to lift `div128_v5_spec` from singleton-`ofProg` cr to shared cr. -/
theorem shared_b12_div128_v5_sub {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v5) a = some i →
           (sharedDivModCode_v5 b) a = some i := by
  unfold sharedDivModCode_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- v5 mirror of `sharedDivModCodeNoNop_v4`: shared DIV/MOD blocks with the
    NOP return slot omitted and the final block using `divK_div128_v5`. -/
abbrev sharedDivModCodeNoNop_v5 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + div128Off)     divK_div128_v5
  ]

/-- v5 div128 block is included in `sharedDivModCodeNoNop_v5 base`. -/
theorem sharedNoNop_b11_div128_v5_sub {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v5) a = some i →
           (sharedDivModCodeNoNop_v5 b) a = some i := by
  unfold sharedDivModCodeNoNop_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- v5 mirror of `divK_loopBody_ofProg_sub_sharedCode_v4`: the loopBody ofProg
    (block 8) is subsumed by `sharedDivModCode_v5`. -/
private theorem divK_loopBody_ofProg_sub_sharedCode_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (sharedDivModCode_v5 base) a = some i := by
  unfold sharedDivModCode_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- v5 mirror of `lb_sub_v4`: singleton at index k of `divK_loopBody` is
    subsumed by `sharedDivModCode_v5 base`. -/
theorem lb_sub_v5 {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 560 7736).length)
    (h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCode_v5 base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_sharedCode_v5 a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + loopBodyOff) (divK_loopBody 560 7736) k hk (by decide)) a i h)

/-- v5 mirror of `divK_loopBody_ofProg_sub_sharedCodeNoNop_v4`: the loopBody
    ofProg (block 8) is subsumed by `sharedDivModCodeNoNop_v5`. -/
private theorem divK_loopBody_ofProg_sub_sharedCodeNoNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (sharedDivModCodeNoNop_v5 base) a = some i := by
  unfold sharedDivModCodeNoNop_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- v5 mirror of `lb_sub_noNop_v4`: singleton at index k of `divK_loopBody` is
    subsumed by `sharedDivModCodeNoNop_v5 base`. -/
theorem lb_sub_noNop_v5 {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 560 7736).length)
    (h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCodeNoNop_v5 base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_sharedCodeNoNop_v5 a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + loopBodyOff) (divK_loopBody 560 7736) k hk (by decide)) a i h)

end EvmAsm.Evm64
