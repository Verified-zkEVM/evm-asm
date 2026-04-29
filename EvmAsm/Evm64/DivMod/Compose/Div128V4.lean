/-
  EvmAsm.Evm64.DivMod.Compose.Div128V4

  div128 subroutine composition for the v4 algorithm — the FULL
  Knuth Algorithm D with 2-correction in BOTH Phase 1b and Phase 2b.

  The v4 RV64 program `divK_div128_v4` (defined in `Program.lean`) is
  identical to `divK_div128_v2` for instructions [0..46], then adds a
  Phase 2b 2nd D3 correction at [47..70] (vs v2's single correction at
  [47..56]). Total length: 75 vs 61 instructions for v2.

  Companion to `Compose/Div128.lean` (v1 + v2 specs). PR-A2 of the
  v2 → v4 migration plan.

  Issue #1337 algorithm fix migration / Issue #61 stack spec closure.
-/

import EvmAsm.Evm64.DivMod.Compose.Div128
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2v4
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 15-v4: div128 subroutine composition (v4 algorithm).
-- ============================================================================

-- v4 helper: singleton at index k of divK_div128_v4 ⊆ ofProg-based v4 cr.
-- Mirrors `d128_v2_sub` but uses `divK_div128_v4`.
private theorem d128_v4_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128_v4.length)
    (h_addr : addr = (base + div128Off) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128_v4.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (CodeReq.ofProg (base + div128Off) divK_div128_v4) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => CodeReq.singleton_mono
    (CodeReq.ofProg_lookup (base + div128Off) divK_div128_v4 k hk (by decide)) a i h

/-- Bundled postcondition for `div128_v4_spec`.

    Mirrors `div128V2SpecPost` but uses `q0''` (post-Phase-2b-2nd-D3)
    instead of `q0'`, matching `div128Quot_v4`'s output. The Phase 1
    intermediates (q1, rhat, q1c, rhatc, q1', rhat', q1'', rhat'') are
    identical between v2 and v4 — the v4 fix is in Phase 2b only.

    `@[irreducible]` to keep the let-chain out of the theorem signature. -/
@[irreducible]
def div128V4SpecPost (sp retAddr d uLo uHi : Word) : Assertion :=
  -- Phase 1 split intermediates (unchanged from v2).
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  -- Step 1 1st D3 (unchanged).
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  -- Step 1 2nd D3 (unchanged from v2).
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
              then q1' + signExtend12 4095 else q1'
  let rhat'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                then rhat' + dHi else rhat'
  -- compute_un21 (unchanged shape — uses q1''/rhat'').
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  -- Step 2 init/clamp (unchanged shape).
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  -- Phase 2b 1st D3 (unchanged shape — same `div128Quot_phase2b_q0'`).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  -- Phase 2b 2nd D3 (NEW in v4).
  let rhat2' :=
    if rhat2c >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2c := q0c * dLo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
      if BitVec.ult rhatUn0 qDlo2c then rhat2c + dHi else rhat2c
    else rhat2c
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo un0
  let q := (q1'' <<< (32 : BitVec 6).toNat) ||| q0''
  -- Memory: scratch slot 3936 holds the saved rhat2c (un-incremented;
  -- the SD at instr [52] saves rhat2c BEFORE the optional `+= dHi` at [60]).
  -- Register and memory state (final). Exit register layout matches v2's
  -- `div128V2SpecPost` for x10 (q1'') and x11 (combined q), with the
  -- transient x1/x5/x6/x7 values folded into TODO once the full proof is
  -- wired (they depend on the BLTU paths taken).
  -- TODO: pin x1/x5/x6/x7 exit values once the proof body is filled in.
  (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ q1'') **
  (.x11 ↦ᵣ q) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ retAddr) **
  (sp + signExtend12 3960 ↦ₘ d) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ rhat2c)

/-- **STUB**: equivalence between `divK_div128_v4` (full Knuth D RISC-V)
    and `div128Quot_v4` (Lean abstraction).

    Mirrors `div128_v2_spec` but for the v4 algorithm. Proof structure:
    - Block 1 (Phase 1, instrs [0..9]): identical to v2.
    - Block 2 (Step1 v2, instrs [10..34]): identical to v2 — Phase 1b
      2-correction is the same.
    - Block 3 (compute_un21, instrs [35..39]): identical shape — uses
      q1''/rhat'' (post-Phase-1b-2nd-D3).
    - Block 4 (Step2 + Phase 2b 1st D3 + 2nd D3, instrs [40..70]):
      **NEW for v4**. v2's Step2 covered [40..56]; v4's covers [40..70]
      with 14 extra instructions for the 2nd Phase 2b D3 correction.
    - Block 5 (end, instrs [71..74]): identical shape — combine + return.

    The Block 4 proof requires:
    - `divK_div128_step2_v4_spec` (NEW): RV64 → val256 spec for instrs
      [40..70] producing q0''.
    - This in turn requires either reusing `div128Quot_phase2b_q0'`
      twice (matching v4's Lean def) or composing 1st D3 + 2nd D3
      sub-specs.

    Estimated: ~700 LOC for the full proof (vs ~600 for v2). -/
theorem div128_v4_spec (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (_halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTriple (base + div128Off) retAddr
      (CodeReq.ofProg (base + div128Off) divK_div128_v4)
      (-- Precondition: same as div128_v2_spec, plus the new scratch slot
       -- 3936 (used to save rhat2c across the un0 LD clobber).
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V4SpecPost sp retAddr d uLo uHi) := by
  sorry  -- PR-A2 stub. Proof composes 5 blocks via cpsTriple_seq_perm_same_cr,
         -- mirroring `div128_v2_spec` (in `Compose/Div128.lean` line 419-629).
         -- Translation table from v2 → v4:
         --
         --   Block 1: phase1    [base+1072..base+1112]  10 inst (same as v2)
         --     Reuse `divK_div128_phase1_spec`. Code-extend with `d128_v4_sub`
         --     for indices [0..9]. Frame x0.
         --
         --   Block 2: step1_v2  [base+1112..base+1212]  25 inst (same as v2)
         --     Reuse `divK_div128_step1_v2_spec`. Code-extend with `d128_v4_sub`
         --     for indices [10..34]. Frame ((x2 ↦ retAddr) ** mem3968 **
         --     mem3960 ** mem3944 ** mem3936).
         --
         --   Block 3: compute_un21 [base+1212..base+1232]  5 inst (same as v2)
         --     Reuse `divK_div128_compute_un21_spec`. Code-extend with
         --     `d128_v4_sub` for indices [35..39]. Frame.
         --
         --   Block 4: step2_v4  [base+1232..base+1356]  31 inst (NEW for v4)
         --     Use `divK_div128_step2_v4_spec` (still sorry'd). Code-extend
         --     with `d128_v4_sub` for indices [40..70]. Frame ((x10 ↦ q1'') **
         --     (x2 ↦ retAddr) ** mem3968 ** mem3960). NB: step2_v4 owns
         --     mem3936 (saves rhat2c there).
         --
         --   Block 5: end       [base+1356..base+1372]  4 inst (same shape)
         --     Reuse `divK_div128_end_spec` with q1 = q1'', q0 = q0''.
         --     Code-extend with `d128_v4_sub` for indices [71..74]. Frame
         --     ((x7 ↦ x7Exit_v4) ** (x6 ↦ dHi) ** (x1 ↦ x1Exit_v4) ** x0 **
         --      mem3960 ** mem3952 ** mem3944 ** mem3936).
         --
         -- Final: cpsTriple_weaken with two xperm_hyp to reshape pre/post
         -- to match `div128V4SpecPost` definition order.
         --
         -- The proof is ~600 LOC of mechanical block-composition; structurally
         -- identical to v2 except Block 4 (step2_v4) extends 14 more
         -- instructions and threads the new mem3936 cell.

/-- Lifted `div128_v4_spec` over `sharedDivModCode_v4 base` — a thin
    wrapper that lifts the cr from singleton `ofProg`-form to the
    shared cr via `cpsTriple_extend_code` + `shared_b12_div128_v4_sub`.

    Future v4-migrated specs (loop body, full path) will use this
    lifted form. -/
theorem div128_v4_spec_shared (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTriple (base + div128Off) retAddr (sharedDivModCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V4SpecPost sp retAddr d uLo uHi) :=
  cpsTriple_extend_code (hmono := shared_b12_div128_v4_sub)
    (div128_v4_spec sp retAddr d uLo uHi base v1Old v6Old v11Old
      retMem dMem dloMem un0Mem scratchMem halign)

end EvmAsm.Evm64
