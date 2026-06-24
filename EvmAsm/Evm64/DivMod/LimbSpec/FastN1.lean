/-
  EvmAsm.Evm64.DivMod.LimbSpec.FastN1

  Per-block CPS specs for the n=1 single-limb fast path (issue #9303):
  `divK_fastDenorm`, `divK_fastSetup`, `divK_fastDigit`, `divK_dispatchN1`.
  The reused blocks (`divK_clz`, `divK_normA`, `divK_copyAU`,
  `divK_div_epilogue`) keep their existing specs.
-/

import EvmAsm.Evm64.DivMod.FastN1Program
import EvmAsm.Evm64.DivMod.Compose.Div128V5
import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev divK_fastDenorm_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_fastDenorm

/-- Single-limb remainder de-normalization (MOD): `u[0] := u[0] >> s` and zero
    the upper remainder limbs `u[1..3]`. `s` (the CLZ shift) is read from the
    scratch slot at `sp + 3992`. 7 instructions. -/
theorem divK_fastDenorm_spec_within (sp : Word) (base : Word)
    (s u0 u1m u2m u3m v5 v6 : Word) :
    let cr := divK_fastDenorm_code base
    cpsTripleWithin 7 base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1m) **
       ((sp + signExtend12 4040) ↦ₘ u2m) ** ((sp + signExtend12 4032) ↦ₘ u3m))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (u0 >>> (s.toNat % 64))) ** (.x6 ↦ᵣ s) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ (u0 >>> (s.toNat % 64))) **
       ((sp + signExtend12 4048) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4040) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4032) ↦ₘ (0 : Word))) := by
  intro cr
  have I0 := ld_spec_gen_within .x6 .x12 sp v6 s 3992 base (by nofun)
  have I1 := ld_spec_gen_within .x5 .x12 sp v5 u0 4056 (base + 4) (by nofun)
  have I2 := srl_spec_gen_rd_eq_rs1_within .x5 .x6 u0 s (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x5 sp (u0 >>> (s.toNat % 64)) u0 4056 (base + 12)
  have I4 := sd_x0_spec_gen_within .x12 sp u1m 4048 (base + 16)
  have I5 := sd_x0_spec_gen_within .x12 sp u2m 4040 (base + 20)
  have I6 := sd_x0_spec_gen_within .x12 sp u3m 4032 (base + 24)
  runBlock I0 I1 I2 I3 I4 I5 I6

abbrev divK_fastSetup_b0prime_code (base : Word) : CodeReq :=
  CodeReq.ofProg base [.LD .x5 .x12 32, .SLL .x5 .x5 .x6, .SD .x12 .x5 3984]

/-- `divK_fastSetup` divisor-normalization block (the 3 instructions after the
    antiShift setup, which is `divK_phaseC2_body`): load `b0` from `sp + 32`,
    compute `b0' = b0 <<< s` (`s` = CLZ shift in `x6`), and store `b0'` at
    `sp + 3984`. Mirror of `divK_normB_last`. -/
theorem divK_fastSetup_b0prime_spec_within (sp : Word) (base : Word)
    (s b0 v5 m3984 : Word) :
    let result := b0 <<< (s.toNat % 64)
    let cr := divK_fastSetup_b0prime_code base
    cpsTripleWithin 3 base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) **
       ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3984) ↦ₘ m3984))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ s) **
       ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3984) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen_within .x5 .x12 sp v5 b0 32 base (by nofun)
  have I1 := sll_spec_gen_rd_eq_rs1_within .x5 .x6 b0 s (base + 4) (by nofun)
  have I2 := sd_spec_gen_within .x12 .x5 sp result m3984 3984 (base + 8)
  runBlock I0 I1 I2

-- ============================================================================
-- Digit step: load window/divisor, (call div128), recover threaded remainder
-- ============================================================================

abbrev divK_fastDigit_loads_code (uHiOff uLoOff : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base [.LD .x7 .x12 uHiOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984]

/-- Digit-step argument loads (3 instructions): `x7 = uHi = u[j+1]` (the running
    remainder), `x5 = uLo = u[j]`, `x10 = d = b0'`. Establishes the
    `div128_v5_spec` input registers. -/
theorem divK_fastDigit_loads_spec_within (uHiOff uLoOff : BitVec 12)
    (sp uHi uLo d v5 v7 v10 : Word) (base : Word) :
    let cr := divK_fastDigit_loads_code uHiOff uLoOff base
    cpsTripleWithin 3 base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ uHi) ** (.x5 ↦ᵣ uLo) ** (.x10 ↦ᵣ d) **
       ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d)) := by
  intro cr
  have I0 := ld_spec_gen_within .x7 .x12 sp v7 uHi uHiOff base (by nofun)
  have I1 := ld_spec_gen_within .x5 .x12 sp v5 uLo uLoOff (base + 4) (by nofun)
  have I2 := ld_spec_gen_within .x10 .x12 sp v10 d 3984 (base + 8) (by nofun)
  runBlock I0 I1 I2

abbrev divK_fastDigit_post_code (uLoOff qOff : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    [.SD .x12 .x11 qOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984,
     .MUL .x7 .x11 .x10, .SUB .x5 .x5 .x7, .SD .x12 .x5 uLoOff]

/-- Digit-step post-call block (6 instructions): store the exact quotient digit
    `q[j] = x11` to `qOff`; recover the threaded remainder
    `u[j] := u[j] -₆₄ q·b0'` (`b0'` reloaded from `sp + 3984`) and store it to
    `uLoOff`. Valid since the true 128-bit remainder is `< b0' < 2^64`, so its
    low 64 bits are exact. -/
theorem divK_fastDigit_post_spec_within (uLoOff qOff : BitVec 12)
    (sp q uLo d v5 v7 v10 qm : Word) (base : Word) :
    let cr := divK_fastDigit_post_code uLoOff qOff base
    cpsTripleWithin 6 base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 qOff) ↦ₘ qm) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** (.x5 ↦ᵣ (uLo - q * d)) ** (.x10 ↦ᵣ d) **
       (.x7 ↦ᵣ (q * d)) **
       ((sp + signExtend12 qOff) ↦ₘ q) ** ((sp + signExtend12 uLoOff) ↦ₘ (uLo - q * d)) **
       ((sp + signExtend12 3984) ↦ₘ d)) := by
  intro cr
  have I0 := sd_spec_gen_within .x12 .x11 sp q qm qOff base
  have I1 := ld_spec_gen_within .x5 .x12 sp v5 uLo uLoOff (base + 4) (by nofun)
  have I2 := ld_spec_gen_within .x10 .x12 sp v10 d 3984 (base + 8) (by nofun)
  have I3 := mul_spec_gen_within .x7 .x11 .x10 v7 q d (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1_within .x5 .x7 uLo (q * d) (base + 16) (by nofun)
  have I5 := sd_spec_gen_within .x12 .x5 sp (uLo - q * d) uLo uLoOff (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

/-- Digit-step call: `JAL x2 callOff` (at `jalPc`) into the fast path's own
    `divK_div128_v5` copy (at `divBase + div128Off`), returning to `retAddr`
    with `x11 = q = div128 quotient`. Adapts `divK_trial_call_path_spec_within`
    to a self-contained copy. Steps: 1 (JAL) + 83 (div128). -/
theorem divK_fastDigit_call_spec_within
    (sp uLo uHi d retAddr jalPc divBase : Word) (callOff : BitVec 21)
    (v2Old v6Old v9Old v11Old retMem dMem dloMem un0Mem scratchMem : Word)
    (htarget : jalPc + signExtend21 callOff = divBase + div128Off)
    (hret : jalPc + 4 = retAddr)
    (halign : (retAddr + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = retAddr)
    (hdisj : (CodeReq.singleton jalPc (.JAL .x2 callOff)).Disjoint
              (CodeReq.ofProg (divBase + div128Off) divK_div128_v5)) :
    cpsTripleWithin 84 jalPc retAddr
      ((CodeReq.singleton jalPc (.JAL .x2 callOff)).union
        (CodeReq.ofProg (divBase + div128Off) divK_div128_v5))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** (.x10 ↦ᵣ d) ** (.x5 ↦ᵣ uLo) **
       (.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ v6Old) ** (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V5SpecPost sp retAddr d uLo uHi scratchMem) := by
  set unionCr := (CodeReq.singleton jalPc (.JAL .x2 callOff)).union
    (CodeReq.ofProg (divBase + div128Off) divK_div128_v5) with hUnion
  have J := jal_spec_within .x2 v2Old callOff jalPc (by nofun)
  rw [htarget, hret] at J
  have Je := cpsTripleWithin_extend_code (cr' := unionCr)
    (hmono := fun a i h => CodeReq.union_mono_left a i h) J
  have D := div128_v5_spec sp retAddr d uLo uHi divBase v9Old v6Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign
  have De := cpsTripleWithin_extend_code (cr' := unionCr)
    (hmono := CodeReq.mono_union_right hdisj (fun a i h => h)) D
  have Jf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ d) ** (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
     (.x6 ↦ᵣ v6Old) ** (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) Je
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf De
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq) full

/-- Digit step through the div128 return: 3 loads ;; (JAL + div128_v5 copy).
    From `base` to `base + 16` (the post-call PC), ending in `div128V5SpecPost`
    with the window mem cells `u[j+1]`, `u[j]`, `b0'` framed through. -/
theorem divK_fastDigit_loadsCall_spec_within
    (sp uHi uLo d : Word) (uHiOff uLoOff : BitVec 12) (callOff : BitVec 21)
    (base divBase : Word)
    (v2 v5 v6 v7 v9 v10 v11 retMem dMem dloMem un0Mem scratchMem : Word)
    (htarget : (base + 12) + signExtend21 callOff = divBase + div128Off)
    (halign : ((base + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 16)
    (hdisj_loads : (divK_fastDigit_loads_code uHiOff uLoOff base).Disjoint
      ((CodeReq.singleton (base + 12) (.JAL .x2 callOff)).union
        (CodeReq.ofProg (divBase + div128Off) divK_div128_v5)))
    (hdisj_jal : (CodeReq.singleton (base + 12) (.JAL .x2 callOff)).Disjoint
      (CodeReq.ofProg (divBase + div128Off) divK_div128_v5)) :
    cpsTripleWithin 87 base (base + 16)
      ((divK_fastDigit_loads_code uHiOff uLoOff base).union
        ((CodeReq.singleton (base + 12) (.JAL .x2 callOff)).union
          (CodeReq.ofProg (divBase + div128Off) divK_div128_v5)))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V5SpecPost sp (base + 16) d uLo uHi scratchMem **
       ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d)) := by
  have L := divK_fastDigit_loads_spec_within uHiOff uLoOff sp uHi uLo d v5 v7 v10 base
  have C := divK_fastDigit_call_spec_within sp uLo uHi d (base + 16) (base + 12) divBase
    callOff v2 v6 v9 v11 retMem dMem dloMem un0Mem scratchMem htarget (by bv_omega) halign hdisj_jal
  -- Frame L with the registers/scratch that the call needs.
  have Lf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x9 ↦ᵣ v9) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) L
  -- Frame C with the window mem cells that loads established.
  have Cf := cpsTripleWithin_frameR
    (((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
     ((sp + signExtend12 3984) ↦ₘ d))
    (by pcFree) C
  set fullCr := (divK_fastDigit_loads_code uHiOff uLoOff base).union
    ((CodeReq.singleton (base + 12) (.JAL .x2 callOff)).union
      (CodeReq.ofProg (divBase + div128Off) divK_div128_v5)) with hFull
  have Le := cpsTripleWithin_extend_code (cr' := fullCr)
    (hmono := fun a i h => CodeReq.union_mono_left a i h) Lf
  have Ce := cpsTripleWithin_extend_code (cr' := fullCr)
    (hmono := CodeReq.mono_union_right hdisj_loads (fun a i h => h)) Cf
  have full := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) Le Ce
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) full

-- ============================================================================
-- Dispatch prologue: OR-reduce b1|b2|b3 (the n≥2 detector)
-- ============================================================================

abbrev divK_dispatchN1_orReduce_code (base : Word) : CodeReq :=
  CodeReq.ofProg base
    [.LD .x5 .x12 40, .LD .x10 .x12 48, .OR .x5 .x5 .x10,
     .LD .x10 .x12 56, .OR .x5 .x5 .x10]

/-- Dispatch OR-reduce (the 5 instructions before the `BNE` n≥2 test): load the
    upper divisor limbs `b1, b2, b3` and reduce `x5 = b1 ||| b2 ||| b3`
    (zero iff the divisor is single-limb). Mirror of the `divK_phaseA`
    OR-reduce. Exits at `base + 20` (the `BNE`). -/
theorem divK_dispatchN1_orReduce_spec_within (sp : Word) (base : Word)
    (b1 b2 b3 v5 v10 : Word) :
    let cr := divK_dispatchN1_orReduce_code base
    cpsTripleWithin 5 base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
       ((sp + signExtend12 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) **
       ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
       ((sp + signExtend12 56) ↦ₘ b3)) := by
  intro cr
  have I0 := ld_spec_gen_within .x5 .x12 sp v5 b1 40 base (by nofun)
  have I1 := ld_spec_gen_within .x10 .x12 sp v10 b2 48 (base + 4) (by nofun)
  have I2 := or_spec_gen_rd_eq_rs1_within .x5 .x10 b1 b2 (base + 8) (by nofun)
  have I3 := ld_spec_gen_within .x10 .x12 sp b2 b3 56 (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1_within .x5 .x10 (b1 ||| b2) b3 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Weaken the div128 spec post to the digit-threading (ownership) form
-- ============================================================================

/-- Weaken `div128V5SpecPost` to the digit-threading form: keep `x12 = sp`,
    `x2 = retAddr`, `x11 = div128V5CodeQuot uHi uLo d` (the exact quotient — the
    spec post's `x11` is this by construction), `x0 = 0`; weaken the clobbered
    registers `x5/x6/x7/x9/x10` and the five div128 scratch cells to ownership.
    Reusable for threading each digit's call result. -/
theorem div128V5SpecPost_to_owned (sp retAddr d uLo uHi scratchMem : Word) :
    ∀ h, (div128V5SpecPost sp retAddr d uLo uHi scratchMem) h →
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** regOwn .x10 ** regOwn .x5 ** regOwn .x7 **
       regOwn .x6 ** regOwn .x9 ** (.x11 ↦ᵣ div128V5CodeQuot uHi uLo d) **
       (.x0 ↦ᵣ (0 : Word)) **
       memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
       memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  unfold div128V5SpecPost at hp
  exact sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x10) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x9) (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x) (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))))))))))) h hp

/-- Post-call block with the clobbered input registers `x5/x10/x7` exposed as
    ownership (the form produced by `div128V5SpecPost_to_owned`). Derived from
    `divK_fastDigit_post_spec_within` by ∀-regIs→regOwn lifting, peeling one
    register at a time (reassociating the precondition between peels). -/
theorem divK_fastDigit_post_own_spec_within (uLoOff qOff : BitVec 12)
    (sp q uLo d qm : Word) (base : Word) :
    cpsTripleWithin 6 base (base + 24) (divK_fastDigit_post_code uLoOff qOff base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) **
       ((sp + signExtend12 qOff) ↦ₘ qm) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
       ((sp + signExtend12 3984) ↦ₘ d) ** regOwn .x5 ** regOwn .x10 ** regOwn .x7)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** (.x5 ↦ᵣ (uLo - q * d)) ** (.x10 ↦ᵣ d) **
       (.x7 ↦ᵣ (q * d)) **
       ((sp + signExtend12 qOff) ↦ₘ q) ** ((sp + signExtend12 uLoOff) ↦ₘ (uLo - q * d)) **
       ((sp + signExtend12 3984) ↦ₘ d)) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** ((sp + signExtend12 qOff) ↦ₘ qm) **
        ((sp + signExtend12 uLoOff) ↦ₘ uLo) ** ((sp + signExtend12 3984) ↦ₘ d) **
        regOwn .x5 ** regOwn .x10) (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** ((sp + signExtend12 qOff) ↦ₘ qm) **
        ((sp + signExtend12 uLoOff) ↦ₘ uLo) ** ((sp + signExtend12 3984) ↦ₘ d) **
        regOwn .x5 ** (.x7 ↦ᵣ v7)) (r := .x10) (fun v10 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q) ** ((sp + signExtend12 qOff) ↦ₘ qm) **
        ((sp + signExtend12 uLoOff) ↦ₘ uLo) ** ((sp + signExtend12 3984) ↦ₘ d) **
        (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10)) (r := .x5) (fun v5 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (divK_fastDigit_post_spec_within uLoOff qOff sp q uLo d v5 v7 v10 qm base)

/-- **Full digit step** `loads ;; (JAL + own div128_v5) ;; post`, from `base` to
    `base + 40`. Stores the exact quotient digit `q = div128V5CodeQuot uHi uLo d`
    at `qOff` and the threaded remainder `u[j] := uLo -₆₄ q·d` (= next iteration's
    `uHi`) at `uLoOff`. Clobbered registers and div128 scratch are owned. -/
theorem divK_fastDigit_full_spec_within
    (sp uHi uLo d : Word) (uHiOff uLoOff qOff : BitVec 12) (callOff : BitVec 21)
    (base divBase : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (htarget : (base + 12) + signExtend21 callOff = divBase + div128Off)
    (halign : ((base + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 16)
    (hdisj_loads : (divK_fastDigit_loads_code uHiOff uLoOff base).Disjoint
      ((CodeReq.singleton (base + 12) (.JAL .x2 callOff)).union
        (CodeReq.ofProg (divBase + div128Off) divK_div128_v5)))
    (hdisj_jal : (CodeReq.singleton (base + 12) (.JAL .x2 callOff)).Disjoint
      (CodeReq.ofProg (divBase + div128Off) divK_div128_v5))
    (hdisj_post : ((divK_fastDigit_loads_code uHiOff uLoOff base).union
      ((CodeReq.singleton (base + 12) (.JAL .x2 callOff)).union
        (CodeReq.ofProg (divBase + div128Off) divK_div128_v5))).Disjoint
      (divK_fastDigit_post_code uLoOff qOff (base + 16))) :
    cpsTripleWithin 93 base (base + 40)
      (((divK_fastDigit_loads_code uHiOff uLoOff base).union
        ((CodeReq.singleton (base + 12) (.JAL .x2 callOff)).union
          (CodeReq.ofProg (divBase + div128Off) divK_div128_v5))).union
        (divK_fastDigit_post_code uLoOff qOff (base + 16)))
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem)) **
       ((sp + signExtend12 qOff) ↦ₘ qm))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (div128V5CodeQuot uHi uLo d)) **
        (.x5 ↦ᵣ (uLo - div128V5CodeQuot uHi uLo d * d)) ** (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 qOff) ↦ₘ (div128V5CodeQuot uHi uLo d)) **
        ((sp + signExtend12 uLoOff) ↦ₘ (uLo - div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 uHiOff) ↦ₘ uHi))) := by
  have LC := divK_fastDigit_loadsCall_spec_within sp uHi uLo d uHiOff uLoOff callOff
    base divBase v2 v5 v6 v7 v9 v10 v11 retMem dMem dloMem un0Mem scratchMem
    htarget halign hdisj_loads hdisj_jal
  -- Weaken the div128 post to the owned digit-threading form.
  have LC' := cpsTripleWithin_weaken (fun _ hp => hp)
    (sepConj_mono (div128V5SpecPost_to_owned sp (base + 16) d uLo uHi scratchMem)
      (fun _ x => x)) LC
  -- Frame in the q[j] output cell that the post block writes.
  have LCf := cpsTripleWithin_frameR (((sp + signExtend12 qOff) ↦ₘ qm)) (by pcFree) LC'
  have P := divK_fastDigit_post_own_spec_within uLoOff qOff sp
    (div128V5CodeQuot uHi uLo d) uLo d qm (base + 16)
  -- Frame the post block with the div128 pass-through atoms (all owned/clean).
  have Pf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (base + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
     memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
     memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
     memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 uHiOff) ↦ₘ uHi))
    (by pcFree) P
  set fullCr := ((divK_fastDigit_loads_code uHiOff uLoOff base).union
    ((CodeReq.singleton (base + 12) (.JAL .x2 callOff)).union
      (CodeReq.ofProg (divBase + div128Off) divK_div128_v5))).union
      (divK_fastDigit_post_code uLoOff qOff (base + 16)) with hFull
  have LCe := cpsTripleWithin_extend_code (cr' := fullCr)
    (hmono := fun a i h => CodeReq.union_mono_left a i h) LCf
  have Pe := cpsTripleWithin_extend_code (cr' := fullCr)
    (hmono := CodeReq.mono_union_right hdisj_post (fun a i h => h)) Pf
  have full := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) LCe Pe
  rw [show (base + 16 + 24 : Word) = base + 40 from by bv_omega] at full
  exact full

end EvmAsm.Evm64
