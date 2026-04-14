/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Cases

  Per-case full n=2 DIV path lemmas (base → base+1064), one for each
  of the 7 non-all-max combinations of (bltu_2, bltu_1, bltu_0).

  Each case has its OWN postcondition definition that uses `iterN2Max`/`iterN2Call`
  directly (matching the proof-level let-bindings). The postcondition consequence
  step then uses `delta fullDivN2_XXX_Post` to expand to expressions that exactly
  match the proof's let-bindings, allowing `xperm_hyp` to succeed.

  The (F,F,F) case is already in FullPathN2Full.lean as `fullDivN2AllMaxPost` /
  `evm_div_n2_full_all_max_spec`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Per-case postcondition definitions
-- ============================================================================

/-- Full path postcondition for n=2 DIV case (F,F,T): r2=Max, r1=Max, r0=Call.
    Scratch cells: j=0 call scratch. -/
@[irreducible]
def fullDivN2_FFT_Post (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1') **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
  (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)

/-- Full path postcondition for n=2 DIV case (F,T,F): r2=Max, r1=Call, r0=Max.
    Scratch cells: j=1 call scratch. -/
@[irreducible]
def fullDivN2_FTF_Post (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1') **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
  (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)

/-- Full path postcondition for n=2 DIV case (F,T,T): r2=Max, r1=Call, r0=Call.
    Scratch cells: j=0 call scratch. -/
@[irreducible]
def fullDivN2_FTT_Post (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1') **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
  (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)

/-- Full path postcondition for n=2 DIV case (T,F,F): r2=Call, r1=Max, r0=Max.
    Scratch cells: j=2 call scratch. -/
@[irreducible]
def fullDivN2_TFF_Post (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1') **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u3_s)

/-- Full path postcondition for n=2 DIV case (T,F,T): r2=Call, r1=Max, r0=Call.
    Scratch cells: j=0 call scratch. -/
@[irreducible]
def fullDivN2_TFT_Post (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1') **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
  (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)

/-- Full path postcondition for n=2 DIV case (T,T,F): r2=Call, r1=Call, r0=Max.
    Scratch cells: j=1 call scratch. -/
@[irreducible]
def fullDivN2_TTF_Post (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1') **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
  (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)

/-- Full path postcondition for n=2 DIV case (T,T,T): r2=Call, r1=Call, r0=Call.
    Scratch cells: j=0 call scratch. -/
@[irreducible]
def fullDivN2_TTT_Post (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1') **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
  (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)

-- ============================================================================
-- Case (F,F,T): r2=Max, r1=Max, r0=Call — j0 call scratch
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
theorem evm_div_n2_full_FFT_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 false a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 false false a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 false false true a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullDivN2_FFT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 v1') v0' v1' v2' v3'
    u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec false false true sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_2 hbltu_1 hbltu_0
  -- 2. Post-loop: base+904 → base+1064
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1') **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_false,
        loopIterPostN2_call, loopIterPostN2Call,
        sepConj_emp_right', loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2_FFT_Post; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Case (F,T,F): r2=Max, r1=Call, r0=Max — j1 call scratch
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
theorem evm_div_n2_full_FTF_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 false a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 false true a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 false true false a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullDivN2_FTF_Post sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3'
    u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec false true false sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_2 hbltu_1 hbltu_0
  -- 2. Post-loop: base+904 → base+1064
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1') **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_false, iterN2_true,
        loopIterPostN2_max, loopIterPostN2Max,
        sepConj_emp_right', loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2_FTF_Post; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Case (F,T,T): r2=Max, r1=Call, r0=Call — j0 call scratch
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
theorem evm_div_n2_full_FTT_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 false a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 false true a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 false true true a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullDivN2_FTT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 v1') v0' v1' v2' v3'
    u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec false true true sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_2 hbltu_1 hbltu_0
  -- 2. Post-loop: base+904 → base+1064
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1') **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_false, iterN2_true,
        loopIterPostN2_call, loopIterPostN2Call,
        sepConj_emp_right', loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2_FTT_Post; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Case (T,F,F): r2=Call, r1=Max, r0=Max — j2 call scratch
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
theorem evm_div_n2_full_TFF_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 true a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 true false a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 true false false a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullDivN2_TFF_Post sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3'
    u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec true false false sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_2 hbltu_1 hbltu_0
  -- 2. Post-loop: base+904 → base+1064
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1') **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u3_s))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_false, iterN2_true,
        loopIterPostN2_max, loopIterPostN2Max,
        sepConj_emp_right', loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2_TFF_Post; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Case (T,F,T): r2=Call, r1=Max, r0=Call — j0 call scratch
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
theorem evm_div_n2_full_TFT_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 true a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 true false a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 true false true a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullDivN2_TFT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 v1') v0' v1' v2' v3'
    u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec true false true sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_2 hbltu_1 hbltu_0
  -- 2. Post-loop: base+904 → base+1064
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1') **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_false, iterN2_true,
        loopIterPostN2_call, loopIterPostN2Call,
        sepConj_emp_right', loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2_TFT_Post; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Case (T,T,F): r2=Call, r1=Call, r0=Max — j1 call scratch
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
theorem evm_div_n2_full_TTF_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 true a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 true true a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 true true false a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullDivN2_TTF_Post sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3'
    u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec true true false sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_2 hbltu_1 hbltu_0
  -- 2. Post-loop: base+904 → base+1064
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1') **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_true,
        loopIterPostN2_max, loopIterPostN2Max,
        sepConj_emp_right', loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2_TTF_Post; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Case (T,T,T): r2=Call, r1=Call, r0=Call — j0 call scratch
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
theorem evm_div_n2_full_TTT_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 true a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 true true a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 true true true a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullDivN2_TTT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r2 := iterN2Call v0' v1' v2' v3' u2_s u3_s u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 v1') v0' v1' v2' v3'
    u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec true true true sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_2 hbltu_1 hbltu_0
  -- 2. Post-loop: base+904 → base+1064
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1') **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_true,
        loopIterPostN2_call, loopIterPostN2Call,
        sepConj_emp_right', loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2_TTT_Post; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
