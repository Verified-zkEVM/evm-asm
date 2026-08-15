/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Body

  Body compose for `zkvm_sha256` (#12018):
    Setup (B+28→B+100) → Outer (B+100→B+196) → PadThenBitlen (both rem
    arms, B+196→B+396) → SqueezeToExit (B+396→B+452).

  Operational digest `sha256BodyDigest` is the machine post at bodyExit;
  SpecRef equality is the named bridge `sha256BodyDigest_eq_specref` in Top.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Final
import EvmAsm.Codegen.Proofs.HashBridgeSha256Pad
import EvmAsm.Codegen.Proofs.HashBridgeSha256SqueezeLoop
import EvmAsm.Codegen.Proofs.HashBridgeSha256OuterBody
import EvmAsm.Codegen.Proofs.HashBridgeSha256Setup
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SAsm.PhaseSplit
import EvmAsm.Rv64.ZiskAccel
import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.SAsm.AccelStep

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Accel
open EvmAsm.Codegen
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev ShaState : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_state
private abbrev ShaInput : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_input
private abbrev ShaIv : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_iv
private abbrev ShaParams : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL
private abbrev sha256BlockStep : Nat := 64

local macro "pcf" : tactic =>
  `(tactic| repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _
    | exact pcFree_anyBytes _ _
    | assumption)

/-! ## Operational digest (machine body post, not SpecRef) -/

/-- BSS image of SpecRef `sha256IV` (4 LE dwords = 32 bytes). -/
def sha256IvBytes : List (BitVec 8) :=
  (u32sToDwords sha256IV).flatMap dwordBytes

theorem sha256IvBytes_length : sha256IvBytes.length = 32 := by
  simp only [sha256IvBytes, sha256IV]
  rw [length_flatMap_dwordBytes, length_u32sToDwords]
  decide

/-- Bit-length word written by setup (`SLLI x20, x11, 3`). -/
def sha256BitLenW (N rem : Nat) : Word :=
  BitVec.ofNat 64 (sha256BlockStep * N + rem) <<< 3

/-- Byte `j` of the BE bit-length field written by `sha256BitlenBE`. -/
theorem sha256BitLenW_shift_byte (N rem j : Nat) (_hj : j < 8) :
    ((sha256BitLenW N rem) >>> (8 * (7 - j))).truncate 8 =
      BitVec.ofNat 8 ((((64 * N + rem) * 8) % 2 ^ 64) >>> (8 * (7 - j))) := by
  unfold sha256BitLenW sha256BlockStep
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_mod, Nat.mod_mod]

/-- Residual bytes after `N` full blocks. -/
def sha256Residual (input : List (BitVec 8)) (N : Nat) : List (BitVec 8) :=
  input.drop (sha256BlockStep * N)

/-- Zero scratch used by pad (pad path re-zeros regardless of entry bytes). -/
def sha256ZeroScratch : List (BitVec 8) := List.replicate 64 (0 : BitVec 8)

theorem sha256ZeroScratch_length : sha256ZeroScratch.length = 64 := by
  simp [sha256ZeroScratch]

/-- Final 64-byte block after pad+bitlen for the rem&lt;56 arm. -/
def sha256FinalBlock_lt56 (residual : List (BitVec 8)) (rem : Nat) (bitLen : Word) :
    List (BitVec 8) :=
  sha256BitlenBE (sha256PadScratch_lt56 residual sha256ZeroScratch rem) bitLen

/-- Final 64-byte block after pad+bitlen for the rem≥56 arm. -/
def sha256FinalBlock_ge56 (residual : List (BitVec 8)) (rem : Nat) (bitLen : Word) :
    List (BitVec 8) :=
  sha256BitlenBE (sha256PadScratch_ge56 residual sha256ZeroScratch rem) bitLen

/-- State bytes after absorb + pad-path compress(es), before BE squeeze. -/
def sha256BodyFinalState (input : List (BitVec 8)) (N rem : Nat) : List (BitVec 8) :=
  let stN := sha256AbsorbedState sha256IvBytes input N
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  if rem < 56 then
    sha256CompressBytes stN (sha256FinalBlock_lt56 res rem bitLen)
  else
    let stMid := sha256CompressBytes stN
      (sha256PadScratch_lt56 res sha256ZeroScratch rem)
    sha256CompressBytes stMid (sha256FinalBlock_ge56 res rem bitLen)

/-- Operational digest produced by the machine body (absorb + pad + squeeze).
    Must NOT equal `SpecRef.sha256` by definition — that is the named bridge. -/
def sha256BodyDigest (input : List (BitVec 8)) (N rem : Nat) : List (BitVec 8) :=
  sha256SqueezeBE (sha256BodyFinalState input N rem)

theorem sha256BodyDigest_length (input : List (BitVec 8)) (N rem : Nat) :
    (sha256BodyDigest input N rem).length = 32 :=
  sha256SqueezeBE_length _

/-! ## Free temps / ambient helpers -/

/-- Ambient framed under Outer: bitlen, out ptr, x0, IV BSS, output, free A. -/
def sha256OuterFrameAmb (outputBase : Word) (bitLen : Word)
    (iv out0 : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ bitLen) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion ShaIv iv ** bytesRegion outputBase out0 ** A

theorem sha256OuterFrameAmb_pcFree (outputBase : Word) (bitLen : Word)
    (iv out0 : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (sha256OuterFrameAmb outputBase bitLen iv out0 A).pcFree := by
  simp only [sha256OuterFrameAmb]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Pad temps required under PadFocusAmb's free `A` (from SetupOuter / caller). -/
def sha256PadTemps : Assertion :=
  (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30)

theorem sha256PadTemps_pcFree : sha256PadTemps.pcFree := by
  simp only [sha256PadTemps]
  exact pcFree_sepConj (pcFree_regOwn (r := .x6)) <|
    pcFree_sepConj (pcFree_regOwn (r := .x7)) <|
    pcFree_sepConj (pcFree_regOwn (r := .x28)) <|
    pcFree_sepConj (pcFree_regOwn (r := .x29)) <|
    pcFree_regOwn (r := .x30)

/-! ## Setup post → Outer pre reshape -/

private theorem cursor0 (inputBase : Word) :
    sha256AbsorbCursor inputBase 0 = inputBase :=
  sha256AbsorbCursor_zero inputBase

private theorem absorbed0 (st0 : List (BitVec 8)) (input : List (BitVec 8)) :
    sha256AbsorbedState st0 input 0 = st0 :=
  sha256AbsorbedState_zero st0 input

/-- Setup post (flat) → OuterLoop entry (packaged OuterInv + scratch).
    Demotes ABI x11/x12 and setup x6; keeps x10 concrete, frames OuterAmb. -/
theorem sha256SetupPost_to_outerPre (h : PartialState)
    (inputBase outputBase : Word) (lenW bitLen : Word)
    (input params iv scratch out0 : List (BitVec 8))
    (N rem : Nat) (A : Assertion)
    (hlenW : lenW = BitVec.ofNat 64 (sha256BlockStep * N + rem))
    (hbit : bitLen = lenW <<< 3)
    (hp :
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ bitLen) **
        (.x21 ↦ᵣ ShaInput) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion ShaState iv ** bytesRegion ShaIv iv **
        bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
        bytesRegion inputBase input ** bytesRegion outputBase out0 **
        (.x0 ↦ᵣ (0 : Word)) ** A) h) :
    ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * N + rem)) **
      (regOwn .x5) **
      sha256OuterInv inputBase ShaState ShaInput ShaParams
        input params iv N N **
      (.x10 ↦ᵣ inputBase) ** bytesRegion ShaInput scratch **
      sha256OuterFrameAmb outputBase bitLen iv out0
        ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A)) h := by
  have hq1 :
      ((.x10 ↦ᵣ inputBase) ** (regOwn .x11) ** (regOwn .x12) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ bitLen) **
        (.x21 ↦ᵣ ShaInput) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion ShaState iv ** bytesRegion ShaIv iv **
        bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
        bytesRegion inputBase input ** bytesRegion outputBase out0 **
        (.x0 ↦ᵣ (0 : Word)) ** A) h := by
    -- Peel x10, demote x11 then x12 under the trailing conjunct.
    refine sepConj_mono_right ?_ h hp
    intro h1 hp1
    have hp1' := sepConj_mono_left (regIs_implies_regOwn (r := .x11) (v := lenW)) h1 hp1
    refine sepConj_mono_right ?_ h1 hp1'
    intro h2 hp2
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x12) (v := outputBase)) h2 hp2
  have hp0 :
      ((.x18 ↦ᵣ lenW) ** (regOwn .x5) **
        (.x9 ↦ᵣ inputBase) ** bytesRegion ShaState iv **
        (.x8 ↦ᵣ ShaState) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion inputBase input ** bytesRegion ShaParams params **
        (.x10 ↦ᵣ inputBase) ** bytesRegion ShaInput scratch **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ bitLen) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion ShaIv iv ** bytesRegion outputBase out0 **
        (regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A) h := by
    xperm_chunked hq1
  simp only [hlenW, hbit, sha256OuterInv, sha256OuterAmb, sha256OuterFrameAmb,
    Nat.sub_self, cursor0, absorbed0] at hp0 ⊢
  xperm_chunked hp0

/-! ## Setup framed + reshape = B+28 → B+100 Outer entry -/

/-- Body entry → Outer entry. Fuel 18. -/
theorem sha256SetupToOuterEntry_spec
    (inputBase outputBase : Word) (N rem : Nat)
    (v8 v9 v18 v19 v20 v21 v5 v6 : Word)
    (st0 scratch params iv out0 : List (BitVec 8))
    (input : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hst : st0.length = 32) (hiv : iv.length = 32)
    (_hscratch : scratch.length = 64) (_hparams : params.length = 16)
    (_hout : out0.length = 32) :
    let lenW := BitVec.ofNat 64 (sha256BlockStep * N + rem)
    let bitLen := lenW <<< 3
    cpsTripleWithin 18 (B + 28) (B + 100) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv **
        bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
        bytesRegion inputBase input ** bytesRegion outputBase out0 **
        (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x18 ↦ᵣ lenW) ** (regOwn .x5) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N N **
        (.x10 ↦ᵣ inputBase) ** bytesRegion ShaInput scratch **
        sha256OuterFrameAmb outputBase bitLen iv out0
          ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A)) := by
  intro lenW bitLen
  let Amb : Assertion :=
    bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
      bytesRegion inputBase input ** bytesRegion outputBase out0 **
      (.x0 ↦ᵣ (0 : Word)) ** A
  have hAmb : Amb.pcFree := by
    simp only [Amb]
    exact pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (by pcf) hA
  have c0 := sha256SetupToOuter_spec inputBase lenW outputBase
    v8 v9 v18 v19 v20 v21 v5 v6 st0 iv Amb hAmb hst hiv
  refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢; xperm_chunked hp)
    (fun h hq => by
      simp only [Amb] at hq
      exact sha256SetupPost_to_outerPre h inputBase outputBase lenW bitLen
        input params iv scratch out0 N rem A rfl rfl (by xperm_chunked hq))
    c0

/-! ## Outer framed under OuterFrameAmb -/

/-- Accel residual for one outer-body CSRS at remaining-count `n`. -/
def sha256OuterHsem (_inputBase stateBase scratchBase paramsBase : Word)
    (input params st0 : List (BitVec 8)) (N : Nat) : Prop :=
  ∀ n, n < N →
    ∀ (R : Assertion) (s : MachineState),
      let st := sha256AbsorbedState st0 input (N - (n + 1))
      let blk := (input.drop (sha256BlockStep * (N - (n + 1)))).take sha256BlockStep
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase st ** bytesRegion scratchBase blk) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, sha256CompressPayload st blk)

/-- Outer absorb with OuterFrameAmb framed. Fuel `N*24+2`. -/
theorem sha256OuterLoop_framed
    (inputBase outputBase : Word) (N rem : Nat)
    (input params iv scratch out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hiv : iv.length = 32) (hscratch : scratch.length = 64)
    (hparams : params.length = 16)
    (hrem : rem < sha256BlockStep)
    (hfit : sha256BlockStep * N + rem ≤ input.length)
    (hNbound : sha256BlockStep * N + rem < 2 ^ 63)
    (hcur : inputBase.toNat + sha256BlockStep * N < 2 ^ 64)
    (hsem : sha256OuterHsem inputBase ShaState ShaInput ShaParams input params iv N) :
    let lenW := BitVec.ofNat 64 (sha256BlockStep * N + rem)
    let bitLen := lenW <<< 3
    cpsTripleWithin (N * 24 + 2) (B + 100) (B + 196) sha256Cr
      ((.x18 ↦ᵣ lenW) ** (regOwn .x5) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N N **
        (.x10 ↦ᵣ inputBase) ** bytesRegion ShaInput scratch **
        sha256OuterFrameAmb outputBase bitLen iv out0 A)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N 0 **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        sha256OuterFrameAmb outputBase bitLen iv out0 A) := by
  intro lenW bitLen
  have c0 := sha256OuterLoop_spec inputBase ShaState ShaInput ShaParams
    input params iv scratch N rem inputBase hiv hscratch hparams
    hrem hfit hNbound hcur hsem
  have hF := sha256OuterFrameAmb_pcFree outputBase bitLen iv out0 A hA
  have cF := cpsTripleWithin_frameR
    (sha256OuterFrameAmb outputBase bitLen iv out0 A) hF c0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) cF

/-! ## Setup ∘ Outer : B+28 → B+196 -/

theorem sha256SetupOuter_spec
    (inputBase outputBase : Word) (N rem : Nat)
    (v8 v9 v18 v19 v20 v21 v5 v6 : Word)
    (st0 scratch params iv out0 : List (BitVec 8))
    (input : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hst : st0.length = 32) (hiv : iv.length = 32)
    (hscratch : scratch.length = 64) (hparams : params.length = 16)
    (hout : out0.length = 32)
    (hrem : rem < sha256BlockStep)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hNbound : sha256BlockStep * N + rem < 2 ^ 63)
    (hcur : inputBase.toNat + sha256BlockStep * N < 2 ^ 64)
    (hsem : sha256OuterHsem inputBase ShaState ShaInput ShaParams input params iv N) :
    let lenW := BitVec.ofNat 64 (sha256BlockStep * N + rem)
    let bitLen := lenW <<< 3
    cpsTripleWithin (18 + (N * 24 + 2)) (B + 28) (B + 196) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv **
        bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
        bytesRegion inputBase input ** bytesRegion outputBase out0 **
        (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N 0 **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        sha256OuterFrameAmb outputBase bitLen iv out0
          ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A)) := by
  intro lenW bitLen
  have hfit : sha256BlockStep * N + rem ≤ input.length := by
    simp only [hlen]; exact Nat.le_refl _
  have cSetup := sha256SetupToOuterEntry_spec inputBase outputBase N rem
    v8 v9 v18 v19 v20 v21 v5 v6 st0 scratch params iv out0 input A hA
    hst hiv hscratch hparams hout
  have cOuter := sha256OuterLoop_framed inputBase outputBase N rem
    input params iv scratch out0
    ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A)
    (by pcf) hiv hscratch hparams hrem hfit hNbound hcur hsem
  -- Align let-bound lenW/bitLen in both triples
  have cSetup' : cpsTripleWithin 18 (B + 28) (B + 100) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv **
        bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
        bytesRegion inputBase input ** bytesRegion outputBase out0 **
        (.x0 ↦ᵣ (0 : Word)) ** A)
      ((.x18 ↦ᵣ lenW) ** (regOwn .x5) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N N **
        (.x10 ↦ᵣ inputBase) ** bytesRegion ShaInput scratch **
        sha256OuterFrameAmb outputBase bitLen iv out0
          ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A)) := by
    simpa [lenW, bitLen] using cSetup
  have cOuter' : cpsTripleWithin (N * 24 + 2) (B + 100) (B + 196) sha256Cr
      ((.x18 ↦ᵣ lenW) ** (regOwn .x5) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N N **
        (.x10 ↦ᵣ inputBase) ** bytesRegion ShaInput scratch **
        sha256OuterFrameAmb outputBase bitLen iv out0
          ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A))
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N 0 **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        sha256OuterFrameAmb outputBase bitLen iv out0
          ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** A)) := by
    simpa [lenW, bitLen] using cOuter
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    cSetup' cOuter'


/-! ## Outer post → Pad entry reshape -/

private theorem input_split_eq (inputBase : Word) (input : List (BitVec 8))
    (N rem : Nat) (hlen : input.length = sha256BlockStep * N + rem)
    (hN8 : (sha256BlockStep * N) % 8 = 0) :
    bytesRegion inputBase input =
      (bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        bytesRegion (inputBase + BitVec.ofNat 64 (sha256BlockStep * N))
          (input.drop (sha256BlockStep * N))) := by
  set n := sha256BlockStep * N
  have hpre : (input.take n).length = n := by
    simp only [n, List.length_take, hlen]; omega
  have h8 : 8 ∣ (input.take n).length := by
    rw [hpre]; exact Nat.dvd_of_mod_eq_zero hN8
  have happ := bytesRegion_append inputBase (input.take n) (input.drop n) h8
  rw [List.take_append_drop] at happ
  simpa [hpre] using happ

/-- Pad focus ambient after Outer (state/params/out/IV/prefix + owns). -/
def sha256PadFocusAmb (outputBase inputBase : Word) (input : List (BitVec 8))
    (params iv out0 : List (BitVec 8)) (N : Nat) (A : Assertion) : Assertion :=
  (.x8 ↦ᵣ ShaState) **
    bytesRegion ShaState (sha256AbsorbedState iv input N) **
    bytesRegion ShaParams params **
    (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
    bytesRegion ShaIv iv **
    bytesRegion inputBase (input.take (sha256BlockStep * N)) **
    (regOwn .x10) ** A

theorem sha256PadFocusAmb_pcFree (outputBase inputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N : Nat)
    (A : Assertion) (hA : A.pcFree) :
    (sha256PadFocusAmb outputBase inputBase input params iv out0 N A).pcFree := by
  simp only [sha256PadFocusAmb]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (pcFree_regOwn (r := .x10)) hA

/-- Pad-path core (cursor/residual + pad registers) without scratch/focus amb. -/
def sha256PadCore (inputBase : Word) (input : List (BitVec 8)) (N rem : Nat) : Assertion :=
  (.x21 ↦ᵣ ShaInput) **
    (.x9 ↦ᵣ sha256AbsorbCursor inputBase N) **
    (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
    (.x20 ↦ᵣ sha256BitLenW N rem) **
    (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion (sha256AbsorbCursor inputBase N) (sha256Residual input N)

/-- Pad entry after `sha256OuterPost_to_padEntry` (`anyBytes` trailing for lift).
    Pad temps live in `A` (typically `sha256PadTemps ** …`). -/
def sha256PadEntryPre (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A : Assertion) : Assertion :=
  (sha256PadCore inputBase input N rem **
    sha256PadFocusAmb outputBase inputBase input params iv out0 N A) **
  anyBytes ShaInput 64

/-- Outer post → PadThenBitlen entry (residual focused; scratch still
    `anyBytes` — lift via `cpsTripleWithin_anyBytes_pre` at seq site).
    Does not invent x6/x7/x28 — those stay in ambient `A`. -/
theorem sha256OuterPost_to_padEntry (h : PartialState)
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A : Assertion)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hp :
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams
          input params iv N 0 **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        sha256OuterFrameAmb outputBase (sha256BitLenW N rem) iv out0 A) h) :
    (sha256PadEntryPre inputBase outputBase input params iv out0 N rem A) h := by
  -- Unfold packaged inv/amb into a nested product, then flatten with xperm.
  have hpU :
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        ((.x9 ↦ᵣ sha256AbsorbCursor inputBase N) **
          bytesRegion ShaState (sha256AbsorbedState iv input N) **
            ((.x8 ↦ᵣ ShaState) ** (.x21 ↦ᵣ ShaInput) **
              bytesRegion inputBase input ** bytesRegion ShaParams params)) **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        ((.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ sha256BitLenW N rem) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion ShaIv iv ** bytesRegion outputBase out0 ** A)) h := by
    simpa [sha256OuterInv, sha256OuterAmb, sha256OuterFrameAmb, Nat.sub_zero,
      sha256BitLenW, sha256BlockStep] using hp
  have hpFlat :
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        (.x9 ↦ᵣ sha256AbsorbCursor inputBase N) **
        bytesRegion ShaState (sha256AbsorbedState iv input N) **
        (.x8 ↦ᵣ ShaState) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion inputBase input ** bytesRegion ShaParams params **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ sha256BitLenW N rem) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion ShaIv iv ** bytesRegion outputBase out0 ** A) h := by
    xperm_chunked hpU
  have hN8 : (sha256BlockStep * N) % 8 = 0 := by
    simp only [sha256BlockStep]; omega
  have hsplit := input_split_eq inputBase input N rem hlen hN8
  -- Rewrite the full-input atom to take ** residual (nested), then flatten.
  have hpSplit :
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        (.x9 ↦ᵣ sha256AbsorbCursor inputBase N) **
        bytesRegion ShaState (sha256AbsorbedState iv input N) **
        (.x8 ↦ᵣ ShaState) ** (.x21 ↦ᵣ ShaInput) **
        (bytesRegion inputBase (input.take (sha256BlockStep * N)) **
          bytesRegion (sha256AbsorbCursor inputBase N) (sha256Residual input N)) **
        bytesRegion ShaParams params **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ sha256BitLenW N rem) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion ShaIv iv ** bytesRegion outputBase out0 ** A) h := by
    rw [hsplit,
      show inputBase + BitVec.ofNat 64 (sha256BlockStep * N) =
        sha256AbsorbCursor inputBase N from rfl,
      show input.drop (sha256BlockStep * N) = sha256Residual input N from rfl] at hpFlat
    exact hpFlat
  have hp1 :
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        (.x9 ↦ᵣ sha256AbsorbCursor inputBase N) **
        bytesRegion ShaState (sha256AbsorbedState iv input N) **
        (.x8 ↦ᵣ ShaState) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        bytesRegion (sha256AbsorbCursor inputBase N) (sha256Residual input N) **
        bytesRegion ShaParams params **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ sha256BitLenW N rem) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion ShaIv iv ** bytesRegion outputBase out0 ** A) h := by
    xperm_chunked hpSplit
  -- Target PadEntryPre association: `(core ** focus) ** anyBytes`.
  have hp2 :
      ((sha256PadCore inputBase input N rem **
          sha256PadFocusAmb outputBase inputBase input params iv out0 N A) **
        anyBytes ShaInput 64) h := by
    -- Unfold defs so xperm sees a flat product matching hp1's atoms.
    simp only [sha256PadCore, sha256PadFocusAmb]
    xperm_chunked hp1
  simpa [sha256PadEntryPre] using hp2

/-! ## Accel CSRS residuals (explicit `hsem`; no fake discharges) -/

/-- Mid compress during rem≥56 pad (CSRS at B+288). -/
def sha256BodyPadMidHsem (stateBase scratchBase paramsBase : Word)
    (iv input params : List (BitVec 8)) (N rem : Nat) : Prop :=
  let st0 := sha256AbsorbedState iv input N
  let res := sha256Residual input N
  let payload := sha256CompressPayload st0
    (sha256PadScratch_lt56 res sha256ZeroScratch rem)
  ∀ (R : Assertion) (s : MachineState),
    (((.x8 ↦ᵣ stateBase) **
      (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
      (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
      bytesRegion stateBase st0 **
      bytesRegion scratchBase (sha256PadScratch_lt56 res sha256ZeroScratch rem)) ** R).holdsFor s →
    s.csrsValid 0x805 .x10 = true ∧
    s.csrsWrite 0x805 .x10 = (stateBase, payload)

/-- Final compress CSRS during squeeze (rem&lt;56 arm). -/
def sha256BodySqueezeHsem_lt56 (stateBase scratchBase paramsBase : Word)
    (iv input params : List (BitVec 8)) (N rem : Nat) : Prop :=
  let st0 := sha256AbsorbedState iv input N
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  let scratch := sha256FinalBlock_lt56 res rem bitLen
  let payload := sha256CompressPayload st0 scratch
  ∀ (R : Assertion) (s : MachineState),
    (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
      (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
      bytesRegion stateBase st0 ** bytesRegion scratchBase scratch) ** R).holdsFor s →
    s.csrsValid 0x805 .x10 = true ∧
    s.csrsWrite 0x805 .x10 = (stateBase, payload)

/-- Final compress CSRS during squeeze (rem≥56 arm). -/
def sha256BodySqueezeHsem_ge56 (stateBase scratchBase paramsBase : Word)
    (iv input params : List (BitVec 8)) (N rem : Nat) : Prop :=
  let stMid := sha256CompressBytes (sha256AbsorbedState iv input N)
    (sha256PadScratch_lt56 (sha256Residual input N) sha256ZeroScratch rem)
  let bitLen := sha256BitLenW N rem
  let scratch := sha256FinalBlock_ge56 (sha256Residual input N) rem bitLen
  let payload := sha256CompressPayload stMid scratch
  ∀ (R : Assertion) (s : MachineState),
    (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
      (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
      bytesRegion stateBase stMid ** bytesRegion scratchBase scratch) ** R).holdsFor s →
    s.csrsValid 0x805 .x10 = true ∧
    s.csrsWrite 0x805 .x10 = (stateBase, payload)

/-- State after rem≥56 pad path (mid compress applied). -/
def sha256BodyMidState_ge56 (iv input : List (BitVec 8)) (N rem : Nat) :
    List (BitVec 8) :=
  sha256CompressBytes (sha256AbsorbedState iv input N)
    (sha256PadScratch_lt56 (sha256Residual input N) sha256ZeroScratch rem)

/-- Ambient at body exit (no duplicate state/output atoms). -/
def sha256BodyExitAmb (inputBase : Word) (input iv : List (BitVec 8)) (N : Nat)
    (A : Assertion) : Assertion :=
  bytesRegion ShaIv iv **
    bytesRegion inputBase (input.take (sha256BlockStep * N)) **
    bytesRegion (sha256AbsorbCursor inputBase N) (sha256Residual input N) **
    (regOwn .x9) ** (regOwn .x18) ** (regOwn .x20) ** (regOwn .x0) ** A

theorem sha256BodyExitAmb_pcFree (inputBase : Word) (input iv : List (BitVec 8))
    (N : Nat) (A : Assertion) (hA : A.pcFree) :
    (sha256BodyExitAmb inputBase input iv N A).pcFree := by
  simp only [sha256BodyExitAmb]
  exact pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) hA

/-- Body exit post (matches `sha256SqueezeToExit_spec`, then weakened). -/
def sha256BodyExitPost (inputBase outputBase : Word) (input params iv : List (BitVec 8))
    (N rem : Nat) (A : Assertion) : Assertion :=
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  let scratch :=
    if rem < 56 then sha256FinalBlock_lt56 res rem bitLen
    else sha256FinalBlock_ge56 res rem bitLen
  let st := sha256BodyFinalState input N rem
  ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
    regOwn .x10 ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
    bytesRegion ShaParams params **
    bytesRegion ShaState st **
    bytesRegion ShaInput scratch **
    bytesRegion outputBase (sha256BodyDigest input N rem) **
    regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    sha256BodyExitAmb inputBase input iv N A)

private theorem residual_length_eq (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = sha256BlockStep * N + rem) :
    (sha256Residual input N).length = rem := by
  simp only [sha256Residual, List.length_drop, hlen]; omega

private theorem residual_take_eq (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = sha256BlockStep * N + rem) :
    (sha256Residual input N).take rem = sha256Residual input N :=
  List.take_of_length_le (by rw [residual_length_eq input N rem hlen])

private theorem sep_flat_mid_holds (P A B Q : Assertion) (h : PartialState)
    (hp : (P ** (A ** B) ** Q) h) : (P ** A ** B ** Q) h := by
  have hp' : (P ** ((A ** B) ** Q)) h := by simpa using hp
  exact sepConj_mono_right
    (fun h' hh' => (sepConj_assoc (P := A) (Q := B) (R := Q) h').mp hh')
    h hp'

private theorem sha256BodyFinalState_lt56 (input : List (BitVec 8)) (N rem : Nat)
    (hrem : rem < 56) :
    sha256BodyFinalState input N rem =
      sha256CompressBytes (sha256AbsorbedState sha256IvBytes input N)
        (sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)) := by
  simp only [sha256BodyFinalState, hrem, ↓reduceIte]

private theorem sha256BodyFinalState_ge56 (input : List (BitVec 8)) (N rem : Nat)
    (hrem : 56 ≤ rem) :
    sha256BodyFinalState input N rem =
      sha256CompressBytes (sha256BodyMidState_ge56 sha256IvBytes input N rem)
        (sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)) := by
  unfold sha256BodyFinalState
  simp only [Nat.not_lt.mpr hrem, ↓reduceIte, sha256BodyMidState_ge56]

private theorem sha256AbsorbedState_ivBytes (iv input : List (BitVec 8)) (N : Nat)
    (hivEq : iv = sha256IvBytes) :
    sha256AbsorbedState iv input N = sha256AbsorbedState sha256IvBytes input N := by
  subst hivEq; rfl

private theorem sha256ShaInput_align8 : ShaInput.toNat % 8 = 0 := by decide

private theorem sha256ShaInput_hover : ShaInput.toNat + 64 < 2 ^ 64 := by decide

private theorem sha256ShaState_align8 : ShaState.toNat % 8 = 0 := by decide

private theorem sha256ShaState_over : ShaState.toNat + 32 ≤ 2 ^ 64 := by decide

/-- Pad ambient during PadThenBitlen: focus owns that stay ambient through pad
    (`x29`/`x30` only — `x6`/`x7`/`x28` are pad-active). -/
def sha256PadThenBitlenAmb (outputBase inputBase : Word) (input params iv out0 : List (BitVec 8))
    (N : Nat) (A : Assertion) : Assertion :=
  sha256PadFocusAmb outputBase inputBase input params iv out0 N
    ((regOwn .x29) ** (regOwn .x30) ** A)

theorem sha256PadThenBitlenAmb_pcFree (outputBase inputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N : Nat)
    (A : Assertion) (hA : A.pcFree) :
    (sha256PadThenBitlenAmb outputBase inputBase input params iv out0 N A).pcFree := by
  simp only [sha256PadThenBitlenAmb, sha256PadFocusAmb]
  apply sha256PadFocusAmb_pcFree
  exact pcFree_sepConj (pcFree_regOwn (r := .x29)) <|
    pcFree_sepConj (pcFree_regOwn (r := .x30)) hA

/-- PadThenBitlen post (rem&lt;56) with canonical zero scratch. -/
def sha256PadThenBitlenPost_lt56 (cursor : Word) (res : List (BitVec 8)) (bitLen : Word)
    (rem : Nat) (F : Assertion) : Assertion :=
  ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
    (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
    (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
    (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion cursor res **
    bytesRegion ShaInput (sha256FinalBlock_lt56 res rem bitLen) **
    regOwn .x28 ** F)

/-- Pad tail ambient (no x8/state/params — those are post-local in rem≥56). -/
def sha256PadTailAmb (outputBase inputBase : Word) (input iv out0 : List (BitVec 8))
    (N : Nat) (A : Assertion) : Assertion :=
  (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
    bytesRegion ShaIv iv **
    bytesRegion inputBase (input.take (sha256BlockStep * N)) **
    ((regOwn .x29) ** (regOwn .x30) ** A)

theorem sha256PadTailAmb_pcFree (outputBase inputBase : Word)
    (input iv out0 : List (BitVec 8)) (N : Nat)
    (A : Assertion) (hA : A.pcFree) :
    (sha256PadTailAmb outputBase inputBase input iv out0 N A).pcFree := by
  simp only [sha256PadTailAmb]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) hA

/-- PadThenBitlen post (rem≥56) with mid writeback + canonical final scratch. -/
@[irreducible]
def sha256PadThenBitlenPost_ge56 (cursor : Word) (res : List (BitVec 8)) (bitLen : Word)
    (rem : Nat) (stMid params : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
    (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
    (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
    (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ ShaState) ** (.x10 ↦ᵣ ShaParams) **
    bytesRegion cursor res **
    bytesRegion ShaInput (sha256FinalBlock_ge56 res rem bitLen) **
    bytesRegion ShaParams params **
    bytesRegion ShaState stMid **
    regOwn .x28 ** F)

@[irreducible]
def sha256PadFramedPre_ge56 (inputBase outputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N rem : Nat) (A0 : Assertion) : Assertion :=
  (sha256PadCore inputBase input N rem **
      sha256PadFocusAmb outputBase inputBase input params iv out0 N
        (sha256PadTemps ** A0)) **
    anyBytes ShaInput 64

theorem sha256PadFramedPre_ge56_eq (inputBase outputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N rem : Nat) (A0 : Assertion) :
    sha256PadFramedPre_ge56 inputBase outputBase input params iv out0 N rem A0 =
      sha256PadEntryPre inputBase outputBase input params iv out0 N rem (sha256PadTemps ** A0) := by
  delta sha256PadFramedPre_ge56 sha256PadEntryPre
  rfl

@[irreducible]
def sha256PadFramedPost_ge56 (inputBase outputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N rem : Nat) (A0 : Assertion) : Assertion :=
  sha256PadThenBitlenPost_ge56 (sha256AbsorbCursor inputBase N)
    (sha256Residual input N) (sha256BitLenW N rem) rem
    (sha256BodyMidState_ge56 iv input N rem) params
    (sha256PadTailAmb outputBase inputBase input iv out0 N A0)

theorem sha256PadFramedPost_ge56_eq (inputBase outputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N rem : Nat) (A0 : Assertion) :
    sha256PadFramedPost_ge56 inputBase outputBase input params iv out0 N rem A0 =
      sha256PadThenBitlenPost_ge56 (sha256AbsorbCursor inputBase N)
        (sha256Residual input N) (sha256BitLenW N rem) rem
        (sha256BodyMidState_ge56 iv input N rem) params
        (sha256PadTailAmb outputBase inputBase input iv out0 N A0) := by
  delta sha256PadFramedPost_ge56
  rfl

private theorem cpsTripleWithin_post_eq {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q Q' : Assertion} (hQ : Q = Q')
    (h : cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr P Q' := by
  subst hQ; exact h

private theorem sha256PadZeroed_eq (scratch : List (BitVec 8)) (h : scratch.length = 64) :
    sha256PadZeroed scratch = sha256ZeroScratch := by
  simpa [sha256ZeroScratch] using sha256PadZeroed_eq_replicate scratch h

private theorem sha256PadScratch_lt56_zero (res : List (BitVec 8)) (scratch0 : List (BitVec 8))
    (rem : Nat) (hscratch : scratch0.length = 64) :
    sha256PadScratch_lt56 res scratch0 rem =
      sha256PadScratch_lt56 res sha256ZeroScratch rem := by
  have h0 := sha256PadZeroed_eq scratch0 hscratch
  have h1 := sha256PadZeroed_eq sha256ZeroScratch sha256ZeroScratch_length
  simp only [sha256PadScratch_lt56, h0, h1]

private theorem sha256FinalBlock_lt56_scratch (res : List (BitVec 8)) (scratch0 : List (BitVec 8))
    (rem : Nat) (bitLen : Word) (hscratch : scratch0.length = 64) :
    sha256BitlenBE (sha256PadScratch_lt56 res scratch0 rem) bitLen =
      sha256FinalBlock_lt56 res rem bitLen := by
  simp only [sha256FinalBlock_lt56]
  rw [sha256PadScratch_lt56_zero res scratch0 rem hscratch]

private theorem sha256PadScratch_ge56_zero (res : List (BitVec 8)) (scratch0 : List (BitVec 8))
    (rem : Nat) (hscratch : scratch0.length = 64) :
    sha256PadScratch_ge56 res scratch0 rem =
      sha256PadScratch_ge56 res sha256ZeroScratch rem := by
  simp only [sha256PadScratch_ge56]
  rw [sha256PadScratch_lt56_zero res scratch0 rem hscratch]

private theorem sha256FinalBlock_ge56_scratch (res : List (BitVec 8)) (scratch0 : List (BitVec 8))
    (rem : Nat) (bitLen : Word) (hscratch : scratch0.length = 64) :
    sha256BitlenBE (sha256PadScratch_ge56 res scratch0 rem) bitLen =
      sha256FinalBlock_ge56 res rem bitLen := by
  simp only [sha256FinalBlock_ge56]
  rw [sha256PadScratch_ge56_zero res scratch0 rem hscratch]

private theorem sha256ShaInput_hover64 : ShaInput.toNat + 64 ≤ 2 ^ 64 := by
  exact Nat.le_of_lt sha256ShaInput_hover

private theorem sha256PadScratch_valid (i : Nat) (hi : i < 64)
    (hvalidScratch : ∀ j < 64, isValidByteAccess (ShaInput + BitVec.ofNat 64 j) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true :=
  hvalidScratch i hi

private theorem sha256PadScratch_valid56 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 56) = true :=
  sha256PadScratch_valid 56 (by decide) hvalidScratch

private theorem sha256PadScratch_valid57 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 57) = true :=
  sha256PadScratch_valid 57 (by decide) hvalidScratch

private theorem sha256PadScratch_valid58 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 58) = true :=
  sha256PadScratch_valid 58 (by decide) hvalidScratch

private theorem sha256PadScratch_valid59 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 59) = true :=
  sha256PadScratch_valid 59 (by decide) hvalidScratch

private theorem sha256PadScratch_valid60 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 60) = true :=
  sha256PadScratch_valid 60 (by decide) hvalidScratch

private theorem sha256PadScratch_valid61 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 61) = true :=
  sha256PadScratch_valid 61 (by decide) hvalidScratch

private theorem sha256PadScratch_valid62 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 62) = true :=
  sha256PadScratch_valid 62 (by decide) hvalidScratch

private theorem sha256PadScratch_valid63 (hvalidScratch : ∀ i < 64,
    isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 63) = true :=
  sha256PadScratch_valid 63 (by decide) hvalidScratch

private theorem sha256PadScratch_validPad (rem : Nat) (hrem : rem < 56)
    (hvalidScratch : ∀ i < 64, isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 rem) = true :=
  sha256PadScratch_valid rem (by omega) hvalidScratch

private theorem sha256PadScratch_validPad_ge56 (rem : Nat) (_hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hvalidScratch : ∀ i < 64, isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    isValidByteAccess (ShaInput + BitVec.ofNat 64 rem) = true :=
  sha256PadScratch_valid rem hrem64 hvalidScratch

private theorem of_forall2_pre {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Tail Post : Assertion} {r1 r2 : Reg}
    (htrip : ∀ (v1 v2 : Word),
      cpsTripleWithin n entry exit cr (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Tail) Post) :
    cpsTripleWithin n entry exit cr (P ** regOwn r1 ** regOwn r2 ** Tail) Post := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hRest, hd0, hu0, hpP0, hpRest⟩ := hpP
  obtain ⟨hR1, hR2rest, hd1, hu1, hpR1, hpR2rest⟩ := hpRest
  obtain ⟨v1, hv1⟩ := hpR1
  obtain ⟨hR2, hTail, hd2, hu2, hpR2, hpTail⟩ := hpR2rest
  obtain ⟨v2, hv2⟩ := hpR2
  have hPR' :
      ((P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Tail) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hRest, hd0, hu0, hpP0,
        ⟨hR1, hR2rest, hd1, hu1, hv1, ⟨hR2, hTail, hd2, hu2, hv2, hpTail⟩⟩⟩, hpR⟩
  exact htrip v1 v2 R hR s hcr hPR' hpc

private theorem of_forall1_pre {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Post : Assertion} {r : Reg}
    (htrip : ∀ (v : Word), cpsTripleWithin n entry exit cr (P ** (r ↦ᵣ v)) Post) :
    cpsTripleWithin n entry exit cr (P ** regOwn r) Post := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hOwn, hd0, hu0, hpP0, hpOwn⟩ := hpP
  obtain ⟨v, hv⟩ := hpOwn
  have hPR' :
      ((P ** (r ↦ᵣ v)) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hOwn, hd0, hu0, hpP0, hv⟩, hpR⟩
  exact htrip v R hR s hcr hPR' hpc

private theorem of_forall3_pre {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Tail Post : Assertion} {r1 r2 r3 : Reg}
    (htrip : ∀ (v1 v2 v3 : Word),
      cpsTripleWithin n entry exit cr
        (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** Tail) Post) :
    cpsTripleWithin n entry exit cr (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** Tail) Post := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hRest, hd0, hu0, hpP0, hpRest⟩ := hpP
  obtain ⟨hR1, hR2rest, hd1, hu1, hpR1, hpR2rest⟩ := hpRest
  obtain ⟨v1, hv1⟩ := hpR1
  obtain ⟨hR2, hTail, hd2, hu2, hpR2, hpTail⟩ := hpR2rest
  obtain ⟨v2, hv2⟩ := hpR2
  obtain ⟨hR3, hTail', hd3, hu3, hpR3, hpTail'⟩ := hpTail
  obtain ⟨v3, hv3⟩ := hpR3
  have hPR' :
      ((P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** Tail) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hRest, hd0, hu0, hpP0,
        ⟨hR1, hR2rest, hd1, hu1, hv1,
          ⟨hR2, hTail, hd2, hu2, hv2, ⟨hR3, hTail', hd3, hu3, hv3, hpTail'⟩⟩⟩⟩, hpR⟩
  exact htrip v1 v2 v3 R hR s hcr hPR' hpc

/-- Zero-step assertion reshape at a fixed PC (same `cr`, no execution). -/
private theorem cpsTripleWithin_reshape0 {entry : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ h, P h → Q h) :
    cpsTripleWithin 0 entry entry cr P Q := by
  intro R hR s hcr hPR hpc
  exact ⟨0, Nat.le_refl 0, s, rfl, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

private theorem setBytes_whole (bs ns : List (BitVec 8))
    (hlen : ns.length = bs.length) : setBytes bs 0 ns = ns := by
  refine List.ext_getElem (by rw [length_setBytes, hlen]) ?_
  intro k hk1 hk2
  have hg := getByteAt_setBytes ns bs 0 k (by omega)
  rw [if_pos ⟨by omega, by omega⟩] at hg
  have hgl : getByteAt (setBytes bs 0 ns) k =
      (setBytes bs 0 ns)[k]'hk1 := by
    unfold getByteAt; rw [dif_pos]
  have hgr : getByteAt ns k = ns[k]'hk2 := by
    unfold getByteAt; rw [dif_pos]
  rw [← hgl, hg, Nat.sub_zero, hgr]

private theorem sha256CsrsWriteback_eq_compress (st0 scratch : List (BitVec 8))
    (payload : List Word) (hst0 : st0.length = 32) (hpayload : payload.length = 4)
    (hpayloadEq : payload = sha256CompressPayload st0 scratch) :
    setBytes st0 0 (payload.flatMap dwordBytes) = sha256CompressBytes st0 scratch := by
  subst hpayloadEq
  have hlen : (sha256CompressBytes st0 scratch).length = st0.length := by
    rw [length_sha256CompressBytes, hst0]
  rw [← sha256CompressBytes_eq_payload]
  exact setBytes_whole st0 (sha256CompressBytes st0 scratch) hlen

private theorem sha256MidWriteback_eq (iv input : List (BitVec 8)) (N rem : Nat)
    (hiv : iv.length = 32) :
    let st0 := sha256AbsorbedState iv input N
    let midScratch := sha256PadScratch_lt56 (sha256Residual input N) sha256ZeroScratch rem
    setBytes st0 0 (sha256CompressPayload st0 midScratch |>.flatMap dwordBytes) =
      sha256BodyMidState_ge56 iv input N rem := by
  intro st0 midScratch
  have hst0 : st0.length = 32 := length_sha256AbsorbedState iv input hiv N
  simp only [sha256BodyMidState_ge56]
  rw [← sha256CompressBytes_eq_payload]
  exact setBytes_whole st0 (sha256CompressBytes st0 midScratch)
    (by rw [length_sha256CompressBytes, hst0])

private theorem bytesRegion_congr (b : Word) {bs bs' : List _} (h : bs = bs') :
    bytesRegion b bs = bytesRegion b bs' := by
  cases h; rfl

private theorem sha256PadThenBitlen_ge56_leaf_post_holds
    (h : PartialState) (cursor : Word) (res : List (BitVec 8)) (bitLen : Word)
    (rem : Nat) (st0 params scratch0 : List (BitVec 8)) (payload : List Word)
    (F : Assertion) (iv input : List (BitVec 8)) (N : Nat) (hiv : iv.length = 32)
    (hst0eq : st0 = sha256AbsorbedState iv input N)
    (hres : res = sha256Residual input N)
    (hscratch : scratch0.length = 64)
    (hpayload : payload = sha256CompressPayload st0
      (sha256PadScratch_lt56 res sha256ZeroScratch rem))
    (hp :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ ShaState) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        bytesRegion ShaInput
          (sha256BitlenBE (sha256PadScratch_ge56 res scratch0 rem) bitLen) **
        bytesRegion ShaParams params **
        bytesRegion ShaState (setBytes st0 0 (payload.flatMap dwordBytes)) **
        regOwn .x28 ** F) h) :
    (sha256PadThenBitlenPost_ge56 cursor res bitLen rem
      (sha256BodyMidState_ge56 iv input N rem) params F) h := by
  have heq : setBytes st0 0 (payload.flatMap dwordBytes) =
      sha256BodyMidState_ge56 iv input N rem := by
    subst hst0eq hres hpayload
    exact sha256MidWriteback_eq iv input N rem hiv
  have hbytes := bytesRegion_congr ShaState heq
  have hscr := sha256FinalBlock_ge56_scratch res scratch0 rem bitLen hscratch
  rw [hscr, hbytes] at hp
  unfold sha256PadThenBitlenPost_ge56
  xperm_chunked hp

/-- Pad entry (concrete scratch, temps in focus) → flat pad-active pre for
    `sha256PadThenBitlen_lt56` (x6/x7 still owned; x28 pad-active). -/
private theorem sha256PadEntry_to_padActive_lt56 (h : PartialState)
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (scratch0 : List (BitVec 8)) (A0 : Assertion)
    (hp :
      ((sha256PadCore inputBase input N rem **
          sha256PadFocusAmb outputBase inputBase input params iv out0 N
            (sha256PadTemps ** A0)) **
        bytesRegion ShaInput scratch0) h) :
    let cursor := sha256AbsorbCursor inputBase N
    let res := sha256Residual input N
    let bitLen := sha256BitLenW N rem
    let F := sha256PadThenBitlenAmb outputBase inputBase input params iv out0 N A0
    ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
      (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
      (regOwn .x6) ** (regOwn .x7) **
      (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
      regOwn .x28 ** F) h := by
  intro cursor res bitLen F
  have hpFlat :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState (sha256AbsorbedState iv input N) **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) **
        (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) **
        (regOwn .x30) ** A0 **
        bytesRegion ShaInput scratch0) h := by
    simp only [sha256PadCore, sha256PadFocusAmb, sha256PadTemps, cursor, res, bitLen] at hp ⊢
    xperm_chunked hp
  have hp1 :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        (regOwn .x6) ** (regOwn .x7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
        regOwn .x28 **
        ((.x8 ↦ᵣ ShaState) **
          bytesRegion ShaState (sha256AbsorbedState iv input N) **
          bytesRegion ShaParams params **
          (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
          bytesRegion ShaIv iv **
          bytesRegion inputBase (input.take (sha256BlockStep * N)) **
          (regOwn .x10) ** (regOwn .x29) ** (regOwn .x30) ** A0)) h := by
    xperm_chunked hpFlat
  simp only [sha256PadThenBitlenAmb, sha256PadFocusAmb, F] at hp1 ⊢
  xperm_chunked hp1

/-- Pad entry (concrete scratch) → flat pad-active pre for rem≥56 pad path. -/
private theorem sha256PadEntry_to_padActive_ge56 (h : PartialState)
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (scratch0 : List (BitVec 8)) (A0 : Assertion)
    (hp :
      ((sha256PadCore inputBase input N rem **
          sha256PadFocusAmb outputBase inputBase input params iv out0 N
            (sha256PadTemps ** A0)) **
        bytesRegion ShaInput scratch0) h) :
    let cursor := sha256AbsorbCursor inputBase N
    let res := sha256Residual input N
    let bitLen := sha256BitLenW N rem
    let st0 := sha256AbsorbedState iv input N
    let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
    ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
      (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
      (regOwn .x6) ** (regOwn .x7) ** (regOwn .x10) **
      (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
      (.x8 ↦ᵣ ShaState) ** bytesRegion ShaParams params ** bytesRegion ShaState st0 **
      regOwn .x28 ** F) h := by
  intro cursor res bitLen st0 F
  have hpFlat :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) **
        (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) **
        (regOwn .x30) ** A0 **
        bytesRegion ShaInput scratch0) h := by
    simp only [sha256PadCore, sha256PadFocusAmb, sha256PadTemps, cursor, res, bitLen, st0] at hp ⊢
    xperm_chunked hp
  have hp1 :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        (regOwn .x6) ** (regOwn .x7) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        regOwn .x28 **
        ((.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
          bytesRegion ShaIv iv **
          bytesRegion inputBase (input.take (sha256BlockStep * N)) **
          (regOwn .x29) ** (regOwn .x30) ** A0)) h := by
    xperm_chunked hpFlat
  simp only [sha256PadTailAmb, F] at hp1 ⊢
  xperm_chunked hp1

/-- PadThenBitlen framed under pad focus (rem&lt;56). Caller packages
    `(regOwn .x6) ** A0` into the focus slot. -/
private theorem sha256PadThenBitlen_framed_lt56
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A0 : Assertion) (hA0 : A0.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hrem : rem < 56)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
      ((sha256PadCore inputBase input N rem **
          sha256PadFocusAmb outputBase inputBase input params iv out0 N
            (sha256PadTemps ** A0)) **
        anyBytes ShaInput 64)
      (sha256PadThenBitlenPost_lt56 (sha256AbsorbCursor inputBase N)
        (sha256Residual input N) (sha256BitLenW N rem) rem
        (sha256PadThenBitlenAmb outputBase inputBase input params iv out0 N A0)) := by
  let cursor := sha256AbsorbCursor inputBase N
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  let F := sha256PadThenBitlenAmb outputBase inputBase input params iv out0 N A0
  have hF : F.pcFree :=
    sha256PadThenBitlenAmb_pcFree outputBase inputBase input params iv out0 N A0 hA0
  have hinp : rem ≤ res.length := by
    rw [residual_length_eq input N rem hlen]
  -- Concrete pad+bitlen for each scratch contents, then lift anyBytes.
  have hconc : ∀ (scratch0 : List (BitVec 8)) (v6 v7 : Word),
      scratch0.length = 64 →
      cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
        ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
          (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
          regOwn .x28 ** F)
        (sha256PadThenBitlenPost_lt56 cursor res bitLen rem F) := by
    intro scratch0 v6 v7 hscratch
    have hraw := sha256PadThenBitlen_lt56 ShaInput cursor bitLen res scratch0 rem
      (BitVec.ofNat 64 sha256BlockStep) v6 v7 F hF
      hcurAlign sha256ShaInput_align8 hscratch hinp hrem hcurOver sha256ShaInput_hover
      hvalidS (fun i hi => hvalidScratch i (by omega))
      (sha256PadScratch_validPad rem hrem hvalidScratch)
      (sha256PadScratch_valid56 hvalidScratch) (sha256PadScratch_valid57 hvalidScratch)
      (sha256PadScratch_valid58 hvalidScratch) (sha256PadScratch_valid59 hvalidScratch)
      (sha256PadScratch_valid60 hvalidScratch) (sha256PadScratch_valid61 hvalidScratch)
      (sha256PadScratch_valid62 hvalidScratch) (sha256PadScratch_valid63 hvalidScratch)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp only [sha256PadThenBitlenPost_lt56, sha256FinalBlock_lt56]
        rw [sha256FinalBlock_lt56_scratch res scratch0 rem bitLen hscratch] at hq
        exact hq)
      hraw
  -- Lift regOwn x6, then x7 (keep x28 pad-active).
  have hlift : ∀ (scratch0 : List (BitVec 8)), scratch0.length = 64 →
      cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
        ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
          (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** F)
        (sha256PadThenBitlenPost_lt56 cursor res bitLen rem F) := by
    intro scratch0 hscratch
    let Pcore : Assertion :=
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep))
    let Qtail : Assertion :=
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
        regOwn .x28 ** F
    have hc2 : ∀ v6 v7, cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
        (Pcore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** Qtail)
        (sha256PadThenBitlenPost_lt56 cursor res bitLen rem F) := by
      intro v6 v7
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => hq)
        (hconc scratch0 v6 v7 hscratch)
    have hown : cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
        (Pcore ** regOwn .x6 ** regOwn .x7 ** Qtail)
        (sha256PadThenBitlenPost_lt56 cursor res bitLen rem F) :=
      of_forall2_pre (P := Pcore) (Tail := Qtail)
        (Post := sha256PadThenBitlenPost_lt56 cursor res bitLen rem F)
        (r1 := .x6) (r2 := .x7) hc2
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => hq) hown
  -- Lift trailing scratch `anyBytes` (before pad-active temps).
  let PadPrefix : Assertion :=
    ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
      (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion cursor res)
  let PadSuffix : Assertion := regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** F
  have hany0 : cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
      ((PadPrefix ** PadSuffix) ** anyBytes ShaInput 64)
      (sha256PadThenBitlenPost_lt56 cursor res bitLen rem F) := by
    refine cpsTripleWithin_anyBytes_pre (P := PadPrefix ** PadSuffix) (b := ShaInput)
      (len := 64) ?_
    intro scratch0 hlen
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => hq)
      (hlift scratch0 hlen)
  have hany : cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
      (PadPrefix ** anyBytes ShaInput 64 ** PadSuffix)
      (sha256PadThenBitlenPost_lt56 cursor res bitLen rem F) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => hq) hany0
  -- Reshape pad entry → pad-active + ambient (0 fuel).
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp' : (PadPrefix ** anyBytes ShaInput 64 ** PadSuffix) h := by
        have hpU :
            ((sha256PadCore inputBase input N rem **
                sha256PadFocusAmb outputBase inputBase input params iv out0 N
                  (sha256PadTemps ** A0)) **
              anyBytes ShaInput 64) h := by
          xperm_hyp hp
        have hpFlat :
            ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
              (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
              (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** (.x0 ↦ᵣ (0 : Word)) **
              bytesRegion cursor res **
              ((.x8 ↦ᵣ ShaState) **
                bytesRegion ShaState (sha256AbsorbedState iv input N) **
                bytesRegion ShaParams params **
                (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
                bytesRegion ShaIv iv **
                bytesRegion inputBase (input.take (sha256BlockStep * N)) **
                (regOwn .x10) **
                (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) **
                (regOwn .x30) ** A0) **
              anyBytes ShaInput 64) h := by
          simp only [sha256PadCore, sha256PadFocusAmb, sha256PadTemps] at hpU ⊢
          xperm_chunked hpU
        simp only [sha256PadThenBitlenAmb, sha256PadFocusAmb, F, PadPrefix, PadSuffix] at hpFlat ⊢
        xperm_chunked hpFlat
      exact hp')
    (fun _ hq => hq)
    hany

/-- Concrete scratch: flat pad-active pre → raw `sha256PadThenBitlen_ge56` post. -/
private theorem sha256PadThenBitlen_ge56_conc
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A0 : Assertion) (hA0 : A0.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hiv : iv.length = 32)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true)
    (hsemMid : sha256BodyPadMidHsem ShaState ShaInput ShaParams iv input params N rem) :
    ∀ (scratch0 : List (BitVec 8)) (v6 v7 v10 : Word),
      scratch0.length = 64 →
      let cursor := sha256AbsorbCursor inputBase N
      let res := sha256Residual input N
      let bitLen := sha256BitLenW N rem
      let st0 := sha256AbsorbedState iv input N
      let payload := sha256CompressPayload st0
        (sha256PadScratch_lt56 res sha256ZeroScratch rem)
      let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
      cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
        ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
          (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
          (.x8 ↦ᵣ ShaState) ** bytesRegion ShaParams params **
          bytesRegion ShaState st0 **
          regOwn .x28 ** F)
        ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
          (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
          (.x8 ↦ᵣ ShaState) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
          (.x20 ↦ᵣ bitLen) **
          (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
          (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion cursor res **
          bytesRegion ShaInput
            (sha256BitlenBE (sha256PadScratch_ge56 res scratch0 rem) bitLen) **
          bytesRegion ShaParams params **
          bytesRegion ShaState (setBytes st0 0 (payload.flatMap dwordBytes)) **
          regOwn .x28 ** F) := by
  intro scratch0 v6 v7 v10 hscratch
  let cursor := sha256AbsorbCursor inputBase N
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  let st0 := sha256AbsorbedState iv input N
  let payload := sha256CompressPayload st0
    (sha256PadScratch_lt56 res sha256ZeroScratch rem)
  let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
  have hF : F.pcFree := sha256PadTailAmb_pcFree outputBase inputBase input iv out0 N A0 hA0
  have hst0 : st0.length = 32 := length_sha256AbsorbedState iv input hiv N
  have hpayload : payload.length = 4 :=
    sha256CompressPayload_length st0 (sha256PadScratch_lt56 res sha256ZeroScratch rem)
  have hinp : rem ≤ res.length := by
    rw [residual_length_eq input N rem hlen]
  have hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ ShaState) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
        (.x21 ↦ᵣ ShaInput) ** bytesRegion ShaParams params **
        bytesRegion ShaState st0 **
        bytesRegion ShaInput (sha256PadScratch_lt56 res scratch0 rem)) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (ShaState, payload) := by
    intro R s hR
    have hR' :
        (((.x8 ↦ᵣ ShaState) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
          (.x21 ↦ᵣ ShaInput) ** bytesRegion ShaParams params **
          bytesRegion ShaState st0 **
          bytesRegion ShaInput (sha256PadScratch_lt56 res sha256ZeroScratch rem)) ** R).holdsFor s := by
      rw [sha256PadScratch_lt56_zero res scratch0 rem hscratch] at hR
      exact hR
    exact hsemMid R s hR'
  have hraw := sha256PadThenBitlen_ge56 ShaInput cursor ShaState ShaParams bitLen
    res scratch0 st0 params payload rem
    (BitVec.ofNat 64 sha256BlockStep) v6 v7 v10 F hF
    hcurAlign sha256ShaInput_align8 hscratch hst0 hpayload hinp hrem hrem64
    hcurOver sha256ShaInput_hover
    hvalidS (fun i hi => hvalidScratch i (by omega))
    (sha256PadScratch_validPad_ge56 rem hrem hrem64 hvalidScratch)
    (sha256PadScratch_valid56 hvalidScratch) (sha256PadScratch_valid57 hvalidScratch)
    (sha256PadScratch_valid58 hvalidScratch) (sha256PadScratch_valid59 hvalidScratch)
    (sha256PadScratch_valid60 hvalidScratch) (sha256PadScratch_valid61 hvalidScratch)
    (sha256PadScratch_valid62 hvalidScratch) (sha256PadScratch_valid63 hvalidScratch)
    hsem
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hraw

/-- Pack raw ge56 post → `sha256PadThenBitlenPost_ge56` via `leaf_post_holds`.
    The `_payload` let mirrors `sha256PadThenBitlen_ge56_conc`'s statement shape
    so callers intro the same binders; this proof does not name it. -/
private theorem sha256PadThenBitlen_ge56_conc_pack
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A0 : Assertion) (hA0 : A0.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hiv : iv.length = 32)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true)
    (hsemMid : sha256BodyPadMidHsem ShaState ShaInput ShaParams iv input params N rem) :
    ∀ (scratch0 : List (BitVec 8)) (v6 v7 v10 : Word),
      scratch0.length = 64 →
      let cursor := sha256AbsorbCursor inputBase N
      let res := sha256Residual input N
      let bitLen := sha256BitLenW N rem
      let st0 := sha256AbsorbedState iv input N
      let _payload := sha256CompressPayload st0
        (sha256PadScratch_lt56 res sha256ZeroScratch rem)
      let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
      cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
        ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
          (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
          (.x8 ↦ᵣ ShaState) ** bytesRegion ShaParams params **
          bytesRegion ShaState st0 **
          regOwn .x28 ** F)
        (sha256PadThenBitlenPost_ge56 cursor res bitLen rem
          (sha256BodyMidState_ge56 iv input N rem) params F) := by
  intro scratch0 v6 v7 v10 hscratch
  let cursor := sha256AbsorbCursor inputBase N
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  let st0 := sha256AbsorbedState iv input N
  let payload := sha256CompressPayload st0
    (sha256PadScratch_lt56 res sha256ZeroScratch rem)
  let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun h hq =>
      sha256PadThenBitlen_ge56_leaf_post_holds h cursor res bitLen rem st0 params scratch0
        payload F iv input N hiv rfl rfl hscratch rfl hq)
    (sha256PadThenBitlen_ge56_conc inputBase outputBase input params iv out0 N rem A0 hA0
      hlen hiv hrem hrem64 hcurAlign hcurOver hvalidS hvalidScratch hsemMid
      scratch0 v6 v7 v10 hscratch)

/-- Lift pad-active temps x6/x7/x10 (keep x28 pad-active). -/
private theorem sha256PadThenBitlen_ge56_lift_temps
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A0 : Assertion) (hA0 : A0.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hiv : iv.length = 32)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true)
    (hsemMid : sha256BodyPadMidHsem ShaState ShaInput ShaParams iv input params N rem) :
    ∀ (scratch0 : List (BitVec 8)), scratch0.length = 64 →
      let cursor := sha256AbsorbCursor inputBase N
      let res := sha256Residual input N
      let bitLen := sha256BitLenW N rem
      let st0 := sha256AbsorbedState iv input N
      let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
      cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
        ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
          (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion cursor res ** bytesRegion ShaInput scratch0 **
          (.x8 ↦ᵣ ShaState) ** bytesRegion ShaParams params **
          bytesRegion ShaState st0 **
          regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x28 ** F)
        (sha256PadThenBitlenPost_ge56 cursor res bitLen rem
          (sha256BodyMidState_ge56 iv input N rem) params F) := by
  intro scratch0 hscratch
  let cursor := sha256AbsorbCursor inputBase N
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  let st0 := sha256AbsorbedState iv input N
  let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
  let PadPrefix : Assertion :=
    ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
      (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion cursor res)
  let PadMid : Assertion :=
    (.x8 ↦ᵣ ShaState) ** bytesRegion ShaParams params ** bytesRegion ShaState st0
  let PadTail : Assertion := regOwn .x28 ** F
  let PadSuffix : Assertion :=
    PadMid ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** PadTail
  have hc3 : ∀ (v6 v7 v10 : Word),
      cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
        ((PadPrefix ** bytesRegion ShaInput scratch0 ** PadMid) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** PadTail)
        (sha256PadThenBitlenPost_ge56 cursor res bitLen rem
          (sha256BodyMidState_ge56 iv input N rem) params F) := by
    intro v6 v7 v10
    have h := sha256PadThenBitlen_ge56_conc_pack inputBase outputBase input params iv out0 N rem A0
      hA0 hlen hiv hrem hrem64 hcurAlign hcurOver hvalidS hvalidScratch hsemMid
      scratch0 v6 v7 v10 hscratch
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq) h
  have hown0 : cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
      ((PadPrefix ** bytesRegion ShaInput scratch0 ** PadMid) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** PadTail)
      (sha256PadThenBitlenPost_ge56 cursor res bitLen rem
        (sha256BodyMidState_ge56 iv input N rem) params F) :=
    of_forall3_pre (P := PadPrefix ** bytesRegion ShaInput scratch0 ** PadMid)
      (Tail := PadTail)
      (Post := sha256PadThenBitlenPost_ge56 cursor res bitLen rem
        (sha256BodyMidState_ge56 iv input N rem) params F)
      (r1 := .x6) (r2 := .x7) (r3 := .x10) hc3
  have hown : cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
      (PadPrefix ** bytesRegion ShaInput scratch0 **
        PadMid ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** PadTail)
      (sha256PadThenBitlenPost_ge56 cursor res bitLen rem
        (sha256BodyMidState_ge56 iv input N rem) params F) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq) hown0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq) hown

/-- PadThenBitlen framed under pad focus (rem≥56). Caller packages
    `(regOwn .x6) ** A0` into the focus slot. -/
private theorem sha256PadThenBitlen_framed_ge56
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A0 : Assertion) (hA0 : A0.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hiv : iv.length = 32)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true)
    (hsemMid : sha256BodyPadMidHsem ShaState ShaInput ShaParams iv input params N rem) :
    cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
      (sha256PadFramedPre_ge56 inputBase outputBase input params iv out0 N rem A0)
      (sha256PadFramedPost_ge56 inputBase outputBase input params iv out0 N rem A0) := by
  let cursor := sha256AbsorbCursor inputBase N
  let res := sha256Residual input N
  let bitLen := sha256BitLenW N rem
  let st0 := sha256AbsorbedState iv input N
  let F := sha256PadTailAmb outputBase inputBase input iv out0 N A0
  let PadPrefix : Assertion :=
    ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
      (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion cursor res)
  let PadMid : Assertion :=
    (.x8 ↦ᵣ ShaState) ** bytesRegion ShaParams params ** bytesRegion ShaState st0
  let PadTail : Assertion := regOwn .x28 ** F
  let PadSuffix : Assertion :=
    PadMid ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** PadTail
  have hany0 : cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
      ((PadPrefix ** PadSuffix) ** anyBytes ShaInput 64)
      (sha256PadFramedPost_ge56 inputBase outputBase input params iv out0 N rem A0) := by
    refine cpsTripleWithin_anyBytes_pre (P := PadPrefix ** PadSuffix) (b := ShaInput)
      (len := 64) ?_
    intro scratch0' hscratch'
    have hlift := sha256PadThenBitlen_ge56_lift_temps inputBase outputBase input params iv out0 N rem
      A0 hA0 hlen hiv hrem hrem64 hcurAlign hcurOver hvalidS hvalidScratch hsemMid
      scratch0' hscratch'
    have hPostEq :
        sha256PadThenBitlenPost_ge56 cursor res bitLen rem
          (sha256BodyMidState_ge56 iv input N rem) params F =
        sha256PadFramedPost_ge56 inputBase outputBase input params iv out0 N rem A0 := by
      simp only [cursor, res, bitLen, F]
      exact (sha256PadFramedPost_ge56_eq inputBase outputBase input params iv out0 N rem A0).symm
    have hlift' := cpsTripleWithin_post_eq hPostEq hlift
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq) hlift'
  have hany : cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
      (PadPrefix ** anyBytes ShaInput 64 ** PadSuffix)
      (sha256PadFramedPost_ge56 inputBase outputBase input params iv out0 N rem A0) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => hq) hany0
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp' : (PadPrefix ** anyBytes ShaInput 64 ** PadSuffix) h := by
        have hpU :
            (sha256PadFramedPre_ge56 inputBase outputBase input params iv out0 N rem A0) h := by
          xperm_hyp hp
        have hpFlat :
            ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
              (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
              (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** (.x0 ↦ᵣ (0 : Word)) **
              bytesRegion cursor res **
              ((.x8 ↦ᵣ ShaState) **
                bytesRegion ShaState st0 **
                bytesRegion ShaParams params **
                (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
                bytesRegion ShaIv iv **
                bytesRegion inputBase (input.take (sha256BlockStep * N)) **
                (regOwn .x10) **
                (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) **
                (regOwn .x30) ** A0) **
              anyBytes ShaInput 64) h := by
          simp only [sha256PadFramedPre_ge56, sha256PadCore, sha256PadFocusAmb, sha256PadTemps,
            cursor, res, bitLen, st0] at hpU ⊢
          xperm_chunked hpU
        simp only [sha256PadTailAmb, F, PadPrefix, PadMid, PadSuffix, PadTail] at hpFlat ⊢
        xperm_chunked hpFlat
      exact hp')
    (fun _ hq => hq)
    hany

/-- PadThenBitlen post → `sha256SqueezeToExit_spec` pre (rem&lt;56). -/
private theorem sha256PadThenBitlenPost_to_squeezePre_lt56
    (h : PartialState) (inputBase outputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (_hlen : input.length = sha256BlockStep * N + rem)
    (hp :
      (sha256PadThenBitlenPost_lt56 (sha256AbsorbCursor inputBase N)
        (sha256Residual input N) (sha256BitLenW N rem) rem
        (sha256PadThenBitlenAmb outputBase inputBase input params iv out0 N A)) h) :
    let st0 := sha256AbsorbedState iv input N
    let scratch := sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)
    ((.x5 ↦ᵣ (ShaInput + (56 : Word))) ** (.x6 ↦ᵣ ((sha256BitLenW N rem) >>> 8)) **
      (.x8 ↦ᵣ ShaState) ** (regOwn .x10) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
      bytesRegion ShaParams params ** bytesRegion ShaState st0 **
      bytesRegion ShaInput scratch ** bytesRegion outputBase out0 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      sha256BodyExitAmb inputBase input iv N A) h := by
  intro st0 scratch
  set cursor := sha256AbsorbCursor inputBase N
  set res := sha256Residual input N
  set bitLen := sha256BitLenW N rem
  have hp0 :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        bytesRegion ShaInput (sha256FinalBlock_lt56 res rem bitLen) **
        regOwn .x28 **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) ** (regOwn .x29) ** (regOwn .x30) ** A) h := by
    simpa [sha256PadThenBitlenPost_lt56, sha256PadThenBitlenAmb, sha256PadFocusAmb,
      cursor, res, bitLen, st0, scratch] using hp
  have hp1 :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        regOwn .x28 **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) ** (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp0
    intro h1 hp1
    refine sepConj_mono_right ?_ h1 hp1
    intro h2 hp2
    refine sepConj_mono_right ?_ h2 hp2
    intro h3 hp3
    refine sepConj_mono_right ?_ h3 hp3
    intro h4 hp4
    refine sepConj_mono_right ?_ h4 hp4
    intro h5 hp5
    refine sepConj_mono_right ?_ h5 hp5
    intro h6 hp6
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x7) (v := (0 : Word))) h6 hp6
  have hp2 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        regOwn .x28 **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) ** (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp1
    intro h1 hp1'
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x9) (v := cursor)) h1 hp1'
  have hp3 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) ** (regOwn .x18) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        regOwn .x28 **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) ** (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp2
    intro h1 hp1'
    refine sepConj_mono_right ?_ h1 hp1'
    intro h2 hp2'
    exact sepConj_mono_left
      (regIs_implies_regOwn (r := .x18) (v := BitVec.ofNat 64 rem)) h2 hp2'
  have hp4 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) ** (regOwn .x18) ** (regOwn .x20) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        regOwn .x28 **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) ** (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp3
    intro h1 hp1'
    refine sepConj_mono_right ?_ h1 hp1'
    intro h2 hp2'
    refine sepConj_mono_right ?_ h2 hp2'
    intro h3 hp3'
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x20) (v := bitLen)) h3 hp3'
  have hp5 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) ** (regOwn .x18) ** (regOwn .x20) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (regOwn .x0) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        regOwn .x28 **
        (.x8 ↦ᵣ ShaState) **
        bytesRegion ShaState st0 **
        bytesRegion ShaParams params **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x10) ** (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp4
    intro h1 hp1'
    refine sepConj_mono_right ?_ h1 hp1'
    intro h2 hp2'
    refine sepConj_mono_right ?_ h2 hp2'
    intro h3 hp3'
    refine sepConj_mono_right ?_ h3 hp3'
    intro h4 hp4'
    refine sepConj_mono_right ?_ h4 hp4'
    intro h5 hp5'
    refine sepConj_mono_right ?_ h5 hp5'
    intro h6 hp6'
    refine sepConj_mono_right ?_ h6 hp6'
    intro h7 hp7'
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x0) (v := (0 : Word))) h7 hp7'
  simp only [sha256BodyExitAmb, cursor, res, bitLen, st0, scratch] at hp5 ⊢
  xperm_chunked hp5

/-- `sha256SqueezeToExit_spec` post → `sha256BodyExitPost` (rem&lt;56). -/
private theorem sha256SqueezePost_to_bodyExit_lt56
    (h : PartialState) (inputBase outputBase : Word)
    (input params iv _out0 : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (hivEq : iv = sha256IvBytes) (hrem : rem < 56)
    (hp :
      let st0 := sha256AbsorbedState iv input N
      let scratch := sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)
      let _payload := sha256CompressPayload st0 scratch
      let st := sha256CompressBytes st0 scratch
      ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion ShaParams params ** bytesRegion ShaState st **
        bytesRegion ShaInput scratch **
        bytesRegion outputBase (sha256SqueezeBE st) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        sha256BodyExitAmb inputBase input iv N A) h) :
    (sha256BodyExitPost inputBase outputBase input params iv N rem A) h := by
  have hstFinal :
      sha256CompressBytes (sha256AbsorbedState iv input N)
        (sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)) =
        sha256BodyFinalState input N rem := by
    rw [sha256AbsorbedState_ivBytes iv input N hivEq]
    exact (sha256BodyFinalState_lt56 input N rem hrem).symm
  have hdig :
      sha256SqueezeBE (sha256CompressBytes (sha256AbsorbedState iv input N)
        (sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem))) =
        sha256BodyDigest input N rem := by
    simp only [sha256BodyDigest, hstFinal]
  have hp1 :
      ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
        (regOwn .x10) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion ShaParams params **
        bytesRegion ShaState
          (sha256CompressBytes (sha256AbsorbedState iv input N)
            (sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem))) **
        bytesRegion ShaInput
          (sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)) **
        bytesRegion outputBase
          (sha256SqueezeBE
            (sha256CompressBytes (sha256AbsorbedState iv input N)
              (sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)))) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        sha256BodyExitAmb inputBase input iv N A) h := by
    refine sepConj_mono_right ?_ h hp
    intro h1 hp1
    refine sepConj_mono_right ?_ h1 hp1
    intro h2 hp2
    refine sepConj_mono_right ?_ h2 hp2
    intro h3 hp3
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x10) (v := (0 : Word))) h3 hp3
  have hdig' : sha256SqueezeBE (sha256BodyFinalState input N rem) = sha256BodyDigest input N rem := by
    rw [← hstFinal, hdig]
  rw [hstFinal, hdig'] at hp1
  simp only [sha256BodyExitPost, sha256BodyExitAmb, if_pos hrem] at hp1 ⊢
  xperm_chunked hp1

/-- Fuel `rem*7+44+295` (pad `rem*7+33` + squeeze 295, mono to unified body fuel). -/
theorem sha256PadSqueeze_lt56
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A0 : Assertion) (hA0 : A0.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hiv : iv.length = 32) (hivEq : iv = sha256IvBytes)
    (hout : out0.length = 32) (_hparams : params.length = 16)
    (hrem : rem < 56)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (houtAlign : outputBase.toNat % 8 = 0)
    (houtOver : outputBase.toNat + 32 ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true)
    (hvalidSq : ∀ i < 32,
      isValidByteAccess (ShaState + BitVec.ofNat 64 (i ^^^ 3)) = true)
    (hvalidD : ∀ i < 32, isValidByteAccess (outputBase + BitVec.ofNat 64 i) = true)
    (hsem : sha256BodySqueezeHsem_lt56 ShaState ShaInput ShaParams iv input params N rem) :
    cpsTripleWithin (rem * 7 + 44 + 295) (B + 196) (B + 452) sha256Cr
      (sha256PadEntryPre inputBase outputBase input params iv out0 N rem
        (sha256PadTemps ** A0))
      (sha256BodyExitPost inputBase outputBase input params iv N rem A0) := by
  let st0 := sha256AbsorbedState iv input N
  let scratch := sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)
  let payload := sha256CompressPayload st0 scratch
  let F := sha256BodyExitAmb inputBase input iv N A0
  have hF : F.pcFree := sha256BodyExitAmb_pcFree inputBase input iv N A0 hA0
  have hst0 : st0.length = 32 := length_sha256AbsorbedState iv input hiv N
  have hpayload : payload.length = 4 := sha256CompressPayload_length st0 scratch
  have cPad := sha256PadThenBitlen_framed_lt56 inputBase outputBase input params iv out0
    N rem A0 hA0 hlen hrem hcurAlign hcurOver hvalidS hvalidScratch
  let SqueezeCore :=
    ((.x5 ↦ᵣ (ShaInput + (56 : Word))) **
      (.x6 ↦ᵣ ((sha256BitLenW N rem) >>> 8)) **
      (.x8 ↦ᵣ ShaState) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
      bytesRegion ShaParams params ** bytesRegion ShaState st0 **
      bytesRegion ShaInput scratch ** bytesRegion outputBase out0 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F)
  let SqueezePre := SqueezeCore ** regOwn .x10
  have cPre : cpsTripleWithin 0 (B + 396) (B + 396) sha256Cr
      (sha256PadThenBitlenPost_lt56 (sha256AbsorbCursor inputBase N)
        (sha256Residual input N) (sha256BitLenW N rem) rem
        (sha256PadThenBitlenAmb outputBase inputBase input params iv out0 N A0))
      SqueezePre :=
    cpsTripleWithin_reshape0 fun h hp => by
      have hq := sha256PadThenBitlenPost_to_squeezePre_lt56 h inputBase outputBase input params iv
        out0 N rem A0 hlen hp
      simp only [SqueezePre, SqueezeCore, st0, scratch, F] at hq ⊢
      xperm_chunked hq
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) cPad cPre
  let SqueezePost :=
    ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
      bytesRegion ShaParams params **
      bytesRegion ShaState (sha256CompressBytes st0 scratch) **
      bytesRegion ShaInput scratch **
      bytesRegion outputBase (sha256SqueezeBE (sha256CompressBytes st0 scratch)) **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F)
  have cSqVal (v10 : Word) :
      cpsTripleWithin 295 (B + 396) (B + 452) sha256Cr
        (SqueezeCore ** (.x10 ↦ᵣ v10)) SqueezePost := by
    have hraw := sha256SqueezeToExit_spec ShaInput ShaState ShaParams outputBase
      scratch st0 params out0 payload
      (ShaInput + (56 : Word)) ((sha256BitLenW N rem) >>> 8) v10
      hst0 hpayload hout
      sha256ShaState_align8 houtAlign sha256ShaState_over houtOver
      hvalidSq hvalidD hsem F hF
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        rw [sha256CsrsWriteback_eq_compress st0 scratch payload hst0 hpayload rfl] at hq
        xperm_chunked hq) hraw
  have cSqOwn : cpsTripleWithin 295 (B + 396) (B + 452) sha256Cr SqueezePre SqueezePost :=
    of_forall1_pre (P := SqueezeCore) (Post := SqueezePost) (r := .x10) cSqVal
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 cSqOwn
  have cExit : cpsTripleWithin 0 (B + 452) (B + 452) sha256Cr
      SqueezePost
      (sha256BodyExitPost inputBase outputBase input params iv N rem A0) :=
    cpsTripleWithin_reshape0 fun h hp =>
      sha256SqueezePost_to_bodyExit_lt56 h inputBase outputBase input params iv out0
        N rem A0 hivEq hrem hp
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c012 cExit
  have hfuel : (rem * 7 + 33) + 295 ≤ rem * 7 + 44 + 295 := by omega
  refine cpsTripleWithin_mono_nSteps hfuel ?_
  refine cpsTripleWithin_weaken (fun _ hp => by
      simpa [sha256PadEntryPre] using hp) (fun _ hq => hq) cAll

private theorem sha256BodyMidState_ge56_iv (iv input : List (BitVec 8)) (N rem : Nat)
    (hivEq : iv = sha256IvBytes) :
    sha256BodyMidState_ge56 iv input N rem = sha256BodyMidState_ge56 sha256IvBytes input N rem := by
  subst hivEq; rfl

private theorem sha256PadThenBitlenPost_ge56_holds_of
    (h : PartialState) (cursor : Word) (res : List (BitVec 8)) (bitLen : Word)
    (rem : Nat) (stMid params : List (BitVec 8)) (F : Assertion)
    (hp : (sha256PadThenBitlenPost_ge56 cursor res bitLen rem stMid params F) h) :
    ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
      (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
      (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
      (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x8 ↦ᵣ ShaState) ** (.x10 ↦ᵣ ShaParams) **
      bytesRegion cursor res **
      bytesRegion ShaInput (sha256FinalBlock_ge56 res rem bitLen) **
      bytesRegion ShaParams params ** bytesRegion ShaState stMid **
      regOwn .x28 ** F) h := by
  simp only [sha256PadThenBitlenPost_ge56] at hp ⊢
  exact hp

/-- PadThenBitlen post → squeeze pre (rem≥56): permute like lt56. -/
private theorem sha256PadThenBitlenPost_to_squeezePre_ge56
    (h : PartialState) (inputBase outputBase : Word)
    (input params iv out0 : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (_hlen : input.length = sha256BlockStep * N + rem)
    (hp :
      (sha256PadThenBitlenPost_ge56 (sha256AbsorbCursor inputBase N)
        (sha256Residual input N) (sha256BitLenW N rem) rem
        (sha256BodyMidState_ge56 iv input N rem) params
        (sha256PadTailAmb outputBase inputBase input iv out0 N A)) h) :
    let stMid := sha256BodyMidState_ge56 iv input N rem
    let scratch := sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)
    ((.x5 ↦ᵣ (ShaInput + (56 : Word))) ** (.x6 ↦ᵣ ((sha256BitLenW N rem) >>> 8)) **
      (.x8 ↦ᵣ ShaState) ** (regOwn .x10) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
      bytesRegion ShaParams params ** bytesRegion ShaState stMid **
      bytesRegion ShaInput scratch ** bytesRegion outputBase out0 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      sha256BodyExitAmb inputBase input iv N A) h := by
  intro stMid scratch
  set cursor := sha256AbsorbCursor inputBase N
  set res := sha256Residual input N
  set bitLen := sha256BitLenW N rem
  set F := sha256PadTailAmb outputBase inputBase input iv out0 N A
  have hp0 :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ ShaState) ** (regOwn .x10) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        bytesRegion ShaParams params ** bytesRegion ShaState stMid **
        regOwn .x28 **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x29) ** (regOwn .x30) ** A) h := by
    have hp' := sha256PadThenBitlenPost_ge56_holds_of h cursor res bitLen rem stMid params F hp
    have hp'' :
        ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
          (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
          (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
          (.x6 ↦ᵣ (bitLen >>> 8)) ** (.x7 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ ShaState) ** (.x10 ↦ᵣ ShaParams) **
          bytesRegion cursor res **
          bytesRegion ShaInput scratch **
          bytesRegion ShaParams params ** bytesRegion ShaState stMid **
          regOwn .x28 **
          (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
          bytesRegion ShaIv iv **
          bytesRegion inputBase (input.take (sha256BlockStep * N)) **
          (regOwn .x29) ** (regOwn .x30) ** A) h := by
      simpa [cursor, res, bitLen, stMid, scratch, F, sha256PadTailAmb] using hp'
    refine sepConj_mono_right ?_ h hp''
    intro h1 hp1
    refine sepConj_mono_right ?_ h1 hp1
    intro h2 hp2
    refine sepConj_mono_right ?_ h2 hp2
    intro h3 hp3
    refine sepConj_mono_right ?_ h3 hp3
    intro h4 hp4
    refine sepConj_mono_right ?_ h4 hp4
    intro h5 hp5
    refine sepConj_mono_right ?_ h5 hp5
    intro h6 hp6
    refine sepConj_mono_right ?_ h6 hp6
    intro h7 hp7
    refine sepConj_mono_right ?_ h7 hp7
    intro h8 hp8
    refine sepConj_mono_right ?_ h8 hp8
    intro h9 hp9
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x10) (v := ShaParams)) h9 hp9
  have hp1 :
      ((.x21 ↦ᵣ ShaInput) ** (.x9 ↦ᵣ cursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ ShaState) ** (regOwn .x10) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        bytesRegion ShaParams params ** bytesRegion ShaState stMid **
        regOwn .x28 **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp0
    intro h1 hp1
    refine sepConj_mono_right ?_ h1 hp1
    intro h2 hp2
    refine sepConj_mono_right ?_ h2 hp2
    intro h3 hp3
    refine sepConj_mono_right ?_ h3 hp3
    intro h4 hp4
    refine sepConj_mono_right ?_ h4 hp4
    intro h5 hp5
    refine sepConj_mono_right ?_ h5 hp5
    intro h6 hp6
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x7) (v := (0 : Word))) h6 hp6
  have hp2 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) ** (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ ShaState) ** (regOwn .x10) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        bytesRegion ShaParams params ** bytesRegion ShaState stMid **
        regOwn .x28 **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp1
    intro h1 hp1'
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x9) (v := cursor)) h1 hp1'
  have hp3 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) ** (regOwn .x18) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ ShaState) ** (regOwn .x10) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        bytesRegion ShaParams params ** bytesRegion ShaState stMid **
        regOwn .x28 **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp2
    intro h1 hp1'
    refine sepConj_mono_right ?_ h1 hp1'
    intro h2 hp2'
    exact sepConj_mono_left
      (regIs_implies_regOwn (r := .x18) (v := BitVec.ofNat 64 rem)) h2 hp2'
  have hp4 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) ** (regOwn .x18) ** (regOwn .x20) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ ShaState) ** (regOwn .x10) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        bytesRegion ShaParams params ** bytesRegion ShaState stMid **
        regOwn .x28 **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp3
    intro h1 hp1'
    refine sepConj_mono_right ?_ h1 hp1'
    intro h2 hp2'
    refine sepConj_mono_right ?_ h2 hp2'
    intro h3 hp3'
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x20) (v := bitLen)) h3 hp3'
  have hp5 :
      ((.x21 ↦ᵣ ShaInput) ** (regOwn .x9) ** (regOwn .x18) ** (regOwn .x20) **
        (.x5 ↦ᵣ (ShaInput + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) ** (regOwn .x7) ** (regOwn .x0) **
        (.x8 ↦ᵣ ShaState) ** (regOwn .x10) **
        bytesRegion cursor res **
        bytesRegion ShaInput scratch **
        bytesRegion ShaParams params ** bytesRegion ShaState stMid **
        regOwn .x28 **
        (.x19 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion ShaIv iv **
        bytesRegion inputBase (input.take (sha256BlockStep * N)) **
        (regOwn .x29) ** (regOwn .x30) ** A) h := by
    refine sepConj_mono_right ?_ h hp4
    intro h1 hp1'
    refine sepConj_mono_right ?_ h1 hp1'
    intro h2 hp2'
    refine sepConj_mono_right ?_ h2 hp2'
    intro h3 hp3'
    refine sepConj_mono_right ?_ h3 hp3'
    intro h4 hp4'
    refine sepConj_mono_right ?_ h4 hp4'
    intro h5 hp5'
    refine sepConj_mono_right ?_ h5 hp5'
    intro h6 hp6'
    refine sepConj_mono_right ?_ h6 hp6'
    intro h7 hp7'
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x0) (v := (0 : Word))) h7 hp7'
  simp only [sha256BodyExitAmb, cursor, res, bitLen, stMid, scratch] at hp5 ⊢
  xperm_chunked hp5

/-- `sha256SqueezeToExit_spec` post → `sha256BodyExitPost` (rem≥56). -/
private theorem sha256SqueezePost_to_bodyExit_ge56
    (h : PartialState) (inputBase outputBase : Word)
    (input params iv _out0 : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (hivEq : iv = sha256IvBytes) (hrem : 56 ≤ rem)
    (hp :
      let stMid := sha256BodyMidState_ge56 iv input N rem
      let scratch := sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)
      let _payload := sha256CompressPayload stMid scratch
      let st := sha256CompressBytes stMid scratch
      ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion ShaParams params ** bytesRegion ShaState st **
        bytesRegion ShaInput scratch **
        bytesRegion outputBase (sha256SqueezeBE st) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        sha256BodyExitAmb inputBase input iv N A) h) :
    (sha256BodyExitPost inputBase outputBase input params iv N rem A) h := by
  have hstFinal :
      sha256CompressBytes (sha256BodyMidState_ge56 iv input N rem)
        (sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)) =
        sha256BodyFinalState input N rem := by
    rw [sha256BodyMidState_ge56_iv iv input N rem hivEq]
    exact (sha256BodyFinalState_ge56 input N rem hrem).symm
  have hdig :
      sha256SqueezeBE (sha256CompressBytes (sha256BodyMidState_ge56 iv input N rem)
        (sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem))) =
        sha256BodyDigest input N rem := by
    simp only [sha256BodyDigest, hstFinal]
  have hp1 :
      ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
        (regOwn .x10) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion ShaParams params **
        bytesRegion ShaState
          (sha256CompressBytes (sha256BodyMidState_ge56 iv input N rem)
            (sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem))) **
        bytesRegion ShaInput
          (sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)) **
        bytesRegion outputBase
          (sha256SqueezeBE
            (sha256CompressBytes (sha256BodyMidState_ge56 iv input N rem)
              (sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)))) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        sha256BodyExitAmb inputBase input iv N A) h := by
    refine sepConj_mono_right ?_ h hp
    intro h1 hp1
    refine sepConj_mono_right ?_ h1 hp1
    intro h2 hp2
    refine sepConj_mono_right ?_ h2 hp2
    intro h3 hp3
    exact sepConj_mono_left (regIs_implies_regOwn (r := .x10) (v := (0 : Word))) h3 hp3
  have hdig' : sha256SqueezeBE (sha256BodyFinalState input N rem) = sha256BodyDigest input N rem := by
    rw [← hstFinal, hdig]
  rw [hstFinal, hdig'] at hp1
  have hnotLt : ¬ rem < 56 := Nat.not_lt.mpr hrem
  simp only [sha256BodyExitPost, sha256BodyExitAmb, if_neg hnotLt] at hp1 ⊢
  xperm_chunked hp1

/-! ## PadThenBitlen ∘ SqueezeToExit (rem≥56): B+196 → B+452 -/

theorem sha256PadSqueeze_ge56
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A0 : Assertion) (hA0 : A0.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hiv : iv.length = 32) (hivEq : iv = sha256IvBytes)
    (hout : out0.length = 32) (_hparams : params.length = 16)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (houtAlign : outputBase.toNat % 8 = 0)
    (houtOver : outputBase.toNat + 32 ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true)
    (hvalidSq : ∀ i < 32,
      isValidByteAccess (ShaState + BitVec.ofNat 64 (i ^^^ 3)) = true)
    (hvalidD : ∀ i < 32, isValidByteAccess (outputBase + BitVec.ofNat 64 i) = true)
    (hsemMid : sha256BodyPadMidHsem ShaState ShaInput ShaParams iv input params N rem)
    (hsemSq : sha256BodySqueezeHsem_ge56 ShaState ShaInput ShaParams iv input params N rem) :
    cpsTripleWithin (rem * 7 + 44 + 295) (B + 196) (B + 452) sha256Cr
      (sha256PadEntryPre inputBase outputBase input params iv out0 N rem
        (sha256PadTemps ** A0))
      (sha256BodyExitPost inputBase outputBase input params iv N rem A0) := by
  let stMid := sha256BodyMidState_ge56 iv input N rem
  let scratch := sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)
  let payload := sha256CompressPayload stMid scratch
  let F := sha256BodyExitAmb inputBase input iv N A0
  have hF : F.pcFree := sha256BodyExitAmb_pcFree inputBase input iv N A0 hA0
  have hstMid : stMid.length = 32 := by
    simp only [stMid, sha256BodyMidState_ge56, length_sha256CompressBytes]
  have hpayload : payload.length = 4 := sha256CompressPayload_length stMid scratch
  have cPad := sha256PadThenBitlen_framed_ge56 inputBase outputBase input params iv out0
    N rem A0 hA0 hlen hiv hrem hrem64 hcurAlign hcurOver hvalidS hvalidScratch hsemMid
  let SqueezeCore :=
    ((.x5 ↦ᵣ (ShaInput + (56 : Word))) **
      (.x6 ↦ᵣ ((sha256BitLenW N rem) >>> 8)) **
      (.x8 ↦ᵣ ShaState) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
      bytesRegion ShaParams params ** bytesRegion ShaState stMid **
      bytesRegion ShaInput scratch ** bytesRegion outputBase out0 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F)
  let SqueezePre := SqueezeCore ** regOwn .x10
  have cPre : cpsTripleWithin 0 (B + 396) (B + 396) sha256Cr
      (sha256PadFramedPost_ge56 inputBase outputBase input params iv out0 N rem A0)
      SqueezePre :=
    cpsTripleWithin_reshape0 fun h hp => by
      have hp' :
          (sha256PadThenBitlenPost_ge56 (sha256AbsorbCursor inputBase N)
            (sha256Residual input N) (sha256BitLenW N rem) rem
            (sha256BodyMidState_ge56 iv input N rem) params
            (sha256PadTailAmb outputBase inputBase input iv out0 N A0)) h :=
        (congr_fun (sha256PadFramedPost_ge56_eq inputBase outputBase input params iv out0 N rem A0) h).mp hp
      have hp'' : (sha256PadThenBitlenPost_ge56 (sha256AbsorbCursor inputBase N)
          (sha256Residual input N) (sha256BitLenW N rem) rem stMid params
          (sha256PadTailAmb outputBase inputBase input iv out0 N A0)) h := by
        simpa [stMid] using hp'
      have hq := sha256PadThenBitlenPost_to_squeezePre_ge56 h inputBase outputBase input params iv
        out0 N rem A0 hlen hp''
      simp only [SqueezePre, SqueezeCore, stMid, scratch, F] at hq ⊢
      xperm_chunked hq
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) cPad cPre
  let SqueezePost :=
    ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
      bytesRegion ShaParams params **
      bytesRegion ShaState (sha256CompressBytes stMid scratch) **
      bytesRegion ShaInput scratch **
      bytesRegion outputBase (sha256SqueezeBE (sha256CompressBytes stMid scratch)) **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F)
  have cSqVal (v10 : Word) :
      cpsTripleWithin 295 (B + 396) (B + 452) sha256Cr
        (SqueezeCore ** (.x10 ↦ᵣ v10)) SqueezePost := by
    have hraw := sha256SqueezeToExit_spec ShaInput ShaState ShaParams outputBase
      scratch stMid params out0 payload
      (ShaInput + (56 : Word)) ((sha256BitLenW N rem) >>> 8) v10
      hstMid hpayload hout
      sha256ShaState_align8 houtAlign sha256ShaState_over houtOver
      hvalidSq hvalidD hsemSq F hF
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        rw [sha256CsrsWriteback_eq_compress stMid scratch payload hstMid hpayload rfl] at hq
        xperm_chunked hq) hraw
  have cSqOwn : cpsTripleWithin 295 (B + 396) (B + 452) sha256Cr SqueezePre SqueezePost :=
    of_forall1_pre (P := SqueezeCore) (Post := SqueezePost) (r := .x10) cSqVal
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 cSqOwn
  have cExit : cpsTripleWithin 0 (B + 452) (B + 452) sha256Cr
      SqueezePost
      (sha256BodyExitPost inputBase outputBase input params iv N rem A0) :=
    cpsTripleWithin_reshape0 fun h hp =>
      sha256SqueezePost_to_bodyExit_ge56 h inputBase outputBase input params iv out0
        N rem A0 hivEq hrem hp
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c012 cExit
  refine cpsTripleWithin_weaken
    (fun h hp => (congr_fun (sha256PadFramedPre_ge56_eq inputBase outputBase input params iv out0 N rem A0).symm h).mp hp)
    (fun _ hq => hq) cAll

/-! ## Full body: SetupOuter → PadSqueeze (B+28 → B+452) -/

private theorem sha256PadEntryPre_amb_perm (h : PartialState)
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A : Assertion)
    (hp :
      (sha256PadEntryPre inputBase outputBase input params iv out0 N rem
        ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) **
          (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30) ** A)) h) :
    (sha256PadEntryPre inputBase outputBase input params iv out0 N rem
      (sha256PadTemps ** (regOwn .x11) ** (regOwn .x12) ** A)) h := by
  simp only [sha256PadEntryPre, sha256PadFocusAmb, sha256PadTemps] at hp ⊢
  xperm_chunked hp

private theorem sha256OuterFrameAmb_padTemps (h : PartialState)
    (outputBase : Word) (bitLen : Word) (iv out0 : List (BitVec 8))
    (A : Assertion)
    (hp :
      (sha256OuterFrameAmb outputBase bitLen iv out0
        ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) **
          (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30) ** A)) h) :
    (sha256OuterFrameAmb outputBase bitLen iv out0
      (sha256PadTemps ** (regOwn .x11) ** (regOwn .x12) ** A)) h := by
  simp only [sha256OuterFrameAmb, sha256PadTemps] at hp ⊢
  xperm_chunked hp

private theorem sha256OuterPost_padEntry_frame (h : PartialState)
    (inputBase : Word) (input params iv : List (BitVec 8)) (N rem : Nat)
    (outputBase : Word) (bitLen : Word) (out0 : List (BitVec 8)) (A : Assertion)
    (hp :
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams input params iv N 0 **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        sha256OuterFrameAmb outputBase bitLen iv out0
          ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) **
            (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30) ** A)) h) :
    ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
      (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
      sha256OuterInv inputBase ShaState ShaInput ShaParams input params iv N 0 **
      (regOwn .x10) ** anyBytes ShaInput 64 **
      sha256OuterFrameAmb outputBase bitLen iv out0
        (sha256PadTemps ** (regOwn .x11) ** (regOwn .x12) ** A)) h := by
  refine sepConj_mono_right
    (fun h1 hp1 =>
      sepConj_mono_right
        (fun h2 hp2 =>
          sepConj_mono_right
            (fun h3 hp3 =>
              sepConj_mono_right
                (fun h4 hp4 =>
                  sepConj_mono_right
                    (fun h5 hpFrame0 =>
                      sha256OuterFrameAmb_padTemps h5 outputBase bitLen iv out0 A hpFrame0)
                    h4 hp4)
                h3 hp3)
            h2 hp2)
        h1 hp1)
    h hp

theorem sha256Body_spec
    (inputBase outputBase : Word) (input params iv out0 : List (BitVec 8))
    (N rem : Nat) (A : Assertion) (hA : A.pcFree)
    (v8 v9 v18 v19 v20 v21 v5 v6 : Word)
    (st0 scratch : List (BitVec 8))
    (hlen : input.length = sha256BlockStep * N + rem)
    (hrem : rem < 64)
    (hst : st0.length = 32)
    (hiv : iv.length = 32) (hivEq : iv = sha256IvBytes)
    (hout : out0.length = 32) (hparams : params.length = 16)
    (hscratch : scratch.length = 64)
    (hNbound : sha256BlockStep * N + rem < 2 ^ 63)
    (hcur : inputBase.toNat + sha256BlockStep * N < 2 ^ 64)
    (hcurAlign : (sha256AbsorbCursor inputBase N).toNat % 8 = 0)
    (hcurOver : (sha256AbsorbCursor inputBase N).toNat + rem ≤ 2 ^ 64)
    (houtAlign : outputBase.toNat % 8 = 0)
    (houtOver : outputBase.toNat + 32 ≤ 2 ^ 64)
    (hvalidS : ∀ i < rem,
      isValidByteAccess (sha256AbsorbCursor inputBase N + BitVec.ofNat 64 i) = true)
    (hvalidScratch : ∀ i < 64,
      isValidByteAccess (ShaInput + BitVec.ofNat 64 i) = true)
    (hvalidSq : ∀ i < 32,
      isValidByteAccess (ShaState + BitVec.ofNat 64 (i ^^^ 3)) = true)
    (hvalidD : ∀ i < 32, isValidByteAccess (outputBase + BitVec.ofNat 64 i) = true)
    (hsemOuter : sha256OuterHsem inputBase ShaState ShaInput ShaParams input params iv N)
    (hsemSqLt : rem < 56 →
      sha256BodySqueezeHsem_lt56 ShaState ShaInput ShaParams iv input params N rem)
    (hsemMid : 56 ≤ rem →
      sha256BodyPadMidHsem ShaState ShaInput ShaParams iv input params N rem)
    (hsemSqGe : 56 ≤ rem →
      sha256BodySqueezeHsem_ge56 ShaState ShaInput ShaParams iv input params N rem) :
    cpsTripleWithin (18 + (N * 24 + 2) + (rem * 7 + 44) + 295) (B + 28) (B + 452) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * N + rem)) **
        (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv **
        bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
        bytesRegion inputBase input ** bytesRegion outputBase out0 **
        (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30) ** A)
      (sha256BodyExitPost inputBase outputBase input params iv N rem
        ((regOwn .x11) ** (regOwn .x12) ** A)) := by
  let lenW := BitVec.ofNat 64 (sha256BlockStep * N + rem)
  let bitLen := lenW <<< 3
  let AOuter := (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30) ** A
  have hAOuter : AOuter.pcFree := by pcf
  have hfit : sha256BlockStep * N + rem ≤ input.length := by
    simp only [hlen]; exact Nat.le_refl _
  have cSetup := sha256SetupOuter_spec inputBase outputBase N rem
    v8 v9 v18 v19 v20 v21 v5 v6 st0 scratch params iv out0 input AOuter hAOuter
    hst hiv hscratch hparams hout hrem hlen hNbound hcur hsemOuter
  have cToPad : cpsTripleWithin 0 (B + 196) (B + 196) sha256Cr
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase ShaState ShaInput ShaParams input params iv N 0 **
        (regOwn .x10) ** anyBytes ShaInput 64 **
        sha256OuterFrameAmb outputBase bitLen iv out0
          ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x6) ** AOuter))
      (sha256PadEntryPre inputBase outputBase input params iv out0 N rem
        (sha256PadTemps ** (regOwn .x11) ** (regOwn .x12) ** A)) :=
    cpsTripleWithin_reshape0 fun h hp => by
      have hp1 :=
        sha256OuterPost_padEntry_frame h inputBase input params iv N rem outputBase
          (sha256BitLenW N rem) out0 A
          (by simpa [bitLen, sha256BitLenW, lenW, sha256BlockStep, AOuter] using hp)
      exact sha256OuterPost_to_padEntry h inputBase outputBase input params iv out0 N rem
        (sha256PadTemps ** (regOwn .x11) ** (regOwn .x12) ** A) hlen hp1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) cSetup cToPad
  by_cases hlt : rem < 56
  · have cPadSq := sha256PadSqueeze_lt56 inputBase outputBase input params iv out0 N rem
      ((regOwn .x11) ** (regOwn .x12) ** A) (by pcf) hlen hiv hivEq hout hparams hlt
      hcurAlign hcurOver houtAlign houtOver hvalidS hvalidScratch hvalidSq hvalidD
      (hsemSqLt hlt)
    have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 cPadSq
    refine cpsTripleWithin_weaken (fun _ hp => by
        simp only [AOuter]
        xperm_chunked hp) (fun _ hq => hq) cAll
  · have hremge : 56 ≤ rem := Nat.le_of_not_gt hlt
    have cPadSq := sha256PadSqueeze_ge56 inputBase outputBase input params iv out0 N rem
      ((regOwn .x11) ** (regOwn .x12) ** A) (by pcf) hlen hiv hivEq hout hparams hremge hrem
      hcurAlign hcurOver houtAlign houtOver hvalidS hvalidScratch hvalidSq hvalidD
      (hsemMid hremge) (hsemSqGe hremge)
    have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 cPadSq
    refine cpsTripleWithin_weaken (fun _ hp => by
        simp only [AOuter]
        xperm_chunked hp) (fun _ hq => hq) cAll

end EvmAsm.Codegen.Proofs
