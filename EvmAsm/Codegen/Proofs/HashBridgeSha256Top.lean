/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Top

  Top triple `zkvm_sha256_spec_within` (#12018).

  Route (A) per coord 2026-08-14: the *exported* post states
  `SpecRef.sha256` directly so `erh_hash_one`'s `shaCallWithinShape` /
  `shaCallReturn` can discharge. Operational body digest is an internal
  LHS for the SpecRef bridge (`sha256BodyDigest_eq_specref`); that bridge
  is in-scope for #12018, not a follow-on bead.

  Domain: `input.length = 64*N + rem` with `rem < 64`. Both pad arms are
  in scope — `rem < 56` (BLT taken) and `rem ≥ 56` (fall-through extra
  compress at B+288). Leaving rem≥56 implicit would silently diverge.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Body
import EvmAsm.Codegen.Proofs.HashBridgeSha256Bridge
import EvmAsm.Codegen.Proofs.HashBridgeSha256Frame
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

local macro "pcf" : tactic =>
  `(tactic| repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _
    | assumption)

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev ShaState : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_state
private abbrev ShaInput : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_input
private abbrev ShaIv : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_iv
private abbrev ShaParams : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL
private abbrev sha256BlockStep : Nat := 64

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]
  norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins sha256ProgL_bound a i h

/-- Clobberable temps under the SHA body (frame regs x8/x9/x18–x21 live in
    `regsAt sha256Frame`; ABI a0–a2 carry values). -/
def sha256BodyFreeTemps : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30]

/-- Body fuel: Setup 18 + Outer `N*24+2` + PadThenBitlen rem≥56 `rem*7+44`
    + SqueezeToExit 295. Covers rem&lt;56 via `mono_nSteps`. -/
def sha256BodyFuel (N rem : Nat) : Nat :=
  18 + (N * 24 + 2) + (rem * 7 + 44) + 295

/-- Frame-entry values for the six saved regs. -/
def sha256EntryVals (v8 v9 v18 v19 v20 v21 : Word) : Reg → Word
  | .x8 => v8
  | .x9 => v9
  | .x18 => v18
  | .x19 => v19
  | .x20 => v20
  | .x21 => v21
  | _ => (0 : Word)

/-- Caller ambient at entry (no frame regs — those sit in `regsAt`).
    BSS: 32-byte state, 64-byte scratch/block, 32-byte IV, 16-byte params. -/
def shaCallerPre (inputBase lenW outputBase : Word)
    (st0 scratch0 iv params input out0 : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwns sha256BodyFreeTemps **
    bytesRegion ShaState st0 **
    bytesRegion ShaIv iv **
    bytesRegion ShaInput scratch0 **
    bytesRegion ShaParams params **
    bytesRegion inputBase input **
    bytesRegion outputBase out0 ** A

theorem shaCallerPre_pcFree (inputBase lenW outputBase : Word)
    (st0 scratch0 iv params input out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A).pcFree := by
  simp only [shaCallerPre]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- BSS finals at exit (split input carried separately at top). -/
def sha256PadFreeBss (input params iv : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) : Assertion :=
  let scratch :=
    if rem < 56 then sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)
    else sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)
  bytesRegion ShaParams params **
    bytesRegion ShaState (sha256BodyFinalState input N rem) **
    bytesRegion ShaInput scratch **
    bytesRegion ShaIv iv ** A

theorem sha256PadFreeBss_pcFree (input params iv : List (BitVec 8))
    (N rem : Nat) (A : Assertion) (hA : A.pcFree) :
    (sha256PadFreeBss input params iv N rem A).pcFree := by
  unfold sha256PadFreeBss
  split_ifs
  all_goals
    exact pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Exit pad-free ambient: BSS finals + split input (recombine at top if needed). -/
def sha256PadFreeA (inputBase : Word) (input params iv : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) : Assertion :=
  sha256PadFreeBss input params iv N rem
    (bytesRegion inputBase (input.take (64 * N)) **
      bytesRegion (sha256AbsorbCursor inputBase N) (sha256Residual input N) ** A)

theorem sha256PadFreeA_pcFree (inputBase : Word) (input params iv : List (BitVec 8))
    (N rem : Nat) (A : Assertion) (hA : A.pcFree) :
    (sha256PadFreeA inputBase input params iv N rem A).pcFree := by
  simp only [sha256PadFreeA]
  exact sha256PadFreeBss_pcFree input params iv N rem
    (bytesRegion inputBase (input.take (64 * N)) **
      bytesRegion (sha256AbsorbCursor inputBase N) (sha256Residual input N) ** A)
    (pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA)

/-- Exported caller post: SpecRef digest (route A). ABI args owned;
    input preserved; BSS finals + split input in `sha256PadFreeA`. -/
def shaCallerPost (inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) (A : Assertion) : Assertion :=
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
    regOwn .x0 **
    regOwns sha256BodyFreeTemps **
    bytesRegion outputBase (sha256 input) **
    sha256PadFreeA inputBase input params iv N rem A

theorem shaCallerPost_pcFree (inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) (hA : A.pcFree) :
    (shaCallerPost inputBase outputBase input params iv N rem A).pcFree := by
  simp only [shaCallerPost]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    sha256PadFreeA_pcFree inputBase input params iv N rem A hA

/-- Operational post used inside the frame wrap before SpecRef rewrite. -/
def shaCallerPostOp (inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) (A : Assertion) : Assertion :=
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
    regOwn .x0 **
    regOwns sha256BodyFreeTemps **
    bytesRegion outputBase (sha256BodyDigest input N rem) **
    sha256PadFreeA inputBase input params iv N rem A

theorem shaCallerPostOp_pcFree (inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) (hA : A.pcFree) :
    (shaCallerPostOp inputBase outputBase input params iv N rem A).pcFree := by
  simp only [shaCallerPostOp]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    sha256PadFreeA_pcFree inputBase input params iv N rem A hA

/-- Flat frame regs (no trailing emp). -/
private abbrev frameRegsIs (v8 v9 v18 v19 v20 v21 : Word) : Assertion :=
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
  (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21)

private abbrev frameRegsOwn : Assertion :=
  (regOwn .x8) ** (regOwn .x9) ** (regOwn .x18) **
  (regOwn .x19) ** (regOwn .x20) ** (regOwn .x21)

private theorem regsAt_flat (v8 v9 v18 v19 v20 v21 : Word) :
    regsAt sha256Frame (sha256EntryVals v8 v9 v18 v19 v20 v21) =
      frameRegsIs v8 v9 v18 v19 v20 v21 := by
  simp only [frameRegsIs, sha256Frame, regsAt, sha256EntryVals, List.foldr,
    sepConj_emp_right']

private theorem regsOwnAt_flat :
    regsOwnAt sha256Frame = frameRegsOwn := by
  simp only [frameRegsOwn, sha256Frame, regsOwnAt, List.foldr,
    sepConj_emp_right']

/-- Pad temps carried in body-spec ambient `A`. -/
private def sha256BodyEntryPad (A : Assertion) : Assertion :=
  (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30) ** A

/-- Body entry core without clobberable x5/x6 (peeled for `regOwn`). -/
def sha256BodyEntryCore (inputBase lenW outputBase : Word)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch params iv input out0 : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
    (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
    (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    bytesRegion ShaState st0 ** bytesRegion ShaIv iv **
    bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
    bytesRegion inputBase input ** bytesRegion outputBase out0 **
    (.x0 ↦ᵣ (0 : Word)) ** A

/-- Body entry pre at `sha256BodyEntry` (matches `sha256Body_spec` pre). -/
def sha256BodyEntryPre (inputBase lenW outputBase : Word)
    (v8 v9 v18 v19 v20 v21 v5 v6 : Word)
    (st0 scratch params iv input out0 : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
    (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
    (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
    bytesRegion ShaState st0 ** bytesRegion ShaIv iv **
    bytesRegion ShaInput scratch ** bytesRegion ShaParams params **
    bytesRegion inputBase input ** bytesRegion outputBase out0 **
    (.x0 ↦ᵣ (0 : Word)) **
    (regOwn .x7) ** (regOwn .x28) ** (regOwn .x29) ** (regOwn .x30) ** A

private theorem bodyEntry_trailing_to_pre
    (inputBase lenW outputBase : Word)
    (v8 v9 v18 v19 v20 v21 v5 v6 : Word)
    (st0 scratch params iv input out0 : List (BitVec 8)) (A : Assertion)
    {h : PartialState}
    (hp :
      (sha256BodyEntryCore inputBase lenW outputBase v8 v9 v18 v19 v20 v21
        st0 scratch params iv input out0 (sha256BodyEntryPad A) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6)) h) :
    sha256BodyEntryPre inputBase lenW outputBase v8 v9 v18 v19 v20 v21 v5 v6
      st0 scratch params iv input out0 A h := by
  simp only [sha256BodyEntryCore, sha256BodyEntryPre, sha256BodyEntryPad] at hp ⊢
  xperm_chunked hp

/-- Peeled body entry: core + pad + `regOwn` x5/x6 (for flat caller hookup). -/
private def sha256BodyEntryPeeled (inputBase lenW outputBase : Word)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch params iv input out0 : List (BitVec 8))
    (A : Assertion) : Assertion :=
  sha256BodyEntryCore inputBase lenW outputBase v8 v9 v18 v19 v20 v21
    st0 scratch params iv input out0 (sha256BodyEntryPad A) ** regOwns [.x5, .x6]

/-- `regsAt` + `shaCallerPre` → peeled body entry (Keccak-style, no frame suffix). -/
private theorem entryCore_to_body (h : PartialState)
    (inputBase lenW outputBase : Word)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch params iv input out0 : List (BitVec 8)) (A : Assertion)
    (hp :
      (regsAt sha256Frame (sha256EntryVals v8 v9 v18 v19 v20 v21) **
        shaCallerPre inputBase lenW outputBase st0 scratch iv params input out0 A) h) :
    (sha256BodyEntryPeeled inputBase lenW outputBase v8 v9 v18 v19 v20 v21
      st0 scratch params iv input out0 A) h := by
  have hp1 :
      (frameRegsIs v8 v9 v18 v19 v20 v21 **
        shaCallerPre inputBase lenW outputBase st0 scratch iv params input out0 A) h := by
    simpa [regsAt_flat] using hp
  simp only [frameRegsIs, shaCallerPre, sha256BodyEntryPeeled, sha256BodyEntryCore,
    sha256BodyEntryPad, sha256BodyFreeTemps, regOwns,
    regOwns_cons, sepConj_emp_right'] at hp1 ⊢
  xperm_chunked hp1

/-- `sha256BodyExitPost` → `regsOwnAt` + `shaCallerPostOp`. -/
private theorem exitCore_to_caller (h : PartialState)
    (inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (hp :
      sha256BodyExitPost inputBase outputBase input params iv N rem
        ((regOwn .x11) ** (regOwn .x12) ** A) h) :
    (regsOwnAt sha256Frame **
      shaCallerPostOp inputBase outputBase input params iv N rem A) h := by
  have hp0 :
      ((.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ ShaState) **
        regOwn .x10 ** (.x19 ↦ᵣ outputBase) ** (.x21 ↦ᵣ ShaInput) **
        bytesRegion ShaParams params **
        bytesRegion ShaState (sha256BodyFinalState input N rem) **
        bytesRegion ShaInput
          (if rem < 56 then sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)
           else sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)) **
        bytesRegion outputBase (sha256BodyDigest input N rem) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        sha256BodyExitAmb inputBase input iv N (regOwn .x11 ** regOwn .x12 ** A)) h := by
    simpa [sha256BodyExitPost] using hp
  have hp1 :
      (regOwn .x5 ** regOwn .x6 ** regOwn .x8 ** regOwn .x10 **
        regOwn .x19 ** regOwn .x21 **
        bytesRegion ShaParams params **
        bytesRegion ShaState (sha256BodyFinalState input N rem) **
        bytesRegion ShaInput
          (if rem < 56 then sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)
           else sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)) **
        bytesRegion outputBase (sha256BodyDigest input N rem) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        sha256BodyExitAmb inputBase input iv N (regOwn .x11 ** regOwn .x12 ** A)) h := by
    refine sepConj_mono (regIs_implies_regOwn (r := .x5) (v := (32 : Word))) ?_ h hp0
    intro h1 hp1'
    refine sepConj_mono (regIs_implies_regOwn (r := .x6) (v := (32 : Word))) ?_ h1 hp1'
    intro h2 hp2'
    refine sepConj_mono (regIs_implies_regOwn (r := .x8) (v := ShaState)) ?_ h2 hp2'
    intro h3 hp3'
    have hp3b :
        (regOwn .x10 ** regOwn .x19 ** (.x21 ↦ᵣ ShaInput) **
          bytesRegion ShaParams params **
          bytesRegion ShaState (sha256BodyFinalState input N rem) **
          bytesRegion ShaInput
            (if rem < 56 then sha256FinalBlock_lt56 (sha256Residual input N) rem (sha256BitLenW N rem)
             else sha256FinalBlock_ge56 (sha256Residual input N) rem (sha256BitLenW N rem)) **
          bytesRegion outputBase (sha256BodyDigest input N rem) **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          sha256BodyExitAmb inputBase input iv N (regOwn .x11 ** regOwn .x12 ** A)) h3 :=
      sepConj_mono_right
        (fun h4 hp4' =>
          sepConj_mono_left (regIs_implies_regOwn (r := .x19) (v := outputBase)) h4 hp4')
        h3 hp3'
    exact sepConj_mono_right
      (fun h5 hp5' =>
        sepConj_mono_right
          (fun h6 hp6' =>
            sepConj_mono_left (regIs_implies_regOwn (r := .x21) (v := ShaInput)) h6 hp6')
          h5 hp5')
      h3 hp3b
  have hp2 :
      (frameRegsOwn **
        shaCallerPostOp inputBase outputBase input params iv N rem A) h := by
    simp only [sha256BodyExitAmb] at hp1
    simp only [frameRegsOwn, shaCallerPostOp, sha256PadFreeA, sha256PadFreeBss,
      regOwns, sha256BodyFreeTemps, regOwns_cons, sepConj_emp_right'] at hp1 ⊢
    xperm_chunked hp1
  simpa [regsOwnAt_flat] using hp2

/-- Framed body triple for the no-ra wrap (operational digest post). -/
theorem sha256Body_framed (sp0 ret : Word)
    (inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hlen : input.length = sha256BlockStep * N + rem)
    (hrem : rem < 64)
    (hst : st0.length = 32)
    (hiv : iv.length = 32) (hivEq : iv = sha256IvBytes)
    (hparams : params.length = 16)
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
      sha256BodySqueezeHsem_ge56 ShaState ShaInput ShaParams iv input params N rem)
    /- Arbitrary initial output cell. Sound because squeeze fully overwrites all
       32 bytes: `sha256SqueezePrefix_full` (`SqueezeLoop.lean`) shows
       `sha256SqueezePrefix st out0 32 = sha256SqueezeBE st` independent of `out0`. -/
    (out0 : List (BitVec 8)) (hout : out0.length = 32) :
    let newSp := sp0 + signExtend12 ((-48 : BitVec 12))
    let vals := sha256EntryVals v8 v9 v18 v19 v20 v21
    let lenW := BitVec.ofNat 64 (sha256BlockStep * N + rem)
    cpsTripleWithin (sha256BodyFuel N rem)
      (sha256BodyEntry B) (sha256BodyExit B) sha256Cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame newSp vals **
        shaCallerPre inputBase lenW outputBase st0 scratch iv params input out0 A)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsOwnAt sha256Frame **
        frameSlotsSaved sha256Frame newSp vals **
        shaCallerPostOp inputBase outputBase input params iv N rem A) := by
  intro newSp vals lenW
  let entryPadA := sha256BodyEntryPad A
  have hbodyAll : ∀ v5 v6,
      cpsTripleWithin (sha256BodyFuel N rem) (B + 28) (B + 452) sha256Cr
        (sha256BodyEntryCore inputBase lenW outputBase v8 v9 v18 v19 v20 v21
          st0 scratch params iv input out0 entryPadA ** ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6)))
        (sha256BodyExitPost inputBase outputBase input params iv N rem
          ((regOwn .x11) ** (regOwn .x12) ** A)) :=
    fun v5 v6 =>
      cpsTripleWithin_weaken
        (fun hstate hp =>
          bodyEntry_trailing_to_pre inputBase lenW outputBase v8 v9 v18 v19 v20 v21
            v5 v6 st0 scratch params iv input out0 A hp)
        (fun _ hq => hq)
        (sha256Body_spec inputBase outputBase input params iv out0 N rem A hA
          v8 v9 v18 v19 v20 v21 v5 v6 st0 scratch
          hlen hrem hst hiv hivEq hout hparams hscratch hNbound hcur hcurAlign hcurOver
          houtAlign houtOver hvalidS hvalidScratch hvalidSq hvalidD
          hsemOuter hsemSqLt hsemMid hsemSqGe)
  have hbodyPeeled := cpsTripleWithin_peel_regOwns [.x5, .x6] (by decide)
    (P := sha256BodyEntryCore inputBase lenW outputBase v8 v9 v18 v19 v20 v21
      st0 scratch params iv input out0 entryPadA)
    (Q := sha256BodyExitPost inputBase outputBase input params iv N rem
      ((regOwn .x11) ** (regOwn .x12) ** A))
    (fun vf => by
      convert hbodyAll (vf .x5) (vf .x6) using 1
      simp [regAtomsOf, sepConj_emp_right'])
  have hbody0 := hbodyPeeled
  have hslots : (frameSlotsSaved sha256Frame newSp vals).pcFree :=
    pcFree_frameSlotsSaved _ _ _
  have hbodyF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
      frameSlotsSaved sha256Frame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hslots))
    hbody0
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp1 :
          ((regsAt sha256Frame vals **
              shaCallerPre inputBase lenW outputBase st0 scratch iv params input out0 A) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
              frameSlotsSaved sha256Frame newSp vals)) h := by
        xperm_hyp hp
      refine sepConj_mono ?_ (fun _ => id) h hp1
      intro h1 hp1'
      exact entryCore_to_body h1 inputBase lenW outputBase v8 v9 v18 v19 v20 v21
        st0 scratch params iv input out0 A (by simpa [vals] using hp1'))
    (fun h hq => by
      have hq1 :
          ((regsOwnAt sha256Frame **
              shaCallerPostOp inputBase outputBase input params iv N rem A) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
              frameSlotsSaved sha256Frame newSp vals)) h := by
        refine sepConj_mono ?_ (fun _ => id) h hq
        intro h1 hp1
        exact exitCore_to_caller h1 inputBase outputBase input params iv N rem A
          (by simpa using hp1)
      xperm_hyp hq1)
    hbodyF

/-- Named bridge obligation (#12018): operational machine digest = SpecRef.
    Covers full `rem < 64` (both rem&lt;56 and rem≥56 pad arms).
    Proof in `HashBridgeSha256Bridge.lean`. -/
-- re-exported from HashBridgeSha256Bridge
theorem shaCallerPostOp_to_shaCallerPost (inputBase outputBase : Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (hlen : input.length = sha256BlockStep * N + rem) (hrem : rem < 64)
    (h : PartialState) :
    shaCallerPostOp inputBase outputBase input params iv N rem A h →
      shaCallerPost inputBase outputBase input params iv N rem A h := by
  intro hp
  have hbridge := sha256BodyDigest_eq_specref input N rem
    (by simpa [sha256BlockStep] using hlen) hrem
  simp only [shaCallerPostOp, shaCallerPost, sha256PadFreeA, sha256PadFreeBss] at hp ⊢
  rw [hbridge] at hp
  xperm_chunked hp

/-- Top triple for `zkvm_sha256`. Exported post = SpecRef.sha256.
    Internal decomposition: `sha256Body_framed` (operational digest) +
    `sha256BodyDigest_eq_specref` + `sha256Frame_spec_own` (fuel 7+body+8).
    Pad domain: rem &lt; 64 includes rem ≥ 56. -/
theorem zkvm_sha256_spec_within (sp0 ret : Word)
    (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch0 iv params : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : input.length = 64 * N + rem)
    (hrem : rem < 64)
    (hst : st0.length = 32)
    (hscratch : scratch0.length = 64)
    (hiv : iv.length = 32) (hivEq : iv = sha256IvBytes)
    (hparams : params.length = 16)
    (hNbound : 64 * N + rem < 2 ^ 63)
    (hcur : inputBase.toNat + 64 * N < 2 ^ 64)
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
      sha256BodySqueezeHsem_ge56 ShaState ShaInput ShaParams iv input params N rem)
    /- Initial output cell, length 32. Fully overwritten by squeeze
       (`sha256SqueezePrefix_full`); post is still `sha256 input`. -/
    (out0 : List (BitVec 8)) (hout : out0.length = 32) :
    let vals := sha256EntryVals v8 v9 v18 v19 v20 v21
    let lenW := BitVec.ofNat 64 (64 * N + rem)
    let newSp := sp0 + signExtend12 ((-48 : BitVec 12))
    cpsTripleWithin (7 + sha256BodyFuel N rem + 8) B ret sha256Cr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsOwn sha256Frame newSp **
        shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame newSp vals **
        shaCallerPost inputBase outputBase input params iv N rem A) := by
  intro vals lenW newSp
  have hbody0 := sha256Body_framed sp0 ret inputBase outputBase input params iv N rem
    v8 v9 v18 v19 v20 v21 st0 scratch0 A hA
    (by simpa [sha256BlockStep] using hlen) hrem hst hiv hivEq hparams hscratch
    (by simpa [sha256BlockStep] using hNbound) hcur hcurAlign hcurOver houtAlign houtOver
    hvalidS hvalidScratch hvalidSq hvalidD hsemOuter hsemSqLt hsemMid hsemSqGe out0 hout
  -- Align `sha256Body_framed`'s let-bound newSp/vals/lenW with this theorem's lets.
  have hbody : cpsTripleWithin (sha256BodyFuel N rem)
      (sha256BodyEntry B) (sha256BodyExit B) sha256Cr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt sha256Frame vals **
        frameSlotsSaved sha256Frame newSp vals **
        shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsOwnAt sha256Frame **
        frameSlotsSaved sha256Frame newSp vals **
        shaCallerPostOp inputBase outputBase input params iv N rem A) := by
    simpa [newSp, vals, lenW, sha256BlockStep, sha256BodyFuel,
      sha256BodyEntry, sha256BodyExit] using hbody0
  have hmemS : ∀ a i, CodeReq.ofProg (B + 4) (storeProg sha256Frame) a = some i →
      sha256Cr a = some i := by
    intro a i h
    have hsub := CodeReq.ofProg_mono_subrange B
      [(.ADDI .x2 .x2 (-48 : BitVec 12))]
      (storeProg sha256Frame)
      (sha256ProgL.drop 7)
      (by
        have : sha256ProgL =
            [(.ADDI .x2 .x2 (-48 : BitVec 12))] ++ storeProg sha256Frame ++
              sha256ProgL.drop 7 := by
          simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of,
            storeProg, sha256Frame]
          decide
        rw [← this]; exact sha256ProgL_bound)
      a i h
    exact hsub
  have hmemL : ∀ a i, CodeReq.ofProg (sha256BodyExit B) (loadProg sha256Frame) a = some i →
      sha256Cr a = some i := by
    intro a i h
    have hsub := CodeReq.ofProg_mono_subrange B
      (sha256ProgL.take 113)
      (loadProg sha256Frame)
      (sha256ProgL.drop 119)
      (by
        have : sha256ProgL =
            sha256ProgL.take 113 ++ loadProg sha256Frame ++ sha256ProgL.drop 119 := by
          simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of,
            loadProg, sha256Frame]
          decide
        rw [← this]; exact sha256ProgL_bound)
      a i (by
        have hExit : sha256BodyExit B = B + BitVec.ofNat 64 (4 * 113) := by
          simp only [sha256BodyExit]; decide
        have hlen113 : (sha256ProgL.take 113).length = 113 := by
          simp only [List.length_take, sha256ProgL_len]; norm_num
        simpa [hlen113, hExit, sha256BodyExit] using h)
    exact hsub
  have hOp := sha256Frame_spec_own sha256Cr B sp0 ret vals (sha256BodyFuel N rem)
    (shaCallerPre inputBase lenW outputBase st0 scratch0 iv params input out0 A)
    (shaCallerPostOp inputBase outputBase input params iv N rem A)
    halign_ret
    (shaCallerPre_pcFree inputBase lenW outputBase st0 scratch0 iv params input out0 A hA)
    (shaCallerPostOp_pcFree inputBase outputBase input params iv N rem A hA)
    (mem_at 0 (.ADDI .x2 .x2 (-48 : BitVec 12)) B
      (by decide) (by rw [sha256ProgL_len]; norm_num) (by rfl))
    hmemS hmemL
    (mem_at 119 (.ADDI .x2 .x2 (48 : BitVec 12)) (B + 476)
      (by decide) (by rw [sha256ProgL_len]; norm_num) (by rfl))
    (mem_at 120 (.JALR .x0 .x1 (0 : BitVec 12)) (B + 480)
      (by decide) (by rw [sha256ProgL_len]; norm_num) (by rfl))
    hbody
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      refine sepConj_mono_right (fun h1 hp1 =>
        sepConj_mono_right (fun h2 hp2 =>
          sepConj_mono_right (fun h3 hp3 =>
            sepConj_mono_right (fun h4 hp4 =>
              shaCallerPostOp_to_shaCallerPost inputBase outputBase input params iv N rem A
                (by simpa [sha256BlockStep] using hlen) hrem h4 hp4) h3 hp3) h2 hp2) h1 hp1) h hq)
    hOp

end EvmAsm.Codegen.Proofs
