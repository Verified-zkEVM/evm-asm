/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakBody

  Body compose for `zkvm_keccak256` (bodyEntry → bodyExit):
    setup → outer absorb (LI reload) → rem path → pad+CSRS+digest+LI0.

  Geometry (base = GuestAddrs.zkvm_keccak256 = 0x800033b0):
    bodyEntry B+20   (idx 5)
    outer LI  B+64   (idx 16)  — JAL target 0x8000368c
    BLT       B+68   (idx 17)  — 0x80003690  (≠ LI; BLT-hdr lemma unapplied)
    remHdr    B+136  (idx 34)
    beqHdr    B+144  (idx 36)
    padHdr    B+180  (idx 45)
    bodyExit  B+252  (idx 63)

  PR note: outer uses `signedCountdownLoop_reload_spec` (hdr=LI); the BLT-header
  `signedCountdownLoop_spec` does not apply (JAL→LI ≠ BLT).
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakSetup
import EvmAsm.Codegen.Proofs.HashBridgeKeccakOuterBody
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTail
import EvmAsm.Codegen.Proofs.HashBridgeKeccakWrap
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256
private abbrev Zk3 : Word := BitVec.ofNat 64 GuestAddrs.zk3_state
private abbrev keccakProgL : List Instr := zkvmKeccak256_prog
private abbrev keccakCr : CodeReq := CodeReq.ofProg B keccakProgL

private theorem keccakProgL_len : keccakProgL.length = 69 := by
  simp only [keccakProgL, zkvmKeccak256_prog, zkvmKeccak256_prog_of]
  decide

private theorem keccakProgL_bound : 4 * keccakProgL.length < 2 ^ 64 := by
  rw [keccakProgL_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < keccakProgL.length)
    (hins : keccakProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → keccakCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A keccakProgL k ins hA hk hins keccakProgL_bound a i h

private theorem jal_back :
    ((B + 64 : Word) + 8) + 60 + signExtend21 (-68 : BitVec 21) = B + 64 := by
  decide
private theorem blt_exit :
    ((B + 64 : Word) + 4) + signExtend13 (68 : BitVec 13) = B + 136 := by
  decide
private theorem beq_to_pad :
    (B + 144 : Word) + signExtend13 (36 : BitVec 13) = B + 180 := by
  decide
private theorem pad_plus_72 : (B + 180 : Word) + 72 = B + 252 := by decide
private theorem rem_plus_8 : (B + 136 : Word) + 8 = B + 144 := by decide
private theorem beq_rem_exit : ((B + 144 : Word) + 4) + 32 = B + 180 := by decide

/-- Fuel: setup 107 + outer (N*146+2) + remSetup 2 + remPath (1+rem*8) + pad 18. -/
def keccakBodyFuel (N rem : Nat) : Nat :=
  107 + (N * (keccakAbsorbOuterBodyFuel + 2) + 2) + 2 + (1 + rem * 8) + 18

/-- Pure guest sponge after outer absorb + rem XOR (pre-pad). -/
def keccakBodyPrePad (input : List (BitVec 8)) (N rem : Nat) : List (BitVec 8) :=
  let stN := keccakAbsorbedPrefix input N
  let tail := (input.drop (keccakAbsorbStep * N)).take rem
  keccakRemAbsorbed stN tail rem

/-- Final digest bytes produced by guest path (pre pure-bridge to keccak256). -/
def keccakBodyDigest (input : List (BitVec 8)) (N rem : Nat) : List (BitVec 8) :=
  let st := keccakBodyPrePad input N rem
  let padded := keccakGuestPad st rem
  keccakDigestCopy (setBytes padded 0 (keccakBytes padded 0))

/-- Free temps needed by outer/rem/pad that setup does not initialize.
    Includes all of `keccakAbsorbOuterTemps` except x11/x12/x28 (setup leaves
    those concrete and the reshape drops them to owns). -/
def keccakBodyFreeTemps : List Reg :=
  [.x5, .x6, .x7, .x13, .x14, .x15, .x16, .x17, .x30, .x31]

/-- Ambient under outer: output pointer + zeroed digest + free A. -/
def keccakOuterAmb (outputBase : Word) (out0 : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 ** A

theorem keccakOuterAmb_pcFree (outputBase : Word) (out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (keccakOuterAmb outputBase out0 A).pcFree :=
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Body exit post (a0=0, digest written, sponge final).
    Free `A` carries input buffer + leftover owns (x9/x20) from pad path. -/
def keccakBodyExitPost (outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) : Assertion :=
  (.x8 ↦ᵣ Zk3) ** (.x18 ↦ᵣ outputBase) **
    (regOwn .x5) ** (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion Zk3
      (setBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0
        (keccakBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0)) **
    bytesRegion outputBase (keccakBodyDigest input N rem) **
    ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 ** A)

/-- Body entry pre at bodyEntry (after frame prologue). -/
def keccakBodyEntryPre (inputBase lenW outputBase : Word)
    (v20 v9 v18 v8 v28 v29 : Word)
    (os : List (BitVec 8)) (input out0 : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
    (.x20 ↦ᵣ v20) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
    (.x8 ↦ᵣ v8) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwns keccakBodyFreeTemps **
    bytesRegion Zk3 os **
    bytesRegion inputBase input **
    bytesRegion outputBase out0 ** A

theorem keccakBodyEntryPre_pcFree (inputBase lenW outputBase : Word)
    (v20 v9 v18 v8 v28 v29 : Word)
    (os input out0 : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (keccakBodyEntryPre inputBase lenW outputBase v20 v9 v18 v8 v28 v29
      os input out0 A).pcFree := by
  simp only [keccakBodyEntryPre]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Setup framed through free temps + input/out buffers. -/
theorem keccakSetupToOuter_framed (inputBase lenW outputBase : Word)
    (v20 v9 v18 v8 v28 v29 : Word)
    (os : List (BitVec 8)) (input out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hlen : os.length = 200)
    (halign : Zk3.toNat % 8 = 0)
    (hover : Zk3.toNat + 200 < 2 ^ 64) :
    cpsTripleWithin 107 (B + 20) (B + 64) keccakCr
      (keccakBodyEntryPre inputBase lenW outputBase v20 v9 v18 v8 v28 v29
        os input out0 A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) **
        (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x29 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion Zk3 keccakZeroStateBytes **
        bytesRegion inputBase input **
        bytesRegion outputBase out0 ** A) := by
  -- Pass free temps + I/O buffers as setup ambient (no frameR — ambient is A)
  let Amb : Assertion :=
    regOwns keccakBodyFreeTemps **
      bytesRegion inputBase input **
      bytesRegion outputBase out0 ** A
  have hAmb : Amb.pcFree :=
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have c0 := keccakSetupToOuter_spec inputBase lenW outputBase
    v20 v9 v18 v8 v28 v29 os Amb hAmb hlen halign hover
  -- setup pre/post already include Amb as trailing A; reshape flat entry ↔ nested
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [keccakBodyEntryPre] at hp
      -- entry flat → setup pre (same atoms, Amb nested as trailing A)
      have hp' : (
          (.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
            (.x20 ↦ᵣ v20) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
            (.x8 ↦ᵣ v8) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** Amb) h := by
        simp only [Amb]
        xperm_hyp hp
      exact hp')
    (fun h hq => by
      simp only [Amb] at hq ⊢
      xperm_hyp hq)
    c0

private theorem cursor0 (inputBase : Word) :
    keccakAbsorbCursor inputBase 0 = inputBase := by
  simp only [keccakAbsorbCursor, Nat.mul_zero]
  rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
  bv_omega

private theorem absorbed0 (input : List (BitVec 8)) :
    keccakAbsorbedPrefix input 0 = keccakZeroStateBytes := by
  simp only [keccakAbsorbedPrefix, keccakZeroStateBytes]

/-- Setup post → outer pre. Drops x10/x11/x12/x28/x29 into OuterCore owns. -/
theorem keccakSetupPost_to_outerPre (h : PartialState)
    (inputBase outputBase : Word) (input : List (BitVec 8))
    (N rem : Nat) (out0 : List (BitVec 8)) (A : Assertion)
    (hp :
      ((.x10 ↦ᵣ inputBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) **
        (.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) **
        (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x29 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion Zk3 keccakZeroStateBytes **
        bytesRegion inputBase input **
        bytesRegion outputBase out0 ** A) h) :
    ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
      (regOwn .x29) **
      keccakAbsorbOuterInv Zk3 inputBase input N N
        (keccakOuterAmb outputBase out0 A)) h := by
  -- Drop concrete values that OuterCore only owns
  have hp1 :=
    sepConj_mono (regIs_implies_regOwn (r := .x10))
      (sepConj_mono (regIs_implies_regOwn (r := .x11))
        (sepConj_mono (regIs_implies_regOwn (r := .x12))
          (sepConj_mono (fun _ => id)
            (sepConj_mono (fun _ => id)
              (sepConj_mono (fun _ => id)
                (sepConj_mono (fun _ => id)
                  (sepConj_mono (regIs_implies_regOwn (r := .x28))
                    (sepConj_mono (regIs_implies_regOwn (r := .x29))
                      (fun _ => id))))))))) h hp
  -- Unfold freeTemps owns (ends in emp) for xperm
  have hp1' : (
      (regOwn .x10) ** (regOwn .x11) ** (regOwn .x12) **
        (.x20 ↦ᵣ inputBase) **
        (.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) **
        (regOwn .x28) ** (regOwn .x29) ** (.x0 ↦ᵣ (0 : Word)) **
        ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          (regOwn .x13) ** (regOwn .x14) ** (regOwn .x15) **
          (regOwn .x16) ** (regOwn .x17) ** (regOwn .x30) **
          (regOwn .x31) ** empAssertion) **
        bytesRegion Zk3 keccakZeroStateBytes **
        bytesRegion inputBase input **
        bytesRegion outputBase out0 ** A) h := by
    simpa [keccakBodyFreeTemps, regOwns] using hp1
  have hp2 : (
      (.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (regOwn .x29) **
        (.x8 ↦ᵣ Zk3) ** (.x20 ↦ᵣ inputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          (regOwn .x28) ** (regOwn .x30) ** (regOwn .x31) **
          (regOwn .x11) ** (regOwn .x12) **
          (regOwn .x13) ** (regOwn .x14) ** (regOwn .x15) **
          (regOwn .x16) ** (regOwn .x17) ** empAssertion) **
        bytesRegion Zk3 keccakZeroStateBytes **
        bytesRegion inputBase input **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 ** A) h := by
    xperm_hyp hp1'
  have hp3 : (
      (.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (regOwn .x29) **
        (.x8 ↦ᵣ Zk3) ** (.x20 ↦ᵣ inputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakAbsorbOuterTemps **
        bytesRegion Zk3 keccakZeroStateBytes **
        bytesRegion inputBase input **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 ** A) h := by
    simpa [keccakAbsorbOuterTemps, regOwns] using hp2
  -- Fold OuterCore / OuterInv / OuterAmb
  have hp4 : (
      (.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (regOwn .x29) **
        keccakAbsorbOuterCore Zk3 inputBase input inputBase
          keccakZeroStateBytes
          (keccakOuterAmb outputBase out0 A)) h := by
    simpa [keccakAbsorbOuterCore, keccakOuterAmb] using hp3
  simpa [keccakAbsorbOuterInv, Nat.sub_self, cursor0, absorbed0] using hp4

/-- Outer loop under body ambient (mem via mem_at). -/
theorem keccakOuterLoop_body (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (out0 : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hrem : rem < keccakAbsorbStep)
    (hfit : keccakAbsorbStep * N + rem ≤ input.length)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8 : Zk3.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (Zk3 + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (N * (keccakAbsorbOuterBodyFuel + 2) + 2)
      (B + 64) (B + 136) keccakCr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (keccakAbsorbStep * N + rem)) **
        (regOwn .x29) **
        keccakAbsorbOuterInv Zk3 inputBase input N N
          (keccakOuterAmb outputBase out0 A))
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        keccakAbsorbOuterInv Zk3 inputBase input N 0
          (keccakOuterAmb outputBase out0 A)) := by
  refine keccakAbsorbOuterLoop_spec keccakCr (B + 64) (B + 136)
    Zk3 inputBase input N rem (keccakOuterAmb outputBase out0 A)
    (keccakOuterAmb_pcFree _ _ _ hA)
    hrem hfit hNbound hb8 hvalid
    blt_exit jal_back
    (mem_at 16 (.LI .x29 (BitVec.ofNat 64 keccakAbsorbStep)) (B + 64)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 17 (.BLT .x9 .x29 (68 : BitVec 13)) (B + 68)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 18 (.MV .x28 .x8) (B + 72)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 19 (.MV .x30 .x20) (B + 76)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 20 (.LI .x31 (17 : Word)) (B + 80)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 21 (.LD .x5 .x30 0) (B + 84)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 22 (.LD .x6 .x28 0) (B + 88)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 23 (.XOR .x6 .x6 .x5) (B + 92)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 24 (.SD .x28 .x6 0) (B + 96)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 25 (.ADDI .x28 .x28 8) (B + 100)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 26 (.ADDI .x30 .x30 8) (B + 104)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 27 (.ADDI .x31 .x31 (-1)) (B + 108)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 28 (.BNE .x31 .x0 (-28)) (B + 112)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 29 (.MV .x10 .x8) (B + 116)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 30 (.CSRS 0x800 .x10) (B + 120)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 31 (.ADDI .x20 .x20 (136 : BitVec 12)) (B + 124)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 32 (.ADDI .x9 .x9 (-136 : BitVec 12)) (B + 128)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 33 (.JAL .x0 (-68 : BitVec 21)) (B + 132)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))

/-- Ambient under rem path: prefix of input (absorbed blocks) + out + free owns. -/
def keccakRemAmb (outputBase : Word) (out0 : List (BitVec 8))
    (inputBase : Word) (absorbedPref : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
    bytesRegion inputBase absorbedPref **
    (regOwn .x10) ** (regOwn .x29) **
    regOwns [.x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x31] ** A

theorem keccakRemAmb_pcFree (outputBase : Word) (out0 : List (BitVec 8))
    (inputBase : Word) (absorbedPref : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (keccakRemAmb outputBase out0 inputBase absorbedPref A).pcFree :=
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (pcFree_regOwns _) hA

/-- Residual after N full blocks (exact-length domain). -/
def keccakResidual (input : List (BitVec 8)) (N : Nat) : List (BitVec 8) :=
  input.drop (keccakAbsorbStep * N)

private theorem residual_length_eq (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = keccakAbsorbStep * N + rem) :
    (keccakResidual input N).length = rem := by
  simp only [keccakResidual, List.length_drop, hlen]; omega

private theorem absorbedPref_length (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = keccakAbsorbStep * N + rem) :
    (input.take (keccakAbsorbStep * N)).length = keccakAbsorbStep * N := by
  simp only [List.length_take, hlen]; omega

private theorem input_split_eq (inputBase : Word) (input : List (BitVec 8))
    (N rem : Nat) (hlen : input.length = keccakAbsorbStep * N + rem)
    (hN8 : (keccakAbsorbStep * N) % 8 = 0) :
    bytesRegion inputBase input =
      (bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
        bytesRegion (inputBase + BitVec.ofNat 64 (keccakAbsorbStep * N))
          (input.drop (keccakAbsorbStep * N))) := by
  set n := keccakAbsorbStep * N
  have hpre : (input.take n).length = n := by
    simp only [n, List.length_take, hlen]; omega
  have h8 : 8 ∣ (input.take n).length := by
    rw [hpre]; exact Nat.dvd_of_mod_eq_zero hN8
  have happ := bytesRegion_append inputBase (input.take n) (input.drop n) h8
  rw [List.take_append_drop] at happ
  simpa [hpre] using happ

/-- Flatten mid nested product at the holds level.
    `sepConj_assoc` is holds-iff (`∀ h, _ ↔ _`), not Assertion equality. -/
private theorem sep_flat_mid_holds (P A B Q : Assertion) (h : PartialState)
    (hp : (P ** (A ** B) ** Q) h) : (P ** A ** B ** Q) h := by
  have hp' : (P ** ((A ** B) ** Q)) h := by simpa using hp
  exact sepConj_mono_right
    (fun h' hh' => (sepConj_assoc (P := A) (Q := B) (R := Q) h').mp hh')
    h hp'

/-- Outer post → rem-setup pre (exact len = 136*N+rem). -/
theorem keccakOuterPost_to_remPre (h : PartialState)
    (inputBase outputBase : Word) (input : List (BitVec 8))
    (N rem : Nat) (out0 : List (BitVec 8)) (A : Assertion)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hp :
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        keccakAbsorbOuterInv Zk3 inputBase input N 0
          (keccakOuterAmb outputBase out0 A)) h) :
    ((.x8 ↦ᵣ Zk3) **
      (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
      (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
      (regOwn .x28) ** (regOwn .x30) **
      (regOwn .x5) ** (regOwn .x6) **
      bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
      bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
      keccakRemAmb outputBase out0 inputBase
        (input.take (keccakAbsorbStep * N)) A) h := by
  have hp0 : (
      (.x9 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        (.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakAbsorbOuterTemps **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion inputBase input **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 ** A) h := by
    simpa [keccakAbsorbOuterInv, keccakAbsorbOuterCore, keccakOuterAmb,
      Nat.sub_zero] using hp
  have hN8 : (keccakAbsorbStep * N) % 8 = 0 := keccakAbsorb_offset_mod8 N
  have hsplit := input_split_eq inputBase input N rem hlen hN8
  -- Split full input → take ** residual (cursor defeq base+offset)
  rw [hsplit,
    show inputBase + BitVec.ofNat 64 (keccakAbsorbStep * N) =
      keccakAbsorbCursor inputBase N from rfl,
    show input.drop (keccakAbsorbStep * N) = keccakResidual input N from rfl] at hp0
  -- hp0 is deep right-assoc ending in sponge ** ((take ** res) ** Tail).
  -- Peel 8 left atoms with mono_right, then flatten the nest under sponge.
  have hp1 : (
      (.x9 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x29 ↦ᵣ BitVec.ofNat 64 keccakAbsorbStep) **
        (.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakAbsorbOuterTemps **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 ** A) h := by
    -- under x9
    refine sepConj_mono_right ?_ h hp0
    intro h1 hp1
    -- under x29
    refine sepConj_mono_right ?_ h1 hp1
    intro h2 hp2
    -- under x8
    refine sepConj_mono_right ?_ h2 hp2
    intro h3 hp3
    -- under x20
    refine sepConj_mono_right ?_ h3 hp3
    intro h4 hp4
    -- under x0
    refine sepConj_mono_right ?_ h4 hp4
    intro h5 hp5
    -- under x10
    refine sepConj_mono_right ?_ h5 hp5
    intro h6 hp6
    -- under temps
    refine sepConj_mono_right ?_ h6 hp6
    intro h7 hp7
    -- hp7 : (sponge ** (take ** res) ** Tail) h7
    exact sep_flat_mid_holds
      (bytesRegion Zk3 (keccakAbsorbedPrefix input N))
      (bytesRegion inputBase (input.take (keccakAbsorbStep * N)))
      (bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N))
      ((.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 ** A)
      h7 hp7
  clear hp0
  -- Drop x29:regIs → regOwn under x9 (keep outerTemps as one atom)
  have hp3 : (
      (.x9 ↦ᵣ BitVec.ofNat 64 rem) **
        (regOwn .x29) **
        (.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakAbsorbOuterTemps **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 ** A) h := by
    refine sepConj_mono_right ?_ h hp1
    intro h1 hp1'
    exact sepConj_mono_left
      (regIs_implies_regOwn (r := .x29) (v := BitVec.ofNat 64 keccakAbsorbStep))
      h1 hp1'
  -- Expand temps; rearrange into rem focus + remAmb
  simp only [keccakAbsorbOuterTemps, regOwns] at hp3
  have hp4 : (
      (.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x28) ** (regOwn .x30) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
        (regOwn .x10) ** (regOwn .x29) **
        regOwns [.x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x31] **
        A) h := by
    simp only [regOwns] at hp3 ⊢
    xperm_hyp hp3
  simpa [keccakRemAmb] using hp4

/-- Rem setup framed under remAmb (fuel 2). -/
theorem keccakRemSetup_body (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat) (out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (v28 v30 : Word) :
    cpsTripleWithin 2 (B + 136) (B + 144) keccakCr
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ Zk3) **
        (.x30 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A) := by
  have hsetup := keccakRemSetup_spec keccakCr (B + 136)
    Zk3 (keccakAbsorbCursor inputBase N) v28 v30
    (mem_at 34 (.MV .x28 .x8) (B + 136)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 35 (.MV .x30 .x20) (B + 140)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
  have hsetupF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
      (regOwn .x5) ** (regOwn .x6) **
      bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
      bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
      keccakRemAmb outputBase out0 inputBase
        (input.take (keccakAbsorbStep * N)) A)
    (by
      exact pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) <|
        keccakRemAmb_pcFree _ _ _ _ _ hA)
    hsetup
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hsetupF

/-- Rem path zero under remAmb → padEntry. -/
theorem keccakRemPath_zero_body (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N : Nat) (out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 1 (B + 144) (B + 180) keccakCr
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ Zk3) **
        (.x30 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)
      (keccakPadEntry Zk3 (keccakAbsorbCursor inputBase N) 0
        (keccakAbsorbedPrefix input N) (keccakResidual input N)
        (keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)) := by
  exact keccakRemPath_zero keccakCr (B + 144) (B + 180)
    Zk3 (keccakAbsorbCursor inputBase N)
    (keccakAbsorbedPrefix input N) (keccakResidual input N)
    (keccakRemAmb outputBase out0 inputBase
      (input.take (keccakAbsorbStep * N)) A)
    (keccakRemAmb_pcFree _ _ _ _ _ hA)
    beq_to_pad
    (mem_at 36 (.BEQ .x9 .x0 (36 : BitVec 13)) (B + 144)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))

/-- Rem path nonzero under remAmb → padEntry with xor'd sponge. -/
theorem keccakRemPath_nonzero_body (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat) (out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hrem_pos : 1 ≤ rem) (hrem_le : rem ≤ 135) (hrem64 : rem < 2 ^ 64)
    (hst : (keccakAbsorbedPrefix input N).length = 200)
    (hinp : rem ≤ (keccakResidual input N).length)
    (hb8s : Zk3.toNat % 8 = 0)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      Zk3.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (Zk3 + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true) :
    cpsTripleWithin (1 + rem * 8) (B + 144) (B + 180) keccakCr
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ Zk3) **
        (.x30 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)
      (keccakPadEntry Zk3 (keccakAbsorbCursor inputBase N) rem
        (xorBytesUpTo (keccakAbsorbedPrefix input N)
          (keccakResidual input N) rem)
        (keccakResidual input N)
        (keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)) := by
  have hrem200 : rem ≤ 200 := Nat.le_trans hrem_le (by norm_num)
  have hpath := keccakRemPath_nonzero keccakCr (B + 144)
    Zk3 (keccakAbsorbCursor inputBase N)
    (keccakAbsorbedPrefix input N) (keccakResidual input N) rem
    (keccakRemAmb outputBase out0 inputBase
      (input.take (keccakAbsorbStep * N)) A)
    (keccakRemAmb_pcFree _ _ _ _ _ hA)
    hrem_pos hrem200 hrem64 hst hinp hb8s hb8i hovers hoveri hvalids hvalidi
    (mem_at 36 (.BEQ .x9 .x0 (36 : BitVec 13)) (B + 144)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 37 (.LBU .x5 .x30 0) (B + 148)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 38 (.LBU .x6 .x28 0) (B + 152)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 39 (.XOR .x5 .x5 .x6) (B + 156)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 40 (.SB .x28 .x5 0) (B + 160)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 41 (.ADDI .x28 .x28 1) (B + 164)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 42 (.ADDI .x30 .x30 1) (B + 168)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 43 (.ADDI .x9 .x9 (-1)) (B + 172)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 44 (.BNE .x9 .x0 (-28)) (B + 176)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
  -- Exit PC: ((B+144)+4)+32 = B+180
  rw [beq_rem_exit] at hpath
  exact hpath

private theorem residual_take_eq (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = keccakAbsorbStep * N + rem) :
    (keccakResidual input N).take rem = keccakResidual input N :=
  List.take_of_length_le (by rw [residual_length_eq input N rem hlen])

private theorem bodyPrePad_zero (input : List (BitVec 8)) (N : Nat) :
    keccakBodyPrePad input N 0 = keccakAbsorbedPrefix input N := by
  simp only [keccakBodyPrePad, keccakRemAbsorbed_zero, List.take_zero]

private theorem bodyPrePad_pos (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hpos : 0 < rem) :
    keccakBodyPrePad input N rem =
      xorBytesUpTo (keccakAbsorbedPrefix input N)
        (keccakResidual input N) rem := by
  have htake := residual_take_eq input N rem hlen
  simp only [keccakBodyPrePad, keccakRemAbsorbed, if_neg (Nat.ne_of_gt hpos)]
  -- BodyPrePad uses (drop).take rem; residual = drop; equal under hlen.
  rw [show (input.drop (keccakAbsorbStep * N)).take rem =
      keccakResidual input N from by simpa [keccakResidual] using htake]

/-- Unified rem path (cases rem = 0 / >0) → padEntry with prePad sponge. -/
theorem keccakRemPath_body (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat) (out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135) (hrem64 : rem < 2 ^ 64)
    (hst : (keccakAbsorbedPrefix input N).length = 200)
    (hb8s : Zk3.toNat % 8 = 0)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      Zk3.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (Zk3 + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true) :
    cpsTripleWithin (1 + rem * 8) (B + 144) (B + 180) keccakCr
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ Zk3) **
        (.x30 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)
      (keccakPadEntry Zk3 (keccakAbsorbCursor inputBase N) rem
        (keccakBodyPrePad input N rem) (keccakResidual input N)
        (keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)) := by
  by_cases hrem0 : rem = 0
  · subst hrem0
    have h0 := keccakRemPath_zero_body inputBase outputBase input N out0 A hA
    have hfuel : (1 + 0 * 8 : Nat) = 1 := by omega
    rw [hfuel]
    refine cpsTripleWithin_weaken (fun _ hp => by
        simp only [BitVec.ofNat_eq_ofNat] at hp ⊢
        exact hp)
      (fun h hq => by
        simpa [bodyPrePad_zero] using hq)
      h0
  · have hrem_pos : 1 ≤ rem := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hrem0)
    have hinp : rem ≤ (keccakResidual input N).length := by
      rw [residual_length_eq input N rem hlen]
    have hpath := keccakRemPath_nonzero_body inputBase outputBase input N rem
      out0 A hA hrem_pos hrem_le hrem64 hst hinp hb8s hb8i
      hovers hoveri hvalids hvalidi
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      simpa [bodyPrePad_pos input N rem hlen (Nat.pos_of_ne_zero hrem0)] using hq)
      hpath

/-- Free A under pad after rem: residual input + absorbedPref + leftovers. -/
def keccakPadFreeA (inputBase : Word) (input : List (BitVec 8)) (N : Nat)
    (A : Assertion) : Assertion :=
  bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
    bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
    (regOwn .x9) ** (regOwn .x20) ** A

theorem keccakPadFreeA_pcFree (inputBase : Word) (input : List (BitVec 8))
    (N : Nat) (A : Assertion) (hA : A.pcFree) :
    (keccakPadFreeA inputBase input N A).pcFree :=
  pcFree_sepConj (bytesRegion_pcFree _ _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (by pcf) hA

/-- padEntry (with remAmb) → keccakPadPre for pad/csrs/digest. -/
theorem keccakPadEntry_to_padPre (h : PartialState)
    (inputBase outputBase : Word) (input : List (BitVec 8))
    (N rem : Nat) (out0 : List (BitVec 8)) (st : List (BitVec 8))
    (A : Assertion)
    (hp :
      keccakPadEntry Zk3 (keccakAbsorbCursor inputBase N) rem st
        (keccakResidual input N)
        (keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A) h) :
    keccakPadPre Zk3 outputBase rem st out0
      (keccakPadFreeA inputBase input N A) h := by
  have hp1 :
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 rem)) **
        (.x30 ↦ᵣ (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 rem)) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 st **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
        (regOwn .x10) ** (regOwn .x29) **
        regOwns [.x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x31] **
        A) h := by
    simpa [keccakPadEntry, keccakRemAmb] using hp
  -- Front x20/x9/x30 then drop to owns.
  -- Drop x20/x9/x30 values to owns in place (mono under right-assoc peel).
  have hp2 :
      ((.x8 ↦ᵣ Zk3) **
        (regOwn .x20) **
        (regOwn .x9) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 rem)) **
        (regOwn .x30) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 st **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
        bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
        (regOwn .x10) ** (regOwn .x29) **
        regOwns [.x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x31] **
        A) h := by
    -- Front three then mono-drop then xperm back.
    have hx :
        ((.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
          ((.x9 ↦ᵣ (0 : Word)) **
            ((.x30 ↦ᵣ (keccakAbsorbCursor inputBase N +
                BitVec.ofNat 64 rem)) **
              ((.x8 ↦ᵣ Zk3) ** (.x0 ↦ᵣ (0 : Word)) **
                (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 rem)) **
                (regOwn .x5) ** (regOwn .x6) **
                bytesRegion Zk3 st **
                bytesRegion (keccakAbsorbCursor inputBase N)
                  (keccakResidual input N) **
                (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
                bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
                (regOwn .x10) ** (regOwn .x29) **
                regOwns [.x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x31] **
                A)))) h := by
      xperm_hyp hp1
    have hx' :
        ((regOwn .x20) ** (regOwn .x9) ** (regOwn .x30) **
          ((.x8 ↦ᵣ Zk3) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 rem)) **
            (regOwn .x5) ** (regOwn .x6) **
            bytesRegion Zk3 st **
            bytesRegion (keccakAbsorbCursor inputBase N)
              (keccakResidual input N) **
            (.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out0 **
            bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
            (regOwn .x10) ** (regOwn .x29) **
            regOwns [.x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x31] **
            A)) h :=
      sepConj_mono (regIs_implies_regOwn (r := .x20))
        (sepConj_mono (regIs_implies_regOwn (r := .x9))
          (sepConj_mono (regIs_implies_regOwn (r := .x30))
            (fun _ => id))) h hx
    xperm_hyp hx'
  -- Expand target fully (no emp from regOwns fold) and xperm.
  have hp3 :
      keccakPadPre Zk3 outputBase rem st out0
        (keccakPadFreeA inputBase input N A) h := by
    simp only [keccakPadPre, keccakPadCsrsAmb, keccakPadRestOwns, keccakPadFreeA,
      regOwns] at hp2 ⊢
    xperm_chunked hp2
  exact hp3

/-- Peel two trailing owns on the pre only (post may pin concrete values). -/
private theorem of_forall2_pre {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 : Reg}
    (htrip : ∀ (v1 v2 : Word),
      cpsTripleWithin n entry exit cr (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) Q) :
    cpsTripleWithin n entry exit cr (P ** regOwn r1 ** regOwn r2) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hRest, hd0, hu0, hpP0, hpRest⟩ := hpP
  obtain ⟨hR1, hR2c, hd1, hu1, hpR1, hpR2c⟩ := hpRest
  obtain ⟨v1, hv1⟩ := hpR1
  obtain ⟨v2, hv2⟩ := hpR2c
  have hPR' :
      ((P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hRest, hd0, hu0, hpP0, ⟨hR1, hR2c, hd1, hu1, hv1, hv2⟩⟩, hpR⟩
  exact htrip v1 v2 R hR s hcr hPR' hpc

/-- Rem setup under owns x28/x30. -/
theorem keccakRemSetup_owns (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat) (out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 2 (B + 136) (B + 144) keccakCr
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x28) ** (regOwn .x30) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ Zk3) **
        (.x30 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A) := by
  -- Concrete setup for all v28/v30, then peel owns.
  have hconc : ∀ v28 v30, cpsTripleWithin 2 (B + 136) (B + 144) keccakCr
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ Zk3) **
        (.x30 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A) := by
    intro v28 v30
    exact keccakRemSetup_body inputBase outputBase input N rem out0 A hA v28 v30
  -- Reassoc to focus ** x28↦ ** x30↦ (right-assoc) for of_forall2_pre
  let Focus : Assertion :=
    (.x8 ↦ᵣ Zk3) **
      (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
      (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
      (regOwn .x5) ** (regOwn .x6) **
      bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
      bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
      keccakRemAmb outputBase out0 inputBase
        (input.take (keccakAbsorbStep * N)) A
  have hconc' : ∀ v28 v30, cpsTripleWithin 2 (B + 136) (B + 144) keccakCr
      (Focus ** (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30))
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ Zk3) **
        (.x30 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A) := by
    intro v28 v30
    refine cpsTripleWithin_weaken (fun _ hp => by
        simp only [Focus] at hp ⊢; xperm_hyp hp)
      (fun _ hq => hq) (hconc v28 v30)
  have hpeel := of_forall2_pre (P := Focus) (r1 := .x28) (r2 := .x30) hconc'
  refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [Focus] at hp ⊢; xperm_hyp hp)
    (fun _ hq => hq) hpeel

/-- Rem setup + path → padEntry (fuel 2 + 1 + rem*8). -/
theorem keccakRemToPad_body (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat) (out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135) (hrem64 : rem < 2 ^ 64)
    (hst : (keccakAbsorbedPrefix input N).length = 200)
    (hb8s : Zk3.toNat % 8 = 0)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      Zk3.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (Zk3 + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true) :
    cpsTripleWithin (2 + (1 + rem * 8)) (B + 136) (B + 180) keccakCr
      ((.x8 ↦ᵣ Zk3) **
        (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x28) ** (regOwn .x30) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
        bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
        keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)
      (keccakPadEntry Zk3 (keccakAbsorbCursor inputBase N) rem
        (keccakBodyPrePad input N rem) (keccakResidual input N)
        (keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)) := by
  have c0 := keccakRemSetup_owns inputBase outputBase input N rem out0 A hA
  have c1 := keccakRemPath_body inputBase outputBase input N rem out0 A hA
    hlen hrem_le hrem64 hst hb8s hb8i hovers hoveri hvalids hvalidi
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- Pad entry → body exit via padCsrsDigest (fuel 18). Requires zeroed out.
    Exit free A is `keccakPadFreeA` (residual+pref split; recombine at top if needed). -/
theorem keccakPadEntry_to_exit (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) (hA : A.pcFree)
    (hst : (keccakBodyPrePad input N rem).length = 200)
    (hrem : rem ≤ 135)
    (halign : Zk3.toNat % 8 = 0)
    (h_over : Zk3.toNat + 200 ≤ 2 ^ 64)
    (hvalidRem : isValidByteAccess (Zk3 + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess (Zk3 + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr (Zk3 + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 18 (B + 180) (B + 252) keccakCr
      (keccakPadEntry Zk3 (keccakAbsorbCursor inputBase N) rem
        (keccakBodyPrePad input N rem) (keccakResidual input N)
        (keccakRemAmb outputBase (List.replicate 32 (0 : BitVec 8)) inputBase
          (input.take (keccakAbsorbStep * N)) A))
      (keccakBodyExitPost outputBase input N rem
        (keccakPadFreeA inputBase input N A)) := by
  have hraw := keccakPadCsrsDigestLi0_spec keccakCr (B + 180)
    Zk3 outputBase (keccakBodyPrePad input N rem) rem
    (keccakPadFreeA inputBase input N A)
    (keccakPadFreeA_pcFree _ _ _ _ hA)
    hst hrem halign h_over hvalidRem hvalid135 hvalidMem
    (mem_at 45 (.LBU .x5 .x28 0) (B + 180)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 46 (.XORI .x5 .x5 1) (B + 184)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 47 (.SB .x28 .x5 0) (B + 188)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 48 (.ADDI .x28 .x8 135) (B + 192)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 49 (.LBU .x5 .x28 0) (B + 196)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 50 (.XORI .x5 .x5 128) (B + 200)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 51 (.SB .x28 .x5 0) (B + 204)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 52 (.MV .x10 .x8) (B + 208)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 53 (.CSRS (2048 : BitVec 12) .x10) (B + 212)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 54 (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 0))) (B + 216)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 55 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 0))) (B + 220)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 56 (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 1))) (B + 224)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 57 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 1))) (B + 228)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 58 (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 2))) (B + 232)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 59 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 2))) (B + 236)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 60 (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 3))) (B + 240)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 61 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 3))) (B + 244)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 62 (.LI .x10 (0 : Word)) (B + 248)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
  rw [pad_plus_72] at hraw
  refine cpsTripleWithin_weaken
    (fun h hp =>
      keccakPadEntry_to_padPre h inputBase outputBase input N rem
        (List.replicate 32 (0 : BitVec 8)) (keccakBodyPrePad input N rem) A hp)
    (fun h hq => by
      simpa [keccakBodyExitPost, keccakBodyDigest] using hq)
    hraw

private theorem bodyPrePad_len (input : List (BitVec 8)) (N rem : Nat) :
    (keccakBodyPrePad input N rem).length = 200 := by
  simp only [keccakBodyPrePad, keccakRemAbsorbed]
  have hst := keccakAbsorbedPrefix_length input N
  by_cases h0 : rem = 0
  · simp only [h0, ↓reduceIte]; exact hst
  · simp only [if_neg h0, xorBytesUpTo_length, hst]

/-- Full body: setup → outer → rem → pad/CSRS/digest/LI0.
    Domain: `input.length = 136*N + rem`, `rem ≤ 135`, zeroed 32-byte out. -/
theorem keccakBody_spec (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (v20 v9 v18 v8 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign : Zk3.toNat % 8 = 0)
    (hover : Zk3.toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem → Zk3.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (Zk3 + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess (Zk3 + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess (Zk3 + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr (Zk3 + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (keccakBodyFuel N rem) (B + 20) (B + 252) keccakCr
      (keccakBodyEntryPre inputBase (BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
        outputBase v20 v9 v18 v8 v28 v29 os input
        (List.replicate 32 (0 : BitVec 8)) A)
      (keccakBodyExitPost outputBase input N rem
        (keccakPadFreeA inputBase input N A)) := by
  set out0 : List (BitVec 8) := List.replicate 32 (0 : BitVec 8)
  set lenW : Word := BitVec.ofNat 64 (keccakAbsorbStep * N + rem)
  have hrem_lt : rem < keccakAbsorbStep := by
    simp only [keccakAbsorbStep]; omega
  have hfit : keccakAbsorbStep * N + rem ≤ input.length := by
    simp only [hlen]; exact Nat.le_refl _
  have hstN : (keccakAbsorbedPrefix input N).length = 200 :=
    keccakAbsorbedPrefix_length _ _
  have hstPad : (keccakBodyPrePad input N rem).length = 200 := bodyPrePad_len input N rem
  have hover_le : Zk3.toNat + 200 ≤ 2 ^ 64 := Nat.le_of_lt hover
  -- 1. setup
  have cSetup := keccakSetupToOuter_framed inputBase lenW outputBase
    v20 v9 v18 v8 v28 v29 os input out0 A hA hos halign hover
  -- 2. setup → outer reshape (0 fuel)
  have cSetupOuter : cpsTripleWithin 107 (B + 20) (B + 64) keccakCr
      (keccakBodyEntryPre inputBase lenW outputBase v20 v9 v18 v8 v28 v29
        os input out0 A)
      ((.x9 ↦ᵣ lenW) ** (regOwn .x29) **
        keccakAbsorbOuterInv Zk3 inputBase input N N
          (keccakOuterAmb outputBase out0 A)) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        simpa [lenW] using
          keccakSetupPost_to_outerPre h inputBase outputBase input N rem out0 A
            (by simpa [lenW] using hq))
      cSetup
  -- 3. outer loop
  have cOuter := keccakOuterLoop_body inputBase outputBase input N rem out0 A hA
    hrem_lt hfit hNbound halign hvalidMem
  -- 4. outer post → rem pre (0 fuel) + rem→pad
  have cRem := keccakRemToPad_body inputBase outputBase input N rem out0 A hA
    hlen hrem_le hrem64 hstN halign hb8i hovers hoveri hvalids hvalidi
  have cOuterRem : cpsTripleWithin
      ((N * (keccakAbsorbOuterBodyFuel + 2) + 2) + (2 + (1 + rem * 8)))
      (B + 64) (B + 180) keccakCr
      ((.x9 ↦ᵣ lenW) ** (regOwn .x29) **
        keccakAbsorbOuterInv Zk3 inputBase input N N
          (keccakOuterAmb outputBase out0 A))
      (keccakPadEntry Zk3 (keccakAbsorbCursor inputBase N) rem
        (keccakBodyPrePad input N rem) (keccakResidual input N)
        (keccakRemAmb outputBase out0 inputBase
          (input.take (keccakAbsorbStep * N)) A)) := by
    have cOuter' : cpsTripleWithin (N * (keccakAbsorbOuterBodyFuel + 2) + 2)
        (B + 64) (B + 136) keccakCr
        ((.x9 ↦ᵣ lenW) ** (regOwn .x29) **
          keccakAbsorbOuterInv Zk3 inputBase input N N
            (keccakOuterAmb outputBase out0 A))
        ((.x8 ↦ᵣ Zk3) **
          (.x20 ↦ᵣ keccakAbsorbCursor inputBase N) **
          (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
          (regOwn .x28) ** (regOwn .x30) **
          (regOwn .x5) ** (regOwn .x6) **
          bytesRegion Zk3 (keccakAbsorbedPrefix input N) **
          bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
          keccakRemAmb outputBase out0 inputBase
            (input.take (keccakAbsorbStep * N)) A) :=
      cpsTripleWithin_weaken (fun _ hp => by simpa [lenW] using hp)
        (fun h hq =>
          keccakOuterPost_to_remPre h inputBase outputBase input N rem out0 A hlen
            (by simpa [lenW] using hq))
        cOuter
    exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      cOuter' cRem
  -- 5. setup+outer+rem
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    cSetupOuter cOuterRem
  -- 6. pad→exit
  have cPad := keccakPadEntry_to_exit inputBase outputBase input N rem A hA
    hstPad hrem_le halign hover_le hvalidRem hvalid135 hvalidMem
  -- 7. full chain
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c012 cPad
  -- fuel
  have hfuel :
      107 + ((N * (keccakAbsorbOuterBodyFuel + 2) + 2) + (2 + (1 + rem * 8))) + 18 =
        keccakBodyFuel N rem := by
    simp only [keccakBodyFuel]; omega
  rw [← hfuel]
  exact cAll

end EvmAsm.Codegen.Proofs












