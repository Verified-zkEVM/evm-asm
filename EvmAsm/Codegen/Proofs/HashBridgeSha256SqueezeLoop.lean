/-
Copyright (c) 2025 zkSecurity. All rights reserved.
Released under Apache 2.0 license.
Authors: EvmAsm contributors

# SHA-256 BE squeeze loop

Geometry:
- BEQ @ B+416 (idx 104); body XORI..ADDI @ B+420..440; JAL -32 @ B+444 → B+412 (LI x6)
- LI x6,32 @ B+412 restores inv at B+416
- Full step fuel 9: BEQ + 6 body + JAL + LI
- Exit BEQ taken → B+448
-/
import EvmAsm.Codegen.Proofs.HashBridgeSha256Squeeze
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.MemRegion
import Mathlib.Data.Nat.Bitwise

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]; decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins
    sha256ProgL_bound a i h

local macro "pcf" : tactic =>
  `(tactic| repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _
    | assumption)

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_3 : signExtend12 (3 : BitVec 12) = (3 : Word) := by decide

private theorem ofNat_succ_sq (k : Nat) :
    BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + (1 : Word) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  exact Nat.add_mod k 1 (2 ^ 64)

private theorem word_ne_32 (done : Nat) (hd : done < 32) :
    BitVec.ofNat 64 done ≠ (32 : Word) := by
  intro heq
  have h1 : done < 2 ^ 64 := Nat.lt_trans hd (by decide)
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt h1] at this
  have h32 : (32 : Word).toNat = 32 := by decide
  rw [h32] at this
  omega

/-- Temps after full body (before peel to owns). -/
def squeezeTemps (stateBase outBase : Word) (st : List (BitVec 8))
    (done : Nat) (hst : done ^^^ 3 < st.length) : Assertion :=
  (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
    (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
    (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
    (.x30 ↦ᵣ (outBase + BitVec.ofNat 64 done))

/-- Core regs + regions (no temps). -/
def squeezeCore (stateBase outBase : Word) (st out : List (BitVec 8))
    (done : Nat) : Assertion :=
  (.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
    (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
    bytesRegion stateBase st ** bytesRegion outBase out

/-- One full iteration. Fuel 9. B+416 → B+416.
    Path: BEQ ntaken, XORI, ADD, LBU, ADD, SB, ADDI, JAL→B+412, LI x6. -/
theorem sha256Squeeze_step
    (stateBase outBase : Word) (st out0 : List (BitVec 8))
    (done : Nat)
    (hst : done ^^^ 3 < st.length) (hout : done < out0.length)
    (hd : done < 32)
    (hsrcAlign : stateBase.toNat % 8 = 0)
    (hdstAlign : outBase.toNat % 8 = 0)
    (hsrcOver : stateBase.toNat + (done ^^^ 3) < 2 ^ 64)
    (hdstOver : outBase.toNat + done < 2 ^ 64)
    (hvalidS : isValidByteAccess (stateBase + BitVec.ofNat 64 (done ^^^ 3)) = true)
    (hvalidD : isValidByteAccess (outBase + BitVec.ofNat 64 done) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 9 (B + 416) (B + 416) sha256Cr
      (sha256SqueezeInv stateBase outBase st out0 done F)
      (sha256SqueezeInv stateBase outBase st
        (out0.set done (st[done ^^^ 3]'hst)) (done + 1) F) := by
  have hne := word_ne_32 done hd
  have hxor := ofNat_xor3 done hd
  -- 1. BEQ ntaken
  have hbr := beq_spec_gen_within .x5 .x6 (32 : BitVec 13)
    (BitVec.ofNat 64 done) (32 : Word) (B + 416)
  have hbrC := cpsBranchWithin_extend_code
    (mem_at 104 (.BEQ .x5 .x6 (32 : BitVec 13)) (B + 416) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  rw [show (B + 416 : Word) + 4 = B + 420 from by decide] at hnt
  have c_beq := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
      bytesRegion stateBase st ** bytesRegion outBase out0 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F)
    (by first | exact hF | pcf) hnt
  -- 2. XORI (peel own x7 rightmost)
  have hx : ∀ v7,
      cpsTripleWithin 1 (B + 420) (B + 424) sha256Cr
        (((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F) **
         (.x7 ↦ᵣ v7))
        ((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F) := by
    intro v7
    have hx0 := xori_spec_gen_within .x7 .x5 v7 (BitVec.ofNat 64 done)
      (3 : BitVec 12) (B + 420) (by decide)
    have hxE := cpsTripleWithin_extend_code
      (mem_at 105 (.XORI .x7 .x5 (3 : BitVec 12)) (B + 420) (by decide)
        (by rw [sha256ProgL_len]; decide) (by rfl)) hx0
    rw [show (B + 420 : Word) + 4 = B + 424 from by decide, se12_3, hxor] at hxE
    have hxF := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
        bytesRegion stateBase st ** bytesRegion outBase out0 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F)
      (by first | exact hF | pcf) hxE
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hxF
  have c_xori := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7) hx
  -- 3. ADD x28 (peel own x28 rightmost)
  have ha28 : ∀ v28,
      cpsTripleWithin 1 (B + 424) (B + 428) sha256Cr
        (((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          regOwn .x29 ** regOwn .x30 ** F) **
         (.x28 ↦ᵣ v28))
        ((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
          regOwn .x29 ** regOwn .x30 ** F) := by
    intro v28
    have ha0 := add_spec_gen_within .x28 .x8 .x7 stateBase
      (BitVec.ofNat 64 (done ^^^ 3)) v28 (B + 424) (by decide)
    have haE := cpsTripleWithin_extend_code
      (mem_at 106 (.ADD .x28 .x8 .x7) (B + 424) (by decide)
        (by rw [sha256ProgL_len]; decide) (by rfl)) ha0
    rw [show (B + 424 : Word) + 4 = B + 428 from by decide] at haE
    have haF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
        (.x19 ↦ᵣ outBase) ** bytesRegion stateBase st **
        bytesRegion outBase out0 **
        regOwn .x29 ** regOwn .x30 ** F)
      (by first | exact hF | pcf) haE
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) haF
  have c_add28 := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28) ha28
  -- 4. LBU x29 (peel own x29)
  have hl29 : ∀ v29,
      cpsTripleWithin 1 (B + 428) (B + 432) sha256Cr
        (((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
          regOwn .x30 ** F) **
         (.x29 ↦ᵣ v29))
        ((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
          (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
          regOwn .x30 ** F) := by
    intro v29
    have hl0 := bytesRegion_lbu_within .x29 .x28 stateBase v29 (B + 428)
      st (done ^^^ 3) (by decide) hsrcAlign hst hsrcOver hvalidS
    have hlE := cpsTripleWithin_extend_code
      (mem_at 107 (.LBU .x29 .x28 0) (B + 428) (by decide)
        (by rw [sha256ProgL_len]; decide) (by rfl)) hl0
    rw [show (B + 428 : Word) + 4 = B + 432 from by decide] at hlE
    have hlF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) ** (.x8 ↦ᵣ stateBase) **
        (.x19 ↦ᵣ outBase) ** bytesRegion outBase out0 **
        regOwn .x30 ** F)
      (by first | exact hF | pcf) hlE
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hlF
  have c_lbu := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29) hl29
  -- 5. ADD x30 (peel own x30)
  have ha30 : ∀ v30,
      cpsTripleWithin 1 (B + 432) (B + 436) sha256Cr
        (((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
          (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) ** F) **
         (.x30 ↦ᵣ v30))
        ((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st ** bytesRegion outBase out0 **
          (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
          (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
          (.x30 ↦ᵣ (outBase + BitVec.ofNat 64 done)) ** F) := by
    intro v30
    have ha0 := add_spec_gen_within .x30 .x19 .x5 outBase
      (BitVec.ofNat 64 done) v30 (B + 432) (by decide)
    have haE := cpsTripleWithin_extend_code
      (mem_at 108 (.ADD .x30 .x19 .x5) (B + 432) (by decide)
        (by rw [sha256ProgL_len]; decide) (by rfl)) ha0
    rw [show (B + 432 : Word) + 4 = B + 436 from by decide] at haE
    have haF := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
        (.x8 ↦ᵣ stateBase) **
        (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
        (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
        bytesRegion stateBase st ** bytesRegion outBase out0 ** F)
      (by first | exact hF | pcf) haE
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) haF
  have c_add30 := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x30) ha30
  -- 6. SB
  have hsb0 := bytesRegion_sb_within .x30 .x29 outBase
    ((st[done ^^^ 3]'hst).zeroExtend 64) (B + 436) out0 done
    hdstAlign hout hdstOver hvalidD
  have hsb := cpsTripleWithin_extend_code
    (mem_at 109 (.SB .x30 .x29 0) (B + 436) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hsb0
  rw [show (B + 436 : Word) + 4 = B + 440 from by decide] at hsb
  have hbyte :
      ((st[done ^^^ 3]'hst).zeroExtend 64).truncate 8 = st[done ^^^ 3]'hst :=
    truncate_zeroExtend_byte _
  simp only [hbyte] at hsb
  have c_sb := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
      (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) ** (.x8 ↦ᵣ stateBase) **
      (.x19 ↦ᵣ outBase) **
      (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
      bytesRegion stateBase st ** F)
    (by first | exact hF | pcf) hsb
  -- 7. ADDI x5
  have ha50 := addi_spec_gen_same_within .x5
    (BitVec.ofNat 64 done) (1 : BitVec 12) (B + 440) (by decide)
  have ha5 := cpsTripleWithin_extend_code
    (mem_at 110 (.ADDI .x5 .x5 1) (B + 440) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) ha50
  rw [show (B + 440 : Word) + 4 = B + 444 from by decide, se12_1] at ha5
  -- ofNat done + 1 = ofNat (done+1) via ofNat_succ_sq.symm
  have hsucc : BitVec.ofNat 64 done + (1 : Word) = BitVec.ofNat 64 (done + 1) :=
    (ofNat_succ_sq done).symm
  simp only [hsucc] at ha5
  have c_addi := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
      (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
      (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
      (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
      (.x30 ↦ᵣ (outBase + BitVec.ofNat 64 done)) **
      bytesRegion stateBase st **
      bytesRegion outBase (out0.set done (st[done ^^^ 3]'hst)) ** F)
    (by first | exact hF | pcf) ha5
  -- 8. JAL → B+412
  have hjal0 := jal_x0_spec_gen_within (-32 : BitVec 21) (B + 444)
  have hjal := cpsTripleWithin_extend_code
    (mem_at 111 (.JAL .x0 (-32 : BitVec 21)) (B + 444) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hjal0
  rw [show (B + 444 : Word) + signExtend21 (-32 : BitVec 21) = B + 412 from by decide]
    at hjal
  have c_jal := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ BitVec.ofNat 64 (done + 1)) ** (.x6 ↦ᵣ (32 : Word)) **
      (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) ** (.x8 ↦ᵣ stateBase) **
      (.x19 ↦ᵣ outBase) **
      (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
      (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
      (.x30 ↦ᵣ (outBase + BitVec.ofNat 64 done)) **
      bytesRegion stateBase st **
      bytesRegion outBase (out0.set done (st[done ^^^ 3]'hst)) ** F)
    (by first | exact hF | pcf) hjal
  have c_jal' := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) c_jal
  -- 9. LI x6,32 @ B+412 → B+416 (idempotent restore)
  have hli60 := li_spec_gen_within .x6 (32 : Word) (32 : Word) (B + 412) (by decide)
  have hli6 := cpsTripleWithin_extend_code
    (mem_at 103 (.LI .x6 (32 : Word)) (B + 412) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hli60
  rw [show (B + 412 : Word) + 4 = B + 416 from by decide] at hli6
  have c_li6 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ BitVec.ofNat 64 (done + 1)) **
      (.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) ** (.x8 ↦ᵣ stateBase) **
      (.x19 ↦ᵣ outBase) **
      (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
      (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
      (.x30 ↦ᵣ (outBase + BitVec.ofNat 64 done)) **
      bytesRegion stateBase st **
      bytesRegion outBase (out0.set done (st[done ^^^ 3]'hst)) ** F)
    (by first | exact hF | pcf) hli6
  -- Compose with xperm bridges for of_forall association (own rightmost)
  have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c_beq c_xori
  have s02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    s01 c_add28
  have s03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    s02 c_lbu
  have s04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    s03 c_add30
  have s05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    s04 c_sb
  have s06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    s05 c_addi
  have s07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    s06 c_jal'
  have s08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    s07 c_li6
  refine cpsTripleWithin_weaken ?_ ?_ s08
  · intro _ hp
    simp only [sha256SqueezeInv] at hp ⊢; xperm_chunked hp
  · intro h hq
    simp only [sha256SqueezeInv]
    have hq1 :
        ((.x7 ↦ᵣ BitVec.ofNat 64 (done ^^^ 3)) **
          (.x28 ↦ᵣ (stateBase + BitVec.ofNat 64 (done ^^^ 3))) **
          (.x29 ↦ᵣ ((st[done ^^^ 3]'hst).zeroExtend 64)) **
          (.x30 ↦ᵣ (outBase + BitVec.ofNat 64 done)) **
          (.x5 ↦ᵣ BitVec.ofNat 64 (done + 1)) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st **
          bytesRegion outBase (out0.set done (st[done ^^^ 3]'hst)) ** F) h := by
      xperm_chunked hq
    have hq2 :
        (regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          (.x5 ↦ᵣ BitVec.ofNat 64 (done + 1)) ** (.x6 ↦ᵣ (32 : Word)) **
          (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
          bytesRegion stateBase st **
          bytesRegion outBase (out0.set done (st[done ^^^ 3]'hst)) ** F) h :=
      (sepConj_mono (regIs_implies_regOwn (r := .x7))
        (sepConj_mono (regIs_implies_regOwn (r := .x28))
          (sepConj_mono (regIs_implies_regOwn (r := .x29))
            (sepConj_mono (regIs_implies_regOwn (r := .x30))
              (fun _ hy => hy))))) h hq1
    xperm_chunked hq2

/-- Progressive squeeze buffer. -/
def sha256SqueezePrefix (st out0 : List (BitVec 8)) (done : Nat) : List (BitVec 8) :=
  (List.range 32).map fun i =>
    if i < done then st.getD (i ^^^ 3) 0 else out0.getD i 0

theorem sha256SqueezePrefix_length (st out0 : List (BitVec 8)) (done : Nat) :
    (sha256SqueezePrefix st out0 done).length = 32 := by
  simp [sha256SqueezePrefix]

theorem sha256SqueezePrefix_zero (st out0 : List (BitVec 8))
    (hout : out0.length = 32) :
    sha256SqueezePrefix st out0 0 = out0 := by
  apply List.ext_getElem
  · simp [sha256SqueezePrefix, hout]
  · intro i _ hi'
    simp only [sha256SqueezePrefix, List.getElem_map, List.getElem_range]
    have : ¬ i < 0 := Nat.not_lt_zero _
    simp [this, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : i < out0.length)]

theorem sha256SqueezePrefix_full (st out0 : List (BitVec 8))
    (hst : st.length = 32) :
    sha256SqueezePrefix st out0 32 = sha256SqueezeBE st := by
  apply List.ext_getElem
  · simp [sha256SqueezePrefix, sha256SqueezeBE]
  · intro i hi _
    have : i < 32 := by simpa [sha256SqueezePrefix] using hi
    simp only [sha256SqueezePrefix, sha256SqueezeBE, List.getElem_map, List.getElem_range]
    have hiSt : i < st.length := by omega
    simp [this, List.getD_eq_getElem?_getD]

theorem sha256SqueezePrefix_succ (st out0 : List (BitVec 8)) (d : Nat)
    (hst : st.length = 32) (_hout : out0.length = 32) (hd : d < 32) :
    (sha256SqueezePrefix st out0 d).set d
        (st[d ^^^ 3]'(by have := xor3_lt_32 d hd; omega)) =
      sha256SqueezePrefix st out0 (d + 1) := by
  have hlenP : (sha256SqueezePrefix st out0 d).length = 32 :=
    sha256SqueezePrefix_length st out0 d
  have hlenL : ((sha256SqueezePrefix st out0 d).set d
      (st[d ^^^ 3]'(by have := xor3_lt_32 d hd; omega))).length = 32 := by
    simp [List.length_set, hlenP]
  have hlenR : (sha256SqueezePrefix st out0 (d + 1)).length = 32 :=
    sha256SqueezePrefix_length st out0 (d + 1)
  refine List.ext_getElem (hlenL.trans hlenR.symm) fun i hi _hi' => ?_
  have hi32 : i < 32 := by omega
  have hiP : i < (sha256SqueezePrefix st out0 d).length := by
    rw [hlenP]; exact hi32
  have hR :
      (sha256SqueezePrefix st out0 (d + 1))[i]'(by omega) =
        if i < d + 1 then st.getD (i ^^^ 3) 0 else out0.getD i 0 := by
    simp [sha256SqueezePrefix]
  have hD :
      (sha256SqueezePrefix st out0 d)[i]'(hiP) =
        if i < d then st.getD (i ^^^ 3) 0 else out0.getD i 0 := by
    simp [sha256SqueezePrefix]
  by_cases heq : i = d
  · -- set at d
    have hL :
        ((sha256SqueezePrefix st out0 d).set d
            (st[d ^^^ 3]'(by have := xor3_lt_32 d hd; omega)))[i]'(by omega) =
          st[d ^^^ 3]'(by have := xor3_lt_32 d hd; omega) := by
      have hcast :
          ((sha256SqueezePrefix st out0 d).set d
              (st[d ^^^ 3]'(by have := xor3_lt_32 d hd; omega)))[i]'(by omega) =
            ((sha256SqueezePrefix st out0 d).set d
                (st[d ^^^ 3]'(by have := xor3_lt_32 d hd; omega)))[d]'(by
              simpa [hlenL, heq] using hi) := by
        simp [heq]
      refine hcast.trans ?_
      exact List.getElem_set_self (by simpa [hlenL] using (show d < 32 from hd))
    have hR' :
        (sha256SqueezePrefix st out0 (d + 1))[i]'(by omega) =
          st.getD (d ^^^ 3) 0 := by
      rw [hR, heq]; simp [Nat.lt_succ_self d]
    rw [hL, hR']
    simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem
        (by have := xor3_lt_32 d hd; omega : d ^^^ 3 < st.length)]
  · -- set leaves i alone
    have hne : d ≠ i := Ne.symm heq
    have hL :
        ((sha256SqueezePrefix st out0 d).set d
            (st[d ^^^ 3]'(by have := xor3_lt_32 d hd; omega)))[i]'(by omega) =
          (sha256SqueezePrefix st out0 d)[i]'(hiP) :=
      List.getElem_set_ne hne _
    rw [hL, hR, hD]
    by_cases hlt : i < d
    · have : i < d + 1 := Nat.lt_succ_of_lt hlt
      simp [hlt, this]
    · have : ¬ i < d + 1 := by omega
      simp [hlt, this]

/-- Loop from done with k remaining. Fuel k*9+1. -/
theorem sha256Squeeze_loop_from
    (stateBase outBase : Word) (st out0 : List (BitVec 8))
    (k done : Nat)
    (hst : st.length = 32) (hout : out0.length = 32)
    (hsum : done + k = 32)
    (hsrcAlign : stateBase.toNat % 8 = 0)
    (hdstAlign : outBase.toNat % 8 = 0)
    (hsrcOver : stateBase.toNat + 32 ≤ 2 ^ 64)
    (hdstOver : outBase.toNat + 32 ≤ 2 ^ 64)
    (hvalidS : ∀ i < 32, isValidByteAccess
      (stateBase + BitVec.ofNat 64 (i ^^^ 3)) = true)
    (hvalidD : ∀ i < 32, isValidByteAccess
      (outBase + BitVec.ofNat 64 i) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (k * 9 + 1) (B + 416) (B + 448) sha256Cr
      (sha256SqueezeInv stateBase outBase st
        (sha256SqueezePrefix st out0 done) done F)
      (sha256SqueezeInv stateBase outBase st
        (sha256SqueezePrefix st out0 32) 32 F) := by
  induction k generalizing done with
  | zero =>
    have hdone : done = 32 := by omega
    subst hdone
    simpa using sha256Squeeze_exit stateBase outBase st
      (sha256SqueezePrefix st out0 32) F hF
  | succ k ih =>
    have hd : done < 32 := by omega
    have hpref_len : (sha256SqueezePrefix st out0 done).length = 32 :=
      sha256SqueezePrefix_length st out0 done
    have hxi := xor3_lt_32 done hd
    have hstep := sha256Squeeze_step stateBase outBase st
      (sha256SqueezePrefix st out0 done) done
      (by omega) (by rw [hpref_len]; exact hd) hd
      hsrcAlign hdstAlign
      (by have : done ^^^ 3 < 32 := hxi; omega)
      (by omega)
      (hvalidS done (by omega)) (hvalidD done (by omega)) F hF
    have hset := sha256SqueezePrefix_succ st out0 done hst hout hd
    have hstep' : cpsTripleWithin 9 (B + 416) (B + 416) sha256Cr
        (sha256SqueezeInv stateBase outBase st
          (sha256SqueezePrefix st out0 done) done F)
        (sha256SqueezeInv stateBase outBase st
          (sha256SqueezePrefix st out0 (done + 1)) (done + 1) F) := by
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hstep
      simpa [hset] using hq
    have hrest := ih (done + 1) (by omega)
    have hseq := cpsTripleWithin_seq_same_cr hstep' hrest
    have hfuel : (k + 1) * 9 + 1 = 9 + (k * 9 + 1) := by omega
    rw [hfuel]
    exact hseq

/-- Entry done=0. Fuel 32*9+1=289. Post = sha256SqueezeBE st. -/
theorem sha256Squeeze_loop
    (stateBase outBase : Word) (st out0 : List (BitVec 8))
    (hst : st.length = 32) (hout : out0.length = 32)
    (hsrcAlign : stateBase.toNat % 8 = 0)
    (hdstAlign : outBase.toNat % 8 = 0)
    (hsrcOver : stateBase.toNat + 32 ≤ 2 ^ 64)
    (hdstOver : outBase.toNat + 32 ≤ 2 ^ 64)
    (hvalidS : ∀ i < 32, isValidByteAccess
      (stateBase + BitVec.ofNat 64 (i ^^^ 3)) = true)
    (hvalidD : ∀ i < 32, isValidByteAccess
      (outBase + BitVec.ofNat 64 i) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 289 (B + 416) (B + 448) sha256Cr
      (sha256SqueezeInv stateBase outBase st out0 0 F)
      (sha256SqueezeInv stateBase outBase st (sha256SqueezeBE st) 32 F) := by
  have hpre : sha256SqueezePrefix st out0 0 = out0 :=
    sha256SqueezePrefix_zero st out0 hout
  have h := sha256Squeeze_loop_from stateBase outBase st out0 32 0
    hst hout (by decide) hsrcAlign hdstAlign hsrcOver hdstOver
    hvalidS hvalidD F hF
  refine cpsTripleWithin_weaken ?_ ?_ h
  · intro _ hp; simpa [hpre] using hp
  · intro _ hq; simpa [sha256SqueezePrefix_full st out0 hst] using hq

end EvmAsm.Codegen.Proofs
