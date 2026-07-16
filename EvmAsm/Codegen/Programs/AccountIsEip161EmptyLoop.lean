/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyLoop

  The three byte-scan loop lemmas for the whole-program K137 contract
  `account_is_eip161_empty_spec_within` (`AccountFields.lean`).

  Each loop is proven by `Nat` induction on the `x6` byte-countdown,
  threading the "all-processed-so-far <property>" invariant, following the
  `hesrCopyLoop` LBU-loop template.  This module hosts the nonce
  accumulate-scan loop; the balance all-zero scan and the code-hash
  byte-compare scan follow in sibling modules.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptySpec
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-! ## Address / counter arithmetic helpers -/

/-- Word decrement of a successor counter (the `x6` countdown). -/
private theorem aie_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem aie_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- Pointer advance by 1 byte. -/
private theorem aie_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-- `k`-th instruction membership into the accessor body `aieCode`
    (`ofProg_mem_at` resolves the `getElem` / bound proofs internally). -/
local macro "aieMem" k:term ", " A:term ", " ins:term : term =>
  `(CodeReq.ofProg_mem_at AB $A accountIsEip161Empty_prog $k $ins (by bv_omega)
      (by rw [aie_prog_length]; omega) rfl (by rw [aie_prog_length]; norm_num))

/-! ## Nonce accumulate-scan loop ([28]-[34], `AB+112 → AB+140`)

    The big-endian accumulate loop: `x6` = byte countdown, `x7` = big-endian
    accumulator, `x28` = advancing content pointer.  The exit test is at the
    top (`BEQ x6, x0, +28`); each taken iteration shifts the accumulator left
    a byte and ORs in the next content byte (`beAccFrom`). -/

private theorem aie_x7_or_step (bytes : List (BitVec 8)) (o0 i : Nat)
    (hi : o0 + i < bytes.length) :
    ((beAccFrom bytes o0 i) <<< (8 : BitVec 6).toNat) |||
      ((bytes[o0 + i]'hi).zeroExtend 64) = beAccFrom bytes o0 (i + 1) := by
  rw [beAccFrom_succ]
  have hgetd : bytes.getD (o0 + i) 0 = bytes[o0 + i]'hi := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [hgetd, show (8 : BitVec 6).toNat = 8 from by decide]

/-- **One nonce-loop iteration** ([29]-[34], `AB+116 → AB+112`): shift the
    accumulator, OR in `bytes[o0+i]`, advance the pointer and decrement the
    countdown. -/
private theorem aieNonceBody (accBase : Word) (bytes : List (BitVec 8))
    (o0 i k : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hlt : o0 + i < bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 6 (AB + 116) (AB + 112) aieCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 (i + 1)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  -- [29] SLLI x7, x7, 8
  have h29 := slli_spec_gen_same_within .x7 (beAccFrom bytes o0 i) (8 : BitVec 6)
    (AB + 116) (by decide)
  rw [show (AB + 116 : Word) + 4 = AB + 120 from by bv_omega] at h29
  have e29 := cpsTripleWithin_extend_code
    (aieMem 29, (AB + 116), (.SLLI .x7 .x7 (8 : BitVec 6))) h29
  have f29 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e29
  -- [30] LBU x29 ← bytes[o0+i]
  have h30 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 120) bytes (o0 + i)
    (by decide) halign hlt (by omega) (hvalid (o0 + i) hlt)
  rw [show (AB + 120 : Word) + 4 = AB + 124 from by bv_omega] at h30
  have e30 := cpsTripleWithin_extend_code
    (aieMem 30, (AB + 120), (.LBU .x29 .x28 (0 : BitVec 12))) h30
  have f30 := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ ((beAccFrom bytes o0 i) <<< (8 : BitVec 6).toNat)) **
     ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFreeR) e30
  -- [31] OR x7, x7, x29
  have h31 := or_spec_gen_rd_eq_rs1_within .x7 .x29
    ((beAccFrom bytes o0 i) <<< (8 : BitVec 6).toNat) ((bytes[o0 + i]'hlt).zeroExtend 64)
    (AB + 124) (by decide)
  rw [aie_x7_or_step bytes o0 i hlt,
      show (AB + 124 : Word) + 4 = AB + 128 from by bv_omega] at h31
  have e31 := cpsTripleWithin_extend_code
    (aieMem 31, (AB + 124), (.OR .x7 .x7 .x29)) h31
  have f31 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e31
  -- [32] ADDI x28, x28, 1
  have h32 := addi_spec_gen_same_within .x28 (accBase + BitVec.ofNat 64 (o0 + i))
    (1 : BitVec 12) (AB + 128) (by decide)
  rw [aie_advance accBase (o0 + i),
      show o0 + i + 1 = o0 + (i + 1) from by omega,
      show (AB + 128 : Word) + 4 = AB + 132 from by bv_omega] at h32
  have e32 := cpsTripleWithin_extend_code
    (aieMem 32, (AB + 128), (.ADDI .x28 .x28 (1 : BitVec 12))) h32
  have f32 := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 (i + 1)) **
     ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e32
  -- [33] ADDI x6, x6, -1
  have h33 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12)
    (AB + 132) (by decide)
  rw [aie_succ_dec k, show (AB + 132 : Word) + 4 = AB + 136 from by bv_omega] at h33
  have e33 := cpsTripleWithin_extend_code
    (aieMem 33, (AB + 132), (.ADDI .x6 .x6 (-1 : BitVec 12))) h33
  have f33 := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 (i + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e33
  -- [34] JAL x0, -24  → AB+112
  have h34 := jal_x0_spec_gen_within (-24 : BitVec 21) (AB + 136)
  rw [show AB + 136 + signExtend21 (-24 : BitVec 21) = AB + 112 from by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega] at h34
  have e34 := cpsTripleWithin_extend_code
    (aieMem 34, (AB + 136), (.JAL .x0 (-24 : BitVec 21))) h34
  have f34 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
     ((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 (i + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e34
  rw [sepConj_emp_left'] at f34
  -- compose the six body steps
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f29 f30
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f31
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f32
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f33
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s4 f34
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s5)

/-- **The nonce accumulate-scan loop closure** ([28]-[34], `AB+112 → AB+140`):
    by induction on the byte countdown `n`, process the remaining `n` content
    bytes into the big-endian accumulator and exit through the top `BEQ` with
    `x6 = 0` and `x7 = beAccFrom bytes o0 (i+n)`. -/
theorem aieNonceLoop (accBase : Word) (bytes : List (BitVec 8))
    (o0 n i : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hbound : o0 + i + n ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (7 * n + 1) (AB + 112) (AB + 140) aieCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 (i + n)) **
       regOwn .x28 ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have hbne : (AB + 112 : Word) + signExtend13 (28 : BitVec 13) = AB + 140 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  induction n generalizing i v29 with
  | zero =>
    -- x6 = 0 : BEQ taken → AB+140
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (AB + 112)
    rw [hbne] at hbeq
    have hbeqe := cpsBranchWithin_extend_code
      (aieMem 28, (AB + 112), (.BEQ .x6 .x0 (28 : BitVec 13))) hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          simp only [show i + 0 = i from by omega]
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x6 : Reg) ↦ᵣ (0 : Word)) **
              ((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 i) **
              ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
              ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion accBase bytes) sState := by xperm_chunked hq
          have hq3 := sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x28))) _ hq2
          have hq4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x29)))) _ hq3
          xperm_chunked hq4) htf)
  | succ k ih =>
    -- x6 = k+1 ≠ 0 : BEQ not-taken → AB+116, then body, then IH
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (AB + 112)
    rw [hbne] at hbeq
    have hbeqe := cpsBranchWithin_extend_code
      (aieMem 28, (AB + 112), (.BEQ .x6 .x0 (28 : BitVec 13))) hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact aie_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ beAccFrom bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) hnt
    have hbody := aieNonceBody accBase bytes o0 i k v29 halign (by omega) hover hvalid
    have hih := ih (i + 1) ((bytes[o0 + i]'(by omega)).zeroExtend 64) (by omega)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hntf hbody
    have sfull := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) s1 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show i + 1 + k = i + (k + 1) from by omega] at hq
          xperm_chunked hq) sfull)

#print axioms aieNonceLoop

end EvmAsm.Codegen.AccountIsEip161EmptySpec
