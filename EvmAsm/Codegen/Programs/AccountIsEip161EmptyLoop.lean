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

/-! ## Balance all-zero scan loop ([54]-[59], `AB+216 → {AB+240, AB+384}`)

    `x6` = byte countdown, `x28` = advancing content pointer, `x29` = per-byte
    temp.  The top `BEQ x6, x0, +24` exits (all bytes zero) to `AB+240`; the
    inner `BNE x29, x0, +160` breaks to `AB+384` on the first nonzero byte.
    Proven as two single-exit triples conditioned on the content bytes. -/

/-- General decrement of a positive counter `< 2^64`. -/
private theorem aie_dec (n : Nat) (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 (n - 1) := by
  have h264 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  rw [h264] at hlt
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (show n - 1 < 18446744073709551616 from by omega)]
  omega

/-- A positive counter `< 2^64` is nonzero as a word. -/
private theorem aie_ofNat_ne_zero (n : Nat) (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n : Word) ≠ 0 := by
  intro hc
  have ht : (BitVec.ofNat 64 n : Word).toNat = 0 := by rw [hc]; rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht; omega

/-- **The balance/code-hash loop tail** ([57]-[59], `AB+228 → AB+216`):
    advance the content pointer, decrement the countdown, jump back. -/
private theorem aieBalTail (accBase : Word) (o1 i : Nat) (x6v : Word) :
    cpsTripleWithin 3 (AB + 228) (AB + 216) aieCode
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) ** ((.x6 : Reg) ↦ᵣ x6v))
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + (i + 1)))) **
       ((.x6 : Reg) ↦ᵣ (x6v + signExtend12 (-1 : BitVec 12)))) := by
  -- [57] ADDI x28, x28, 1
  have h57 := addi_spec_gen_same_within .x28 (accBase + BitVec.ofNat 64 (o1 + i))
    (1 : BitVec 12) (AB + 228) (by decide)
  rw [aie_advance accBase (o1 + i), show o1 + i + 1 = o1 + (i + 1) from by omega,
      show (AB + 228 : Word) + 4 = AB + 232 from by bv_omega] at h57
  have e57 := cpsTripleWithin_extend_code
    (aieMem 57, (AB + 228), (.ADDI .x28 .x28 (1 : BitVec 12))) h57
  have f57 := cpsTripleWithin_frameR ((.x6 : Reg) ↦ᵣ x6v) (by pcFreeR) e57
  -- [58] ADDI x6, x6, -1
  have h58 := addi_spec_gen_same_within .x6 x6v (-1 : BitVec 12) (AB + 232) (by decide)
  rw [show (AB + 232 : Word) + 4 = AB + 236 from by bv_omega] at h58
  have e58 := cpsTripleWithin_extend_code
    (aieMem 58, (AB + 232), (.ADDI .x6 .x6 (-1 : BitVec 12))) h58
  have f58 := cpsTripleWithin_frameR
    ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + (i + 1)))) (by pcFreeR) e58
  -- [59] JAL x0, -20  → AB+216
  have h59 := jal_x0_spec_gen_within (-20 : BitVec 21) (AB + 236)
  rw [show AB + 236 + signExtend21 (-20 : BitVec 21) = AB + 216 from by
      rw [show signExtend21 (-20 : BitVec 21) = (-20 : Word) from by decide]; bv_omega] at h59
  have e59 := cpsTripleWithin_extend_code
    (aieMem 59, (AB + 236), (.JAL .x0 (-20 : BitVec 21))) h59
  have f59 := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + (i + 1)))) **
     ((.x6 : Reg) ↦ᵣ (x6v + signExtend12 (-1 : BitVec 12))))
    (by pcFreeR) e59
  rw [sepConj_emp_left'] at f59
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f57 f58
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f59
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s2)

/-- **Balance loop, all-zero exit** ([54]-[59], `AB+216 → AB+240`): when every
    remaining content byte is zero, the loop exhausts the countdown and exits
    through the top `BEQ` with `x6 = 0`. -/
theorem aieBalAllZero (accBase : Word) (bytes : List (BitVec 8))
    (o1 n i : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hbound : o1 + i + n ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true)
    (hz : ∀ k, k < n → bytes.getD (o1 + i + k) 0 = 0) :
    cpsTripleWithin (6 * n + 1) (AB + 216) (AB + 240) aieCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes) := by
  have hbeqt : (AB + 216 : Word) + signExtend13 (24 : BitVec 13) = AB + 240 := by
    rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega
  induction n generalizing i v29 with
  | zero =>
    have hbeq := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (AB + 216)
    rw [hbeqt] at hbeq
    have hbeqe := cpsBranchWithin_extend_code
      (aieMem 54, (AB + 216), (.BEQ .x6 .x0 (24 : BitVec 13))) hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x6 : Reg) ↦ᵣ (0 : Word)) **
              ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
              ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion accBase bytes) sState := by xperm_chunked hq
          have hq3 := sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x28)) _ hq2
          have hq4 := sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x29))) _ hq3
          xperm_chunked hq4) htf)
  | succ k ih =>
    have hlt : o1 + i < bytes.length := by omega
    have hbz : (bytes[o1 + i]'hlt).zeroExtend 64 = (0 : Word) := by
      have hz0 := hz 0 (by omega)
      have hgetd : bytes.getD (o1 + i) 0 = bytes[o1 + i]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [show o1 + i + 0 = o1 + i from by omega, hgetd] at hz0
      rw [hz0]; rfl
    -- [54] BEQ x6, x0 (not taken, x6 = k+1 ≠ 0) → AB+220
    have hbeq := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (AB + 216)
    rw [hbeqt, show (AB + 216 : Word) + 4 = AB + 220 from by bv_omega] at hbeq
    have hbeqe := cpsBranchWithin_extend_code
      (aieMem 54, (AB + 216), (.BEQ .x6 .x0 (24 : BitVec 13))) hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact aie_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) hnt
    -- [55] LBU x29 ← bytes[o1+i] (= 0)
    have h55 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 220) bytes (o1 + i)
      (by decide) halign hlt (by omega) (hvalid (o1 + i) hlt)
    rw [hbz, show (AB + 220 : Word) + 4 = AB + 224 from by bv_omega] at h55
    have e55 := cpsTripleWithin_extend_code
      (aieMem 55, (AB + 220), (.LBU .x29 .x28 (0 : BitVec 12))) h55
    have f55 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcFreeR) e55
    -- [56] BNE x29, x0 (not taken, x29 = 0) → AB+228
    have hbne := bne_spec_gen_within .x29 .x0 (160 : BitVec 13) (0 : Word)
      (0 : Word) (AB + 224)
    rw [show (AB + 224 : Word) + 4 = AB + 228 from by bv_omega] at hbne
    have hbnee := cpsBranchWithin_extend_code
      (aieMem 56, (AB + 224), (.BNE .x29 .x0 (160 : BitVec 13))) hbne
    have hbnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
    have hbntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** bytesRegion accBase bytes)
      (by pcFreeR) hbnt
    -- [57]-[59] tail → AB+216
    have htail := aieBalTail accBase o1 i (BitVec.ofNat 64 (k + 1))
    rw [aie_succ_dec k] at htail
    have htailf := cpsTripleWithin_frameR
      (((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (by pcFreeR) htail
    -- IH
    have hih := ih (i + 1) (0 : Word) (by omega)
      (fun kk hkk => by
        rw [show o1 + (i + 1) + kk = o1 + i + (kk + 1) from by omega]
        exact hz (kk + 1) (by omega))
    -- compose
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf f55
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hbntf
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 htailf
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by xperm_chunked hq) sfull)

#print axioms aieBalAllZero

/-- **Balance loop, nonzero-break exit** ([54]-[59], `AB+216 → AB+384`): when
    the first `j` content bytes are zero and byte `j` is nonzero, the loop
    breaks through the inner `BNE` to `AB+384` (not-empty). -/
theorem aieBalNonEmpty (accBase : Word) (bytes : List (BitVec 8))
    (o1 n i j : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hbound : o1 + i + n ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ jj, jj < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 jj) = true)
    (hj : j < n)
    (hzero : ∀ k, k < j → bytes.getD (o1 + i + k) 0 = 0)
    (hnz : bytes.getD (o1 + i + j) 0 ≠ 0) :
    cpsTripleWithin (6 * j + 3) (AB + 216) (AB + 384) aieCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes) := by
  have hbnet : (AB + 224 : Word) + signExtend13 (160 : BitVec 13) = AB + 384 := by
    rw [show signExtend13 (160 : BitVec 13) = (160 : Word) from by decide]; bv_omega
  induction j generalizing i n v29 with
  | zero =>
    have hlt : o1 + i < bytes.length := by omega
    have hbnz : (bytes[o1 + i]'hlt).zeroExtend 64 ≠ (0 : Word) := by
      have hgetd : bytes.getD (o1 + i) 0 = bytes[o1 + i]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [show o1 + i + 0 = o1 + i from by omega, hgetd] at hnz
      intro hc
      apply hnz
      apply BitVec.eq_of_toNat_eq
      have h1 : ((bytes[o1 + i]'hlt).zeroExtend 64 : Word).toNat = 0 := by rw [hc]; rfl
      rw [BitVec.toNat_setWidth] at h1
      have h2 : (bytes[o1 + i]'hlt).toNat < 256 := (bytes[o1 + i]'hlt).isLt
      rw [Nat.mod_eq_of_lt (Nat.lt_trans h2 (by norm_num))] at h1
      simpa using h1
    -- [54] BEQ x6, x0 (not taken, n ≠ 0) → AB+220
    have hbeq := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 n)
      (0 : Word) (AB + 216)
    rw [show (AB + 216 : Word) + signExtend13 (24 : BitVec 13) = AB + 240 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega,
        show (AB + 216 : Word) + 4 = AB + 220 from by bv_omega] at hbeq
    have hbeqe := cpsBranchWithin_extend_code
      (aieMem 54, (AB + 216), (.BEQ .x6 .x0 (24 : BitVec 13))) hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact aie_ofNat_ne_zero n (by omega) (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) hnt
    -- [55] LBU x29 ← bytes[o1+i] (nonzero)
    have h55 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 220) bytes (o1 + i)
      (by decide) halign hlt (by omega) (hvalid (o1 + i) hlt)
    rw [show (AB + 220 : Word) + 4 = AB + 224 from by bv_omega] at h55
    have e55 := cpsTripleWithin_extend_code
      (aieMem 55, (AB + 220), (.LBU .x29 .x28 (0 : BitVec 12))) h55
    have f55 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcFreeR) e55
    -- [56] BNE x29, x0 (taken, x29 ≠ 0) → AB+384
    have hbne := bne_spec_gen_within .x29 .x0 (160 : BitVec 13)
      ((bytes[o1 + i]'hlt).zeroExtend 64) (0 : Word) (AB + 224)
    rw [hbnet] at hbne
    have hbnee := cpsBranchWithin_extend_code
      (aieMem 56, (AB + 224), (.BNE .x29 .x0 (160 : BitVec 13))) hbne
    have htaken := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hbnz ((sepConj_pure_right _).1 hQ).2)
    have htf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion accBase bytes)
      (by pcFreeR) htaken
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf f55
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          have hq2 : (((.x29 : Reg) ↦ᵣ ((bytes[o1 + i]'hlt).zeroExtend 64)) **
              ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
              ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion accBase bytes) sState := by xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x29) _ hq2
          have hq4 := sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x28)) _ hq3
          have hq5 := sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x6))) _ hq4
          xperm_chunked hq5) sfull)
  | succ m ih =>
    have hlt : o1 + i < bytes.length := by omega
    have hbz : (bytes[o1 + i]'hlt).zeroExtend 64 = (0 : Word) := by
      have hz0 := hzero 0 (by omega)
      have hgetd : bytes.getD (o1 + i) 0 = bytes[o1 + i]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [show o1 + i + 0 = o1 + i from by omega, hgetd] at hz0
      rw [hz0]; rfl
    -- [54] BEQ x6, x0 (not taken, n ≠ 0) → AB+220
    have hbeq := beq_spec_gen_within .x6 .x0 (24 : BitVec 13) (BitVec.ofNat 64 n)
      (0 : Word) (AB + 216)
    rw [show (AB + 216 : Word) + signExtend13 (24 : BitVec 13) = AB + 240 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega,
        show (AB + 216 : Word) + 4 = AB + 220 from by bv_omega] at hbeq
    have hbeqe := cpsBranchWithin_extend_code
      (aieMem 54, (AB + 216), (.BEQ .x6 .x0 (24 : BitVec 13))) hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact aie_ofNat_ne_zero n (by omega) (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) hnt
    -- [55] LBU x29 ← bytes[o1+i] (= 0)
    have h55 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 220) bytes (o1 + i)
      (by decide) halign hlt (by omega) (hvalid (o1 + i) hlt)
    rw [hbz, show (AB + 220 : Word) + 4 = AB + 224 from by bv_omega] at h55
    have e55 := cpsTripleWithin_extend_code
      (aieMem 55, (AB + 220), (.LBU .x29 .x28 (0 : BitVec 12))) h55
    have f55 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcFreeR) e55
    -- [56] BNE x29, x0 (not taken, x29 = 0) → AB+228
    have hbne := bne_spec_gen_within .x29 .x0 (160 : BitVec 13) (0 : Word)
      (0 : Word) (AB + 224)
    rw [show (AB + 224 : Word) + 4 = AB + 228 from by bv_omega] at hbne
    have hbnee := cpsBranchWithin_extend_code
      (aieMem 56, (AB + 224), (.BNE .x29 .x0 (160 : BitVec 13))) hbne
    have hbnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
    have hbntf := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o1 + i))) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion accBase bytes)
      (by pcFreeR) hbnt
    -- [57]-[59] tail → AB+216
    have htail := aieBalTail accBase o1 i (BitVec.ofNat 64 n)
    rw [aie_dec n (by omega) (by omega)] at htail
    have htailf := cpsTripleWithin_frameR
      (((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (by pcFreeR) htail
    -- IH: i+1, n-1, m
    have hih := ih (n - 1) (i + 1) (0 : Word) (by omega) (by omega)
      (fun kk hkk => by
        rw [show o1 + (i + 1) + kk = o1 + i + (kk + 1) from by omega]
        exact hzero (kk + 1) (by omega))
      (by rw [show o1 + (i + 1) + m = o1 + i + (m + 1) from by omega]; exact hnz)
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf f55
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hbntf
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 htailf
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by xperm_chunked hq) sfull)

#print axioms aieBalNonEmpty

/-! ## Code-hash byte-compare loop ([80]-[86], `AB+320 → {AB+348, AB+384}`)

    A do-while comparing the field content (`x28`, `bytesRegion accBase bytes`)
    against the 32-byte `EMPTY_CODE_HASH` constant (`x31`, `bytesRegion ecBase
    aieEmptyCodeHashBytes`).  The inner `BNE x30, x29, +56` breaks to `AB+384`
    on the first mismatch; the bottom `BNE x6, x0, -24` loops until the
    countdown reaches zero, falling through to `AB+348` (all bytes match). -/

/-- The code-hash bottom back-edge target (`BNE x6, x0, -24`). -/
private theorem aie_ch_back : (AB + 344 : Word) + signExtend13 (-24 : BitVec 13) = AB + 320 := by
  rw [show signExtend13 (-24 : BitVec 13) = (-24 : Word) from by decide]; bv_omega

/-- **The code-hash loop tail** ([83]-[85], `AB+332 → AB+344`): advance both
    cursors and decrement the countdown. -/
private theorem aieCHTail (accBase ecBase : Word) (o3 i : Nat) (x6v : Word) :
    cpsTripleWithin 3 (AB + 332) (AB + 344) aieCode
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) ** ((.x6 : Reg) ↦ᵣ x6v))
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + (i + 1)))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 (i + 1))) **
       ((.x6 : Reg) ↦ᵣ (x6v + signExtend12 (-1 : BitVec 12)))) := by
  -- [83] ADDI x28, x28, 1
  have h83 := addi_spec_gen_same_within .x28 (accBase + BitVec.ofNat 64 (o3 + i))
    (1 : BitVec 12) (AB + 332) (by decide)
  rw [aie_advance accBase (o3 + i), show o3 + i + 1 = o3 + (i + 1) from by omega,
      show (AB + 332 : Word) + 4 = AB + 336 from by bv_omega] at h83
  have e83 := cpsTripleWithin_extend_code
    (aieMem 83, (AB + 332), (.ADDI .x28 .x28 (1 : BitVec 12))) h83
  have f83 := cpsTripleWithin_frameR
    (((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) ** ((.x6 : Reg) ↦ᵣ x6v))
    (by pcFreeR) e83
  -- [84] ADDI x31, x31, 1
  have h84 := addi_spec_gen_same_within .x31 (ecBase + BitVec.ofNat 64 i)
    (1 : BitVec 12) (AB + 336) (by decide)
  rw [aie_advance ecBase i, show (AB + 336 : Word) + 4 = AB + 340 from by bv_omega] at h84
  have e84 := cpsTripleWithin_extend_code
    (aieMem 84, (AB + 336), (.ADDI .x31 .x31 (1 : BitVec 12))) h84
  have f84 := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + (i + 1)))) ** ((.x6 : Reg) ↦ᵣ x6v))
    (by pcFreeR) e84
  -- [85] ADDI x6, x6, -1
  have h85 := addi_spec_gen_same_within .x6 x6v (-1 : BitVec 12) (AB + 340) (by decide)
  rw [show (AB + 340 : Word) + 4 = AB + 344 from by bv_omega] at h85
  have e85 := cpsTripleWithin_extend_code
    (aieMem 85, (AB + 340), (.ADDI .x6 .x6 (-1 : BitVec 12))) h85
  have f85 := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + (i + 1)))) **
     ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 (i + 1))))
    (by pcFreeR) e85
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f83 f84
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f85
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) s2)

/-- Byte equality of the account content and the constant at matching indices. -/
private theorem aieCH_byte_eq (bytes : List (BitVec 8)) (o3 i : Nat)
    (hlt : o3 + i < bytes.length) (hle : i < aieEmptyCodeHashBytes.length)
    (hm : bytes.getD (o3 + i) 0 = aieEmptyCodeHashBytes.getD i 0) :
    (bytes[o3 + i]'hlt).zeroExtend 64
      = (aieEmptyCodeHashBytes[i]'hle).zeroExtend 64 := by
  have h1 : bytes.getD (o3 + i) 0 = bytes[o3 + i]'hlt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  have h2 : aieEmptyCodeHashBytes.getD i 0 = aieEmptyCodeHashBytes[i]'hle := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hle]; rfl
  rw [h1, h2] at hm; rw [hm]

/-- **Code-hash loop, all-match exit** ([80]-[86], `AB+320 → AB+348`): when
    every remaining content byte equals the constant, the loop exhausts to
    `AB+348` (empty). -/
theorem aieCHAllMatch (accBase ecBase : Word) (bytes : List (BitVec 8))
    (o3 n i : Nat) (v29 v30 : Word)
    (halignA : accBase.toNat % 8 = 0) (halignE : ecBase.toNat % 8 = 0)
    (hboundA : o3 + i + n ≤ bytes.length) (hboundE : i + n ≤ 32)
    (hoverA : accBase.toNat + bytes.length < 2 ^ 64)
    (hoverE : ecBase.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true)
    (hvalidE : ∀ j, j < 32 →
      isValidByteAccess (ecBase + BitVec.ofNat 64 j) = true)
    (hn : 0 < n)
    (hmatch : ∀ k, k < n →
      bytes.getD (o3 + i + k) 0 = aieEmptyCodeHashBytes.getD (i + k) 0) :
    cpsTripleWithin (7 * n) (AB + 320) (AB + 348) aieCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (regOwn .x6 ** regOwn .x28 ** regOwn .x31 ** regOwn .x30 ** regOwn .x29 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes) := by
  induction n generalizing i v29 v30 with
  | zero => exact absurd hn (by omega)
  | succ m ih =>
    have hltA : o3 + i < bytes.length := by omega
    have hleE : i < aieEmptyCodeHashBytes.length := by
      rw [aieEmptyCodeHashBytes_length]; omega
    have hbeq := aieCH_byte_eq bytes o3 i hltA hleE (by
      have := hmatch 0 (by omega); rwa [show o3 + i + 0 = o3 + i from by omega,
        show i + 0 = i from by omega] at this)
    -- [80] LBU x30 ← bytes[o3+i]
    have h80 := bytesRegion_lbu_within .x30 .x28 accBase v30 (AB + 320) bytes (o3 + i)
      (by decide) halignA hltA (by omega) (hvalidA (o3 + i) hltA)
    rw [show (AB + 320 : Word) + 4 = AB + 324 from by bv_omega] at h80
    have e80 := cpsTripleWithin_extend_code
      (aieMem 80, (AB + 320), (.LBU .x30 .x28 (0 : BitVec 12))) h80
    have f80 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) e80
    -- [81] LBU x29 ← ec[i]
    have h81 := bytesRegion_lbu_within .x29 .x31 ecBase v29 (AB + 324)
      aieEmptyCodeHashBytes i (by decide) halignE hleE (by omega) (hvalidE i (by omega))
    rw [show (AB + 324 : Word) + 4 = AB + 328 from by bv_omega] at h81
    have e81 := cpsTripleWithin_extend_code
      (aieMem 81, (AB + 324), (.LBU .x29 .x31 (0 : BitVec 12))) h81
    have f81 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
      (by pcFreeR) e81
    -- [82] BNE x30, x29 (not taken, equal) → AB+332
    have hbne := bne_spec_gen_within .x30 .x29 (56 : BitVec 13)
      ((bytes[o3 + i]'hltA).zeroExtend 64) ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)
      (AB + 328)
    rw [show (AB + 328 : Word) + 4 = AB + 332 from by bv_omega] at hbne
    have hbnee := cpsBranchWithin_extend_code
      (aieMem 82, (AB + 328), (.BNE .x30 .x29 (56 : BitVec 13))) hbne
    have hbnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 hbeq)
    have hbntf := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) hbnt
    -- [83]-[85] tail → AB+344
    have htail := aieCHTail accBase ecBase o3 i (BitVec.ofNat 64 (m + 1))
    rw [aie_succ_dec m] at htail
    have htailf := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
       ((.x29 : Reg) ↦ᵣ ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) htail
    -- compose head [80]-[82] and tail [83]-[85] → AB+320 to AB+344
    have shead := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f80 f81
    have shead2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) shead hbntf
    have sbody := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) shead2 htailf
    -- [86] BNE x6, x0
    by_cases hm : m = 0
    · -- last iteration: x6 = 0, BNE not taken → AB+348
      subst hm
      have hbne6 := bne_spec_gen_within .x6 .x0 (-24 : BitVec 13) (BitVec.ofNat 64 0)
        (0 : Word) (AB + 344)
      rw [show (AB + 344 : Word) + 4 = AB + 348 from by bv_omega] at hbne6
      have hbne6e := cpsBranchWithin_extend_code
        (aieMem 86, (AB + 344), (.BNE .x6 .x0 (-24 : BitVec 13))) hbne6
      have hnt6 := cpsBranchWithin_ntakenStripPure2 hbne6e (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 (by decide))
      have hnt6f := cpsTripleWithin_frameR
        (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + (i + 1)))) **
         ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 (i + 1))) **
         ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
         ((.x29 : Reg) ↦ᵣ ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)) **
         bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
        (by pcFreeR) hnt6
      have sfull := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) sbody hnt6f
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun sState hq => by
            rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
            have hq2 : (((.x6 : Reg) ↦ᵣ (0 : Word)) **
                ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + (i + 1)))) **
                ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 (i + 1))) **
                ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
                ((.x29 : Reg) ↦ᵣ ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
                sState := by xperm_hyp hq
            have hq2b := sepConj_mono_left (regIs_implies_regOwn .x6) _ hq2
            have hq3 := sepConj_mono_right
              (sepConj_mono_left (regIs_implies_regOwn .x28)) _ hq2b
            have hq4 := sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (regIs_implies_regOwn .x31))) _ hq3
            have hq5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (regIs_implies_regOwn .x30)))) _ hq4
            have hq6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x29))))) _ hq5
            xperm_hyp hq6) sfull)
    · -- more iterations: x6 = m ≠ 0, BNE taken → AB+320, then IH
      have hback : (AB + 344 : Word) + signExtend13 (-24 : BitVec 13) = AB + 320 := by
        rw [show signExtend13 (-24 : BitVec 13) = (-24 : Word) from by decide]; bv_omega
      have hbne6 := bne_spec_gen_within .x6 .x0 (-24 : BitVec 13) (BitVec.ofNat 64 m)
        (0 : Word) (AB + 344)
      rw [hback] at hbne6
      have hbne6e := cpsBranchWithin_extend_code
        (aieMem 86, (AB + 344), (.BNE .x6 .x0 (-24 : BitVec 13))) hbne6
      have htk6 := cpsBranchWithin_takenStripPure2 hbne6e (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact aie_ofNat_ne_zero m (Nat.pos_of_ne_zero hm) (by omega)
          ((sepConj_pure_right _).1 hQ).2)
      have htk6f := cpsTripleWithin_frameR
        (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + (i + 1)))) **
         ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 (i + 1))) **
         ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
         ((.x29 : Reg) ↦ᵣ ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)) **
         bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
        (by pcFreeR) htk6
      have hih := ih (i + 1)
        ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)
        ((bytes[o3 + i]'hltA).zeroExtend 64)
        (by omega) (by omega) (Nat.pos_of_ne_zero hm)
        (fun kk hkk => by
          rw [show o3 + (i + 1) + kk = o3 + i + (kk + 1) from by omega,
              show i + 1 + kk = i + (kk + 1) from by omega]
          exact hmatch (kk + 1) (by omega))
      have sbb := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) sbody htk6f
      have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) sbb hih
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => by xperm_hyp hq) sfull)

#print axioms aieCHAllMatch

set_option maxRecDepth 40000 in
/-- **Code-hash loop, mismatch exit** ([80]-[86], `AB+320 → AB+384`): when the
    first `j` content bytes equal the constant and byte `j` differs, the loop
    breaks through the inner `BNE x30, x29` to `AB+384` (not-empty). -/
theorem aieCHMismatch (accBase ecBase : Word) (bytes : List (BitVec 8))
    (o3 n i j : Nat) (v29 v30 : Word)
    (halignA : accBase.toNat % 8 = 0) (halignE : ecBase.toNat % 8 = 0)
    (hboundA : o3 + i + n ≤ bytes.length) (hboundE : i + n ≤ 32)
    (hoverA : accBase.toNat + bytes.length < 2 ^ 64)
    (hoverE : ecBase.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ jj, jj < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 jj) = true)
    (hvalidE : ∀ jj, jj < 32 →
      isValidByteAccess (ecBase + BitVec.ofNat 64 jj) = true)
    (hj : j < n)
    (hmatch : ∀ k, k < j →
      bytes.getD (o3 + i + k) 0 = aieEmptyCodeHashBytes.getD (i + k) 0)
    (hmm : bytes.getD (o3 + i + j) 0 ≠ aieEmptyCodeHashBytes.getD (i + j) 0) :
    cpsTripleWithin (7 * j + 3) (AB + 320) (AB + 384) aieCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (regOwn .x6 ** regOwn .x28 ** regOwn .x31 ** regOwn .x30 ** regOwn .x29 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes) := by
  have hbnet : (AB + 328 : Word) + signExtend13 (56 : BitVec 13) = AB + 384 := by
    rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega
  induction j generalizing i n v29 v30 with
  | zero =>
    have hltA : o3 + i < bytes.length := by omega
    have hleE : i < aieEmptyCodeHashBytes.length := by
      rw [aieEmptyCodeHashBytes_length]; omega
    have hbne_ne : (bytes[o3 + i]'hltA).zeroExtend 64
        ≠ (aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64 := by
      have h1 : bytes.getD (o3 + i) 0 = bytes[o3 + i]'hltA := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltA]; rfl
      have h2 : aieEmptyCodeHashBytes.getD i 0 = aieEmptyCodeHashBytes[i]'hleE := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hleE]; rfl
      rw [show o3 + i + 0 = o3 + i from by omega, show i + 0 = i from by omega, h1, h2] at hmm
      intro hc
      apply hmm
      have hcn := congrArg BitVec.toNat hc
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at hcn
      have hb1 := (bytes[o3 + i]'hltA).isLt
      have hb2 := (aieEmptyCodeHashBytes[i]'hleE).isLt
      apply BitVec.eq_of_toNat_eq
      rw [Nat.mod_eq_of_lt (Nat.lt_trans hb1 (by norm_num)),
          Nat.mod_eq_of_lt (Nat.lt_trans hb2 (by norm_num))] at hcn
      exact hcn
    -- [80] LBU x30 ← bytes[o3+i]
    have h80 := bytesRegion_lbu_within .x30 .x28 accBase v30 (AB + 320) bytes (o3 + i)
      (by decide) halignA hltA (by omega) (hvalidA (o3 + i) hltA)
    rw [show (AB + 320 : Word) + 4 = AB + 324 from by bv_omega] at h80
    have e80 := cpsTripleWithin_extend_code
      (aieMem 80, (AB + 320), (.LBU .x30 .x28 (0 : BitVec 12))) h80
    have f80 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) e80
    -- [81] LBU x29 ← ec[i]
    have h81 := bytesRegion_lbu_within .x29 .x31 ecBase v29 (AB + 324)
      aieEmptyCodeHashBytes i (by decide) halignE hleE (by omega) (hvalidE i (by omega))
    rw [show (AB + 324 : Word) + 4 = AB + 328 from by bv_omega] at h81
    have e81 := cpsTripleWithin_extend_code
      (aieMem 81, (AB + 324), (.LBU .x29 .x31 (0 : BitVec 12))) h81
    have f81 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
      (by pcFreeR) e81
    -- [82] BNE x30, x29 (taken, mismatch) → AB+384
    have hbne := bne_spec_gen_within .x30 .x29 (56 : BitVec 13)
      ((bytes[o3 + i]'hltA).zeroExtend 64) ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)
      (AB + 328)
    rw [hbnet] at hbne
    have hbnee := cpsBranchWithin_extend_code
      (aieMem 82, (AB + 328), (.BNE .x30 .x29 (56 : BitVec 13))) hbne
    have htaken := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hbne_ne ((sepConj_pure_right _).1 hQ).2)
    have htf := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) htaken
    have shead := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f80 f81
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) shead htf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun sState hq => by
          have hq2 : (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
              ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
              ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
              ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
              ((.x29 : Reg) ↦ᵣ ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
              sState := by xperm_hyp hq
          have hq2b := sepConj_mono_left (regIs_implies_regOwn .x6) _ hq2
          have hq3 := sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x28)) _ hq2b
          have hq4 := sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x31))) _ hq3
          have hq5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x30)))) _ hq4
          have hq6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x29))))) _ hq5
          xperm_hyp hq6) sfull)
  | succ p ih =>
    have hltA : o3 + i < bytes.length := by omega
    have hleE : i < aieEmptyCodeHashBytes.length := by
      rw [aieEmptyCodeHashBytes_length]; omega
    have hbeq := aieCH_byte_eq bytes o3 i hltA hleE (by
      have := hmatch 0 (by omega); rwa [show o3 + i + 0 = o3 + i from by omega,
        show i + 0 = i from by omega] at this)
    -- [80] LBU x30 ← bytes[o3+i]
    have h80 := bytesRegion_lbu_within .x30 .x28 accBase v30 (AB + 320) bytes (o3 + i)
      (by decide) halignA hltA (by omega) (hvalidA (o3 + i) hltA)
    rw [show (AB + 320 : Word) + 4 = AB + 324 from by bv_omega] at h80
    have e80 := cpsTripleWithin_extend_code
      (aieMem 80, (AB + 320), (.LBU .x30 .x28 (0 : BitVec 12))) h80
    have f80 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) e80
    -- [81] LBU x29 ← ec[i]
    have h81 := bytesRegion_lbu_within .x29 .x31 ecBase v29 (AB + 324)
      aieEmptyCodeHashBytes i (by decide) halignE hleE (by omega) (hvalidE i (by omega))
    rw [show (AB + 324 : Word) + 4 = AB + 328 from by bv_omega] at h81
    have e81 := cpsTripleWithin_extend_code
      (aieMem 81, (AB + 324), (.LBU .x29 .x31 (0 : BitVec 12))) h81
    have f81 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
      (by pcFreeR) e81
    -- [82] BNE x30, x29 (not taken, equal) → AB+332
    have hbne := bne_spec_gen_within .x30 .x29 (56 : BitVec 13)
      ((bytes[o3 + i]'hltA).zeroExtend 64) ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)
      (AB + 328)
    rw [show (AB + 328 : Word) + 4 = AB + 332 from by bv_omega] at hbne
    have hbnee := cpsBranchWithin_extend_code
      (aieMem 82, (AB + 328), (.BNE .x30 .x29 (56 : BitVec 13))) hbne
    have hbnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 hbeq)
    have hbntf := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + i))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 i)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) hbnt
    -- [83]-[85] tail → AB+344
    have htail := aieCHTail accBase ecBase o3 i (BitVec.ofNat 64 n)
    rw [aie_dec n (by omega) (by omega)] at htail
    have htailf := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
       ((.x29 : Reg) ↦ᵣ ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) htail
    -- [86] BNE x6, x0 (taken, n-1 ≠ 0) → AB+320
    have hback := aie_ch_back
    have hbne6 := bne_spec_gen_within .x6 .x0 (-24 : BitVec 13) (BitVec.ofNat 64 (n - 1))
      (0 : Word) (AB + 344)
    rw [hback] at hbne6
    have hbne6e := cpsBranchWithin_extend_code
      (aieMem 86, (AB + 344), (.BNE .x6 .x0 (-24 : BitVec 13))) hbne6
    have htk6 := cpsBranchWithin_takenStripPure2 hbne6e (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact aie_ofNat_ne_zero (n - 1) (by omega) (by omega)
        ((sepConj_pure_right _).1 hQ).2)
    have htk6f := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o3 + (i + 1)))) **
       ((.x31 : Reg) ↦ᵣ (ecBase + BitVec.ofNat 64 (i + 1))) **
       ((.x30 : Reg) ↦ᵣ ((bytes[o3 + i]'hltA).zeroExtend 64)) **
       ((.x29 : Reg) ↦ᵣ ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)) **
       bytesRegion accBase bytes ** bytesRegion ecBase aieEmptyCodeHashBytes)
      (by pcFreeR) htk6
    have hih := ih (n - 1) (i + 1)
      ((aieEmptyCodeHashBytes[i]'hleE).zeroExtend 64)
      ((bytes[o3 + i]'hltA).zeroExtend 64)
      (by omega) (by omega) (by omega)
      (fun kk hkk => by
        rw [show o3 + (i + 1) + kk = o3 + i + (kk + 1) from by omega,
            show i + 1 + kk = i + (kk + 1) from by omega]
        exact hmatch (kk + 1) (by omega))
      (by rw [show o3 + (i + 1) + p = o3 + i + (p + 1) from by omega,
              show i + 1 + p = i + (p + 1) from by omega]; exact hmm)
    have shead := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f80 f81
    have shead2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) shead hbntf
    have sbody := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) shead2 htailf
    have sbb := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) sbody htk6f
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) sbb hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) sfull)

#print axioms aieCHMismatch

end EvmAsm.Codegen.AccountIsEip161EmptySpec
