/-
  The nonce big-endian accumulate loop of `accountDecode_prog`
  (`Programs/State.lean`, field 0, instrs [33]-[39], `AB+132 → AB+160`).

  The top-tested `BEQ x6, x0, +28` header exits (to `AB+160`, the nonce `SD`)
  when the byte countdown reaches zero; each taken iteration shifts the
  big-endian accumulator `x7` left one byte and ORs in the next content byte:

    [33] BEQ  x6, x0, +28   -- exit to AB+160 when x6 = 0
    [34] SLLI x7, x7, 8
    [35] LBU  x29, 0(x28)
    [36] OR   x7, x7, x29
    [37] ADDI x28, x28, 1
    [38] ADDI x6,  x6, -1
    [39] JAL  x0, -24       -- back to AB+132

  This is exactly the merged `AccountIsEip161EmptyLoop.aieNonceLoop`
  accumulate-scan (`beAccFrom`), re-derived here at the account-decode guest
  offsets with the content tie the byte-identical `AccountDecodeSpec.beAccum`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.AccountDecodeSpec

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

/-- `k`-th instruction membership of `accountDecode_prog` into the full linked
    closure `fullCode` (via `ad_mono` on the local `adCode`). -/
local macro "adMemF" k:term ", " A:term ", " ins:term : term =>
  `((fun a i h => ad_mono a i
      (CodeReq.ofProg_mem_at AB $A accountDecode_prog $k $ins (by bv_omega)
        (by rw [ad_length]; omega) rfl (by rw [ad_length]; norm_num) a i h)))

/-! ## Nonce accumulate-scan loop ([33]-[39], `AB+132 → AB+160`) -/

/-- The big-endian OR/shift step for `beAccum`, matching `x7 := (x7<<<8)|byte`. -/
private theorem ad_x7_or_step (bytes : List (BitVec 8)) (o0 i : Nat)
    (hi : o0 + i < bytes.length) :
    ((beAccum bytes o0 i) <<< (8 : BitVec 6).toNat) |||
      ((bytes[o0 + i]'hi).zeroExtend 64) = beAccum bytes o0 (i + 1) := by
  rw [show (8 : BitVec 6).toNat = 8 from by decide]
  have hgetd : bytes.getD (o0 + i) 0 = bytes[o0 + i]'hi := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [← hgetd]; rfl

/-- Word decrement of a successor counter (the `x6` countdown). -/
private theorem adn_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem adn_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-- Pointer advance by 1 byte. -/
private theorem adn_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-- **One nonce-loop iteration** ([34]-[39], `AB+136 → AB+132`): shift the
    accumulator, OR in `bytes[o0+i]`, advance the pointer and decrement the
    countdown. -/
private theorem adNonceBody (accBase : Word) (bytes : List (BitVec 8))
    (o0 i k : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hlt : o0 + i < bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 6 (AB + 160) (AB + 156) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x7 : Reg) ↦ᵣ beAccum bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x7 : Reg) ↦ᵣ beAccum bytes o0 (i + 1)) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
       ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  -- [34] SLLI x7, x7, 8
  have h34 := slli_spec_gen_same_within .x7 (beAccum bytes o0 i) (8 : BitVec 6)
    (AB + 160) (by decide)
  rw [show (AB + 160 : Word) + 4 = AB + 164 from by bv_omega] at h34
  have e34 := cpsTripleWithin_extend_code
    (adMemF 40, (AB + 160), (.SLLI .x7 .x7 (8 : BitVec 6))) h34
  have f34 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion accBase bytes)
    (by pcFreeR) e34
  -- [35] LBU x29 ← bytes[o0+i]
  have h35 := bytesRegion_lbu_within .x29 .x28 accBase v29 (AB + 164) bytes (o0 + i)
    (by decide) halign hlt (by omega) (hvalid (o0 + i) hlt)
  rw [show (AB + 164 : Word) + 4 = AB + 168 from by bv_omega] at h35
  have e35 := cpsTripleWithin_extend_code
    (adMemF 41, (AB + 164), (.LBU .x29 .x28 (0 : BitVec 12))) h35
  have f35 := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ ((beAccum bytes o0 i) <<< (8 : BitVec 6).toNat)) **
     ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcFreeR) e35
  -- [36] OR x7, x7, x29
  have h36 := or_spec_gen_rd_eq_rs1_within .x7 .x29
    ((beAccum bytes o0 i) <<< (8 : BitVec 6).toNat) ((bytes[o0 + i]'hlt).zeroExtend 64)
    (AB + 168) (by decide)
  rw [ad_x7_or_step bytes o0 i hlt,
      show (AB + 168 : Word) + 4 = AB + 172 from by bv_omega] at h36
  have e36 := cpsTripleWithin_extend_code
    (adMemF 42, (AB + 168), (.OR .x7 .x7 .x29)) h36
  have f36 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e36
  -- [37] ADDI x28, x28, 1
  have h37 := addi_spec_gen_same_within .x28 (accBase + BitVec.ofNat 64 (o0 + i))
    (1 : BitVec 12) (AB + 172) (by decide)
  rw [adn_advance accBase (o0 + i),
      show o0 + i + 1 = o0 + (i + 1) from by omega,
      show (AB + 172 : Word) + 4 = AB + 176 from by bv_omega] at h37
  have e37 := cpsTripleWithin_extend_code
    (adMemF 43, (AB + 172), (.ADDI .x28 .x28 (1 : BitVec 12))) h37
  have f37 := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ beAccum bytes o0 (i + 1)) **
     ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
     ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e37
  -- [38] ADDI x6, x6, -1
  have h38 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12)
    (AB + 176) (by decide)
  rw [adn_succ_dec k, show (AB + 176 : Word) + 4 = AB + 180 from by bv_omega] at h38
  have e38 := cpsTripleWithin_extend_code
    (adMemF 44, (AB + 176), (.ADDI .x6 .x6 (-1 : BitVec 12))) h38
  have f38 := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ beAccum bytes o0 (i + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e38
  -- [39] JAL x0, -24  → AB+132
  have h39 := jal_x0_spec_gen_within (-24 : BitVec 21) (AB + 180)
  rw [show AB + 180 + signExtend21 (-24 : BitVec 21) = AB + 156 from by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega] at h39
  have e39 := cpsTripleWithin_extend_code
    (adMemF 45, (AB + 180), (.JAL .x0 (-24 : BitVec 21))) h39
  have f39 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
     ((.x7 : Reg) ↦ᵣ beAccum bytes o0 (i + 1)) **
     ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + (i + 1)))) **
     ((.x29 : Reg) ↦ᵣ ((bytes[o0 + i]'hlt).zeroExtend 64)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase bytes)
    (by pcFreeR) e39
  rw [sepConj_emp_left'] at f39
  -- compose the six body steps
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f34 f35
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f36
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 f37
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 f38
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s4 f39
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s5)

/-- **The nonce accumulate-scan loop closure** ([33]-[39], `AB+132 → AB+160`):
    by induction on the byte countdown `n`, process the remaining `n` content
    bytes into the big-endian accumulator and exit through the top `BEQ` with
    `x6 = 0` and `x7 = beAccum bytes o0 (i+n)`.  Content tie identical to the
    merged `aieNonceLoop`. -/
theorem adNonceLoop (accBase : Word) (bytes : List (BitVec 8))
    (o0 n i : Nat) (v29 : Word)
    (halign : accBase.toNat % 8 = 0)
    (hbound : o0 + i + n ≤ bytes.length)
    (hover : accBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (accBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (7 * n + 1) (AB + 156) (AB + 184) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x7 : Reg) ↦ᵣ beAccum bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes)
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ beAccum bytes o0 (i + n)) **
       regOwn .x28 ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion accBase bytes) := by
  have hbeq : (AB + 156 : Word) + signExtend13 (28 : BitVec 13) = AB + 184 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  induction n generalizing i v29 with
  | zero =>
    -- x6 = 0 : BEQ taken → AB+160
    have hb := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (AB + 156)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 39, (AB + 156), (.BEQ .x6 .x0 (28 : BitVec 13))) hb
    have htaken := cpsBranchWithin_takenStripPure2 hbe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ beAccum bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          simp only [show i + 0 = i from by omega]
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          have hq2 : (((.x6 : Reg) ↦ᵣ (0 : Word)) **
              ((.x7 : Reg) ↦ᵣ beAccum bytes o0 i) **
              ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
              ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion accBase bytes) sState := by xperm_chunked hq
          have hq3 := sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x28))) _ hq2
          have hq4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (regIs_implies_regOwn .x29)))) _ hq3
          xperm_chunked hq4) htf)
  | succ k ih =>
    -- x6 = k+1 ≠ 0 : BEQ not-taken → AB+136, then body, then IH
    have hb := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (AB + 156)
    rw [hbeq] at hb
    have hbe := cpsBranchWithin_extend_code
      (adMemF 39, (AB + 156), (.BEQ .x6 .x0 (28 : BitVec 13))) hb
    have hnt := cpsBranchWithin_ntakenStripPure2 hbe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact adn_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ beAccum bytes o0 i) **
       ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (o0 + i))) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion accBase bytes)
      (by pcFreeR) hnt
    have hbody := adNonceBody accBase bytes o0 i k v29 halign (by omega) hover hvalid
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

#print axioms adNonceLoop

end EvmAsm.Codegen.AccountDecodeSpec
