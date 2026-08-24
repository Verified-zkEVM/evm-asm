/-
  EvmAsm.Codegen.Programs.RequestsHashVerifyCmp

  The 32-byte hash comparison tail of `requests_hash_verify` (#12206 item 2):
  indices 18 → 31, i.e. from the compare-loop top at 0x80054394 through BOTH
  verdict exits and their joins into the epilogue at 0x800543c8.

  Instruction shape (re-derived from the linked guest ELF):

      18  0x80054394  beqz t2, +32  → 26     [loop top]
      19  0x80054398  lbu  t3, 0(t0)
      20  0x8005439c  lbu  t4, 0(t1)
      21  0x800543a0  bne  t3, t4, +28 → 28
      22  0x800543a4  addi t0, t0, 1
      23  0x800543a8  addi t1, t1, 1
      24  0x800543ac  addi t2, t2, -1
      25  0x800543b0  j    -28      → 18
      26  0x800543b4  li   a0, 0    ; 27  j +16 → 31
      28  0x800543bc  li   a0, 1    ; 29  j  +8 → 31

  This is the same seven-instruction shape as `MptWalkLeafCmp` /
  `MptWalkExtCmp`, but at DIFFERENT registers and — the reason neither of those
  nor `DualReadByteScan.byteScanProg` is reusable here — it is a genuine
  TWO-EXIT loop: the `beqz` exhaustion exit (index 26) and the `bne` mismatch
  exit (index 28) are distinct verdicts, whereas `byteScanProg` merges both into
  one join and re-tests the counter afterwards.

  Because both verdicts rejoin at index 31, this module proves the whole tail as
  a single triple whose post pins `a0` to `if dig = exp then 0 else 1`. The loop
  guard `beqz t2` is read off 0x80054394: it is TOP-tested, so a zero count
  would fall straight through to the match exit — but the count is `li t2, 32`
  at index 17, so the empty case never arises in this routine.
-/

import EvmAsm.Codegen.Programs.RequestsHashVerifyBase
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.LoopFuel

namespace EvmAsm.Codegen.RequestsHashVerifyCmp

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RequestsHashVerifyBase

set_option maxRecDepth 8000

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
private theorem ofNat_zero : BitVec.ofNat 64 0 = (0 : Word) := rfl
private theorem one_plus_neg1 : (1 : Word) + (-1 : Word) = 0 := by decide

private theorem cursor_succ (base : Word) (p : Nat) :
    base + BitVec.ofNat 64 p + (1 : Word) = base + BitVec.ofNat 64 (p + 1) := by
  rw [BitVec.add_assoc, ofNat_succ p]

private theorem cnt_step_down (n : Nat) :
    BitVec.ofNat 64 (n + 1) + (-1 : Word) = BitVec.ofNat 64 n := by
  have e1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + (1 : Word) := (ofNat_succ n).symm
  calc
    BitVec.ofNat 64 (n + 1) + (-1 : Word)
        = (BitVec.ofNat 64 n + (1 : Word)) + (-1 : Word) := by rw [e1]
    _ = BitVec.ofNat 64 n + ((1 : Word) + (-1 : Word)) := by rw [BitVec.add_assoc]
    _ = BitVec.ofNat 64 n + (0 : Word) := by rw [one_plus_neg1]
    _ = BitVec.ofNat 64 n := BitVec.add_zero _

private theorem word_ofNat_succ_ne_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  intro heq
  have htn := congrArg BitVec.toNat heq
  have hmod : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    simp only [BitVec.toNat_ofNat]; omega
  have hz : (0 : Word).toNat = 0 := rfl
  omega

/-- Two distinct bytes stay distinct after `lbu`'s zero extension to 64 bits. -/
private theorem zext_ne_of_ne {a b : BitVec 8} (h : a ≠ b) :
    a.zeroExtend 64 ≠ b.zeroExtend 64 := by
  intro heq
  apply h
  apply BitVec.eq_of_toNat_eq
  have ht : (a.zeroExtend 64).toNat = (b.zeroExtend 64).toNat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_setWidth] at ht
  have ha : a.toNat < 2 ^ 8 := a.isLt
  have hb : b.toNat < 2 ^ 8 := b.isLt
  rwa [Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)] at ht

/-! ## Assertions -/

/-- Compare-loop invariant at the loop top (index 18): `done` bytes already
    compared, `k` remaining in `t2`.

    Registers pinned here are exactly the ones the loop body writes, each read
    off the disassembly: `t0`/`x5` (0x80054384 `auipc`, 0x800543a4 `addi`),
    `t1`/`x6` (0x8005438c `mv`, 0x800543a8 `addi`), `t2`/`x7` (0x80054390 `li`,
    0x800543ac `addi`). `t3`/`x28` and `t4`/`x29` (0x80054398/9c `lbu`) and
    `a0`/`x10` (written only at the verdict exits) are owned, not pinned. -/
def cmpInv (digPtr expPtr : Word) (k done : Nat)
    (dig exp : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
  (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
  (.x7 ↦ᵣ BitVec.ofNat 64 k) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion digPtr dig **
  bytesRegion expPtr exp **
  (regOwn .x28 ** regOwn .x29 ** regOwn .x10) ** F

/-- State at either verdict's `li a0, _` (indices 26 and 28). Both exits are
    reached with the cursors, the counter and the two scratch bytes dead, so
    the two arms share one pre-shape. -/
def cmpPreLi (digPtr expPtr : Word)
    (dig exp : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion digPtr dig **
  bytesRegion expPtr exp **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   regOwn .x28 ** regOwn .x29 ** regOwn .x10) ** F

/-- State at the epilogue join (index 31), verdict `v` in `a0`. -/
def cmpJoin (digPtr expPtr v : Word)
    (dig exp : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ v) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion digPtr dig **
  bytesRegion expPtr exp **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   regOwn .x28 ** regOwn .x29) ** F

theorem cmpInv_pcFree (digPtr expPtr : Word) (k done : Nat)
    (dig exp : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (cmpInv digPtr expPtr k done dig exp F).pcFree := by
  unfold cmpInv; pcf; exact hF

theorem cmpPreLi_pcFree (digPtr expPtr : Word)
    (dig exp : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (cmpPreLi digPtr expPtr dig exp F).pcFree := by
  unfold cmpPreLi; pcf; exact hF

theorem cmpJoin_pcFree (digPtr expPtr v : Word)
    (dig exp : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (cmpJoin digPtr expPtr v dig exp F).pcFree := by
  unfold cmpJoin; pcf; exact hF

/-! ## Exhaustion exit: `beqz t2` taken (index 18 → 26) -/

theorem rhv_cmp_exit_zero
    (digPtr expPtr : Word) (done : Nat)
    (dig exp : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 18) (pc 26) rhvCode
      (cmpInv digPtr expPtr 0 done dig exp F)
      (cmpPreLi digPtr expPtr dig exp F) := by
  have hbr0 := beq_spec_gen_within .x7 .x0 (32 : BitVec 13)
    (0 : Word) (0 : Word) (pc 18)
  rw [pc_beq_match, show (pc 18 : Word) + 4 = pc 19 from pc_succ 18] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 18 (.BEQ .x7 .x0 (32 : BitVec 13)) (pc 18) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hbr0
  have ht := cpsBranchWithin_takenStripPure2 hbr
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  let G : Assertion :=
    bytesRegion digPtr dig ** bytesRegion expPtr exp **
    (regOwn .x5 ** regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x10) ** F
  have hG : G.pcFree := by pcf; exact hF
  have htF := cpsTripleWithin_frameR G hG ht
  refine cpsTripleWithin_weaken ?_ ?_ htF
  · intro h hp
    simp only [cmpInv, ofNat_zero, G] at hp ⊢
    have hp1 :
        (((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done))) **
         ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion digPtr dig ** bytesRegion expPtr exp **
          regOwn .x28 ** regOwn .x29 ** regOwn .x10 ** F)) h := by
      xperm_chunked hp
    have hp2 :=
      sepConj_mono
        (fun h' hx =>
          sepConj_mono (regIs_implies_regOwn .x5) (regIs_implies_regOwn .x6) h' hx)
        (fun _ hx => hx) h hp1
    xperm_chunked hp2
  · intro h hq
    simp only [cmpPreLi, G] at hq ⊢
    have hq1 :
        ((.x7 ↦ᵣ (0 : Word)) **
         ((.x0 ↦ᵣ (0 : Word)) **
          bytesRegion digPtr dig ** bytesRegion expPtr exp **
          regOwn .x5 ** regOwn .x6 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x10 ** F)) h := by
      xperm_chunked hq
    have hq2 := sepConj_mono (regIs_implies_regOwn .x7) (fun _ hx => hx) h hq1
    xperm_chunked hq2

/-! ## Mismatch exit: `bne t3, t4` taken (index 18 → 28) -/

set_option maxRecDepth 12000 in
theorem rhv_cmp_mismatch
    (digPtr expPtr : Word) (k done : Nat)
    (dig exp : List (BitVec 8))
    (hdig : done < dig.length) (hexp : done < exp.length)
    (hne : (dig[done]'hdig) ≠ (exp[done]'hexp))
    (hdigAlign : digPtr.toNat % 8 = 0)
    (hexpAlign : expPtr.toNat % 8 = 0)
    (hdigOver : digPtr.toNat + done < 2 ^ 64)
    (hexpOver : expPtr.toNat + done < 2 ^ 64)
    (hkbound : k + 1 < 2 ^ 64)
    (hvalidD : isValidByteAccess (digPtr + BitVec.ofNat 64 done) = true)
    (hvalidE : isValidByteAccess (expPtr + BitVec.ofNat 64 done) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 18) (pc 28) rhvCode
      (cmpInv digPtr expPtr (k + 1) done dig exp F)
      (cmpPreLi digPtr expPtr dig exp F) := by
  have hnez := word_ofNat_succ_ne_zero k hkbound
  -- index 18: BEQ not taken (counter is k+1 ≠ 0)
  have hbr0 := beq_spec_gen_within .x7 .x0 (32 : BitVec 13)
    (BitVec.ofNat 64 (k + 1)) (0 : Word) (pc 18)
  rw [pc_beq_match, show (pc 18 : Word) + 4 = pc 19 from pc_succ 18] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 18 (.BEQ .x7 .x0 (32 : BitVec 13)) (pc 18) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hnez ((sepConj_pure_right _).1 hQ).2)
  have hbeq := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp **
     (regOwn .x28 ** regOwn .x29 ** regOwn .x10) ** F)
    (by pcf; exact hF) hnt
  -- index 19: LBU t3, 0(t0)
  have hlbuD : ∀ v28,
      cpsTripleWithin 1 (pc 19) (pc 20) rhvCode
        (((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          bytesRegion digPtr dig **
          (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion expPtr exp ** regOwn .x29 ** regOwn .x10 ** F) **
         (.x28 ↦ᵣ v28))
        (((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          bytesRegion digPtr dig **
          (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion expPtr exp ** regOwn .x29 ** regOwn .x10 ** F)) := by
    intro v28
    have hlbu := bytesRegion_lbu_within .x28 .x5 digPtr v28 (pc 19)
      dig done (by decide) hdigAlign hdig hdigOver hvalidD
    have hlbuE := cpsTripleWithin_extend_code
      (mem_at 19 (.LBU .x28 .x5 (0 : BitVec 12)) (pc 19) rfl
        (by rw [rhvProgL_len]; norm_num) (by decide)) hlbu
    rw [pc_succ 19] at hlbuE
    have hFr := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
       (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion expPtr exp ** regOwn .x29 ** regOwn .x10 ** F)
      (by pcf; exact hF) hlbuE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuDown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28) hlbuD
  -- index 20: LBU t4, 0(t1)
  have hlbuE2 : ∀ v29,
      cpsTripleWithin 1 (pc 20) (pc 21) rhvCode
        (((.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          bytesRegion expPtr exp **
          (.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion digPtr dig ** regOwn .x10 ** F) **
         (.x29 ↦ᵣ v29))
        (((.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64)) **
          bytesRegion expPtr exp **
          (.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion digPtr dig ** regOwn .x10 ** F)) := by
    intro v29
    have hlbu := bytesRegion_lbu_within .x29 .x6 expPtr v29 (pc 20)
      exp done (by decide) hexpAlign hexp hexpOver hvalidE
    have hlbuE := cpsTripleWithin_extend_code
      (mem_at 20 (.LBU .x29 .x6 (0 : BitVec 12)) (pc 20) rfl
        (by rw [rhvProgL_len]; norm_num) (by decide)) hlbu
    rw [pc_succ 20] at hlbuE
    have hFr := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
       (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
       (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion digPtr dig ** regOwn .x10 ** F)
      (by pcf; exact hF) hlbuE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuEown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29) hlbuE2
  -- index 21: BNE taken (the bytes differ)
  have hneW :
      ((dig[done]'hdig).zeroExtend 64) ≠ ((exp[done]'hexp).zeroExtend 64) :=
    zext_ne_of_ne hne
  have hbrm0 := bne_spec_gen_within .x28 .x29 (28 : BitVec 13)
    ((dig[done]'hdig).zeroExtend 64) ((exp[done]'hexp).zeroExtend 64) (pc 21)
  rw [pc_bne_mismatch, show (pc 21 : Word) + 4 = pc 22 from pc_succ 21] at hbrm0
  have hbrm := cpsBranchWithin_extend_code
    (mem_at 21 (.BNE .x28 .x29 (28 : BitVec 13)) (pc 21) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hbrm0
  have htm := cpsBranchWithin_takenStripPure2 hbrm
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hneW ((sepConj_pure_right _).1 hQ).2)
  have htmF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
     (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp ** regOwn .x10 ** F)
    (by pcf; exact hF) htm
  -- compose 18 → 19 → 20 → 21 → 28
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hbeq hlbuDown
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0 hlbuEown
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 htmF
  refine cpsTripleWithin_weaken ?_ ?_ c
  · intro h hp; simp only [cmpInv] at hp ⊢; xperm_chunked hp
  · intro h hq
    simp only [cmpPreLi] at hq ⊢
    have h5 := regIs_implies_regOwn (v := digPtr + BitVec.ofNat 64 done) .x5
    have h6 := regIs_implies_regOwn (v := expPtr + BitVec.ofNat 64 done) .x6
    have h7 := regIs_implies_regOwn (v := BitVec.ofNat 64 (k + 1)) .x7
    have h28 := regIs_implies_regOwn (v := (dig[done]'hdig).zeroExtend 64) .x28
    have h29 := regIs_implies_regOwn (v := (exp[done]'hexp).zeroExtend 64) .x29
    have hq1 :
        (((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
          (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64))) **
         ((.x0 ↦ᵣ (0 : Word)) ** bytesRegion digPtr dig **
          bytesRegion expPtr exp ** regOwn .x10 ** F)) h := by
      xperm_chunked hq
    have hq2 :=
      sepConj_mono
        (fun h' hx => sepConj_mono h5 (sepConj_mono h6 (sepConj_mono h7
          (sepConj_mono h28 h29))) h' hx)
        (fun _ hx => hx) h hq1
    xperm_chunked hq2

/-! ## One matching step (index 18 → 18) -/

set_option maxRecDepth 12000 in
theorem rhv_cmp_step
    (digPtr expPtr : Word) (k done : Nat)
    (dig exp : List (BitVec 8))
    (hdig : done < dig.length) (hexp : done < exp.length)
    (hmatch : (dig[done]'hdig) = (exp[done]'hexp))
    (hdigAlign : digPtr.toNat % 8 = 0)
    (hexpAlign : expPtr.toNat % 8 = 0)
    (hdigOver : digPtr.toNat + done < 2 ^ 64)
    (hexpOver : expPtr.toNat + done < 2 ^ 64)
    (hkbound : k + 1 < 2 ^ 64)
    (hvalidD : isValidByteAccess (digPtr + BitVec.ofNat 64 done) = true)
    (hvalidE : isValidByteAccess (expPtr + BitVec.ofNat 64 done) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 18) (pc 18) rhvCode
      (cmpInv digPtr expPtr (k + 1) done dig exp F)
      (cmpInv digPtr expPtr k (done + 1) dig exp F) := by
  have hnez := word_ofNat_succ_ne_zero k hkbound
  -- index 18: BEQ not taken
  have hbr0 := beq_spec_gen_within .x7 .x0 (32 : BitVec 13)
    (BitVec.ofNat 64 (k + 1)) (0 : Word) (pc 18)
  rw [pc_beq_match, show (pc 18 : Word) + 4 = pc 19 from pc_succ 18] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 18 (.BEQ .x7 .x0 (32 : BitVec 13)) (pc 18) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hnez ((sepConj_pure_right _).1 hQ).2)
  have hbeq := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp **
     (regOwn .x28 ** regOwn .x29 ** regOwn .x10) ** F)
    (by pcf; exact hF) hnt
  -- index 19: LBU t3, 0(t0)
  have hlbuD : ∀ v28,
      cpsTripleWithin 1 (pc 19) (pc 20) rhvCode
        (((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          bytesRegion digPtr dig **
          (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion expPtr exp ** regOwn .x29 ** regOwn .x10 ** F) **
         (.x28 ↦ᵣ v28))
        (((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          bytesRegion digPtr dig **
          (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion expPtr exp ** regOwn .x29 ** regOwn .x10 ** F)) := by
    intro v28
    have hlbu := bytesRegion_lbu_within .x28 .x5 digPtr v28 (pc 19)
      dig done (by decide) hdigAlign hdig hdigOver hvalidD
    have hlbuE := cpsTripleWithin_extend_code
      (mem_at 19 (.LBU .x28 .x5 (0 : BitVec 12)) (pc 19) rfl
        (by rw [rhvProgL_len]; norm_num) (by decide)) hlbu
    rw [pc_succ 19] at hlbuE
    have hFr := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
       (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion expPtr exp ** regOwn .x29 ** regOwn .x10 ** F)
      (by pcf; exact hF) hlbuE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuDown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28) hlbuD
  -- index 20: LBU t4, 0(t1)
  have hlbuE2 : ∀ v29,
      cpsTripleWithin 1 (pc 20) (pc 21) rhvCode
        (((.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          bytesRegion expPtr exp **
          (.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion digPtr dig ** regOwn .x10 ** F) **
         (.x29 ↦ᵣ v29))
        (((.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
          (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64)) **
          bytesRegion expPtr exp **
          (.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
          (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion digPtr dig ** regOwn .x10 ** F)) := by
    intro v29
    have hlbu := bytesRegion_lbu_within .x29 .x6 expPtr v29 (pc 20)
      exp done (by decide) hexpAlign hexp hexpOver hvalidE
    have hlbuE := cpsTripleWithin_extend_code
      (mem_at 20 (.LBU .x29 .x6 (0 : BitVec 12)) (pc 20) rfl
        (by rw [rhvProgL_len]; norm_num) (by decide)) hlbu
    rw [pc_succ 20] at hlbuE
    have hFr := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
       (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
       (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion digPtr dig ** regOwn .x10 ** F)
      (by pcf; exact hF) hlbuE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuEown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29) hlbuE2
  -- index 21: BNE not taken (the bytes match)
  have heqW :
      ((dig[done]'hdig).zeroExtend 64) = ((exp[done]'hexp).zeroExtend 64) := by
    simp only [hmatch]
  have hbrm0 := bne_spec_gen_within .x28 .x29 (28 : BitVec 13)
    ((dig[done]'hdig).zeroExtend 64) ((exp[done]'hexp).zeroExtend 64) (pc 21)
  rw [pc_bne_mismatch, show (pc 21 : Word) + 4 = pc 22 from pc_succ 21] at hbrm0
  have hbrm := cpsBranchWithin_extend_code
    (mem_at 21 (.BNE .x28 .x29 (28 : BitVec 13)) (pc 21) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hbrm0
  have hntm := cpsBranchWithin_ntakenStripPure2 hbrm
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 heqW)
  have hntmF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
     (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp ** regOwn .x10 ** F)
    (by pcf; exact hF) hntm
  -- index 22: ADDI t0, t0, 1
  have hadd50 := addi_spec_gen_same_within .x5 (digPtr + BitVec.ofNat 64 done)
    (1 : BitVec 12) (pc 22) (by decide)
  have hadd5 := cpsTripleWithin_extend_code
    (mem_at 22 (.ADDI .x5 .x5 (1 : BitVec 12)) (pc 22) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hadd50
  rw [pc_succ 22, se12_1] at hadd5
  have hadd5F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done)) **
     (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
     (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp ** regOwn .x10 ** F)
    (by pcf; exact hF) hadd5
  -- index 23: ADDI t1, t1, 1
  have hadd60 := addi_spec_gen_same_within .x6 (expPtr + BitVec.ofNat 64 done)
    (1 : BitVec 12) (pc 23) (by decide)
  have hadd6 := cpsTripleWithin_extend_code
    (mem_at 23 (.ADDI .x6 .x6 (1 : BitVec 12)) (pc 23) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hadd60
  rw [pc_succ 23, se12_1] at hadd6
  have hadd6F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x7 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
     (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp ** regOwn .x10 ** F)
    (by pcf; exact hF) hadd6
  -- index 24: ADDI t2, t2, -1
  have hadd70 := addi_spec_gen_same_within .x7 (BitVec.ofNat 64 (k + 1))
    (-1 : BitVec 12) (pc 24) (by decide)
  have hadd7 := cpsTripleWithin_extend_code
    (mem_at 24 (.ADDI .x7 .x7 (-1 : BitVec 12)) (pc 24) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hadd70
  rw [pc_succ 24, se12_m1] at hadd7
  have hadd7F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
     (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp ** regOwn .x10 ** F)
    (by pcf; exact hF) hadd7
  -- index 25: J back to the loop top
  have hjal0 := jal_x0_spec_gen_within (-28 : BitVec 21) (pc 25)
  have hjal := cpsTripleWithin_extend_code
    (mem_at 25 (.JAL .x0 (-28 : BitVec 21)) (pc 25) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hjal0
  rw [pc_jal_back] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 done + (1 : Word))) **
     (.x7 ↦ᵣ (BitVec.ofNat 64 (k + 1) + (-1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
     (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64)) **
     bytesRegion digPtr dig ** bytesRegion expPtr exp ** regOwn .x10 ** F)
    (by pcf; exact hF) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  -- compose the eight steps
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hbeq hlbuDown
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0 hlbuEown
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hntmF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hadd5F
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 hadd6F
  have c012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 hadd7F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012345 hjalW
  have hcur5 := cursor_succ digPtr done
  have hcur6 := cursor_succ expPtr done
  have hrem := cnt_step_down k
  refine cpsTripleWithin_weaken ?_ ?_ c
  · intro h hp; simp only [cmpInv] at hp ⊢; xperm_chunked hp
  · intro h hq
    simp only [hcur5, hcur6, hrem] at hq
    simp only [cmpInv] at ⊢
    have h28 := regIs_implies_regOwn (v := (dig[done]'hdig).zeroExtend 64) .x28
    have h29 := regIs_implies_regOwn (v := (exp[done]'hexp).zeroExtend 64) .x29
    have hq1 :
        (((.x28 ↦ᵣ ((dig[done]'hdig).zeroExtend 64)) **
          (.x29 ↦ᵣ ((exp[done]'hexp).zeroExtend 64))) **
         ((.x5 ↦ᵣ (digPtr + BitVec.ofNat 64 (done + 1))) **
          (.x6 ↦ᵣ (expPtr + BitVec.ofNat 64 (done + 1))) **
          (.x7 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion digPtr dig ** bytesRegion expPtr exp **
          regOwn .x10 ** F)) h := by
      xperm_chunked hq
    have hq2 :=
      sepConj_mono (fun h' hx => sepConj_mono h28 h29 h' hx) (fun _ hx => hx) h hq1
    xperm_chunked hq2

/-! ## The two verdict writes (indices 26/27 and 28/29 → 31)

    Both verdicts are the same two instructions — `li a0, v` then an
    unconditional `j` to the shared epilogue at index 31 — so they are proved
    once, parameterised over the index, the verdict value and the jump
    offset. -/

private theorem rhv_verdict_join
    (digPtr expPtr : Word) (dig exp : List (BitVec 8))
    (j : Nat) (v : Word) (off : BitVec 21)
    (hj : j < rhvProgL.length) (hins : rhvProgL[j]'hj = .LI .x10 v)
    (hj1 : j + 1 < rhvProgL.length) (hins1 : rhvProgL[j + 1]'hj1 = .JAL .x0 off)
    (hjmp : (pc (j + 1) : Word) + signExtend21 off = pc 31)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc j) (pc 31) rhvCode
      (cmpPreLi digPtr expPtr dig exp F)
      (cmpJoin digPtr expPtr v dig exp F) := by
  let G : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion digPtr dig ** bytesRegion expPtr exp **
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29) ** F
  have hG : G.pcFree := by pcf; exact hF
  -- index j: LI a0, v
  have hli : ∀ v10,
      cpsTripleWithin 1 (pc j) (pc (j + 1)) rhvCode
        (G ** (.x10 ↦ᵣ v10))
        ((.x10 ↦ᵣ v) ** G) := by
    intro v10
    have h0 := li_spec_gen_within .x10 v10 v (pc j) (by decide)
    have h1 := cpsTripleWithin_extend_code
      (mem_at j (.LI .x10 v) (pc j) rfl hj hins) h0
    rw [pc_succ j] at h1
    have hFr := cpsTripleWithin_frameR G hG h1
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hliOwn := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10) hli
  -- index j+1: unconditional J to the epilogue join
  have hjal0 := jal_x0_spec_gen_within off (pc (j + 1))
  have hjal := cpsTripleWithin_extend_code
    (mem_at (j + 1) (.JAL .x0 off) (pc (j + 1)) rfl hj1 hins1) hjal0
  rw [hjmp] at hjal
  have hjalF := cpsTripleWithin_frameR ((.x10 ↦ᵣ v) ** G)
    (pcFree_sepConj pcFree_regIs hG) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hliOwn hjalW
  refine cpsTripleWithin_weaken ?_ ?_ c
  · intro h hp; simp only [cmpPreLi, G] at hp ⊢; xperm_chunked hp
  · intro h hq; simp only [cmpJoin, G] at hq ⊢; xperm_chunked hq

/-- `li a0, 0; j +16` at indices 26–27 (the match verdict). -/
theorem rhv_match_join
    (digPtr expPtr : Word) (dig exp : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 26) (pc 31) rhvCode
      (cmpPreLi digPtr expPtr dig exp F)
      (cmpJoin digPtr expPtr (0 : Word) dig exp F) :=
  rhv_verdict_join digPtr expPtr dig exp 26 (0 : Word) (16 : BitVec 21)
    (by rw [rhvProgL_len]; norm_num) (by decide)
    (by rw [rhvProgL_len]; norm_num) (by decide)
    pc_jal_match_join F hF

/-- `li a0, 1; j +8` at indices 28–29 (the mismatch verdict). -/
theorem rhv_mismatch_join
    (digPtr expPtr : Word) (dig exp : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 28) (pc 31) rhvCode
      (cmpPreLi digPtr expPtr dig exp F)
      (cmpJoin digPtr expPtr (1 : Word) dig exp F) :=
  rhv_verdict_join digPtr expPtr dig exp 28 (1 : Word) (8 : BitVec 21)
    (by rw [rhvProgL_len]; norm_num) (by decide)
    (by rw [rhvProgL_len]; norm_num) (by decide)
    pc_jal_mismatch_join F hF

end EvmAsm.Codegen.RequestsHashVerifyCmp
