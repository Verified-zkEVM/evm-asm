/-
  Extension path-nibble compare loop (#11799): pc162→pc170.

  Top-tested countdown on x29 (remaining):
    BEQ rem,0 → pc170 match exit
    LBU buf; LBU path; BNE mismatch → pc297
    ADDI buf+1; ADDI path+1; ADDI rem-1; JAL → pc162

  Domain: HP segment nibbles equal path nibbles (exact match).
-/
import EvmAsm.Codegen.Programs.MptWalkExtPostHp
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.LoopFuel

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private theorem signExtend12_1c : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem signExtend12_m1c : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
private theorem ofNat_zero : BitVec.ofNat 64 0 = (0 : Word) := by decide
private theorem one_plus_neg1 : (1 : Word) + (-1 : Word) = 0 := by decide

private theorem beq_cmp_exit_off :
    pc 162 + signExtend13 (32 : BitVec 13) = pc 170 := by
  unfold pc walkB signExtend13; decide

/-- Mismatch BNE lands at pc297 (status-1), not pc300. -/
private theorem bne_cmp_mis_off :
    pc 165 + signExtend13 (528 : BitVec 13) = pc 297 := by
  unfold pc walkB signExtend13; decide

private theorem jal_cmp_back_off :
    pc 169 + signExtend21 (-28 : BitVec 21) = pc 162 := by
  unfold pc walkB
  rw [show signExtend21 (-28 : BitVec 21) = (-28 : Word) from by decide]
  bv_omega

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

/-- Compare-loop invariant at header pc162. -/
def extCmpInv (bufBase pathCurBase : Word) (k done : Nat)
    (bufBytes pathSeg : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
  (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
  (.x29 ↦ᵣ BitVec.ofNat 64 k) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bufBase bufBytes **
  bytesRegion pathCurBase pathSeg **
  (regOwn .x30 ** regOwn .x31) ** F

/-- Match exit at pc170. -/
def extCmpMatch (bufBase pathCurBase : Word) (count : Nat)
    (bufBytes pathSeg : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 count)) **
  (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 count)) **
  (.x29 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bufBase bufBytes **
  bytesRegion pathCurBase pathSeg **
  (regOwn .x30 ** regOwn .x31) ** F

/-! ## Exit when remaining = 0 -/

theorem ext_cmp_exit_zero
    (bufBase pathCurBase : Word) (count : Nat)
    (bufBytes pathSeg : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 162) (pc 170) fullCode
      (extCmpInv bufBase pathCurBase 0 count bufBytes pathSeg F)
      (extCmpMatch bufBase pathCurBase count bufBytes pathSeg F) := by
  have hbr0 := beq_spec_gen_within .x29 .x0 (32 : BitVec 13)
    (0 : Word) (0 : Word) (pc 162)
  rw [beq_cmp_exit_off, show pc 162 + 4 = pc 163 from pc_succ 162] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 162) 162 (.BEQ .x29 .x0 (32 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have ht := cpsBranchWithin_takenStripPure2 hbr
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  let G : Assertion :=
    (.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 count)) **
    (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 count)) **
    bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg **
    (regOwn .x30 ** regOwn .x31) ** F
  have hG : G.pcFree := by pcf; exact hF
  have htF := cpsTripleWithin_frameR G hG ht
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [extCmpInv, ofNat_zero, G] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      simp only [extCmpMatch, G] at hq ⊢
      xperm_chunked hq)
    htF

/-! ## One matching step (remaining = k+1 → k) -/

set_option maxRecDepth 8000 in
theorem ext_cmp_step
    (bufBase pathCurBase : Word) (k done : Nat)
    (bufBytes pathSeg : List (BitVec 8))
    (hbuf : done < bufBytes.length)
    (hpath : done < pathSeg.length)
    (hmatch : bufBytes[done]'hbuf = pathSeg[done]'hpath)
    (hbufAlign : bufBase.toNat % 8 = 0)
    (hpathAlign : pathCurBase.toNat % 8 = 0)
    (hbufOver : bufBase.toNat + done < 2 ^ 64)
    (hpathOver : pathCurBase.toNat + done < 2 ^ 64)
    (hkbound : k + 1 < 2 ^ 64)
    (hvalidB : isValidByteAccess (bufBase + BitVec.ofNat 64 done) = true)
    (hvalidP : isValidByteAccess (pathCurBase + BitVec.ofNat 64 done) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 162) (pc 162) fullCode
      (extCmpInv bufBase pathCurBase (k + 1) done bufBytes pathSeg F)
      (extCmpInv bufBase pathCurBase k (done + 1) bufBytes pathSeg F) := by
  have hne := word_ofNat_succ_ne_zero k hkbound
  -- Stable frame through the whole step (no x7/x28/x29/x0/bytes/x30/x31)
  let Frest : Assertion := F
  have hFrest : Frest.pcFree := hF
  -- BEQ ntaken
  have hbr0 := beq_spec_gen_within .x29 .x0 (32 : BitVec 13)
    (BitVec.ofNat 64 (k + 1)) (0 : Word) (pc 162)
  rw [beq_cmp_exit_off, show pc 162 + 4 = pc 163 from pc_succ 162] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 162) 162 (.BEQ .x29 .x0 (32 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  have hbeq := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
     (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
     bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg **
     (regOwn .x30 ** regOwn .x31) ** Frest)
    (by pcf; exact hFrest) hnt
  -- LBU buf: of_forall peels x30 rightmost
  have hlbuB : ∀ v30,
      cpsTripleWithin 1 (pc 163) (pc 164) fullCode
        (((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
          bytesRegion bufBase bufBytes **
          (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion pathCurBase pathSeg ** regOwn .x31 ** Frest) **
         (.x30 ↦ᵣ v30))
        (((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
          (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
          bytesRegion bufBase bufBytes **
          (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion pathCurBase pathSeg ** regOwn .x31 ** Frest)) := by
    intro v30
    have hlbu := bytesRegion_lbu_within .x30 .x7 bufBase v30 (pc 163)
      bufBytes done (by decide) hbufAlign hbuf hbufOver hvalidB
    have hlbuE := cpsTripleWithin_extend_code
      (walkMem (pc 163) 163 (.LBU .x30 .x7 (0 : BitVec 12))
        (by decide) (by unfold pc walkB; decide) rfl) hlbu
    rw [pc_succ 163] at hlbuE
    have hFr := cpsTripleWithin_frameR
      ((.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
       (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion pathCurBase pathSeg ** regOwn .x31 ** Frest)
      (by pcf; exact hFrest) hlbuE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuBown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x30) hlbuB
  -- LBU path: peel x31
  have hlbuP : ∀ v31,
      cpsTripleWithin 1 (pc 164) (pc 165) fullCode
        (((.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
          bytesRegion pathCurBase pathSeg **
          (.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
          (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion bufBase bufBytes ** Frest) **
         (.x31 ↦ᵣ v31))
        (((.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
          (.x31 ↦ᵣ ((pathSeg[done]'hpath).zeroExtend 64)) **
          bytesRegion pathCurBase pathSeg **
          (.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
          (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion bufBase bufBytes ** Frest)) := by
    intro v31
    have hlbu := bytesRegion_lbu_within .x31 .x28 pathCurBase v31 (pc 164)
      pathSeg done (by decide) hpathAlign hpath hpathOver hvalidP
    have hlbuE := cpsTripleWithin_extend_code
      (walkMem (pc 164) 164 (.LBU .x31 .x28 (0 : BitVec 12))
        (by decide) (by unfold pc walkB; decide) rfl) hlbu
    rw [pc_succ 164] at hlbuE
    have hFr := cpsTripleWithin_frameR
      ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
       (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
       (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion bufBase bufBytes ** Frest)
      (by pcf; exact hFrest) hlbuE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuPown := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31) hlbuP
  -- BNE match
  have heqW :
      (bufBytes[done]'hbuf).zeroExtend 64 = (pathSeg[done]'hpath).zeroExtend 64 := by
    simp only [hmatch]
  have hbrm0 := bne_spec_gen_within .x30 .x31 (528 : BitVec 13)
    ((bufBytes[done]'hbuf).zeroExtend 64)
    ((pathSeg[done]'hpath).zeroExtend 64) (pc 165)
  rw [bne_cmp_mis_off, show pc 165 + 4 = pc 166 from pc_succ 165] at hbrm0
  have hbrm := cpsBranchWithin_extend_code
    (walkMem (pc 165) 165 (.BNE .x30 .x31 (528 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbrm0
  have hntm := cpsBranchWithin_ntakenStripPure2 hbrm
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 heqW)
  have hntmF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done)) **
     (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
     (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg ** Frest)
    (by pcf; exact hFrest) hntm
  -- ADDIs
  have hadd70 := addi_spec_gen_same_within .x7 (bufBase + BitVec.ofNat 64 done)
    (1 : BitVec 12) (pc 166) (by decide)
  have hadd7 := cpsTripleWithin_extend_code
    (walkMem (pc 166) 166 (.ADDI .x7 .x7 (1 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hadd70
  rw [pc_succ 166, signExtend12_1c] at hadd7
  have hadd7F := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done)) **
     (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
     (.x31 ↦ᵣ ((pathSeg[done]'hpath).zeroExtend 64)) **
     bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg ** Frest)
    (by pcf; exact hFrest) hadd7
  have hadd280 := addi_spec_gen_same_within .x28 (pathCurBase + BitVec.ofNat 64 done)
    (1 : BitVec 12) (pc 167) (by decide)
  have hadd28 := cpsTripleWithin_extend_code
    (walkMem (pc 167) 167 (.ADDI .x28 .x28 (1 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hadd280
  rw [pc_succ 167, signExtend12_1c] at hadd28
  have hadd28F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x29 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
     (.x31 ↦ᵣ ((pathSeg[done]'hpath).zeroExtend 64)) **
     bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg ** Frest)
    (by pcf; exact hFrest) hadd28
  have hadd290 := addi_spec_gen_same_within .x29 (BitVec.ofNat 64 (k + 1))
    (-1 : BitVec 12) (pc 168) (by decide)
  have hadd29 := cpsTripleWithin_extend_code
    (walkMem (pc 168) 168 (.ADDI .x29 .x29 (-1 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hadd290
  rw [pc_succ 168, signExtend12_m1c] at hadd29
  have hadd29F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
     (.x31 ↦ᵣ ((pathSeg[done]'hpath).zeroExtend 64)) **
     bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg ** Frest)
    (by pcf; exact hFrest) hadd29
  -- JAL back
  have hjal0 := jal_x0_spec_gen_within (-28 : BitVec 21) (pc 169)
  have hjal := cpsTripleWithin_extend_code
    (walkMem (pc 169) 169 (.JAL .x0 (-28 : BitVec 21))
      (by decide) (by unfold pc walkB; decide) rfl) hjal0
  rw [jal_cmp_back_off] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x29 ↦ᵣ (BitVec.ofNat 64 (k + 1) + (-1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
     (.x31 ↦ᵣ ((pathSeg[done]'hpath).zeroExtend 64)) **
     bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg ** Frest)
    (by pcf; exact hFrest) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  -- Compose
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hbeq hlbuBown
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0 hlbuPown
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hntmF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hadd7F
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 hadd28F
  have c012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 hadd29F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012345 hjalW
  -- Rewrite cursors + drop x30/x31 → owns
  have hcur7 := cursor_succ bufBase done
  have hcur28 := cursor_succ pathCurBase done
  have hrem := cnt_step_down k
  have c' : cpsTripleWithin 8 (pc 162) (pc 162) fullCode
      (extCmpInv bufBase pathCurBase (k + 1) done bufBytes pathSeg F)
      ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 (done + 1))) **
       (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 (done + 1))) **
       (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
       (.x31 ↦ᵣ ((pathSeg[done]'hpath).zeroExtend 64)) **
       bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg ** F) := by
    refine cpsTripleWithin_weaken ?_ ?_ c
    · intro h hp; simp only [extCmpInv] at hp ⊢; xperm_chunked hp
    · intro h hq
      simp only [hcur7, hcur28, hrem] at hq
      xperm_chunked hq
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ c'
  intro h hq
  have hq1 :
      (((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 (done + 1))) **
        (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 (done + 1))) **
        (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg ** F) **
       ((.x30 ↦ᵣ ((bufBytes[done]'hbuf).zeroExtend 64)) **
        (.x31 ↦ᵣ ((pathSeg[done]'hpath).zeroExtend 64)))) h := by
    xperm_chunked hq
  have hq2 :=
    sepConj_mono_right
      (fun h' hx =>
        sepConj_mono
          (regIs_implies_regOwn (r := .x30))
          (regIs_implies_regOwn (r := .x31)) h' hx)
      h hq1
  simp only [extCmpInv] at hq2 ⊢
  xperm_chunked hq2

/-- Exact match over `count` nibbles. -/
def ExtPathMatch (bufBytes pathSeg : List (BitVec 8)) (count : Nat) : Prop :=
  ∃ (hb : count ≤ bufBytes.length) (hp : count ≤ pathSeg.length),
    ∀ i : Nat, (hi : i < count) →
      bufBytes[i]'(Nat.lt_of_lt_of_le hi hb) =
        pathSeg[i]'(Nat.lt_of_lt_of_le hi hp)

/-! ## Full match loop -/

theorem ext_cmp_loop_match
    (bufBase pathCurBase : Word) (count : Nat)
    (bufBytes pathSeg : List (BitVec 8))
    (hmatch : ExtPathMatch bufBytes pathSeg count)
    (hbufAlign : bufBase.toNat % 8 = 0)
    (hpathAlign : pathCurBase.toNat % 8 = 0)
    (hbufOver : ∀ d, d < count → bufBase.toNat + d < 2 ^ 64)
    (hpathOver : ∀ d, d < count → pathCurBase.toNat + d < 2 ^ 64)
    (hcount : count < 2 ^ 64)
    (hvalidB : ∀ d, d < count →
      isValidByteAccess (bufBase + BitVec.ofNat 64 d) = true)
    (hvalidP : ∀ d, d < count →
      isValidByteAccess (pathCurBase + BitVec.ofNat 64 d) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (count * 8 + 1) (pc 162) (pc 170) fullCode
      (extCmpInv bufBase pathCurBase count 0 bufBytes pathSeg F)
      (extCmpMatch bufBase pathCurBase count bufBytes pathSeg F) := by
  suffices h : ∀ n, n ≤ count →
      cpsTripleWithin (n * 8 + 1) (pc 162) (pc 170) fullCode
        (extCmpInv bufBase pathCurBase n (count - n) bufBytes pathSeg F)
        (extCmpMatch bufBase pathCurBase count bufBytes pathSeg F) by
    simpa [Nat.sub_self] using h count (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro _
    simpa [Nat.sub_zero] using
      ext_cmp_exit_zero bufBase pathCurBase count bufBytes pathSeg F hF
  | succ k ih =>
    intro hk
    have hklt : k < count := Nat.lt_of_succ_le hk
    obtain ⟨hbLen, hpLen, hbytes⟩ := hmatch
    have hstep := ext_cmp_step bufBase pathCurBase k (count - (k + 1))
      bufBytes pathSeg
      (by omega) (by omega)
      (hbytes (count - (k + 1)) (by omega))
      hbufAlign hpathAlign
      (hbufOver _ (by omega)) (hpathOver _ (by omega))
      (by omega)
      (hvalidB _ (by omega)) (hvalidP _ (by omega))
      F hF
    have hih := ih (Nat.le_of_lt hklt)
    have hdoneEq : count - (k + 1) + 1 = count - k := by omega
    have hstep' : cpsTripleWithin 8 (pc 162) (pc 162) fullCode
        (extCmpInv bufBase pathCurBase (k + 1) (count - (k + 1)) bufBytes pathSeg F)
        (extCmpInv bufBase pathCurBase k (count - k) bufBytes pathSeg F) := by
      convert hstep using 1; simp only [extCmpInv, hdoneEq]
    have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
      hstep' hih
    convert c using 1; omega

/-- From setup regs through match exit. -/
theorem ext_cmp_setup_to_match
    (bufBase pathCurBase countW : Word)
    (bufBytes pathSeg : List (BitVec 8))
    (hmatch : ExtPathMatch bufBytes pathSeg countW.toNat)
    (hbufAlign : bufBase.toNat % 8 = 0)
    (hpathAlign : pathCurBase.toNat % 8 = 0)
    (hbufOver : ∀ d, d < countW.toNat → bufBase.toNat + d < 2 ^ 64)
    (hpathOver : ∀ d, d < countW.toNat → pathCurBase.toNat + d < 2 ^ 64)
    (hcount : countW.toNat < 2 ^ 64)
    (hvalidB : ∀ d, d < countW.toNat →
      isValidByteAccess (bufBase + BitVec.ofNat 64 d) = true)
    (hvalidP : ∀ d, d < countW.toNat →
      isValidByteAccess (pathCurBase + BitVec.ofNat 64 d) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (countW.toNat * 8 + 1) (pc 162) (pc 170) fullCode
      ((.x7 ↦ᵣ bufBase) ** (.x28 ↦ᵣ pathCurBase) **
       (.x29 ↦ᵣ countW) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg **
       (regOwn .x30 ** regOwn .x31) ** F)
      (extCmpMatch bufBase pathCurBase countW.toNat bufBytes pathSeg F) := by
  have hloop := ext_cmp_loop_match bufBase pathCurBase countW.toNat
    bufBytes pathSeg hmatch hbufAlign hpathAlign hbufOver hpathOver
    hcount hvalidB hvalidP F hF
  refine cpsTripleWithin_weaken ?_ (fun _ hq => hq) hloop
  intro h hp
  have hb0 : bufBase + BitVec.ofNat 64 0 = bufBase := by
    rw [ofNat_zero]; exact BitVec.add_zero _
  have hp0 : pathCurBase + BitVec.ofNat 64 0 = pathCurBase := by
    rw [ofNat_zero]; exact BitVec.add_zero _
  have hcW : BitVec.ofNat 64 countW.toNat = countW := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt countW.isLt
  have hgoal :
      ((.x7 ↦ᵣ (bufBase + BitVec.ofNat 64 0)) **
       (.x28 ↦ᵣ (pathCurBase + BitVec.ofNat 64 0)) **
       (.x29 ↦ᵣ BitVec.ofNat 64 countW.toNat) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion bufBase bufBytes ** bytesRegion pathCurBase pathSeg **
       (regOwn .x30 ** regOwn .x31) ** F) h := by
    simp only [hb0, hp0, hcW]
    xperm_chunked hp
  simpa only [extCmpInv] using hgoal

end EvmAsm.Codegen.MptWalkSpec
