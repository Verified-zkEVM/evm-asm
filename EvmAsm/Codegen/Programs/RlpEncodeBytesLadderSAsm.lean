/-
  EvmAsm.Codegen.Programs.RlpEncodeBytesLadderSAsm

  **The length-of-length byte-count ladder** of `rlp_encode_bytes`, instructions
  [30]-[51] — `rebBase+120 → rebBase+208`.  Its own module because the eight arms
  come to ~850 lines and `RlpEncodeBytesSAsm.lean` still has the loops, the
  dispatch and three tails to hold; the precedent for splitting one routine
  across modules is `WithdrawalDecodeClose` → `Close2..5`.

  ## Why eight arms and not one folded lemma

  The ladder is a seven-way `BLTU` chain against `256 << 8k`, every arm jumping
  to the same join point [52].  It is **not** a loop, so there is nothing to
  induct over, and it cannot be folded into a generic "one ladder step" lemma:
  each step needs its own *concrete* address, which is what lets `runBlock`
  discharge code membership by evaluation (`rebBase` is the concrete numeral
  `GuestAddrs.rlp_encode_bytes`).  A lemma generic over the step address would
  leave membership unprovable.  The same constraint forces the routine's two
  payload copy loops apart.

  The arms are mechanically uniform, so they were generated rather than typed:
  arm `k` differs only in the `x29` comparand (`2^(8k)`), the `BLTU` offset
  (`80 - 12(k-1)`) and the addresses (`BLTU k` at `rebBase + 128 + 12(k-1)`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpEncodeBytesSAsm

namespace EvmAsm.Codegen

namespace RlpEncodeBytesSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpListEncodedSizeSAsm (u64ByteLen)

/-- `BitVec.ult` against a concrete bound is the `toNat` comparison. -/
private theorem ult_of_lt (v b : Word) (h : v.toNat < b.toNat) :
    BitVec.ult v b = true := by
  simp only [BitVec.ult, decide_eq_true_eq]
  omega

set_option maxRecDepth 8000 in
/-- **Ladder arm 1**: the first 0 `BLTU`s fall through and the 1th is taken. -/
private theorem rebLadder_bc1 (len v28 v29 : Word) (hlo : 1 ≤ len.toNat) (hhi : len.toNat < 256) :
    cpsTripleWithin 3 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 1 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + signExtend13 (80 : BitVec 13) = rebBase + 208 from by
        rw [show signExtend13 (80 : BitVec 13) = (80 : Word) from by decide]
        bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb10 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hne := ((sepConj_pure_right _).1 hpure).2
      exact hne (ult_of_lt len (256 : Word) (by
        rw [show (256 : Word).toNat = 256 from by decide]; omega))))
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 3 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (256 : Word))) from by
      (runBlock hL1 hL2 hb1))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 1 = (1 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1

set_option maxRecDepth 8000 in
/-- **Ladder arm 2**: the first 1 `BLTU`s fall through and the 2th is taken. -/
private theorem rebLadder_bc2 (len v28 v29 : Word) (hlo : 256 ≤ len.toNat) (hhi : len.toNat < 65536) :
    cpsTripleWithin 6 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 2 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + 4 = rebBase + 132 from by bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb10 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (256 : Word).toNat = 256 from by decide] at hult
      omega))
  have hL2a := li_spec_gen_within .x28 (1 : Word) (2 : Word) (rebBase + 132) (by decide)
  rw [show rebBase + 132 + 4 = rebBase + 136 from by bv_omega] at hL2a
  have hS2 := slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6)
    (rebBase + 136) (by decide)
  rw [show rebBase + 136 + 4 = rebBase + 140 from by bv_omega,
      show (256 : Word) <<< (8 : BitVec 6).toNat = (65536 : Word) from by decide] at hS2
  have hb20 := bltu_spec_gen_within .x6 .x29 (68 : BitVec 13) len (65536 : Word)
    (rebBase + 140)
  rw [show rebBase + 140 + signExtend13 (68 : BitVec 13) = rebBase + 208 from by
        rw [show signExtend13 (68 : BitVec 13) = (68 : Word) from by decide]
        bv_omega] at hb20
  have hb2 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb20 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hne := ((sepConj_pure_right _).1 hpure).2
      exact hne (ult_of_lt len (65536 : Word) (by
        rw [show (65536 : Word).toNat = 65536 from by decide]; omega))))
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 6 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (2 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (65536 : Word))) from by
      (runBlock hL1 hL2 hb1 hL2a hS2 hb2))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 2 = (2 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1

set_option maxRecDepth 8000 in
/-- **Ladder arm 3**: the first 2 `BLTU`s fall through and the 3th is taken. -/
private theorem rebLadder_bc3 (len v28 v29 : Word) (hlo : 65536 ≤ len.toNat) (hhi : len.toNat < 16777216) :
    cpsTripleWithin 9 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 3 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + 4 = rebBase + 132 from by bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb10 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (256 : Word).toNat = 256 from by decide] at hult
      omega))
  have hL2a := li_spec_gen_within .x28 (1 : Word) (2 : Word) (rebBase + 132) (by decide)
  rw [show rebBase + 132 + 4 = rebBase + 136 from by bv_omega] at hL2a
  have hS2 := slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6)
    (rebBase + 136) (by decide)
  rw [show rebBase + 136 + 4 = rebBase + 140 from by bv_omega,
      show (256 : Word) <<< (8 : BitVec 6).toNat = (65536 : Word) from by decide] at hS2
  have hb20 := bltu_spec_gen_within .x6 .x29 (68 : BitVec 13) len (65536 : Word)
    (rebBase + 140)
  rw [show rebBase + 140 + 4 = rebBase + 144 from by bv_omega] at hb20
  have hb2 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb20 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (65536 : Word).toNat = 65536 from by decide] at hult
      omega))
  have hL3a := li_spec_gen_within .x28 (2 : Word) (3 : Word) (rebBase + 144) (by decide)
  rw [show rebBase + 144 + 4 = rebBase + 148 from by bv_omega] at hL3a
  have hS3 := slli_spec_gen_same_within .x29 (65536 : Word) (8 : BitVec 6)
    (rebBase + 148) (by decide)
  rw [show rebBase + 148 + 4 = rebBase + 152 from by bv_omega,
      show (65536 : Word) <<< (8 : BitVec 6).toNat = (16777216 : Word) from by decide] at hS3
  have hb30 := bltu_spec_gen_within .x6 .x29 (56 : BitVec 13) len (16777216 : Word)
    (rebBase + 152)
  rw [show rebBase + 152 + signExtend13 (56 : BitVec 13) = rebBase + 208 from by
        rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]
        bv_omega] at hb30
  have hb3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb30 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hne := ((sepConj_pure_right _).1 hpure).2
      exact hne (ult_of_lt len (16777216 : Word) (by
        rw [show (16777216 : Word).toNat = 16777216 from by decide]; omega))))
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 9 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (3 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (16777216 : Word))) from by
      (runBlock hL1 hL2 hb1 hL2a hS2 hb2 hL3a hS3 hb3))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 3 = (3 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1

set_option maxRecDepth 8000 in
/-- **Ladder arm 4**: the first 3 `BLTU`s fall through and the 4th is taken. -/
private theorem rebLadder_bc4 (len v28 v29 : Word) (hlo : 16777216 ≤ len.toNat) (hhi : len.toNat < 4294967296) :
    cpsTripleWithin 12 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 4 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + 4 = rebBase + 132 from by bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb10 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (256 : Word).toNat = 256 from by decide] at hult
      omega))
  have hL2a := li_spec_gen_within .x28 (1 : Word) (2 : Word) (rebBase + 132) (by decide)
  rw [show rebBase + 132 + 4 = rebBase + 136 from by bv_omega] at hL2a
  have hS2 := slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6)
    (rebBase + 136) (by decide)
  rw [show rebBase + 136 + 4 = rebBase + 140 from by bv_omega,
      show (256 : Word) <<< (8 : BitVec 6).toNat = (65536 : Word) from by decide] at hS2
  have hb20 := bltu_spec_gen_within .x6 .x29 (68 : BitVec 13) len (65536 : Word)
    (rebBase + 140)
  rw [show rebBase + 140 + 4 = rebBase + 144 from by bv_omega] at hb20
  have hb2 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb20 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (65536 : Word).toNat = 65536 from by decide] at hult
      omega))
  have hL3a := li_spec_gen_within .x28 (2 : Word) (3 : Word) (rebBase + 144) (by decide)
  rw [show rebBase + 144 + 4 = rebBase + 148 from by bv_omega] at hL3a
  have hS3 := slli_spec_gen_same_within .x29 (65536 : Word) (8 : BitVec 6)
    (rebBase + 148) (by decide)
  rw [show rebBase + 148 + 4 = rebBase + 152 from by bv_omega,
      show (65536 : Word) <<< (8 : BitVec 6).toNat = (16777216 : Word) from by decide] at hS3
  have hb30 := bltu_spec_gen_within .x6 .x29 (56 : BitVec 13) len (16777216 : Word)
    (rebBase + 152)
  rw [show rebBase + 152 + 4 = rebBase + 156 from by bv_omega] at hb30
  have hb3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb30 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (16777216 : Word).toNat = 16777216 from by decide] at hult
      omega))
  have hL4a := li_spec_gen_within .x28 (3 : Word) (4 : Word) (rebBase + 156) (by decide)
  rw [show rebBase + 156 + 4 = rebBase + 160 from by bv_omega] at hL4a
  have hS4 := slli_spec_gen_same_within .x29 (16777216 : Word) (8 : BitVec 6)
    (rebBase + 160) (by decide)
  rw [show rebBase + 160 + 4 = rebBase + 164 from by bv_omega,
      show (16777216 : Word) <<< (8 : BitVec 6).toNat = (4294967296 : Word) from by decide] at hS4
  have hb40 := bltu_spec_gen_within .x6 .x29 (44 : BitVec 13) len (4294967296 : Word)
    (rebBase + 164)
  rw [show rebBase + 164 + signExtend13 (44 : BitVec 13) = rebBase + 208 from by
        rw [show signExtend13 (44 : BitVec 13) = (44 : Word) from by decide]
        bv_omega] at hb40
  have hb4 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb40 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hne := ((sepConj_pure_right _).1 hpure).2
      exact hne (ult_of_lt len (4294967296 : Word) (by
        rw [show (4294967296 : Word).toNat = 4294967296 from by decide]; omega))))
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 12 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (4 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (4294967296 : Word))) from by
      (runBlock hL1 hL2 hb1 hL2a hS2 hb2 hL3a hS3 hb3 hL4a hS4 hb4))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 4 = (4 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1

set_option maxRecDepth 8000 in
/-- **Ladder arm 5**: the first 4 `BLTU`s fall through and the 5th is taken. -/
private theorem rebLadder_bc5 (len v28 v29 : Word) (hlo : 4294967296 ≤ len.toNat) (hhi : len.toNat < 1099511627776) :
    cpsTripleWithin 15 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 5 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + 4 = rebBase + 132 from by bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb10 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (256 : Word).toNat = 256 from by decide] at hult
      omega))
  have hL2a := li_spec_gen_within .x28 (1 : Word) (2 : Word) (rebBase + 132) (by decide)
  rw [show rebBase + 132 + 4 = rebBase + 136 from by bv_omega] at hL2a
  have hS2 := slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6)
    (rebBase + 136) (by decide)
  rw [show rebBase + 136 + 4 = rebBase + 140 from by bv_omega,
      show (256 : Word) <<< (8 : BitVec 6).toNat = (65536 : Word) from by decide] at hS2
  have hb20 := bltu_spec_gen_within .x6 .x29 (68 : BitVec 13) len (65536 : Word)
    (rebBase + 140)
  rw [show rebBase + 140 + 4 = rebBase + 144 from by bv_omega] at hb20
  have hb2 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb20 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (65536 : Word).toNat = 65536 from by decide] at hult
      omega))
  have hL3a := li_spec_gen_within .x28 (2 : Word) (3 : Word) (rebBase + 144) (by decide)
  rw [show rebBase + 144 + 4 = rebBase + 148 from by bv_omega] at hL3a
  have hS3 := slli_spec_gen_same_within .x29 (65536 : Word) (8 : BitVec 6)
    (rebBase + 148) (by decide)
  rw [show rebBase + 148 + 4 = rebBase + 152 from by bv_omega,
      show (65536 : Word) <<< (8 : BitVec 6).toNat = (16777216 : Word) from by decide] at hS3
  have hb30 := bltu_spec_gen_within .x6 .x29 (56 : BitVec 13) len (16777216 : Word)
    (rebBase + 152)
  rw [show rebBase + 152 + 4 = rebBase + 156 from by bv_omega] at hb30
  have hb3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb30 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (16777216 : Word).toNat = 16777216 from by decide] at hult
      omega))
  have hL4a := li_spec_gen_within .x28 (3 : Word) (4 : Word) (rebBase + 156) (by decide)
  rw [show rebBase + 156 + 4 = rebBase + 160 from by bv_omega] at hL4a
  have hS4 := slli_spec_gen_same_within .x29 (16777216 : Word) (8 : BitVec 6)
    (rebBase + 160) (by decide)
  rw [show rebBase + 160 + 4 = rebBase + 164 from by bv_omega,
      show (16777216 : Word) <<< (8 : BitVec 6).toNat = (4294967296 : Word) from by decide] at hS4
  have hb40 := bltu_spec_gen_within .x6 .x29 (44 : BitVec 13) len (4294967296 : Word)
    (rebBase + 164)
  rw [show rebBase + 164 + 4 = rebBase + 168 from by bv_omega] at hb40
  have hb4 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb40 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (4294967296 : Word).toNat = 4294967296 from by decide] at hult
      omega))
  have hL5a := li_spec_gen_within .x28 (4 : Word) (5 : Word) (rebBase + 168) (by decide)
  rw [show rebBase + 168 + 4 = rebBase + 172 from by bv_omega] at hL5a
  have hS5 := slli_spec_gen_same_within .x29 (4294967296 : Word) (8 : BitVec 6)
    (rebBase + 172) (by decide)
  rw [show rebBase + 172 + 4 = rebBase + 176 from by bv_omega,
      show (4294967296 : Word) <<< (8 : BitVec 6).toNat = (1099511627776 : Word) from by decide] at hS5
  have hb50 := bltu_spec_gen_within .x6 .x29 (32 : BitVec 13) len (1099511627776 : Word)
    (rebBase + 176)
  rw [show rebBase + 176 + signExtend13 (32 : BitVec 13) = rebBase + 208 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]
        bv_omega] at hb50
  have hb5 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb50 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hne := ((sepConj_pure_right _).1 hpure).2
      exact hne (ult_of_lt len (1099511627776 : Word) (by
        rw [show (1099511627776 : Word).toNat = 1099511627776 from by decide]; omega))))
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 15 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (5 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (1099511627776 : Word))) from by
      (runBlock hL1 hL2 hb1 hL2a hS2 hb2 hL3a hS3 hb3 hL4a hS4 hb4 hL5a hS5 hb5))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 5 = (5 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1

set_option maxRecDepth 8000 in
/-- **Ladder arm 6**: the first 5 `BLTU`s fall through and the 6th is taken. -/
private theorem rebLadder_bc6 (len v28 v29 : Word) (hlo : 1099511627776 ≤ len.toNat) (hhi : len.toNat < 281474976710656) :
    cpsTripleWithin 18 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 6 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + 4 = rebBase + 132 from by bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb10 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (256 : Word).toNat = 256 from by decide] at hult
      omega))
  have hL2a := li_spec_gen_within .x28 (1 : Word) (2 : Word) (rebBase + 132) (by decide)
  rw [show rebBase + 132 + 4 = rebBase + 136 from by bv_omega] at hL2a
  have hS2 := slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6)
    (rebBase + 136) (by decide)
  rw [show rebBase + 136 + 4 = rebBase + 140 from by bv_omega,
      show (256 : Word) <<< (8 : BitVec 6).toNat = (65536 : Word) from by decide] at hS2
  have hb20 := bltu_spec_gen_within .x6 .x29 (68 : BitVec 13) len (65536 : Word)
    (rebBase + 140)
  rw [show rebBase + 140 + 4 = rebBase + 144 from by bv_omega] at hb20
  have hb2 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb20 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (65536 : Word).toNat = 65536 from by decide] at hult
      omega))
  have hL3a := li_spec_gen_within .x28 (2 : Word) (3 : Word) (rebBase + 144) (by decide)
  rw [show rebBase + 144 + 4 = rebBase + 148 from by bv_omega] at hL3a
  have hS3 := slli_spec_gen_same_within .x29 (65536 : Word) (8 : BitVec 6)
    (rebBase + 148) (by decide)
  rw [show rebBase + 148 + 4 = rebBase + 152 from by bv_omega,
      show (65536 : Word) <<< (8 : BitVec 6).toNat = (16777216 : Word) from by decide] at hS3
  have hb30 := bltu_spec_gen_within .x6 .x29 (56 : BitVec 13) len (16777216 : Word)
    (rebBase + 152)
  rw [show rebBase + 152 + 4 = rebBase + 156 from by bv_omega] at hb30
  have hb3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb30 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (16777216 : Word).toNat = 16777216 from by decide] at hult
      omega))
  have hL4a := li_spec_gen_within .x28 (3 : Word) (4 : Word) (rebBase + 156) (by decide)
  rw [show rebBase + 156 + 4 = rebBase + 160 from by bv_omega] at hL4a
  have hS4 := slli_spec_gen_same_within .x29 (16777216 : Word) (8 : BitVec 6)
    (rebBase + 160) (by decide)
  rw [show rebBase + 160 + 4 = rebBase + 164 from by bv_omega,
      show (16777216 : Word) <<< (8 : BitVec 6).toNat = (4294967296 : Word) from by decide] at hS4
  have hb40 := bltu_spec_gen_within .x6 .x29 (44 : BitVec 13) len (4294967296 : Word)
    (rebBase + 164)
  rw [show rebBase + 164 + 4 = rebBase + 168 from by bv_omega] at hb40
  have hb4 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb40 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (4294967296 : Word).toNat = 4294967296 from by decide] at hult
      omega))
  have hL5a := li_spec_gen_within .x28 (4 : Word) (5 : Word) (rebBase + 168) (by decide)
  rw [show rebBase + 168 + 4 = rebBase + 172 from by bv_omega] at hL5a
  have hS5 := slli_spec_gen_same_within .x29 (4294967296 : Word) (8 : BitVec 6)
    (rebBase + 172) (by decide)
  rw [show rebBase + 172 + 4 = rebBase + 176 from by bv_omega,
      show (4294967296 : Word) <<< (8 : BitVec 6).toNat = (1099511627776 : Word) from by decide] at hS5
  have hb50 := bltu_spec_gen_within .x6 .x29 (32 : BitVec 13) len (1099511627776 : Word)
    (rebBase + 176)
  rw [show rebBase + 176 + 4 = rebBase + 180 from by bv_omega] at hb50
  have hb5 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb50 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (1099511627776 : Word).toNat = 1099511627776 from by decide] at hult
      omega))
  have hL6a := li_spec_gen_within .x28 (5 : Word) (6 : Word) (rebBase + 180) (by decide)
  rw [show rebBase + 180 + 4 = rebBase + 184 from by bv_omega] at hL6a
  have hS6 := slli_spec_gen_same_within .x29 (1099511627776 : Word) (8 : BitVec 6)
    (rebBase + 184) (by decide)
  rw [show rebBase + 184 + 4 = rebBase + 188 from by bv_omega,
      show (1099511627776 : Word) <<< (8 : BitVec 6).toNat = (281474976710656 : Word) from by decide] at hS6
  have hb60 := bltu_spec_gen_within .x6 .x29 (20 : BitVec 13) len (281474976710656 : Word)
    (rebBase + 188)
  rw [show rebBase + 188 + signExtend13 (20 : BitVec 13) = rebBase + 208 from by
        rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]
        bv_omega] at hb60
  have hb6 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb60 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hne := ((sepConj_pure_right _).1 hpure).2
      exact hne (ult_of_lt len (281474976710656 : Word) (by
        rw [show (281474976710656 : Word).toNat = 281474976710656 from by decide]; omega))))
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 18 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (6 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (281474976710656 : Word))) from by
      (runBlock hL1 hL2 hb1 hL2a hS2 hb2 hL3a hS3 hb3 hL4a hS4 hb4 hL5a hS5 hb5 hL6a hS6 hb6))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 6 = (6 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1

set_option maxRecDepth 8000 in
/-- **Ladder arm 7**: the first 6 `BLTU`s fall through and the 7th is taken. -/
private theorem rebLadder_bc7 (len v28 v29 : Word) (hlo : 281474976710656 ≤ len.toNat) (hhi : len.toNat < 72057594037927936) :
    cpsTripleWithin 21 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 7 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + 4 = rebBase + 132 from by bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb10 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (256 : Word).toNat = 256 from by decide] at hult
      omega))
  have hL2a := li_spec_gen_within .x28 (1 : Word) (2 : Word) (rebBase + 132) (by decide)
  rw [show rebBase + 132 + 4 = rebBase + 136 from by bv_omega] at hL2a
  have hS2 := slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6)
    (rebBase + 136) (by decide)
  rw [show rebBase + 136 + 4 = rebBase + 140 from by bv_omega,
      show (256 : Word) <<< (8 : BitVec 6).toNat = (65536 : Word) from by decide] at hS2
  have hb20 := bltu_spec_gen_within .x6 .x29 (68 : BitVec 13) len (65536 : Word)
    (rebBase + 140)
  rw [show rebBase + 140 + 4 = rebBase + 144 from by bv_omega] at hb20
  have hb2 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb20 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (65536 : Word).toNat = 65536 from by decide] at hult
      omega))
  have hL3a := li_spec_gen_within .x28 (2 : Word) (3 : Word) (rebBase + 144) (by decide)
  rw [show rebBase + 144 + 4 = rebBase + 148 from by bv_omega] at hL3a
  have hS3 := slli_spec_gen_same_within .x29 (65536 : Word) (8 : BitVec 6)
    (rebBase + 148) (by decide)
  rw [show rebBase + 148 + 4 = rebBase + 152 from by bv_omega,
      show (65536 : Word) <<< (8 : BitVec 6).toNat = (16777216 : Word) from by decide] at hS3
  have hb30 := bltu_spec_gen_within .x6 .x29 (56 : BitVec 13) len (16777216 : Word)
    (rebBase + 152)
  rw [show rebBase + 152 + 4 = rebBase + 156 from by bv_omega] at hb30
  have hb3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb30 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (16777216 : Word).toNat = 16777216 from by decide] at hult
      omega))
  have hL4a := li_spec_gen_within .x28 (3 : Word) (4 : Word) (rebBase + 156) (by decide)
  rw [show rebBase + 156 + 4 = rebBase + 160 from by bv_omega] at hL4a
  have hS4 := slli_spec_gen_same_within .x29 (16777216 : Word) (8 : BitVec 6)
    (rebBase + 160) (by decide)
  rw [show rebBase + 160 + 4 = rebBase + 164 from by bv_omega,
      show (16777216 : Word) <<< (8 : BitVec 6).toNat = (4294967296 : Word) from by decide] at hS4
  have hb40 := bltu_spec_gen_within .x6 .x29 (44 : BitVec 13) len (4294967296 : Word)
    (rebBase + 164)
  rw [show rebBase + 164 + 4 = rebBase + 168 from by bv_omega] at hb40
  have hb4 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb40 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (4294967296 : Word).toNat = 4294967296 from by decide] at hult
      omega))
  have hL5a := li_spec_gen_within .x28 (4 : Word) (5 : Word) (rebBase + 168) (by decide)
  rw [show rebBase + 168 + 4 = rebBase + 172 from by bv_omega] at hL5a
  have hS5 := slli_spec_gen_same_within .x29 (4294967296 : Word) (8 : BitVec 6)
    (rebBase + 172) (by decide)
  rw [show rebBase + 172 + 4 = rebBase + 176 from by bv_omega,
      show (4294967296 : Word) <<< (8 : BitVec 6).toNat = (1099511627776 : Word) from by decide] at hS5
  have hb50 := bltu_spec_gen_within .x6 .x29 (32 : BitVec 13) len (1099511627776 : Word)
    (rebBase + 176)
  rw [show rebBase + 176 + 4 = rebBase + 180 from by bv_omega] at hb50
  have hb5 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb50 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (1099511627776 : Word).toNat = 1099511627776 from by decide] at hult
      omega))
  have hL6a := li_spec_gen_within .x28 (5 : Word) (6 : Word) (rebBase + 180) (by decide)
  rw [show rebBase + 180 + 4 = rebBase + 184 from by bv_omega] at hL6a
  have hS6 := slli_spec_gen_same_within .x29 (1099511627776 : Word) (8 : BitVec 6)
    (rebBase + 184) (by decide)
  rw [show rebBase + 184 + 4 = rebBase + 188 from by bv_omega,
      show (1099511627776 : Word) <<< (8 : BitVec 6).toNat = (281474976710656 : Word) from by decide] at hS6
  have hb60 := bltu_spec_gen_within .x6 .x29 (20 : BitVec 13) len (281474976710656 : Word)
    (rebBase + 188)
  rw [show rebBase + 188 + 4 = rebBase + 192 from by bv_omega] at hb60
  have hb6 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb60 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (281474976710656 : Word).toNat = 281474976710656 from by decide] at hult
      omega))
  have hL7a := li_spec_gen_within .x28 (6 : Word) (7 : Word) (rebBase + 192) (by decide)
  rw [show rebBase + 192 + 4 = rebBase + 196 from by bv_omega] at hL7a
  have hS7 := slli_spec_gen_same_within .x29 (281474976710656 : Word) (8 : BitVec 6)
    (rebBase + 196) (by decide)
  rw [show rebBase + 196 + 4 = rebBase + 200 from by bv_omega,
      show (281474976710656 : Word) <<< (8 : BitVec 6).toNat = (72057594037927936 : Word) from by decide] at hS7
  have hb70 := bltu_spec_gen_within .x6 .x29 (8 : BitVec 13) len (72057594037927936 : Word)
    (rebBase + 200)
  rw [show rebBase + 200 + signExtend13 (8 : BitVec 13) = rebBase + 208 from by
        rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]
        bv_omega] at hb70
  have hb7 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb70 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hne := ((sepConj_pure_right _).1 hpure).2
      exact hne (ult_of_lt len (72057594037927936 : Word) (by
        rw [show (72057594037927936 : Word).toNat = 72057594037927936 from by decide]; omega))))
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 21 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (7 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (72057594037927936 : Word))) from by
      (runBlock hL1 hL2 hb1 hL2a hS2 hb2 hL3a hS3 hb3 hL4a hS4 hb4 hL5a hS5 hb5 hL6a hS6 hb6 hL7a hS7 hb7))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 7 = (7 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1

set_option maxRecDepth 8000 in
/-- **Ladder arm 8**: every `BLTU` falls through, so `[51]` sets `x28 = 8` and the
    block ends by falling into `[52]`.  22 steps, not `3*8 = 24` — the arm has no
    branch of its own, which is why the uniform `3*bc` bound is an over-estimate
    here rather than an equality. -/
private theorem rebLadder_bc8 (len v28 v29 : Word) (hlo : 72057594037927936 ≤ len.toNat) :
    cpsTripleWithin 22 (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  have hbc : u64ByteLen len = 8 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have hL1 := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 120) (by decide)
  rw [show rebBase + 120 + 4 = rebBase + 124 from by bv_omega] at hL1
  have hL2 := li_spec_gen_within .x29 v29 (256 : Word) (rebBase + 124) (by decide)
  rw [show rebBase + 124 + 4 = rebBase + 128 from by bv_omega] at hL2
  have hb10 := bltu_spec_gen_within .x6 .x29 (80 : BitVec 13) len (256 : Word)
    (rebBase + 128)
  rw [show rebBase + 128 + 4 = rebBase + 132 from by bv_omega] at hb10
  have hb1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb10 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (256 : Word).toNat = 256 from by decide] at hult
      omega))
  have hL2a := li_spec_gen_within .x28 (1 : Word) (2 : Word) (rebBase + 132) (by decide)
  rw [show rebBase + 132 + 4 = rebBase + 136 from by bv_omega] at hL2a
  have hS2 := slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6)
    (rebBase + 136) (by decide)
  rw [show rebBase + 136 + 4 = rebBase + 140 from by bv_omega,
      show (256 : Word) <<< (8 : BitVec 6).toNat = (65536 : Word) from by decide] at hS2
  have hb20 := bltu_spec_gen_within .x6 .x29 (68 : BitVec 13) len (65536 : Word)
    (rebBase + 140)
  rw [show rebBase + 140 + 4 = rebBase + 144 from by bv_omega] at hb20
  have hb2 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb20 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (65536 : Word).toNat = 65536 from by decide] at hult
      omega))
  have hL3a := li_spec_gen_within .x28 (2 : Word) (3 : Word) (rebBase + 144) (by decide)
  rw [show rebBase + 144 + 4 = rebBase + 148 from by bv_omega] at hL3a
  have hS3 := slli_spec_gen_same_within .x29 (65536 : Word) (8 : BitVec 6)
    (rebBase + 148) (by decide)
  rw [show rebBase + 148 + 4 = rebBase + 152 from by bv_omega,
      show (65536 : Word) <<< (8 : BitVec 6).toNat = (16777216 : Word) from by decide] at hS3
  have hb30 := bltu_spec_gen_within .x6 .x29 (56 : BitVec 13) len (16777216 : Word)
    (rebBase + 152)
  rw [show rebBase + 152 + 4 = rebBase + 156 from by bv_omega] at hb30
  have hb3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb30 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (16777216 : Word).toNat = 16777216 from by decide] at hult
      omega))
  have hL4a := li_spec_gen_within .x28 (3 : Word) (4 : Word) (rebBase + 156) (by decide)
  rw [show rebBase + 156 + 4 = rebBase + 160 from by bv_omega] at hL4a
  have hS4 := slli_spec_gen_same_within .x29 (16777216 : Word) (8 : BitVec 6)
    (rebBase + 160) (by decide)
  rw [show rebBase + 160 + 4 = rebBase + 164 from by bv_omega,
      show (16777216 : Word) <<< (8 : BitVec 6).toNat = (4294967296 : Word) from by decide] at hS4
  have hb40 := bltu_spec_gen_within .x6 .x29 (44 : BitVec 13) len (4294967296 : Word)
    (rebBase + 164)
  rw [show rebBase + 164 + 4 = rebBase + 168 from by bv_omega] at hb40
  have hb4 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb40 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (4294967296 : Word).toNat = 4294967296 from by decide] at hult
      omega))
  have hL5a := li_spec_gen_within .x28 (4 : Word) (5 : Word) (rebBase + 168) (by decide)
  rw [show rebBase + 168 + 4 = rebBase + 172 from by bv_omega] at hL5a
  have hS5 := slli_spec_gen_same_within .x29 (4294967296 : Word) (8 : BitVec 6)
    (rebBase + 172) (by decide)
  rw [show rebBase + 172 + 4 = rebBase + 176 from by bv_omega,
      show (4294967296 : Word) <<< (8 : BitVec 6).toNat = (1099511627776 : Word) from by decide] at hS5
  have hb50 := bltu_spec_gen_within .x6 .x29 (32 : BitVec 13) len (1099511627776 : Word)
    (rebBase + 176)
  rw [show rebBase + 176 + 4 = rebBase + 180 from by bv_omega] at hb50
  have hb5 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb50 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (1099511627776 : Word).toNat = 1099511627776 from by decide] at hult
      omega))
  have hL6a := li_spec_gen_within .x28 (5 : Word) (6 : Word) (rebBase + 180) (by decide)
  rw [show rebBase + 180 + 4 = rebBase + 184 from by bv_omega] at hL6a
  have hS6 := slli_spec_gen_same_within .x29 (1099511627776 : Word) (8 : BitVec 6)
    (rebBase + 184) (by decide)
  rw [show rebBase + 184 + 4 = rebBase + 188 from by bv_omega,
      show (1099511627776 : Word) <<< (8 : BitVec 6).toNat = (281474976710656 : Word) from by decide] at hS6
  have hb60 := bltu_spec_gen_within .x6 .x29 (20 : BitVec 13) len (281474976710656 : Word)
    (rebBase + 188)
  rw [show rebBase + 188 + 4 = rebBase + 192 from by bv_omega] at hb60
  have hb6 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb60 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (281474976710656 : Word).toNat = 281474976710656 from by decide] at hult
      omega))
  have hL7a := li_spec_gen_within .x28 (6 : Word) (7 : Word) (rebBase + 192) (by decide)
  rw [show rebBase + 192 + 4 = rebBase + 196 from by bv_omega] at hL7a
  have hS7 := slli_spec_gen_same_within .x29 (281474976710656 : Word) (8 : BitVec 6)
    (rebBase + 196) (by decide)
  rw [show rebBase + 196 + 4 = rebBase + 200 from by bv_omega,
      show (281474976710656 : Word) <<< (8 : BitVec 6).toNat = (72057594037927936 : Word) from by decide] at hS7
  have hb70 := bltu_spec_gen_within .x6 .x29 (8 : BitVec 13) len (72057594037927936 : Word)
    (rebBase + 200)
  rw [show rebBase + 200 + 4 = rebBase + 204 from by bv_omega] at hb70
  have hb7 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb70 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hult := ((sepConj_pure_right _).1 hpure).2
      simp only [BitVec.ult, decide_eq_true_eq,
        show (72057594037927936 : Word).toNat = 72057594037927936 from by decide] at hult
      omega))
  have hL8a := li_spec_gen_within .x28 (7 : Word) (8 : Word) (rebBase + 204) (by decide)
  rw [show rebBase + 204 + 4 = rebBase + 208 from by bv_omega] at hL8a
  rw [hbc]
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 22 (rebBase + 120) (rebBase + 208) rebCode
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x6 : Reg) ↦ᵣ len))
        (((.x28 : Reg) ↦ᵣ (8 : Word)) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x29 : Reg) ↦ᵣ (72057594037927936 : Word))) from by
      (runBlock hL1 hL2 hb1 hL2a hS2 hb2 hL3a hS3 hb3 hL4a hS4 hb4 hL5a hS5 hb5 hL6a hS6 hb6 hL7a hS7 hb7 hL8a))
  · xperm_hyp hp
  · rw [show BitVec.ofNat 64 8 = (8 : Word) from by decide]
    have hp1 := sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x29)) h hp
    xperm_hyp hp1


/-! Range characterisations of `u64ByteLen`, hoisted to top level.  Inlining these
    into `rebLadder`'s eight-deep `by_cases` made `split_ifs` carry nine ambient
    hypotheses and blow the heartbeat limit; `maxHeartbeats` is prohibited here, so
    the fix is to run the tactic shallow. -/
private theorem u64ByteLen_eq_1 (v : Word) (h1 : 1 ≤ v.toNat)
    (h2 : v.toNat < 256) : u64ByteLen v = 1 := by
  unfold u64ByteLen
  split_ifs <;> omega

private theorem u64ByteLen_eq_2 (v : Word) (h1 : 256 ≤ v.toNat)
    (h2 : v.toNat < 65536) : u64ByteLen v = 2 := by
  unfold u64ByteLen
  split_ifs <;> omega

private theorem u64ByteLen_eq_3 (v : Word) (h1 : 65536 ≤ v.toNat)
    (h2 : v.toNat < 16777216) : u64ByteLen v = 3 := by
  unfold u64ByteLen
  split_ifs <;> omega

private theorem u64ByteLen_eq_4 (v : Word) (h1 : 16777216 ≤ v.toNat)
    (h2 : v.toNat < 4294967296) : u64ByteLen v = 4 := by
  unfold u64ByteLen
  split_ifs <;> omega

private theorem u64ByteLen_eq_5 (v : Word) (h1 : 4294967296 ≤ v.toNat)
    (h2 : v.toNat < 1099511627776) : u64ByteLen v = 5 := by
  unfold u64ByteLen
  split_ifs <;> omega

private theorem u64ByteLen_eq_6 (v : Word) (h1 : 1099511627776 ≤ v.toNat)
    (h2 : v.toNat < 281474976710656) : u64ByteLen v = 6 := by
  unfold u64ByteLen
  split_ifs <;> omega

private theorem u64ByteLen_eq_7 (v : Word) (h1 : 281474976710656 ≤ v.toNat)
    (h2 : v.toNat < 72057594037927936) : u64ByteLen v = 7 := by
  unfold u64ByteLen
  split_ifs <;> omega

private theorem u64ByteLen_eq_8 (v : Word) (h1 : 72057594037927936 ≤ v.toNat) :
    u64ByteLen v = 8 := by
  unfold u64ByteLen
  split_ifs <;> omega

set_option maxRecDepth 8000 in
/-- **The `bc` ladder** ([30]-[51]), `rebBase+120 → rebBase+208`: on entry `x6`
    holds the payload length, on exit `x28` holds its minimal byte count.

    Reached only from the long-form dispatch, so `56 ≤ len` — and that bound is
    load-bearing rather than incidental.  The ladder's first test is `len < 256`,
    which yields `bc = 1`, whereas `u64ByteLen 0 = 0`: ⚠️ **at `len = 0` the
    ladder and the model disagree.**  They agree on every reachable input only
    because the dispatch has already excluded `len < 56`.

    The step bound is `3 * bc`, exact for `bc ≤ 7` and a slight over-estimate at
    `bc = 8` (22 actual): that arm takes no branch of its own, it falls through
    all seven and lands on `[51]`. -/
theorem rebLadder (len v28 v29 : Word) (hlo : 56 ≤ len.toNat) :
    cpsTripleWithin (3 * u64ByteLen len) (rebBase + 120) (rebBase + 208) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (u64ByteLen len)) ** regOwn .x29) := by
  by_cases c1 : len.toNat < 256
  · have hbc := u64ByteLen_eq_1 len (by omega) (by omega)
    refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc1 len v28 v29 (by omega) (by omega))
    omega
  by_cases c2 : len.toNat < 65536
  · have hbc := u64ByteLen_eq_2 len (by omega) (by omega)
    refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc2 len v28 v29 (by omega) (by omega))
    omega
  by_cases c3 : len.toNat < 16777216
  · have hbc := u64ByteLen_eq_3 len (by omega) (by omega)
    refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc3 len v28 v29 (by omega) (by omega))
    omega
  by_cases c4 : len.toNat < 4294967296
  · have hbc := u64ByteLen_eq_4 len (by omega) (by omega)
    refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc4 len v28 v29 (by omega) (by omega))
    omega
  by_cases c5 : len.toNat < 1099511627776
  · have hbc := u64ByteLen_eq_5 len (by omega) (by omega)
    refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc5 len v28 v29 (by omega) (by omega))
    omega
  by_cases c6 : len.toNat < 281474976710656
  · have hbc := u64ByteLen_eq_6 len (by omega) (by omega)
    refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc6 len v28 v29 (by omega) (by omega))
    omega
  by_cases c7 : len.toNat < 72057594037927936
  · have hbc := u64ByteLen_eq_7 len (by omega) (by omega)
    refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc7 len v28 v29 (by omega) (by omega))
    omega
  have hbc := u64ByteLen_eq_8 len (by omega)
  refine cpsTripleWithin_mono_nSteps ?_ (rebLadder_bc8 len v28 v29 (by omega))
  omega

end RlpEncodeBytesSAsm

end EvmAsm.Codegen
