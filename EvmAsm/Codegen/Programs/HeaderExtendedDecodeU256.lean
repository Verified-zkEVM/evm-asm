/-
  The base_fee (u256) numeric-field store block of `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39): field 15, `base_fee_per_gas`, written
  big-endian into the 32-byte struct slot at `outBase + 96`.

  The u256 field occupies five instructions at `S = HB + 4·k`:

    [k]   SUB x10, x10, x12     [k+1] MV x11, x12    [k+2] ADDI x12, x18, 96
    [k+3] JAL rlp_content_to_u256_be
    [k+4] BNE x10, x0, →fail

  Unlike `hedU64Store`, the callee `rlp_content_to_u256_be` WRITES the 32-byte
  output region directly (no result `SD`), the output pointer is materialised by
  the extra `ADDI x12, x18, 96`, and the status lands in **x10** (not x11).  The
  callee's four-way status (too-long=2, empty=0, non-canonical=3, success=0)
  collapses here to ok (region written, `u256Ok`) / fail (`u256Fail`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeCall
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm EvmAsm.EL.RLP

/-- The `rlp_content_to_u256_be` callee post as re-based onto `fullCode`: the
    surrendered temporaries, the preserved `x0`/`ra`/input bytes, and the
    four-way status disjunction (too-long, empty, non-canonical, success).
    Matches the post of `rlp_content_to_u256_be_spec_within` with `base := CU256B`. -/
def hedU256Post (srcBase outPtr raVal : Word) (srcBytes : List (BitVec 8)) (srcOff lenN : Nat) : Assertion :=
  (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 lenN) ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
    regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) **
  (fun h =>
    (((.x10 ↦ᵣ (2 : Word)) ** memOwnU256 outPtr ** ⌜32 < lenN⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
       ⌜lenN = 0⌝) h) ∨
    (((.x10 ↦ᵣ (3 : Word)) ** memOwnU256 outPtr **
       ⌜0 < lenN ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - lenN) srcOff lenN) **
       ⌜0 < lenN ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))

/-- The u256 ok post at `S + 20`: the callee wrote the 32-byte big-endian value
    into the struct slot `outBase + off`, pinned to the model `u256Ok`. -/
def hedU256Ok (srcBase outBase raVal lenW : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (off : BitVec 12) (Extra : Assertion) : Assertion :=
  fun h => ∃ out : List (BitVec 8),
    ((bytesRegion ((outBase + signExtend12 off) : Word) out ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ ((outBase + signExtend12 off) : Word)) **
      ((.x18 : Reg) ↦ᵣ outBase) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** Extra) **
     ⌜u256Ok srcBytes srcOff lenW out⌝) h

/-- The u256 fail post at `HB + 664`: the scalar was malformed (`u256Fail`); the
    32-byte output region keeps arbitrary owned content (`memOwnU256`). -/
def hedU256Fail (srcBase outBase raVal lenW : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (off : BitVec 12) (Extra : Assertion) : Assertion :=
  (memOwnU256 ((outBase + signExtend12 off) : Word) ** regOwn .x10 ** ((.x11 : Reg) ↦ᵣ lenW) **
    ((.x12 : Reg) ↦ᵣ ((outBase + signExtend12 off) : Word)) ** ((.x18 : Reg) ↦ᵣ outBase) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** Extra) **
   ⌜u256Fail srcBytes srcOff lenW⌝

set_option maxRecDepth 8000 in
/-- **u256 base_fee store.**  Arg-shuffle (`SUB`/`MV`/`ADDI`), the wrapped
    `rlp_content_to_u256_be` call (`hcall`), and the `BNE x10, x0` dispatch.
    The callee writes the 32-byte output region directly, so there is no result
    `SD`; the block is a branch: fail → `HB + 664` (`hedU256Fail`), ok →
    `S + 20` (`hedU256Ok`). -/
theorem hedU256Store {n : Nat} {Prest : Assertion}
    (S srcBase adv lenW outBase raOld v11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff lenN : Nat) (off : BitVec 12) (boff : BitVec 13)
    (hPrest : Prest.pcFree)
    (hlen64 : lenN < 2 ^ 64) (hlenW : lenW = BitVec.ofNat 64 lenN)
    (hcp : adv - lenW = srcBase + BitVec.ofNat 64 srcOff)
    (htgt : (S + 16) + signExtend13 boff = HB + 664)
    (hSUB : ∀ a i, CodeReq.singleton S (.SUB .x10 .x10 .x12) a = some i → fullCode a = some i)
    (hMV : ∀ a i, CodeReq.singleton (S + 4) (.MV .x11 .x12) a = some i → fullCode a = some i)
    (hADDI : ∀ a i, CodeReq.singleton (S + 8) (.ADDI .x12 .x18 off) a = some i → fullCode a = some i)
    (hBNE : ∀ a i, CodeReq.singleton (S + 16) (.BNE .x10 .x0 boff) a = some i → fullCode a = some i)
    (hcall : cpsTripleWithin n (S + 12) (S + 16) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) **
        (((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ lenW) **
          (((.x12 : Reg) ↦ᵣ ((outBase + signExtend12 off) : Word)) ** ((.x18 : Reg) ↦ᵣ outBase) **
            memOwnU256 ((outBase + signExtend12 off) : Word) ** Prest)))
      (hedU256Post srcBase ((outBase + signExtend12 off) : Word) raOld srcBytes srcOff lenN **
        (((.x18 : Reg) ↦ᵣ outBase) ** Prest))) :
    cpsBranchWithin (1 + (1 + (1 + n)) + 1) S fullCode
      (((.x10 : Reg) ↦ᵣ adv) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ lenW) **
        ((.x18 : Reg) ↦ᵣ outBase) ** memOwnU256 ((outBase + signExtend12 off) : Word) **
        ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
      (HB + 664) (hedU256Fail srcBase outBase raOld lenW srcBytes srcOff off Prest)
      (S + 20) (hedU256Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
  set outPtr := (outBase + signExtend12 off : Word) with houtPtr
  set cptr := srcBase + BitVec.ofNat 64 srcOff with hcptr
  -- ===== front: SUB ; MV ; ADDI ; call  (S → S + 16) =====
  have hsub := sub_spec_gen_rd_eq_rs1_within .x10 .x12 adv lenW S (by decide)
  rw [hcp] at hsub
  have hsubL := cpsTripleWithin_extend_code hSUB hsub
  have hsubF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x18 : Reg) ↦ᵣ outBase) ** memOwnU256 outPtr **
     ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
    (by unfold memOwnU256; repeat' first | exact pcFree_regIs | exact pcFree_memOwn | exact hPrest | apply pcFree_sepConj)
    hsubL
  have hmv := mv_spec_gen_within .x11 .x12 lenW v11 (S + 4) (by decide)
  rw [show (S + 4) + 4 = S + 8 from by bv_omega] at hmv
  have hmvL := cpsTripleWithin_extend_code hMV hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ cptr) ** ((.x18 : Reg) ↦ᵣ outBase) ** memOwnU256 outPtr **
     ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
    (by unfold memOwnU256; repeat' first | exact pcFree_regIs | exact pcFree_memOwn | exact hPrest | apply pcFree_sepConj)
    hmvL
  have haddi := addi_spec_gen_within .x12 .x18 lenW outBase off (S + 8) (by decide)
  rw [show (S + 8) + 4 = S + 12 from by bv_omega, ← houtPtr] at haddi
  have haddiL := cpsTripleWithin_extend_code hADDI haddi
  have haddiF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ cptr) ** ((.x11 : Reg) ↦ᵣ lenW) ** memOwnU256 outPtr **
     ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
    (by unfold memOwnU256; repeat' first | exact pcFree_regIs | exact pcFree_memOwn | exact hPrest | apply pcFree_sepConj)
    haddiL
  have hf1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsubF hmvF
  have hf2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf1 haddiF
  have hfront := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hf2 hcall
  -- ===== ok continuation: BNE falls through (x10 = 0) → S + 20 =====
  have hokc : cpsBranchWithin 1 (S + 16) fullCode
      (fun h => ∃ out : List (BitVec 8),
        ((bytesRegion outPtr out ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ lenW) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜u256Ok srcBytes srcOff lenW out⌝) h)
      (HB + 664) (hedU256Fail srcBase outBase raOld lenW srcBytes srcOff off Prest)
      (S + 20) (hedU256Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
    refine cpsBranchWithin_exists_pre (fun out => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hbne := bne_spec_gen_within .x10 .x0 boff (0 : Word) (0 : Word) (S + 16)
    rw [show (S + 16) + 4 = S + 20 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code hBNE hbne
    have hfall := cpsBranchWithin_ntakenStripPure2 hbneL (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl ((sepConj_pure_right _).1 h_pure).2)
    have hfallF := cpsTripleWithin_frameR
      (bytesRegion outPtr out ** ((.x11 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x18 : Reg) ↦ᵣ outBase) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact hPrest | apply pcFree_sepConj)
      hfall
    have hout : cpsTripleWithin 1 (S + 16) (S + 20) fullCode
        (bytesRegion outPtr out ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ lenW) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
        (hedU256Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hfallF
      exact ⟨out, (sepConj_pure_right _).2 ⟨by xperm_hyp hq, hok⟩⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right (HB + 664)
        (hedU256Fail srcBase outBase raOld lenW srcBytes srcOff off Prest) hout)
  -- ===== fail continuation: BNE taken (x10 ≠ 0) → HB + 664 =====
  have hfailc : cpsBranchWithin 1 (S + 16) fullCode
      (fun h => ∃ st : Word,
        ((((.x10 : Reg) ↦ᵣ st) ** memOwnU256 outPtr ** ((.x11 : Reg) ↦ᵣ lenW) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜st ≠ (0 : Word) ∧ u256Fail srcBytes srcOff lenW⌝) h)
      (HB + 664) (hedU256Fail srcBase outBase raOld lenW srcBytes srcOff off Prest)
      (S + 20) (hedU256Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
    refine cpsBranchWithin_exists_pre (fun st => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hst => ?_)
    obtain ⟨hst_ne, hfail⟩ := hst
    have hbne := bne_spec_gen_within .x10 .x0 boff st (0 : Word) (S + 16)
    rw [htgt, show (S + 16) + 4 = S + 20 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code hBNE hbne
    have htk := cpsBranchWithin_takenStripPure2 hbneL (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact hst_ne ((sepConj_pure_right _).1 h_pure).2)
    have htkF := cpsTripleWithin_frameR
      (memOwnU256 outPtr ** ((.x11 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x18 : Reg) ↦ᵣ outBase) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
      (by unfold memOwnU256; repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_memOwn | exact pcFree_regIs | exact pcFree_regOwn | exact hPrest | apply pcFree_sepConj)
      htk
    have hout : cpsTripleWithin 1 (S + 16) (HB + 664) fullCode
        (((.x10 : Reg) ↦ᵣ st) ** memOwnU256 outPtr ** ((.x11 : Reg) ↦ᵣ lenW) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
        (hedU256Fail srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htkF
      refine (sepConj_pure_right _).2 ⟨?_, hfail⟩
      have hq2 : (((.x10 : Reg) ↦ᵣ st) ** memOwnU256 outPtr ** ((.x11 : Reg) ↦ᵣ lenW) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) h := by
        xperm_hyp hq
      have hq3 := sepConj_mono_left (regIs_implies_regOwn .x10) _ hq2
      xperm_hyp hq3
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_left (S + 20)
        (hedU256Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) hout)
  -- ===== dispatch: fold the four callee arms into ok ∨ fail =====
  have hdisp : cpsBranchWithin 1 (S + 16) fullCode
      (hedU256Post srcBase outPtr raOld srcBytes srcOff lenN **
        (((.x18 : Reg) ↦ᵣ outBase) ** Prest))
      (HB + 664) (hedU256Fail srcBase outBase raOld lenW srcBytes srcOff off Prest)
      (S + 20) (hedU256Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_pre_or hokc hfailc)
    unfold hedU256Post at hp
    obtain ⟨g1, g2, gd, gu, hFD, hExtraPart⟩ := hp
    obtain ⟨k1, k2, kd, ku, hFrame, hDisj⟩ := hFD
    have rebuild : ∀ (arm : Assertion), arm k2 →
        ((((((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 lenN) ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwn .x5 **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes) ** arm) **
          (((.x18 : Reg) ↦ᵣ outBase) ** Prest))) h :=
      fun arm ha => ⟨g1, g2, gd, gu, ⟨k1, k2, kd, ku, hFrame, ha⟩, hExtraPart⟩
    rcases hDisj with a2 | a0e | a3 | a0s
    · -- status 2: too-long (fail)
      refine Or.inr ⟨(2 : Word), ?_⟩
      have hR := rebuild _ a2
      have hR2 : ((((.x10 : Reg) ↦ᵣ (2 : Word)) ** memOwnU256 outPtr ** ((.x11 : Reg) ↦ᵣ lenW) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜32 < lenN⌝) h := by rw [hlenW]; xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, by decide, ?_⟩
      exact Or.inl (by rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]; omega)
    · -- status 0: empty (ok, all-zero)
      refine Or.inl ⟨List.replicate 32 (0 : BitVec 8), ?_⟩
      have hR := rebuild _ a0e
      have hR2 : ((bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
          ((.x11 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜lenN = 0⌝) h := by rw [hlenW]; xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, ?_⟩
      exact Or.inl ⟨by rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, hP], rfl⟩
    · -- status 3: non-canonical (fail)
      refine Or.inr ⟨(3 : Word), ?_⟩
      have hR := rebuild _ a3
      have hR2 : ((((.x10 : Reg) ↦ᵣ (3 : Word)) ** memOwnU256 outPtr ** ((.x11 : Reg) ↦ᵣ lenW) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜0 < lenN ∧ getByteAt srcBytes srcOff = 0⌝) h := by rw [hlenW]; xperm_hyp hR
      obtain ⟨hreg, hlo, hgb⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, by decide, ?_⟩
      exact Or.inr ⟨by rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]; omega, hgb⟩
    · -- status 0: success (ok, big-endian written)
      refine Or.inl ⟨copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - lenN) srcOff lenN, ?_⟩
      have hR := rebuild _ a0s
      have hR2 : ((bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - lenN) srcOff lenN) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜0 < lenN ∧ getByteAt srcBytes srcOff ≠ 0⌝) h := by rw [hlenW]; xperm_hyp hR
      obtain ⟨hreg, hlo, hgb⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, ?_⟩
      refine Or.inr ⟨by rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]; omega, hgb, ?_⟩
      rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]
  -- ===== assemble: front ;; dispatch =====
  have hfront' := cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x) hfront
    (P' := ((.x10 : Reg) ↦ᵣ adv) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ lenW) **
      ((.x18 : Reg) ↦ᵣ outBase) ** memOwnU256 outPtr ** ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_branch_same_cr hfront' hdisp)

#print axioms hedU256Store

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
