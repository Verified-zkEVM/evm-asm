/-
  The numeric-field store blocks of `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39): the six u64 fields (number, gas_limit,
  gas_used, timestamp, blob_gas_used, excess_blob_gas).

  Each u64 field occupies five instructions at `S = HB + 4·k`:

    [k]   SUB x10, x10, x12   [k+1] MV x11, x12   [k+2] JAL rlp_content_to_u64
    [k+3] BNE x11, x0, →fail  [k+4] SD x18, x10, off

  The arg-shuffle turns the walk step's advanced cursor / length into the content
  pointer (`x10 = adv − len`) and the content length (`x11 = len`); the callee
  decodes the scalar; the `BNE` rejects a malformed scalar to `HB + 664`; and the
  `SD` stores the decoded value at the field's struct offset.  `hedU64Store`
  collapses the callee's four-way status into ok (value stored, `u64Ok`) / fail
  (`u64Fail`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeCall
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm EvmAsm.EL.RLP

/-- The `rlp_content_to_u64` callee post as re-based onto `fullCode`: the
    clobbered temporaries, the preserved `x0`/`ra`/input bytes, and the four-way
    status disjunction (too-long, empty, non-canonical, success).  Matches the
    post of `rlp_content_to_u64_spec_within` with `base := CU64B`. -/
def hedU64Post (srcBase raVal : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) **
  (fun h =>
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
       ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
    (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
       (.x11 ↦ᵣ (0 : Word)) **
       ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))

/-- The u64 ok post at `S + 20`: the decoded scalar `v` is stored at the field
    offset (`outBase + off`), pinned to the model `u64Ok`. -/
def hedU64Ok (srcBase outBase raVal lenW : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (off : BitVec 12) (Extra : Assertion) : Assertion :=
  fun h => ∃ v : Word,
    (((((outBase + signExtend12 off) : Word) ↦ₘ v) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** Extra) **
     ⌜u64Ok srcBytes srcOff lenW v⌝) h

/-- The u64 fail post at `HB + 664`: the scalar was malformed (`u64Fail`); the
    store did not run so the field cell keeps its old value. -/
def hedU64Fail (srcBase outBase raVal lenW vold : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (off : BitVec 12) (Extra : Assertion) : Assertion :=
  ((((outBase + signExtend12 off) : Word) ↦ₘ vold) ** regOwn .x10 ** regOwn .x11 **
    ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** Extra) **
   ⌜u64Fail srcBytes srcOff lenW⌝

set_option maxRecDepth 8000 in
/-- **u64 numeric-field store.**  Arg-shuffle (`SUB`/`MV`), the wrapped
    `rlp_content_to_u64` call (`hcall`), `BNE` dispatch, and the result `SD`.
    Given the content-pointer tie (`adv − lenW = srcBase + srcOff`) and length
    tie (`lenW = ofNat lenN`, `lenN < 2^64`), the block is a branch:
    fail → `HB + 664` (`hedU64Fail`), ok → `S + 20` (`hedU64Ok`). -/
theorem hedU64Store {n : Nat} {Prest : Assertion}
    (S srcBase adv lenW outBase raOld v11 vold : Word)
    (srcBytes : List (BitVec 8)) (srcOff lenN : Nat) (off : BitVec 12) (boff : BitVec 13)
    (hPrest : Prest.pcFree)
    (hlen64 : lenN < 2 ^ 64) (hlenW : lenW = BitVec.ofNat 64 lenN)
    (hcp : adv - lenW = srcBase + BitVec.ofNat 64 srcOff)
    (htgt : (S + 12) + signExtend13 boff = HB + 664)
    (hSUB : ∀ a i, CodeReq.singleton S (.SUB .x10 .x10 .x12) a = some i → fullCode a = some i)
    (hMV : ∀ a i, CodeReq.singleton (S + 4) (.MV .x11 .x12) a = some i → fullCode a = some i)
    (hBNE : ∀ a i, CodeReq.singleton (S + 12) (.BNE .x11 .x0 boff) a = some i → fullCode a = some i)
    (hSD : ∀ a i, CodeReq.singleton (S + 16) (.SD .x18 .x10 off) a = some i → fullCode a = some i)
    (hcall : cpsTripleWithin n (S + 8) (S + 12) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) **
        (((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ lenW) **
          (((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
            (((outBase + signExtend12 off) : Word) ↦ₘ vold) ** Prest)))
      (hedU64Post srcBase raOld srcBytes srcOff lenN **
        (((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
          (((outBase + signExtend12 off) : Word) ↦ₘ vold) ** Prest))) :
    cpsBranchWithin (1 + (1 + n) + 2) S fullCode
      (((.x10 : Reg) ↦ᵣ adv) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ lenW) **
        ((.x18 : Reg) ↦ᵣ outBase) ** (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
        ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
      (HB + 664) (hedU64Fail srcBase outBase raOld lenW vold srcBytes srcOff off Prest)
      (S + 20) (hedU64Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
  set cptr := srcBase + BitVec.ofNat 64 srcOff with hcptr
  -- ===== front: SUB ; MV ; call  (S → S + 12) =====
  have hsub := sub_spec_gen_rd_eq_rs1_within .x10 .x12 adv lenW (S) (by decide)
  rw [hcp] at hsub
  have hsubL := cpsTripleWithin_extend_code hSUB hsub
  have hsubF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x18 : Reg) ↦ᵣ outBase) **
     (((outBase + signExtend12 off) : Word) ↦ₘ vold) ** ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hPrest | apply pcFree_sepConj)
    hsubL
  have hmv := mv_spec_gen_within .x11 .x12 lenW v11 (S + 4) (by decide)
  rw [show (S + 4) + 4 = S + 8 from by bv_omega] at hmv
  have hmvL := cpsTripleWithin_extend_code hMV hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ cptr) ** ((.x18 : Reg) ↦ᵣ outBase) **
     (((outBase + signExtend12 off) : Word) ↦ₘ vold) ** ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hPrest | apply pcFree_sepConj)
    hmvL
  have hmvc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hmvF hcall
  have hfront := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsubF hmvc
  -- ===== dispatch: fold the four callee arms into ok ∨ fail =====
  have hokc : cpsBranchWithin 2 (S + 12) fullCode
      (fun h => ∃ v : Word,
        ((((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ lenW) **
          ((.x18 : Reg) ↦ᵣ outBase) ** (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜u64Ok srcBytes srcOff lenW v⌝) h)
      (HB + 664) (hedU64Fail srcBase outBase raOld lenW vold srcBytes srcOff off Prest)
      (S + 20) (hedU64Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
    refine cpsBranchWithin_exists_pre (fun v => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 boff (0 : Word) (0 : Word) (S + 12)
    rw [show (S + 12) + 4 = S + 16 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code hBNE hbne
    have hfall := cpsBranchWithin_ntakenStripPure2 hbneL (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl ((sepConj_pure_right _).1 h_pure).2)
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ v) ** ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
       (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x1 : Reg) ↦ᵣ raOld) **
       bytesRegion srcBase srcBytes ** Prest)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact hPrest | apply pcFree_sepConj)
      hfall
    have hsd := sd_spec_gen_within .x18 .x10 outBase v vold off (S + 16)
    rw [show (S + 16) + 4 = S + 20 from by bv_omega] at hsd
    have hsdL := cpsTripleWithin_extend_code hSD hsd
    have hsdF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ lenW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact hPrest | apply pcFree_sepConj)
      hsdL
    have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hfallF hsdF
    have hout : cpsTripleWithin 2 (S + 12) (S + 20) fullCode
        (((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ lenW) **
          ((.x18 : Reg) ↦ᵣ outBase) ** (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
        (hedU64Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      exact ⟨v, (sepConj_pure_right _).2 ⟨by xperm_hyp hq, hok⟩⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right (HB + 664)
        (hedU64Fail srcBase outBase raOld lenW vold srcBytes srcOff off Prest) hout)
  have hfailc : cpsBranchWithin 2 (S + 12) fullCode
      (fun h => ∃ st : Word,
        ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ st) ** ((.x12 : Reg) ↦ᵣ lenW) **
          ((.x18 : Reg) ↦ᵣ outBase) ** (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜st ≠ (0 : Word) ∧ u64Fail srcBytes srcOff lenW⌝) h)
      (HB + 664) (hedU64Fail srcBase outBase raOld lenW vold srcBytes srcOff off Prest)
      (S + 20) (hedU64Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
    refine cpsBranchWithin_exists_pre (fun st => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hst => ?_)
    obtain ⟨hst_ne, hfail⟩ := hst
    have hbne := bne_spec_gen_within .x11 .x0 boff st (0 : Word) (S + 12)
    rw [htgt, show (S + 12) + 4 = S + 16 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code hBNE hbne
    have htk := cpsBranchWithin_takenStripPure2 hbneL (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact hst_ne ((sepConj_pure_right _).1 h_pure).2)
    have htkF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
       (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact hPrest | apply pcFree_sepConj)
      htk
    have hout : cpsTripleWithin 1 (S + 12) (HB + 664) fullCode
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ st) ** ((.x12 : Reg) ↦ᵣ lenW) **
          ((.x18 : Reg) ↦ᵣ outBase) ** (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest)
        (hedU64Fail srcBase outBase raOld lenW vold srcBytes srcOff off Prest) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htkF
      refine (sepConj_pure_right _).2 ⟨?_, hfail⟩
      have hq2 : ((((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ st) ** ((.x12 : Reg) ↦ᵣ lenW) **
          ((.x18 : Reg) ↦ᵣ outBase) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) h := by xperm_hyp hq
      have hq3 := sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x10)
          (sepConj_mono (regIs_implies_regOwn .x11) (fun _ x => x))) h hq2
      xperm_hyp hq3
    have hb := cpsTripleWithin_as_cpsBranchWithin_left (S + 20)
      (hedU64Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) hout
    refine cpsBranchWithin_mono_nSteps ?_ hb
    omega
  have hdisp : cpsBranchWithin 2 (S + 12) fullCode
      (hedU64Post srcBase raOld srcBytes srcOff lenN **
        (((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
          (((outBase + signExtend12 off) : Word) ↦ₘ vold) ** Prest))
      (HB + 664) (hedU64Fail srcBase outBase raOld lenW vold srcBytes srcOff off Prest)
      (S + 20) (hedU64Ok srcBase outBase raOld lenW srcBytes srcOff off Prest) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_pre_or hokc hfailc)
    unfold hedU64Post at hp
    obtain ⟨g1, g2, gd, gu, hFD, hExtraPart⟩ := hp
    obtain ⟨k1, k2, kd, ku, hFrame, hDisj⟩ := hFD
    have rebuild : ∀ (arm : Assertion), arm k2 →
        ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes) ** arm) **
          (((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
            (((outBase + signExtend12 off) : Word) ↦ₘ vold) ** Prest))) h :=
      fun arm ha => ⟨g1, g2, gd, gu, ⟨k1, k2, kd, ku, hFrame, ha⟩, hExtraPart⟩
    rcases hDisj with a2 | a0e | a3 | a0s
    · -- status 2: too-long
      refine Or.inr ⟨(2 : Word), ?_⟩
      have hR := rebuild _ a2
      have hR2 : ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
          ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
          (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜8 < lenN⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, by decide, ?_⟩
      exact Or.inl (by rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]; omega)
    · -- status 0: empty  (value 0)
      refine Or.inl ⟨(0 : Word), ?_⟩
      have hR := rebuild _ a0e
      have hR2 : ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
          (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜lenN = 0⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, ?_⟩
      exact Or.inl ⟨by rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, hP], rfl⟩
    · -- status 3: non-canonical
      refine Or.inr ⟨(3 : Word), ?_⟩
      have hR := rebuild _ a3
      have hR2 : ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
          ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
          (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜0 < lenN ∧ lenN ≤ 8 ∧ getByteAt srcBytes srcOff = 0⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hlo, hhi, hgb⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, by decide, ?_⟩
      refine Or.inr ⟨?_, ?_, hgb⟩ <;>
        rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] <;> omega
    · -- status 0: success  (value fromBytesBE)
      refine Or.inl ⟨BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take lenN)), ?_⟩
      have hR := rebuild _ a0s
      have hR2 : ((((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take lenN))) **
          ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ outBase) **
          (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Prest) **
         ⌜0 < lenN ∧ lenN ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hlo, hhi, hgb⟩ := (sepConj_pure_right _).1 hR2
      refine (sepConj_pure_right _).2 ⟨hreg, ?_⟩
      refine Or.inr ⟨?_, ?_, hgb, by rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]⟩ <;>
        rw [hlenW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] <;> omega
  -- ===== assemble: front ;; dispatch =====
  have hfront' := cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x) hfront
    (P' := ((.x10 : Reg) ↦ᵣ adv) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ lenW) **
      ((.x18 : Reg) ↦ᵣ outBase) ** (((outBase + signExtend12 off) : Word) ↦ₘ vold) **
      ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
  exact cpsTripleWithin_seq_branch_same_cr hfront' hdisp

#print axioms hedU64Store

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
