/-
  EvmAsm.Rv64.RLP.ValidatingBytesCopy

  SINGLE-PASS validated fixed-length BYTE-ARRAY field copy (T2/T3 building block of #9373). The
  byte-array analog of `rlp_decode_shortBytes_scalar_store_at`: composes the offset-general
  validating shortBytes decoder with the existing byte-copy engine (`unified_field_bytes_copy`) on
  the decoder's SUCCESS exit. The validating arm leaves the payload pointer in `x13` and payload
  length in `x11`; the copy then streams the `N` payload bytes straight into a fixed slot of an
  output struct — validated and copied in one forward sweep, no reparse.

  Used for `withdrawal_decode`'s 20-byte `address` field (and the header hash fields). `rOut` is a
  callee-saved register holding the output base; `N` (= the validated payload length) is the field's
  fixed width — the surrounding decoder supplies the runtime width check that pins `payloadLen = N`.

  SUCCESS: the output region's slot `[di0, di0+N)` holds the payload bytes, carrying the verdict
  `decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)`. FAIL: the decoder's abort exit.
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItemShortBytesValidatedAt
import EvmAsm.Rv64.RLP.UnifiedFieldBytesCopy
import EvmAsm.Rv64.RLP.ValidatingFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The validating arm leaves `x13` at `(regionBase + O) + signExtend12 1`; that is the payload
    pointer `regionBase + (O+1)` the byte copy consumes. -/
private theorem bytescopy_ptr_eq (regionBase : Word) (O : Nat) :
    (regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12)
    = regionBase + BitVec.ofNat 64 (O + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Sequence a branch onto the TAKEN exit of a branch, converging the follow-on branch's TAKEN exit
    with the first branch's fall exit onto a shared fail exit `exitF`. Used to bolt a length-equality
    check onto a validating decode's success so that *both* a malformed field (the decoder's bound
    failure) and a wrong-length field converge on the one `a0 ≠ 0` exit. -/
theorem cpsBranchWithin_seq_cpsBranchWithin_taken_conv {n1 n2 : Nat}
    {entry mid succ exitF : Word} {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q_t1 Q_f1 Q_t2 Q_succ Q_f : Assertion}
    (h1 : cpsBranchWithin n1 entry cr1 P mid Q_t1 exitF Q_f1)
    (h2 : cpsBranchWithin n2 mid cr2 Q_t1 exitF Q_t2 succ Q_succ)
    (hf1 : ∀ h, Q_f1 h → Q_f h) (hf2 : ∀ h, Q_t2 h → Q_f h) :
    cpsBranchWithin (n1 + n2) entry (cr1.union cr2) P succ Q_succ exitF Q_f := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr1 hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
    obtain ⟨k2, hk2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hcr2' hQ_t1R hpc_t1
    rcases hbranch2 with ⟨hpc_t2, hQ_t2R⟩ | ⟨hpc_f2, hQ_succR⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inr ⟨hpc_t2, by
          obtain ⟨hp, hcompat, hpq⟩ := hQ_t2R
          exact ⟨hp, hcompat, sepConj_mono_left hf2 hp hpq⟩⟩⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inl ⟨hpc_f2, hQ_succR⟩⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1, hstep1,
      Or.inr ⟨hpc_f1, by
        obtain ⟨hp, hcompat, hpq⟩ := hQ_f1R
        exact ⟨hp, hcompat, sepConj_mono_left hf1 hp hpq⟩⟩⟩

/-- Merge two pure facts carried in the two top-level operands of a separating conjunction into a
    single conjunctive pure: `(R1 ** ⌜P⌝) ** (R2 ** ⌜Q⌝) ⟹ (R1 ** R2) ** ⌜P ∧ Q⌝`. General in
    `R1`,`R2`,`P`,`Q`; the work-horse for collapsing the decode verdict and the length-check verdict
    into one pure so a single `xperm` reshape suffices. -/
theorem sepConj_merge_two_pures {R1 R2 : Assertion} {P Q : Prop} :
    ∀ s, ((R1 ** ⌜P⌝) ** (R2 ** ⌜Q⌝)) s → ((R1 ** R2) ** ⌜P ∧ Q⌝) s := by
  intro s hs
  obtain ⟨h1, h2, hd, hu, hL, hR⟩ := hs
  rw [sepConj_pure_right] at hL hR
  obtain ⟨hR1, hP⟩ := hL
  obtain ⟨hR2, hQ⟩ := hR
  rw [sepConj_pure_right]
  exact ⟨⟨h1, h2, hd, hu, hR1, hR2⟩, hP, hQ⟩

/-- `signExtend12` of a small `ofNat` (high bit clear, `< 2^11`) is the zero-extended `ofNat 64`. -/
private theorem signExtend12_ofNat_small (n : Nat) (hn : n < 2 ^ 11) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  unfold signExtend12
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hmsb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
    simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  rw [hmsb, if_neg (by decide)]
  omega

/-- `ofNat`-equality reflects to `Nat`-equality for in-range values. -/
private theorem ofNat_eq_iff_small (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this
  · intro h; rw [h]

set_option linter.unusedVariables false in
/-- **Length-equality check** bolted onto the validating decode's SUCCESS state: `ADDI x10,x0,N` then
    `BNE x11,x10` — taken (`payloadLen ≠ N`) exits at `failPC` (wrong length), fall (`payloadLen = N`)
    continues at `succPC+8`. The decode verdict is dropped here (re-derived at the copy site from
    `payloadLen = N` + availability), keeping a single pure per exit. -/
theorem rlp_shortBytes_length_check
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O expectedN : Nat)
    (v12Old v14Old regionBase : Word)
    (succPC : Word) (lenFailOff : BitVec 13) (failPC : Word)
    (hfail : (succPC + 4) + signExtend13 lenFailOff = failPC)
    (hexp11 : expectedN < 2 ^ 11)
    (hexp64 : expectedN < 2 ^ 64)
    (hpl64 : rlpPrefixShortBytesPayloadLen pfx < 2 ^ 64)
    (hd : (CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).Disjoint
          (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff))) :
    cpsBranchWithin 2 succPC
      ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
       (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
        ⌜decode (pfx :: rest)
          = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                  rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      -- FAIL (taken): wrong length.
      failPC
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
          ⌜rlpPrefixShortBytesPayloadLen pfx ≠ expectedN⌝)
      -- CONTINUE (fall): correct length.
      (succPC + 8)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
          ⌜rlpPrefixShortBytesPayloadLen pfx = expectedN⌝) := by
  set pl := rlpPrefixShortBytesPayloadLen pfx with hpl
  -- ADDI x10, x0, expectedN : x10 := expectedN (the decode verdict in the pre is dropped).
  have addi_raw := addi_x0_spec_gen_within .x10 ((0 : Word) + signExtend12 (0xB8 : BitVec 12))
    (BitVec.ofNat 12 expectedN) succPC (by nofun)
  rw [signExtend12_ofNat_small expectedN hexp11] at addi_raw
  have addiF : cpsTripleWithin 1 succPC (succPC + 4)
      (CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 pl)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = some (.bytes (rest.take pl), rest.drop pl)⌝)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 pl)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by extract_pure hp; obtain ⟨_, hr⟩ := hp; xperm_hyp hr)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x11 ↦ᵣ (BitVec.ofNat 64 pl)) ** (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))))))
        addi_raw)
  -- BNE x11, x10 : compare payloadLen to expectedN.
  have bne_raw := bne_spec_gen_within .x11 .x10 lenFailOff (BitVec.ofNat 64 pl)
    (BitVec.ofNat 64 expectedN) (succPC + 4)
  rw [hfail, show ((succPC + 4) + 4 : Word) = succPC + 8 from by bv_omega] at bne_raw
  have bneF : cpsBranchWithin 1 (succPC + 4)
      (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 pl)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
      failPC
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 pl)) ** (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
          ⌜pl ≠ expectedN⌝)
      (succPC + 8)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 pl)) ** (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
          ⌜pl = expectedN⌝) := by
    refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?tk ?fl
      (cpsBranchWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))))))
        bne_raw)
    · intro h hp
      rw [show (BitVec.ofNat 64 pl ≠ BitVec.ofNat 64 expectedN) = (pl ≠ expectedN) from
            propext (not_congr (ofNat_eq_iff_small pl expectedN hpl64 hexp64))] at hp
      xperm_hyp hp
    · intro h hp
      rw [show (BitVec.ofNat 64 pl = BitVec.ofNat 64 expectedN) = (pl = expectedN) from
            propext (ofNat_eq_iff_small pl expectedN hpl64 hexp64)] at hp
      xperm_hyp hp
  have hseq := cpsTripleWithin_seq_cpsBranchWithin hd addiF bneF
  rw [show (1 + 1) = 2 from rfl] at hseq
  exact hseq

set_option linter.unusedVariables false in
/-- **Single-pass validated fixed-length byte-array copy** at byte offset `O`: validate the
    shortBytes field, then stream its `N`-byte payload into the output slot `outBase + di0`. -/
theorem rlp_decode_shortBytes_bytescopy_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List Byte) (di0 : Nat)
    (off1 off2 succOff : BitVec 13) (base e2_target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (hLfit : (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (hsuccPC : (e2_target + 8) + signExtend13 succOff = succPC)
    (hsalign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hsover : regionBase.toNat + bs.length < 2 ^ 64)
    (hsvalid : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsrc : (O + 1) + rlpPrefixShortBytesPayloadLen pfx ≤ bs.length)
    (hdst : di0 + rlpPrefixShortBytesPayloadLen pfx ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : succPC.toNat + (4 + 20 * rlpPrefixShortBytesPayloadLen pfx) < 2 ^ 64)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hd_copy : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               ((CodeReq.singleton succPC (.ADDI .x14 rOut fieldImm)).union
                 (byteCopyChainCR (succPC + 4) (rlpPrefixShortBytesPayloadLen pfx)))) :
    cpsBranchWithin (7 + (1 + 5 * rlpPrefixShortBytesPayloadLen pfx)) base
      (((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        ((CodeReq.singleton succPC (.ADDI .x14 rOut fieldImm)).union
          (byteCopyChainCR (succPC + 4) (rlpPrefixShortBytesPayloadLen pfx))))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      -- SUCCESS (taken): the payload is copied into the output slot.
      (succPC + 4 + BitVec.ofNat 64 (20 * rlpPrefixShortBytesPayloadLen pfx))
        ((((regOwn .x12) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + rlpPrefixShortBytesPayloadLen pfx))) **
          (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + rlpPrefixShortBytesPayloadLen pfx))) **
          (regOwn .x15) ** (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
          bytesRegion outBase
            (copyRangeGen outBytes bs (O + 1) di0 (rlpPrefixShortBytesPayloadLen pfx))) **
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)))
      -- FAIL (fall): the decoder's abort exit, output untouched.
      (e2_target + 12)
        (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) **
         ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)) := by
  set N := rlpPrefixShortBytesPayloadLen pfx with hN
  -- The validating decoder at offset O; rewrite x13 (both exits) to the payload pointer.
  have decAt := rlp_decode_shortBytes_validated_at pfx rest bs O v10 v11Old v12Old v14Old
    regionBase off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu
  rw [hsuccPC] at decAt
  simp only [bytescopy_ptr_eq] at decAt
  -- Frame the output pointer + region onto both exits.
  have decAtF := cpsBranchWithin_frameR
    ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) decAt
  -- The byte copy at succPC, off = O+1, copying N payload bytes into outBase+di0; framed with the
  -- arm's extra atoms (x5/x10/x11 and the pure verdict) and reordered to decAtF's taken post.
  have copyRaw := unified_field_bytes_copy succPC regionBase rOut outBase fieldImm bs outBytes
    (O + 1) di0 N v12Old v14Old (BitVec.ofNat 64 (pfx :: rest).length)
    hsalign hdalign hsover hsvalid hsrc hdst hdov hdval hcode hImm
  have copyF : cpsTripleWithin (1 + 5 * N) succPC (succPC + 4 + BitVec.ofNat 64 (20 * N))
      ((CodeReq.singleton succPC (.ADDI .x14 rOut fieldImm)).union (byteCopyChainCR (succPC + 4) N))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 N)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)⌝) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      ((((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + N))) **
          (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + N))) ** (regOwn .x15) **
          (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
          bytesRegion outBase (copyRangeGen outBytes bs (O + 1) di0 N)) **
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 N)) **
          ⌜decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)⌝))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 N)) **
          ⌜decode (pfx :: rest) = some (.bytes (rest.take N), rest.drop N)⌝)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs pcFree_pure))))
        copyRaw)
  exact cpsBranchWithin_seq_cpsTripleWithin_taken hd_copy decAtF copyF

end EvmAsm.Rv64.RLP
