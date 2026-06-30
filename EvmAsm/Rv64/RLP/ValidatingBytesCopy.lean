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
import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.Tactics.WPAttr

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
/-- **Single-pass validated fixed-length byte-array copy** at byte offset `O`. Validates the
    shortBytes field, **checks its decoded length equals the Lean argument `expectedN`** (rejecting a
    field of any other length — a DoS guard, since the copy length must not be attacker-controlled),
    then streams **exactly `expectedN`** payload bytes into the output slot `outBase + di0`.

    SUCCESS (taken): the slot `[di0, di0+expectedN)` holds the payload bytes, with
    `⌜payloadLen = expectedN⌝` (so the field IS an `expectedN`-byte string; tie to the pure decode is
    assembled by the caller). FAIL (fall): either malformed (`decode = none`) OR wrong length
    (`payloadLen ≠ expectedN`) — both at the one abort exit, output untouched. -/
theorem rlp_decode_shortBytes_bytescopy_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O expectedN : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List Byte) (di0 : Nat)
    (off1 off2 succOff lenFailOff : BitVec 13) (base e2_target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (hLfit : (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hexp11 : expectedN < 2 ^ 11)
    (hpl64 : rlpPrefixShortBytesPayloadLen pfx < 2 ^ 64)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (hsuccPC : (e2_target + 8) + signExtend13 succOff = succPC)
    (hlenfail : (succPC + 4) + signExtend13 lenFailOff = e2_target + 12)
    (hsalign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hsover : regionBase.toNat + bs.length < 2 ^ 64)
    (hsvalid : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsrc : (O + 1) + expectedN ≤ bs.length)
    (hdst : di0 + expectedN ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : (succPC + 8).toNat + (4 + 20 * expectedN) < 2 ^ 64)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hd_addibne : (CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).Disjoint
                  (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))
    (hd_lencheck : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                 (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff))))
    (hd_copy : (((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
                 ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                   (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))).Disjoint
               ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
                 (byteCopyChainCR (succPC + 8 + 4) expectedN))) :
    cpsBranchWithin ((7 + 2) + (1 + 5 * expectedN)) base
      ((((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
          (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))).union
        ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
          (byteCopyChainCR (succPC + 8 + 4) expectedN)))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      -- SUCCESS (taken): the `expectedN`-byte payload is copied into the output slot.
      (succPC + 8 + 4 + BitVec.ofNat 64 (20 * expectedN))
        ((((regOwn .x12) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + expectedN))) **
          (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + expectedN))) **
          (regOwn .x15) ** (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
          bytesRegion outBase (copyRangeGen outBytes bs (O + 1) di0 expectedN)) **
         ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          ⌜rlpPrefixShortBytesPayloadLen pfx = expectedN⌝)))
      -- FAIL (fall): malformed OR wrong length, output untouched.
      (e2_target + 12)
        (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none ∨ rlpPrefixShortBytesPayloadLen pfx ≠ expectedN⌝) **
         ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)) := by
  -- The validating decoder at offset O (success at succPC, fall at e2_target+12).
  have decAt := rlp_decode_shortBytes_validated_at pfx rest bs O v10 v11Old v12Old v14Old
    regionBase off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu
  rw [hsuccPC] at decAt
  -- The length check on the success exit.
  have lenCheck := rlp_shortBytes_length_check pfx rest bs O expectedN v12Old v14Old regionBase
    succPC lenFailOff (e2_target + 12) hlenfail hexp11 (by omega) hpl64 hd_addibne
  -- Converge: arm fall (decode = none) and length-check fail (payloadLen != expectedN).
  let failPost : Assertion :=
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
      (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
      (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
      (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
      bytesRegion regionBase bs **
      ⌜decode (pfx :: rest) = none ∨ rlpPrefixShortBytesPayloadLen pfx ≠ expectedN⌝)
  have decodeFailToShared : EvmAsm.Rv64.WP.Entails
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs ** ⌜decode (pfx :: rest) = none⌝)) failPost := by
    intro h hp
    show ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = none ∨ rlpPrefixShortBytesPayloadLen pfx ≠ expectedN⌝) h
    extract_pure hp
    obtain ⟨hnone, hst⟩ := hp
    have hstNext := sepConj_mono_left (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (regIs_implies_regOwn .x10))))))) h hst
    have hg := (sepConj_pure_right h).2 ⟨hstNext,
      (Or.inl hnone : decode (pfx :: rest) = none
        ∨ rlpPrefixShortBytesPayloadLen pfx ≠ expectedN)⟩
    xperm_hyp hg
  have lenFailToShared : EvmAsm.Rv64.WP.Entails
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs ** ⌜rlpPrefixShortBytesPayloadLen pfx ≠ expectedN⌝)) failPost := by
    intro h hp
    show ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = none ∨ rlpPrefixShortBytesPayloadLen pfx ≠ expectedN⌝) h
    extract_pure hp
    obtain ⟨hne, hst⟩ := hp
    have hstNext := sepConj_mono_left (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (regIs_implies_regOwn .x10))))))) h hst
    have hg := (sepConj_pure_right h).2 ⟨hstNext,
      (Or.inr hne : decode (pfx :: rest) = none
        ∨ rlpPrefixShortBytesPayloadLen pfx ≠ expectedN)⟩
    xperm_hyp hg
  have armWithLen : cpsBranchWithin (7 + 2) base _ _
      (succPC + 8) _ (e2_target + 12) failPost :=
    (EvmAsm.Rv64.WP.CFG.branchSeqTakenBranchConvergeDisjoint
      (failPost := failPost) hd_lencheck
      (EvmAsm.Rv64.WP.Branch.ofSpec decAt)
      (EvmAsm.Rv64.WP.Branch.ofSpec lenCheck)
      (by rfl) (EvmAsm.Rv64.WP.Entails.refl _)
      decodeFailToShared lenFailToShared).sound
  -- Frame the output pointer + region onto both exits of armWithLen.
  have armWithLenF := cpsBranchWithin_frameR
    ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) armWithLen
  -- The byte copy of exactly `expectedN` bytes, on the success exit (succPC+8).
  have copyRaw := unified_field_bytes_copy (succPC + 8) regionBase rOut outBase fieldImm bs outBytes
    (O + 1) di0 expectedN v12Old v14Old (BitVec.ofNat 64 (pfx :: rest).length)
    hsalign hdalign hsover hsvalid hsrc hdst hdov hdval hcode hImm
  have copyF : cpsTripleWithin (1 + 5 * expectedN) (succPC + 8)
      (succPC + 8 + 4 + BitVec.ofNat 64 (20 * expectedN))
      ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
        (byteCopyChainCR (succPC + 8 + 4) expectedN))
      (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs ** ⌜rlpPrefixShortBytesPayloadLen pfx = expectedN⌝) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      ((((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + expectedN))) **
          (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + expectedN))) ** (regOwn .x15) **
          (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
          bytesRegion outBase (copyRangeGen outBytes bs (O + 1) di0 expectedN)) **
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          ⌜rlpPrefixShortBytesPayloadLen pfx = expectedN⌝))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by rw [bytescopy_ptr_eq] at hp; xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          ⌜rlpPrefixShortBytesPayloadLen pfx = expectedN⌝)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs pcFree_pure))))
        copyRaw)
  exact cpsBranchWithin_seq_cpsTripleWithin_taken hd_copy armWithLenF copyF

/-! ## WP certificate wrapper -/

/-- Code requirement for the validating fixed-length short-bytes copy unit. -/
def validatingShortBytesCopyCR
    (base e2Target succPC : Word) (expectedN : Nat) (rOut : Reg) (fieldImm : BitVec 12)
    (off1 off2 succOff lenFailOff : BitVec 13) : CodeReq :=
  ((((((rlp_phase1_step_code 0x80 off1 base).union
      (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
     (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
    (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).union
    ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
      (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))).union
    ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
      (byteCopyChainCR (succPC + 8 + 4) expectedN)))

/-- Computed precondition for the validating fixed-length short-bytes copy unit. -/
def validatingShortBytesCopyPre
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old regionBase : Word)
    (rOut : Reg) (outBase : Word) (outBytes : List Byte) : Assertion :=
  (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
    (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
    (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
    (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
   ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))

/-- Success postcondition for the validating fixed-length short-bytes copy unit. -/
def validatingShortBytesCopySuccessPost
    (pfx : Byte) (_rest bs : List Byte) (O expectedN : Nat)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (outBytes : List Byte) (di0 : Nat) :
    Assertion :=
  ((((regOwn .x12) **
      (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + expectedN))) **
      (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + expectedN))) **
      (regOwn .x15) ** (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
      bytesRegion outBase (copyRangeGen outBytes bs (O + 1) di0 expectedN)) **
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (BitVec.ofNat 64 expectedN)) **
      (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
      ⌜rlpPrefixShortBytesPayloadLen pfx = expectedN⌝)))

/-- Failure postcondition for the validating fixed-length short-bytes copy unit. -/
def validatingShortBytesCopyFailurePost
    (pfx : Byte) (rest bs : List Byte) (O expectedN : Nat)
    (v12Old v14Old regionBase : Word) (rOut : Reg) (outBase : Word)
    (outBytes : List Byte) : Assertion :=
  (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
    (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
    (.x12 ↦ᵣ v12Old) **
    (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
    (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
    bytesRegion regionBase bs **
    ⌜decode (pfx :: rest) = none ∨ rlpPrefixShortBytesPayloadLen pfx ≠ expectedN⌝) **
   ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))

/-- WP branch certificate for the validating fixed-length short-bytes copy unit.
    This packages the raw `cpsBranchWithin` theorem as a calculator object, so a
    generated schema fold can compose the unit through `wp_rv64_cert`. -/
def validatingShortBytesCopyBranch
    (pfx : Byte) (rest bs : List Byte) (O expectedN : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List Byte) (di0 : Nat)
    (off1 off2 succOff lenFailOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_exp11 : expectedN < 2 ^ 11)
    (h_pl64 : rlpPrefixShortBytesPayloadLen pfx < 2 ^ 64)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_len_fail : (succPC + 4) + signExtend13 lenFailOff = e2Target + 12)
    (h_salign : regionBase.toNat % 8 = 0) (h_dalign : outBase.toNat % 8 = 0)
    (h_sover : regionBase.toNat + bs.length < 2 ^ 64)
    (h_svalid : ∀ i, i < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (h_src : (O + 1) + expectedN ≤ bs.length)
    (h_dst : di0 + expectedN ≤ outBytes.length)
    (h_dov : outBase.toNat + outBytes.length < 2 ^ 64)
    (h_dval : ∀ i, i < outBytes.length →
      isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_code : (succPC + 8).toNat + (4 + 20 * expectedN) < 2 ^ 64)
    (h_imm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (h_addibne : (CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).Disjoint
                  (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))
    (h_lencheck : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                 (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff))))
    (h_copy : (((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).union
                 ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                   (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))).Disjoint
               ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
                 (byteCopyChainCR (succPC + 8 + 4) expectedN))) :
    WP.Branch base
      (validatingShortBytesCopyCR base e2Target succPC expectedN rOut fieldImm
        off1 off2 succOff lenFailOff) :=
  WP.Branch.ofSpec
    (rlp_decode_shortBytes_bytescopy_at pfx rest bs O expectedN v10 v11Old v12Old v14Old
      regionBase rOut outBase fieldImm outBytes di0 off1 off2 succOff lenFailOff base e2Target
      h_class hns h_lfit h_target h_exp11 h_pl64 h_phase3 h_bltu succPC h_succ_pc h_len_fail
      h_salign h_dalign h_sover h_svalid h_src h_dst h_dov h_dval h_code h_imm h_addibne
      h_lencheck h_copy)

/-- The validating-copy branch computes the named precondition. -/
theorem validatingShortBytesCopyBranch_pre
    (pfx : Byte) (rest bs : List Byte) (O expectedN : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List Byte) (di0 : Nat)
    (off1 off2 succOff lenFailOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_exp11 : expectedN < 2 ^ 11)
    (h_pl64 : rlpPrefixShortBytesPayloadLen pfx < 2 ^ 64)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_len_fail : (succPC + 4) + signExtend13 lenFailOff = e2Target + 12)
    (h_salign : regionBase.toNat % 8 = 0) (h_dalign : outBase.toNat % 8 = 0)
    (h_sover : regionBase.toNat + bs.length < 2 ^ 64)
    (h_svalid : ∀ i, i < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (h_src : (O + 1) + expectedN ≤ bs.length)
    (h_dst : di0 + expectedN ≤ outBytes.length)
    (h_dov : outBase.toNat + outBytes.length < 2 ^ 64)
    (h_dval : ∀ i, i < outBytes.length →
      isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_code : (succPC + 8).toNat + (4 + 20 * expectedN) < 2 ^ 64)
    (h_imm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (h_addibne : (CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).Disjoint
                  (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))
    (h_lencheck : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                 (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff))))
    (h_copy : (((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).union
                 ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                   (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))).Disjoint
               ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
                 (byteCopyChainCR (succPC + 8 + 4) expectedN))) :
    (validatingShortBytesCopyBranch pfx rest bs O expectedN v10 v11Old v12Old v14Old
      regionBase rOut outBase fieldImm outBytes di0 off1 off2 succOff lenFailOff base e2Target
      h_class hns h_lfit h_target h_exp11 h_pl64 h_phase3 h_bltu succPC h_succ_pc h_len_fail
      h_salign h_dalign h_sover h_svalid h_src h_dst h_dov h_dval h_code h_imm h_addibne
      h_lencheck h_copy).pre =
      validatingShortBytesCopyPre pfx rest bs O v10 v11Old v12Old v14Old regionBase rOut
        outBase outBytes := by
  rfl

/-- The validating-copy branch's taken exit is the copied-success path. -/
theorem validatingShortBytesCopyBranch_exit_t
    (pfx : Byte) (rest bs : List Byte) (O expectedN : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List Byte) (di0 : Nat)
    (off1 off2 succOff lenFailOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_exp11 : expectedN < 2 ^ 11)
    (h_pl64 : rlpPrefixShortBytesPayloadLen pfx < 2 ^ 64)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_len_fail : (succPC + 4) + signExtend13 lenFailOff = e2Target + 12)
    (h_salign : regionBase.toNat % 8 = 0) (h_dalign : outBase.toNat % 8 = 0)
    (h_sover : regionBase.toNat + bs.length < 2 ^ 64)
    (h_svalid : ∀ i, i < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (h_src : (O + 1) + expectedN ≤ bs.length)
    (h_dst : di0 + expectedN ≤ outBytes.length)
    (h_dov : outBase.toNat + outBytes.length < 2 ^ 64)
    (h_dval : ∀ i, i < outBytes.length →
      isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_code : (succPC + 8).toNat + (4 + 20 * expectedN) < 2 ^ 64)
    (h_imm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (h_addibne : (CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).Disjoint
                  (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))
    (h_lencheck : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                 (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff))))
    (h_copy : (((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).union
                 ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                   (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))).Disjoint
               ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
                 (byteCopyChainCR (succPC + 8 + 4) expectedN))) :
    (validatingShortBytesCopyBranch pfx rest bs O expectedN v10 v11Old v12Old v14Old
      regionBase rOut outBase fieldImm outBytes di0 off1 off2 succOff lenFailOff base e2Target
      h_class hns h_lfit h_target h_exp11 h_pl64 h_phase3 h_bltu succPC h_succ_pc h_len_fail
      h_salign h_dalign h_sover h_svalid h_src h_dst h_dov h_dval h_code h_imm h_addibne
      h_lencheck h_copy).exit_t =
      succPC + 8 + 4 + BitVec.ofNat 64 (20 * expectedN) := by
  rfl

/-- The validating-copy branch's not-taken exit is the shared validation-failure path. -/
theorem validatingShortBytesCopyBranch_exit_f
    (pfx : Byte) (rest bs : List Byte) (O expectedN : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List Byte) (di0 : Nat)
    (off1 off2 succOff lenFailOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_exp11 : expectedN < 2 ^ 11)
    (h_pl64 : rlpPrefixShortBytesPayloadLen pfx < 2 ^ 64)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_len_fail : (succPC + 4) + signExtend13 lenFailOff = e2Target + 12)
    (h_salign : regionBase.toNat % 8 = 0) (h_dalign : outBase.toNat % 8 = 0)
    (h_sover : regionBase.toNat + bs.length < 2 ^ 64)
    (h_svalid : ∀ i, i < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (h_src : (O + 1) + expectedN ≤ bs.length)
    (h_dst : di0 + expectedN ≤ outBytes.length)
    (h_dov : outBase.toNat + outBytes.length < 2 ^ 64)
    (h_dval : ∀ i, i < outBytes.length →
      isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_code : (succPC + 8).toNat + (4 + 20 * expectedN) < 2 ^ 64)
    (h_imm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (h_addibne : (CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).Disjoint
                  (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))
    (h_lencheck : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                 (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff))))
    (h_copy : (((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).union
                 ((CodeReq.singleton succPC (.ADDI .x10 .x0 (BitVec.ofNat 12 expectedN))).union
                   (CodeReq.singleton (succPC + 4) (.BNE .x11 .x10 lenFailOff)))).Disjoint
               ((CodeReq.singleton (succPC + 8) (.ADDI .x14 rOut fieldImm)).union
                 (byteCopyChainCR (succPC + 8 + 4) expectedN))) :
    (validatingShortBytesCopyBranch pfx rest bs O expectedN v10 v11Old v12Old v14Old
      regionBase rOut outBase fieldImm outBytes di0 off1 off2 succOff lenFailOff base e2Target
      h_class hns h_lfit h_target h_exp11 h_pl64 h_phase3 h_bltu succPC h_succ_pc h_len_fail
      h_salign h_dalign h_sover h_svalid h_src h_dst h_dov h_dval h_code h_imm h_addibne
      h_lencheck h_copy).exit_f = e2Target + 12 := by
  rfl

attribute [rv64_wp]
  validatingShortBytesCopyBranch_pre
  validatingShortBytesCopyBranch_exit_t
  validatingShortBytesCopyBranch_exit_f

attribute [rv64_wp_cert]
  validatingShortBytesCopyBranch


end EvmAsm.Rv64.RLP
