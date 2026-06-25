/-
  EvmAsm.Rv64.RLP.ValidatingFieldWalk

  Composition glue for the untrusted RLP field walker (F1 of the verified guest-decoder plan,
  #9373). The validating single-item decoders are 2-exit `cpsBranchWithin`s whose SUCCESS is the
  *taken* exit and FAIL the fall-through. To advance to the next field after a successful decode,
  we must sequence the pointer-advance instructions on the **taken** (success) exit — but the
  existing `cpsBranchWithin_seq_cpsTripleWithin_same_cr` (CPSSpec) only sequences on the fall side.

  `cpsBranchWithin_seq_cpsTripleWithin_taken` is the missing dual: it continues the taken branch
  into a follow-on triple (keeping the fall exit as the abort path), with a CodeReq union. It is the
  reusable step that turns "validating-decode at offset O" into "validating-decode-and-advance".
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.RLP.UnifiedDecodeItemShortBytesValidatedAt
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Rv64

/-- Sequence a triple onto the **taken** (success) exit of a branch, keeping the fall-through exit
    as the (abort) exit. Dual of `cpsBranchWithin_seq_cpsTripleWithin_same_cr`, with a CodeReq
    union. Bounds add. -/
theorem cpsBranchWithin_seq_cpsTripleWithin_taken {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q_t1 Q_f1 Q_t2 : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr1 P mid Q_t1 exit_f Q_f1)
    (h2 : cpsTripleWithin nSteps2 mid target cr2 Q_t1 Q_t2) :
    cpsBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P target Q_t2 exit_f Q_f1 := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr1 hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · -- taken (success): continue into the follow-on triple.
    have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQ_t2R⟩ := h2 R hR s1 hcr2' hQ_t1R hpc_t1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
      Or.inl ⟨hpc2, hQ_t2R⟩⟩
  · -- fall (abort): keep the fall-through exit.
    exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      Or.inr ⟨hpc_f1, hQ_f1R⟩⟩

namespace RLP

open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Validating shortBytes decode-and-advance** (one field step of the untrusted walk, F1 of
    #9373). Runs the offset-general validating shortBytes decoder at byte offset `O`
    (`rlp_decode_shortBytes_validated_at`) and, on its SUCCESS (taken) exit, sequences
    `ADD x13, x13, x11` to advance the cursor `x13` past the just-decoded item's payload.

    SUCCESS post: `x13 = (regionBase + O) + 1 + payloadLen` (item start + prefix + payload — the
    next item start), carrying the pure verdict `decode (pfx :: rest) = some (.bytes …)`. FAIL
    (fall) is the decoder's abort exit unchanged (`decode = none`). -/
theorem rlp_decode_shortBytes_advance_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word)
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
    (hd_add : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))) :
    cpsBranchWithin (7 + 1) base
      (((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        (CodeReq.singleton succPC (.ADD .x13 .x13 .x11)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
      -- SUCCESS (taken): item decoded; cursor advanced past the payload.
      (succPC + 4)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))
                    + BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      -- FAIL (fall): the decoder's abort exit, unchanged.
      (e2_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) := by
  -- The validating decoder at offset `O` (taken = success).
  have decAt := rlp_decode_shortBytes_validated_at pfx rest bs O v10 v11Old v12Old v14Old
    regionBase off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu
  rw [hsuccPC] at decAt
  -- ADD x13, x13, x11 at `succPC`, framed with the 8-atom complement (incl. the pure verdict).
  have add_raw := add_spec_gen_rd_eq_rs1_within .x13 .x11
    ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))
    (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx)) succPC (by nofun)
  have addF : cpsTripleWithin 1 succPC (succPC + 4)
      (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
        (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest)
          = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                  rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
        (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))
                  + BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest)
          = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                  rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure)))))))
        add_raw)
  exact cpsBranchWithin_seq_cpsTripleWithin_taken hd_add decAt addF

end RLP

end EvmAsm.Rv64
