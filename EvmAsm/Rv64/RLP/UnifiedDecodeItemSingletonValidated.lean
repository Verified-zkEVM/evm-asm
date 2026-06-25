/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemSingletonValidated

  Phase B.3 of issue #9373 — the `0x81` SINGLETON-canonical sub-branch of the validating
  shortBytes decoder over UNTRUSTED input. Completes the shortBytes class: B.1
  (`rlp_decode_shortBytes_validated`) covered the non-singleton case (`payloadLen ≠ 1`); this
  covers `payloadLen = 1` (prefix `0x81`), where RLP additionally requires the single payload
  byte to be `≥ 0x80` (else it should have been a bare single-byte encoding — non-canonical).

  Two checks after the shortBytes handler (x11 = 1, x13 = payloadPtr):
    BGEU x11, x15  — bound: `1 ≥ L` ⇒ truncated ⇒ FAIL; `1 < L` ⇒ a payload byte exists.
    LBU x12,x13,0 ; ANDI x10,x12,0x80 ; BEQ x10,x0 — canonical: `b & 0x80 = 0` (`b < 0x80`)
      ⇒ non-canonical ⇒ FAIL; else (`b ≥ 0x80`) ⇒ SUCCESS.
  Both failure routes converge on one `failPC`; success falls through to `e2_target + 24`.
  Result is a 2-exit `cpsBranchWithin` with `⌜decode = none⌝` / `⌜decode = some (.bytes …)⌝`
  posts and NO validity hypotheses (the codegen K20 untrusted-length contract `x15 = L`).
-/

import EvmAsm.Rv64.RLP.Phase1E2FullPath
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.RLP.SingleByteListLoopValidated
import EvmAsm.EL.RLP.ByteStringDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.EL.RLP.ByteStringDecodeBridge
open EvmAsm.Rv64.Tactics

/-- The branch comparison `ult (ofNat a) (ofNat b)` is the `Nat` fact `a < b` when both fit. -/
private theorem ult_ofNat_lt (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) ↔ a < b := by
  rw [BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, decide_eq_true_eq]

set_option maxRecDepth 8000 in
/-- **B1 — handler ⨾ bound check.** The shortBytes handler (6 steps, `x11 = ofNat len`,
    `x13 = regionBase + 1`) followed by `BGEU x11, x15` (1 step). Taken (`¬ult`, i.e. `len ≥ L`)
    exits at `failPC`; fall (`ult`, `len < L`) at `e2_target + 12`, carrying the bound fact. -/
theorem singleton_B1
    (pfx : Byte) (rest : List Byte)
    (v10 v11Old v12Old v14 : Word) (regionBase : Word)
    (off1 off2 bgeuOff : BitVec 13) (base e2_target failPC : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hbgeu : (e2_target + 8) + signExtend13 bgeuOff = failPC)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bgeu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BGEU .x11 .x15 bgeuOff))) :
    let len := rlpPrefixShortBytesPayloadLen pfx
    cpsBranchWithin 7 base
      ((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BGEU .x11 .x15 bgeuOff)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
      failPC
        (((.x11 ↦ᵣ (BitVec.ofNat 64 len)) **
            (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
            ⌜¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) **
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
            (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
            (.x14 ↦ᵣ v14) ** bytesRegion regionBase (pfx :: rest)))
      (e2_target + 12)
        (((.x11 ↦ᵣ (BitVec.ofNat 64 len)) **
            (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
            ⌜BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) **
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
            (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
            (.x14 ↦ᵣ v14) ** bytesRegion regionBase (pfx :: rest))) := by
  intro len
  -- The valid-path handler (6 steps), framed with x12/x14/x15/region.
  have handler := rlp_phase1_e2_full_path_payload_len_of_class_spec_within
    pfx v10 v11Old regionBase off1 off2 base e2_target htarget h_class hd_phase3
  have handlerF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14) **
     (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))) handler
  -- The bound check `BGEU x11, x15` (1 step) at e2_target+8.
  have bgeuF := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
      (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
      bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (bytesRegion_pcFree _ _)))))))
    (bgeu_spec_gen_within .x11 .x15 bgeuOff (BitVec.ofNat 64 len)
      (BitVec.ofNat 64 (pfx :: rest).length) (e2_target + 8))
  -- Reshape the handler's POST to exactly the branch's PRE.
  have handlerF' := cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (Q' := (((.x11 ↦ᵣ (BitVec.ofNat 64 len)) **
              (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length))) **
            ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
              (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
              bytesRegion regionBase (pfx :: rest)))) handlerF
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd_bgeu handlerF' bgeuF
  rw [hbgeu, show e2_target + 8 + 4 = e2_target + 12 from by bv_omega] at composed
  -- Reshape PRE (xperm) and the two posts (regroup the pure fact in).
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?taken ?fall composed
  case taken => intro h hp; xperm_hyp hp
  case fall => intro h hp; xperm_hyp hp

/-- `signExtend12 (0x80 : BitVec 12) = (0x80 : Word)` — the mask is positive, no sign fill. -/
private theorem sext12_0x80 : signExtend12 (0x80 : BitVec 12) = (0x80 : Word) := by decide

/-- `signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1`. -/
private theorem sext12_one : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide

/-- `b < 0x80` ⇒ masking bit 7 yields zero (the converse direction of the existing
    `byte_zext_and_0x80_eq_zero_imp_lt`). -/
private theorem byte_lt_0x80_imp_and_zero {b : BitVec 8} (hlt : b.toNat < 0x80) :
    (b.zeroExtend 64) &&& (0x80 : Word) = 0 := by
  have hb7 : b.getLsbD 7 = false := by
    have hmsb : b.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega)
    rwa [BitVec.msb_eq_getLsbD_last] at hmsb
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  by_cases h7i : i = 7
  · subst h7i; simpa using hb7
  · have h80 : (0x80 : Word).getLsbD i = false := by
      simp only [show (0x80 : Word) = BitVec.ofNat 64 128 from rfl, BitVec.getLsbD_ofNat,
        show (128 : Nat) = 2 ^ 7 from rfl, Nat.testBit_two_pow]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    rw [h80, Bool.and_false]
    simp

/-- A masked-off bit-7 byte that is *nonzero* is `≥ 0x80` (canonical singleton payload). -/
private theorem byte_zext_and_0x80_ne_zero_imp_ge {b : BitVec 8}
    (h : (b.zeroExtend 64) &&& (0x80 : Word) ≠ 0) : ¬ b.toNat < 0x80 :=
  fun hlt => h (byte_lt_0x80_imp_and_zero hlt)

-- `hover` is consumed by `omega` inside `hover1`; the unused-variable linter cannot see into `omega`.
set_option linter.unusedVariables false in
set_option maxRecDepth 8000 in
/-- **B2 — canonical check.** From B1's fall post (a payload byte exists: `⌜ult (ofNat 1) (ofNat L)⌝`),
    `LBU x12,x13,0 ; ANDI x10,x12,0x80 ; BEQ x10,x0` (3 steps). Taken (`b < 0x80`, non-canonical)
    exits at `failPC` with `⌜decode = none⌝`; fall (`b ≥ 0x80`) at `e2_target + 24` with the success
    verdict. Proved by `rcases rest`: empty payload contradicts the carried bound. -/
theorem singleton_B2
    (pfx : Byte) (rest : List Byte)
    (v12Old v14 : Word) (regionBase : Word)
    (beqOff : BitVec 13) (e2_target failPC : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hsingle : rlpPrefixShortBytesPayloadLen pfx = 1)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (pfx :: rest).length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 1) = true)
    (hbeq : (e2_target + 20) + signExtend13 beqOff = failPC)
    (hd_la : (CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).Disjoint
               (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80)))
    (hd_lab : ((CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).union
                 (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))).Disjoint
               (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff))) :
    cpsBranchWithin 3 (e2_target + 12)
      (((CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).union
          (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))).union
        (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff)))
      (((.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          ⌜BitVec.ult (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))
            (BitVec.ofNat 64 (pfx :: rest).length)⌝) **
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14) ** bytesRegion regionBase (pfx :: rest)))
      failPC
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (.x11 ↦ᵣ (BitVec.ofNat 64 1)) ** regOwn .x12 **
          (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest) = none⌝)
      (e2_target + 24)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (.x11 ↦ᵣ (BitVec.ofNat 64 1)) ** regOwn .x12 **
          (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest) = some (.bytes (rest.take 1), rest.drop 1)⌝) := by
  have hover1 : regionBase.toNat + 1 < 2 ^ 64 := by
    have : (1 : Nat) ≤ (pfx :: rest).length := by simp
    omega
  rcases hrest : rest with _ | ⟨b, rest'⟩
  · -- Empty payload: the carried bound `ult (ofNat 1) (ofNat 1)` is false ⇒ vacuous.
    intro R hR s hcr hPR hpc
    exfalso
    -- Peel the carried `⌜ult⌝` out of the precondition's first group.
    have h1 := holdsFor_sepConj_elim_left hPR
    have h2 := holdsFor_sepConj_elim_left h1
    have h3 := holdsFor_sepConj_elim_right h2
    have h4 := holdsFor_sepConj_elim_right h3
    have hult : BitVec.ult (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))
        (BitVec.ofNat 64 ([pfx]).length) = true := holdsFor_pure.mp h4
    rw [hsingle] at hult
    have hlt : (1 : Nat) < ([pfx]).length :=
      (ult_ofNat_lt 1 _ (by norm_num) (by simp)).mp hult
    simp at hlt
  · -- A payload byte `b` exists at region index 1; run the canonical check.
    have hi : 1 < (pfx :: b :: rest').length := by simp
    have hbyte : (pfx :: b :: rest')[1]'hi = b := rfl
    -- LBU x12, x13, 0 — load `b` into x12 (x13 = regionBase + 1).
    have lbu := bytesRegion_lbu_within .x12 .x13 regionBase v12Old (e2_target + 12)
      (pfx :: b :: rest') 1 (by nofun) halign hi hover1 hvalid
    rw [hbyte, show e2_target + 12 + 4 = e2_target + 16 from by bv_omega] at lbu
    -- The two pure verdicts.
    have hsome : (b.zeroExtend 64) &&& signExtend12 (0x80 : BitVec 12) ≠ 0 →
        decode (pfx :: b :: rest') = some (.bytes [b], rest') := by
      intro hne
      rw [sext12_0x80] at hne
      have hge : ¬ b.toNat < 0x80 := byte_zext_and_0x80_ne_zero_imp_ge hne
      have htake : takeBytes (b :: rest') (rlpPrefixShortBytesPayloadLen pfx)
          = some ([b], rest') := by
        rw [hsingle]; unfold takeBytes; rw [if_pos (by simp)]; simp
      rw [decode_cons_eq_decodeAux_fuel,
          show 2 * (b :: rest').length + 2 = (2 * (b :: rest').length + 1) + 1 from rfl,
          decodeAux_cons_shortBytes_eq_some_iff (2 * (b :: rest').length + 1) pfx (b :: rest')
            h_class [b] rest']
      exact ⟨[b], htake, rfl, hge⟩
    have hnone : (b.zeroExtend 64) &&& signExtend12 (0x80 : BitVec 12) = 0 →
        decode (pfx :: b :: rest') = none := by
      intro heq
      rw [sext12_0x80] at heq
      have hlt : b.toNat < 0x80 := byte_zext_and_0x80_eq_zero_imp_lt heq
      have htake : takeBytes (b :: rest') (rlpPrefixShortBytesPayloadLen pfx)
          = some ([b], rest') := by
        rw [hsingle]; unfold takeBytes; rw [if_pos (by simp)]; simp
      rw [decode_cons_eq_decodeAux_fuel,
          show 2 * (b :: rest').length + 2 = (2 * (b :: rest').length + 1) + 1 from rfl]
      exact decodeAux_cons_shortBytes_eq_none_of_singleton_short
        (2 * (b :: rest').length + 1) pfx b (b :: rest') rest' h_class htake hlt
    -- Abbreviations for the uniform state.
    set len := rlpPrefixShortBytesPayloadLen pfx with hlendef
    set L := (pfx :: b :: rest').length with hLdef
    set bz := b.zeroExtend 64 with hbzdef
    set mask := bz &&& signExtend12 (0x80 : BitVec 12) with hmaskdef
    set x10i := (0 : Word) + signExtend12 (0xB8 : BitVec 12) with hx10idef
    rw [sext12_one]
    -- Step 1: LBU x12, x13, 0 — load `b` into x12 (3-step composite below).
    have s_lbu : cpsTripleWithin 1 (e2_target + 12) (e2_target + 16)
        (CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10i) **
         (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ v12Old) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
         (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest'))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10i) **
         (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ bz) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
         (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest')) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10i) **
           (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ BitVec.ofNat 64 L))
          (by pcFree) lbu)
    -- Step 2: ANDI x10, x12, 0x80 — mask bit 7.
    have s_andi : cpsTripleWithin 1 (e2_target + 16) (e2_target + 20)
        (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10i) **
         (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ bz) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
         (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest'))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ mask) **
         (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ bz) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
         (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest')) := by
      have andi_raw := andi_spec_gen_within .x10 .x12 x10i bz 0x80 (e2_target + 16) (by nofun)
      rw [show e2_target + 16 + 4 = e2_target + 20 from by bv_omega] at andi_raw
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
           (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
           (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest'))
          (by pcFree) andi_raw)
    -- Step 3: BEQ x10, x0 — branch on the masked value.
    have s_beq : cpsBranchWithin 1 (e2_target + 20)
        (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ mask) **
         (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ bz) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
         (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest'))
        failPC
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ mask) **
           (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ bz) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
           (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest') **
           ⌜mask = 0⌝)
        (e2_target + 24)
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ mask) **
           (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ bz) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
           (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest') **
           ⌜mask ≠ 0⌝) := by
      have beq_raw := beq_spec_gen_within .x10 .x0 beqOff mask (0 : Word) (e2_target + 20)
      rw [hbeq, show (e2_target + 20 : Word) + 4 = e2_target + 24 from by bv_omega] at beq_raw
      exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by xperm_hyp hp)
        (cpsBranchWithin_frameR
          ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ bz) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
           (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest'))
          (by pcFree) beq_raw)
    -- Chain the three steps.
    have t12 := cpsTripleWithin_seq hd_la s_lbu s_andi
    have composed := cpsTripleWithin_seq_cpsBranchWithin hd_lab t12 s_beq
    have hlen1 : len = 1 := hlendef.trans hsingle
    -- Reshape PRE (drop the carried `⌜ult⌝`, reorder) and POSTs (verdict + regOwn scratch).
    refine cpsBranchWithin_weaken ?pre ?taken ?fall composed
    case pre =>
      intro h hp
      have hp2 : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10i) **
          (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest')) **
          ⌜BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 L)⌝) h := by xperm_hyp hp
      exact ((sepConj_pure_right h).1 hp2).1
    case taken =>
      intro h hp
      have hp2 : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 len) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest') **
          (.x10 ↦ᵣ mask) ** (.x12 ↦ᵣ bz)) ** ⌜mask = 0⌝) h := by xperm_hyp hp
      obtain ⟨hregs, heq0⟩ := (sepConj_pure_right h).1 hp2
      have hdec : decode (pfx :: b :: rest') = none := hnone heq0
      rw [hlen1] at hregs
      have hregs' : ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 1) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest') **
          regOwn .x10 ** regOwn .x12) h :=
        (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
            (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
              (sepConj_mono (fun _ h => h)
                (sepConj_mono (regIs_implies_regOwn .x10) (regIs_implies_regOwn .x12)))))))))
          h hregs
      have hgoal := (sepConj_pure_right h).2 ⟨hregs', hdec⟩
      xperm_hyp hgoal
    case fall =>
      intro h hp
      have hp2 : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 len) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest') **
          (.x10 ↦ᵣ mask) ** (.x12 ↦ᵣ bz)) ** ⌜mask ≠ 0⌝) h := by xperm_hyp hp
      obtain ⟨hregs, hne0⟩ := (sepConj_pure_right h).1 hp2
      have hdec : decode (pfx :: b :: rest') = some (.bytes [b], rest') := hsome hne0
      rw [hlen1] at hregs
      have hregs' : ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 1) **
          (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ BitVec.ofNat 64 L) ** bytesRegion regionBase (pfx :: b :: rest') **
          regOwn .x10 ** regOwn .x12) h :=
        (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
            (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
              (sepConj_mono (fun _ h => h)
                (sepConj_mono (regIs_implies_regOwn .x10) (regIs_implies_regOwn .x12)))))))))
          h hregs
      have hgoal := (sepConj_pure_right h).2 ⟨hregs', by
        show decode (pfx :: b :: rest') = some (.bytes ((b :: rest').take 1), (b :: rest').drop 1)
        simpa using hdec⟩
      xperm_hyp hgoal

set_option maxRecDepth 8000 in
/-- **Validating singleton (`0x81`) single-item decoder, at offset 0.** Composes the bound check
    (B1) with the canonical check (B2). From an untrusted `bytesRegion regionBase (pfx :: rest)` with
    a `shortBytes` prefix of payload length 1 and `x15 = L`, runs the handler then `BGEU` (truncation)
    and `LBU/ANDI/BEQ` (canonicity). Both failure routes converge at `failPC` with `⌜decode = none⌝`;
    success falls through to `e2_target + 24` with `⌜decode = some (.bytes (rest.take 1), rest.drop 1)⌝`.
    No validity hypotheses on the input — this completes the shortBytes class (drops B.1's `hns`). -/
theorem rlp_decode_singleton_validated
    (pfx : Byte) (rest : List Byte)
    (v10 v11Old v12Old v14 : Word) (regionBase : Word)
    (off1 off2 bgeuOff beqOff : BitVec 13) (base e2_target failPC : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hsingle : rlpPrefixShortBytesPayloadLen pfx = 1)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (pfx :: rest).length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 1) = true)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hbgeu : (e2_target + 8) + signExtend13 bgeuOff = failPC)
    (hbeq : (e2_target + 20) + signExtend13 beqOff = failPC)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bgeu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BGEU .x11 .x15 bgeuOff)))
    (hd_la : (CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).Disjoint
               (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80)))
    (hd_lab : ((CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).union
                 (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))).Disjoint
               (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff)))
    (hd_b1b2 : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                (CodeReq.singleton (e2_target + 8) (.BGEU .x11 .x15 bgeuOff))).Disjoint
               (((CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).union
                  (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))).union
                (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff)))) :
    cpsBranchWithin 10 base
      (((((rlp_phase1_step_code 0x80 off1 base).union
            (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
           (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
          (CodeReq.singleton (e2_target + 8) (.BGEU .x11 .x15 bgeuOff))).union
        (((CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).union
            (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))).union
          (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff))))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
      failPC
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (.x11 ↦ᵣ (BitVec.ofNat 64 1)) ** regOwn .x12 **
          (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest) = none⌝)
      (e2_target + 24)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (.x11 ↦ᵣ (BitVec.ofNat 64 1)) ** regOwn .x12 **
          (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest) = some (.bytes (rest.take 1), rest.drop 1)⌝) := by
  have hB1 := singleton_B1 pfx rest v10 v11Old v12Old v14 regionBase off1 off2 bgeuOff
    base e2_target failPC h_class htarget hbgeu hd_phase3 hd_bgeu
  have hB2 := singleton_B2 pfx rest v12Old v14 regionBase beqOff e2_target failPC
    h_class hsingle halign hover hvalid hbeq hd_la hd_lab
  refine cpsBranchWithin_seq_cpsBranchWithin hd_b1b2 hB1 hB2 ?ht1 (fun _ h => h)
  -- ht1: B1's taken exit (truncated, `¬ult`) also yields `⌜decode = none⌝`.
  intro h hp
  have hp2 : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx)) **
      (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
      (.x15 ↦ᵣ BitVec.ofNat 64 (pfx :: rest).length) **
      bytesRegion regionBase (pfx :: rest) **
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old)) **
      ⌜¬ BitVec.ult (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))
        (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by xperm_hyp hp
  obtain ⟨hregs, hnu⟩ := (sepConj_pure_right h).1 hp2
  -- The truncation verdict: `¬ult` with payloadLen 1 forces `rest = []`, so `takeBytes` fails.
  have hLfit : (pfx :: rest).length < 2 ^ 64 := by omega
  have hdec : decode (pfx :: rest) = none := by
    have hge : ¬ rlpPrefixShortBytesPayloadLen pfx < (pfx :: rest).length := by
      intro hlt
      exact hnu ((ult_ofNat_lt _ _ (by rw [hsingle]; norm_num) hLfit).mpr hlt)
    rw [hsingle] at hge
    have hempty : rest = [] := by
      rcases rest with _ | ⟨c, t⟩
      · rfl
      · exact absurd (by simp : (1 : Nat) < (pfx :: c :: t).length) hge
    subst hempty
    have htake : takeBytes ([] : List Byte) (rlpPrefixShortBytesPayloadLen pfx) = none := by
      rw [hsingle]; unfold takeBytes; rw [if_neg (by simp)]
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * ([] : List Byte).length + 2 = (2 * ([] : List Byte).length + 1) + 1 from rfl]
    exact decodeAux_cons_shortBytes_eq_none_of_takeBytes_none _ pfx [] h_class htake
  rw [hsingle] at hregs
  have hregs' : ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ BitVec.ofNat 64 1) **
      (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14) **
      (.x15 ↦ᵣ BitVec.ofNat 64 (pfx :: rest).length) ** bytesRegion regionBase (pfx :: rest) **
      regOwn .x10 ** regOwn .x12) h :=
    (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
      (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h) (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h)
            (sepConj_mono (regIs_implies_regOwn .x10) (regIs_implies_regOwn .x12)))))))))
      h hregs
  have hgoal := (sepConj_pure_right h).2 ⟨hregs', hdec⟩
  xperm_hyp hgoal

-- Concrete cross-check: the canonical singleton `0x81 0xFF` (`0xFF ≥ 0x80`) is a valid RLP
-- encoding; the validating decoder's success exit applies (`classifyPrefix 0x81 = .shortBytes`,
-- `rlpPrefixShortBytesPayloadLen 0x81 = 1`, both by `decide`). The address/disjointness
-- side-conditions ride as parameters (a concrete program discharges them).
example (regionBase base e2_target failPC : Word) (off1 off2 bgeuOff beqOff : BitVec 13)
    (v10 v11 v12 v14 : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + ((0x81 : Byte) :: [0xFF]).length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 1) = true)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hbgeu : (e2_target + 8) + signExtend13 bgeuOff = failPC)
    (hbeq : (e2_target + 20) + signExtend13 beqOff = failPC)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bgeu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BGEU .x11 .x15 bgeuOff)))
    (hd_la : (CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).Disjoint
               (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80)))
    (hd_lab : ((CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).union
                 (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))).Disjoint
               (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff)))
    (hd_b1b2 : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                (CodeReq.singleton (e2_target + 8) (.BGEU .x11 .x15 bgeuOff))).Disjoint
               (((CodeReq.singleton (e2_target + 12) (.LBU .x12 .x13 0)).union
                  (CodeReq.singleton (e2_target + 16) (.ANDI .x10 .x12 0x80))).union
                (CodeReq.singleton (e2_target + 20) (.BEQ .x10 .x0 beqOff)))) :=
  rlp_decode_singleton_validated (0x81 : Byte) [0xFF] v10 v11 v12 v14 regionBase
    off1 off2 bgeuOff beqOff base e2_target failPC (by decide) (by decide) halign hover hvalid
    htarget hbgeu hbeq hd_phase3 hd_bgeu hd_la hd_lab hd_b1b2

end EvmAsm.Rv64.RLP
