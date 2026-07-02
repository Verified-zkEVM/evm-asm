/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemLongBytesValidated

  Phase B of issue #9373 — the VALIDATING longBytes (`0xB8..0xBF`) RLP single-item decoder over
  UNTRUSTED input. The hardest single-item class: a long byte-string decodes iff
    (1) the `lenOfLen = pfx − 0xB7` length-field bytes are present (else `readLength` truncates),
    (2) the length field is canonical — no leading zero (for `lenOfLen ≥ 2`),
    (3) the decoded length `> 55` (else it should have used the short form), and
    (4) the `decodedLen` payload bytes are present.
  Otherwise `decode = none`. NO validity hypotheses on the input (`x15 = L` is the codegen K20
  untrusted-length contract).

  This is built bottom-up. `longbytes_front` (this file, step 1) is the register-only front: the
  e3 classify + Phase-3 long-string entry (`x14 = lenOfLen`, `x11 = 0`, `x13 = regionBase + 1`)
  followed by `BGEU x14, x15` — the length-field bound check (1). Fall-through (`lenOfLen < L`)
  continues with the bound fact in hand (so the length-read loop's window is satisfiable); the taken
  branch (`lenOfLen ≥ L`) is the truncated-length-field failure, `⌜decode = none⌝`. Steps 2–4 (leading-zero,
  `≤55`, payload-bound checks + the region length loop) compose on top in follow-ups.
-/

import EvmAsm.Rv64.RLP.Phase1E3FullPath
import EvmAsm.Rv64.MemRegion
import EvmAsm.EL.RLP.ByteStringDecodeBridge
import EvmAsm.EL.RLP.ReadLength

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
/-- **longBytes front — classify+entry ⨾ length-field bound check.** From an untrusted
    `bytesRegion regionBase (pfx :: rest)` with a `longBytes` prefix and `x15 = L`, runs the
    9-step e3 classify + Phase-3 long-string entry (leaving `x14 = ofNat lenOfLen`, `x11 = 0`,
    `x13 = regionBase + 1`) then `BGEU x14, x15`. The taken branch (`lenOfLen ≥ L`) is the truncated length field:
    `decode (pfx :: rest) = none`. Fall-through (`lenOfLen < L`) carries the bound fact for the
    downstream length-read loop and the canonical/payload checks. -/
theorem longbytes_front
    (pfx : Byte) (rest : List Byte)
    (v10 v11Old v12 v14Old : Word) (regionBase : Word)
    (off1 off2 off3 bgeuOff : BitVec 13) (base e3_target failPC : Word)
    (h_class : classifyPrefix pfx = .longBytes)
    (hover : regionBase.toNat + (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (hbgeu : (e3_target + 12) + signExtend13 bgeuOff = failPC)
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_blt :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.singleton (e3_target + 12) (.BGEU .x14 .x15 bgeuOff))) :
    let lenOfLen := rlpPrefixLongBytesLenOfLen pfx
    cpsBranchWithin 10 base
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
        (CodeReq.singleton (e3_target + 12) (.BGEU .x14 .x15 bgeuOff)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
      -- TAKEN (lenOfLen ≥ L): truncated length field ⇒ decode none.
      failPC
        ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest) = none⌝)
      -- FALL (lenOfLen < L): bound ok, continue.
      ((e3_target + 12) + 4)
        ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) **
          (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest) **
          ⌜lenOfLen < (pfx :: rest).length⌝) := by
  intro lenOfLen
  have hlol8 : lenOfLen ≤ 8 := rlpPrefixLongBytesLenOfLen_le_8_of_class h_class
  have hLfit : (pfx :: rest).length < 2 ^ 64 := by omega
  have hlol_lt : lenOfLen < 2 ^ 64 := by omega
  have hrange := (classifyPrefix_longBytes_iff pfx).mp h_class
  have hmod : pfx.toNat % 18446744073709551616 = pfx.toNat := Nat.mod_eq_of_lt (by omega)
  have hv5_lo : ¬ BitVec.ult (pfx.zeroExtend 64) ((0 : Word) + signExtend12 (0x80 : BitVec 12)) := by
    rw [BitVec.ult_eq_decide]; simp only [BitVec.toNat_setWidth]
    have hk : (((0 : Word) + signExtend12 (0x80 : BitVec 12)).toNat) = 0x80 := by decide
    rw [hk, hmod]; simp only [decide_eq_true_eq]; omega
  have hv5_mid : ¬ BitVec.ult (pfx.zeroExtend 64) ((0 : Word) + signExtend12 (0xB8 : BitVec 12)) := by
    rw [BitVec.ult_eq_decide]; simp only [BitVec.toNat_setWidth]
    have hk : (((0 : Word) + signExtend12 (0xB8 : BitVec 12)).toNat) = 0xB8 := by decide
    rw [hk, hmod]; simp only [decide_eq_true_eq]; omega
  have hv5_hi : BitVec.ult (pfx.zeroExtend 64) ((0 : Word) + signExtend12 (0xC0 : BitVec 12)) := by
    rw [BitVec.ult_eq_decide]; simp only [BitVec.toNat_setWidth]
    have hk : (((0 : Word) + signExtend12 (0xC0 : BitVec 12)).toNat) = 0xC0 := by decide
    rw [hk, hmod]; simp only [decide_eq_true_eq]; omega
  -- The bound-check verdict: `lenOfLen ≥ L` ⇒ the length field truncates ⇒ decode none.
  have hnone : ¬ lenOfLen < (pfx :: rest).length → decode (pfx :: rest) = none := by
    intro hge
    have htake : takeBytes rest lenOfLen = none := by
      unfold takeBytes; rw [if_neg (by simp only [List.length_cons] at hge ⊢; omega)]
    have hread : readLength rest lenOfLen = none := readLength_none_of_takeBytes_none htake
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl]
    exact decodeAux_cons_longBytes_eq_none_of_readLength_none (2 * rest.length + 1) pfx rest h_class hread
  -- The entry handler (9 steps), framed with x12/x15/region, with x14 rewritten to `ofNat lenOfLen`.
  have handler := rlp_phase1_e3_full_path_spec'_within (pfx.zeroExtend 64) v10 v11Old regionBase
    v14Old off1 off2 off3 base e3_target htarget hv5_lo hv5_mid hv5_hi hd_phase3
  have hx14 : (pfx.zeroExtend 64) + signExtend12 (-(0xB7 : BitVec 12))
      = BitVec.ofNat 64 lenOfLen := by
    have hs : signExtend12 (-(0xB7 : BitVec 12)) = -(0xB7 : Word) := by decide
    rw [hs, ← BitVec.sub_eq_add_neg, ← rlpPrefixLongBytesLenOfLen_toWord_of_class pfx h_class]
  rw [hx14] at handler
  have handlerF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
      bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))
    handler
  -- The bound check `BLTU x14, x15` (1 step).
  have bltF := cpsBranchWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
      bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (bytesRegion_pcFree _ _)))))))
    (bgeu_spec_gen_within .x14 .x15 bgeuOff (BitVec.ofNat 64 lenOfLen)
      (BitVec.ofNat 64 (pfx :: rest).length) (e3_target + 12))
  -- Reshape the handler's POST to the branch's PRE (x14/x15 first).
  have handlerF' := cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (Q' := (((.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) **
              (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length))) **
            ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
              (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) ** (.x11 ↦ᵣ (0 : Word)) **
              (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
              bytesRegion regionBase (pfx :: rest)))) handlerF
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd_blt handlerF' bltF
  rw [hbgeu] at composed
  -- Reshape PRE (xperm) and the two posts (verdict in / bound fact in).
  refine cpsBranchWithin_weaken
    (fun h hp => by
      have hp2 : (((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
          (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old)) **
          ((.x12 ↦ᵣ v12) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
            bytesRegion regionBase (pfx :: rest))) h := by xperm_hyp hp
      exact hp2)
    ?taken ?fall composed
  case taken =>
    intro h hp
    have hp2 : (((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest)) **
        ⌜¬ BitVec.ult (BitVec.ofNat 64 lenOfLen) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hnu⟩ := (sepConj_pure_right h).1 hp2
    have hge : ¬ lenOfLen < (pfx :: rest).length :=
      fun hlt => hnu ((ult_ofNat_lt _ _ hlol_lt hLfit).mpr hlt)
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hnone hge⟩
    xperm_hyp hgoal
  case fall =>
    intro h hp
    have hp2 : (((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest)) **
        ⌜BitVec.ult (BitVec.ofNat 64 lenOfLen) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hult⟩ := (sepConj_pure_right h).1 hp2
    have hlt : lenOfLen < (pfx :: rest).length := (ult_ofNat_lt _ _ hlol_lt hLfit).mp hult
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hlt⟩
    xperm_hyp hgoal

/-- **Pure verdict for the leading-zero check.** A `longBytes` prefix whose first length byte is
    `0` never decodes: for `lenOfLen ≥ 2` the length field has a leading zero (`readLength = none`);
    for `lenOfLen = 1` the decoded length is `0 ≤ 55` (short-form-required rejection). -/
theorem longbytes_leadzero_none (pfx b0 : Byte) (rest' : List Byte)
    (h_class : classifyPrefix pfx = .longBytes)
    (hb0 : b0 = 0)
    (hlen : rlpPrefixLongBytesLenOfLen pfx ≤ (b0 :: rest').length) :
    decode (pfx :: b0 :: rest') = none := by
  set n := rlpPrefixLongBytesLenOfLen pfx with hn
  have hn1 : 1 ≤ n := rlpPrefixLongBytesLenOfLen_pos_of_class h_class
  subst hb0
  rw [decode_cons_eq_decodeAux_fuel,
      show 2 * (0 :: rest').length + 2 = (2 * (0 :: rest').length + 1) + 1 from rfl]
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- lenOfLen = 1: readLength = some 0, rejected by the `≤ 55` check.
    have hn_eq : n = 1 := by omega
    have htake : takeBytes ((0 : Byte) :: rest') n = some ([0], rest') := by
      rw [hn_eq]; unfold takeBytes; rw [if_pos (by simp)]; simp
    have hread : readLength ((0 : Byte) :: rest') n = some (0, rest') := by
      rw [readLength_some_of_takeBytes_single htake]; simp
    exact decodeAux_cons_longBytes_eq_none_of_len_le_55 _ pfx ((0 : Byte) :: rest') rest' 0
      h_class hread (by norm_num)
  · -- lenOfLen ≥ 2: leading zero ⇒ readLength = none.
    obtain ⟨c, t, hsplit⟩ : ∃ c t, rest' = c :: t := by
      rcases rest' with _ | ⟨c, t⟩
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · exact ⟨c, t, rfl⟩
    subst hsplit
    obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have htake : takeBytes ((0 : Byte) :: c :: t) n
        = some ((0 : Byte) :: c :: t.take k, t.drop k) := by
      unfold takeBytes
      rw [if_pos (by simp only [List.length_cons] at hlen ⊢; omega), hk]
      rfl
    have hread : readLength ((0 : Byte) :: c :: t) n = none :=
      readLength_none_of_takeBytes_leading_zero htake
    exact decodeAux_cons_longBytes_eq_none_of_readLength_none _ pfx ((0 : Byte) :: c :: t) h_class hread

-- `hover` is consumed by `omega` inside `hover1`; the unused-variable linter cannot see into `omega`.
set_option linter.unusedVariables false in
set_option maxRecDepth 8000 in
/-- **longBytes leading-zero check.** From the bound-checked front state (`x13 = regionBase + 1`
    pointing at the first length byte, `x14 = ofNat lenOfLen`, `⌜lenOfLen < L⌝`), `LBU x12, x13, 0`
    reads that byte and `BEQ x12, x0` rejects a leading zero: taken (`byte = 0`) ⇒ `decode = none`
    (uniformly — via `longbytes_leadzero_none`); fall (`byte ≠ 0`) continues with the no-leading-zero
    fact for the length-read loop. -/
theorem longbytes_leadzero
    (pfx : Byte) (rest : List Byte) (regionBase : Word)
    (beqOff : BitVec 13) (lbuPC failPC : Word)
    (h_class : classifyPrefix pfx = .longBytes)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (pfx :: rest).length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 1) = true)
    (hbeq : (lbuPC + 4) + signExtend13 beqOff = failPC)
    (hd_lb : (CodeReq.singleton lbuPC (.LBU .x12 .x13 0)).Disjoint
               (CodeReq.singleton (lbuPC + 4) (.BEQ .x12 .x0 beqOff))) :
    let lenOfLen := rlpPrefixLongBytesLenOfLen pfx
    cpsBranchWithin 2 lbuPC
      ((CodeReq.singleton lbuPC (.LBU .x12 .x13 0)).union
        (CodeReq.singleton (lbuPC + 4) (.BEQ .x12 .x0 beqOff)))
      ((.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase (pfx :: rest) ** ⌜lenOfLen < (pfx :: rest).length⌝)
      -- TAKEN (byte = 0): leading zero ⇒ decode none.
      failPC
        ((.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** regOwn .x12 **
          (.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: rest) ** ⌜decode (pfx :: rest) = none⌝)
      -- FALL (byte ≠ 0): continue with the no-leading-zero fact.
      (lbuPC + 4 + 4)
        ((.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** regOwn .x12 **
          (.x14 ↦ᵣ (BitVec.ofNat 64 lenOfLen)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: rest) **
          ⌜lenOfLen < (pfx :: rest).length ∧ rest.headD 0 ≠ 0⌝) := by
  intro lenOfLen
  have hn1 : 1 ≤ lenOfLen := rlpPrefixLongBytesLenOfLen_pos_of_class h_class
  have hsext1 : (regionBase + signExtend12 (1 : BitVec 12)) = regionBase + BitVec.ofNat 64 1 := by
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]
  rw [hsext1]
  rcases hrest : rest with _ | ⟨b0, rest1⟩
  · -- Empty rest: the carried bound `lenOfLen < 1` contradicts `1 ≤ lenOfLen`.
    intro R hR s hcr hPR hpc
    exfalso
    have h1 := holdsFor_sepConj_elim_left hPR
    have h2 := holdsFor_sepConj_elim_right h1
    have h3 := holdsFor_sepConj_elim_right h2
    have h4 := holdsFor_sepConj_elim_right h3
    have h5 := holdsFor_sepConj_elim_right h4
    have h6 := holdsFor_sepConj_elim_right h5
    have h7 := holdsFor_sepConj_elim_right h6
    have hlt : lenOfLen < ([pfx] : List Byte).length := holdsFor_pure.mp h7
    simp only [List.length_cons, List.length_nil] at hlt
    omega
  · -- A first length byte `b0` exists at region index 1.
    have hi : 1 < (pfx :: b0 :: rest1).length := by simp
    have hover1 : regionBase.toNat + 1 < 2 ^ 64 := by
      have : (1 : Nat) ≤ (pfx :: b0 :: rest1).length := by simp
      omega
    have hb0z : ∀ {w : BitVec 8}, (w.zeroExtend 64 = (0 : Word)) → w = 0 := by
      intro w hw
      have h := congrArg BitVec.toNat hw
      rw [BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (show w.toNat < 18446744073709551616 by have := w.isLt; omega)] at h
      exact BitVec.eq_of_toNat_eq (by simpa using h)
    -- LBU x12, x13, 0 — load `b0`.
    have lbu := bytesRegion_lbu_within .x12 .x13 regionBase (0 : Word) lbuPC
      (pfx :: b0 :: rest1) 1 (by nofun) halign hi hover1 hvalid
    rw [show (pfx :: b0 :: rest1)[1]'hi = b0 from rfl] at lbu
    have s_lbu : cpsTripleWithin 1 lbuPC (lbuPC + 4)
        (CodeReq.singleton lbuPC (.LBU .x12 .x13 0))
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: b0 :: rest1) **
          ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝)
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ b0.zeroExtend 64) **
          (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: b0 :: rest1) **
          ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝)
          (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs pcFree_pure))) lbu)
    have s_beq : cpsBranchWithin 1 (lbuPC + 4)
        (CodeReq.singleton (lbuPC + 4) (.BEQ .x12 .x0 beqOff))
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ b0.zeroExtend 64) **
          (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: b0 :: rest1) **
          ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝)
        failPC
          ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ b0.zeroExtend 64) **
            (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion regionBase (pfx :: b0 :: rest1) **
            ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝ ** ⌜b0.zeroExtend 64 = (0 : Word)⌝)
        (lbuPC + 4 + 4)
          ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ b0.zeroExtend 64) **
            (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion regionBase (pfx :: b0 :: rest1) **
            ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝ ** ⌜b0.zeroExtend 64 ≠ (0 : Word)⌝) := by
      have beq_raw := beq_spec_gen_within .x12 .x0 beqOff (b0.zeroExtend 64) (0 : Word) (lbuPC + 4)
      rw [hbeq, show (lbuPC + 4 : Word) + 4 = lbuPC + 4 + 4 from by bv_omega] at beq_raw
      exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by xperm_hyp hp)
        (cpsBranchWithin_frameR
          ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) **
            (.x11 ↦ᵣ (0 : Word)) ** bytesRegion regionBase (pfx :: b0 :: rest1) **
            ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝)
          (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure))))
          beq_raw)
    have composed := cpsTripleWithin_seq_cpsBranchWithin hd_lb s_lbu s_beq
    refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?taken ?fall composed
    case taken =>
      intro h hp
      have hp2 : ((((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ b0.zeroExtend 64) **
          (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: b0 :: rest1)) ** ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝) **
          ⌜b0.zeroExtend 64 = (0 : Word)⌝) h := by xperm_hyp hp
      obtain ⟨hr1, hz⟩ := (sepConj_pure_right h).1 hp2
      obtain ⟨hregs, hbnd⟩ := (sepConj_pure_right h).1 hr1
      have hlen : lenOfLen ≤ (b0 :: rest1).length := by
        simp only [List.length_cons] at hbnd ⊢; omega
      have hdec : decode (pfx :: b0 :: rest1) = none :=
        longbytes_leadzero_none pfx b0 rest1 h_class (hb0z hz) hlen
      have hregOwn : ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** regOwn .x12 **
          (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: b0 :: rest1)) h :=
        (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))) h hregs
      have hgoal := (sepConj_pure_right h).2 ⟨hregOwn, hdec⟩
      xperm_hyp hgoal
    case fall =>
      intro h hp
      have hp2 : ((((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ b0.zeroExtend 64) **
          (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: b0 :: rest1)) ** ⌜lenOfLen < (pfx :: b0 :: rest1).length⌝) **
          ⌜b0.zeroExtend 64 ≠ (0 : Word)⌝) h := by xperm_hyp hp
      obtain ⟨hr1, hne⟩ := (sepConj_pure_right h).1 hp2
      obtain ⟨hregs, hbnd⟩ := (sepConj_pure_right h).1 hr1
      have hb0ne : (b0 :: rest1).headD 0 ≠ 0 := by
        simp only [List.headD_cons]; intro hb; subst hb; exact hne (by decide)
      have hregOwn : ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** regOwn .x12 **
          (.x14 ↦ᵣ BitVec.ofNat 64 lenOfLen) ** (.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase (pfx :: b0 :: rest1)) h :=
        (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))) h hregs
      have hgoal := (sepConj_pure_right h).2 ⟨hregOwn,
        (⟨hbnd, hb0ne⟩ : lenOfLen < (pfx :: b0 :: rest1).length ∧ (b0 :: rest1).headD 0 ≠ 0)⟩
      xperm_hyp hgoal

end EvmAsm.Rv64.RLP
