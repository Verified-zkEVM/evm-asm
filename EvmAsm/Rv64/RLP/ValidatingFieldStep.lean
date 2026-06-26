/-
  EvmAsm.Rv64.RLP.ValidatingFieldStep

  Inter-field glue for the SINGLE-PASS untrusted RLP field walker (F1 of #9373). After a validating
  decode-and-advance (`ValidatingFieldWalk.rlp_decode_shortBytes_advance_at`) the cursor `x13` points
  at the next item, but the loop-invariant register `x15` (remaining byte count `bs.length - O`) and
  the prefix register `x5` still describe the *just-consumed* field. This file proves the two register
  updates that re-establish the next field's precondition without a second pass over the input:

      SUB  x15, x15, x11        ; x15 := remaining − payloadLen
      ADDI x15, x15, -1         ; x15 := remaining − payloadLen − 1   (= bytes left from next item)

  `rv64_x15_minus_x11_minus_one` is a generic, position-parameterized 2-instruction spec
  (`x15 := x15 − x11 − 1`), decoupled from the advance unit's PC layout so it composes regardless of
  what store/extract instructions the single-pass walk places before it. The RLP-specific length
  bookkeeping is supplied separately by `x15_remaining_decrement` (a pure `BitVec.ofNat` identity).
-/

import EvmAsm.Rv64.RLP.ValidatingFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

/-- `signExtend12 (-1)` is the all-ones word `-1`. -/
private theorem signExtend12_neg_one : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide

/-- General `ofNat` subtraction: for `b ≤ a < 2^64`, `ofNat a − ofNat b = ofNat (a − b)`. -/
theorem ofNat_sub_ofNat (a b : Nat) (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The `x15` remaining-byte bookkeeping for a shortBytes field: starting from `remaining = L − O`
    bytes available at offset `O`, after consuming the item's prefix byte and `payloadLen` payload
    bytes, `remaining − payloadLen − 1` equals the bytes available at the next item `O+1+payloadLen`.
    Pure `BitVec.ofNat` identity (via `ofNat_sub_ofNat` twice). -/
theorem x15_remaining_decrement (L O payloadLen : Nat)
    (hb : O + 1 + payloadLen ≤ L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 (L - O) - BitVec.ofNat 64 payloadLen) - (1 : Word)
    = BitVec.ofNat 64 (L - (O + 1 + payloadLen)) := by
  rw [ofNat_sub_ofNat (L - O) payloadLen (by omega) (by omega),
      show (1 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_sub_ofNat ((L - O) - payloadLen) 1 (by omega) (by omega)]
  congr 1
  omega

/-- **Generic `x15 := x15 − x11 − 1` register update** (two instructions, position-parameterized):
    `SUB x15,x15,x11` then `ADDI x15,x15,-1`. Decoupled from any surrounding layout so the
    single-pass field walk can place it after whatever store/extract code precedes it. -/
theorem rv64_x15_minus_x11_minus_one (b : Word) (w pl : Word) :
    cpsTripleWithin 2 b (b + 8)
      ((CodeReq.singleton b (.SUB .x15 .x15 .x11)).union
       (CodeReq.singleton (b + 4) (.ADDI .x15 .x15 (-1 : BitVec 12))))
      ((.x15 ↦ᵣ w) ** (.x11 ↦ᵣ pl))
      ((.x15 ↦ᵣ (w - pl - 1)) ** (.x11 ↦ᵣ pl)) := by
  have hd : (CodeReq.singleton b (.SUB .x15 .x15 .x11)).Disjoint
            (CodeReq.singleton (b + 4) (.ADDI .x15 .x15 (-1 : BitVec 12))) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  -- SUB x15,x15,x11 : x15 := w - pl.
  have sub_raw := sub_spec_gen_rd_eq_rs1_within .x15 .x11 w pl b (by nofun)
  -- ADDI x15,x15,-1 framed with x11 : x15 := (w - pl) + signExtend12 (-1) = (w - pl) - 1.
  have addi_raw := addi_spec_gen_same_within .x15 (w - pl) (-1 : BitVec 12) (b + 4) (by nofun)
  have addiF : cpsTripleWithin 1 (b + 4) (b + 4 + 4)
      (CodeReq.singleton (b + 4) (.ADDI .x15 .x15 (-1 : BitVec 12)))
      ((.x15 ↦ᵣ (w - pl)) ** (.x11 ↦ᵣ pl))
      ((.x15 ↦ᵣ (w - pl - 1)) ** (.x11 ↦ᵣ pl)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by
        rw [signExtend12_neg_one, ← BitVec.sub_eq_add_neg] at hp
        xperm_hyp hp)
      (cpsTripleWithin_frameR (.x11 ↦ᵣ pl) (by pcFree) addi_raw)
  have hseq := cpsTripleWithin_seq hd sub_raw addiF
  -- 1 + 1 = 2 and (b+4)+4 = b+8.
  rw [show (b + 4 + 4 : Word) = b + 8 from by bv_omega] at hseq
  exact hseq

end EvmAsm.Rv64.RLP
