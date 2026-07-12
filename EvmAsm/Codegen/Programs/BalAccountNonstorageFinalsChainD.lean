/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainD

  Balance-station glue (bead evm-asm-4ch8f.43.5, slice 4f):

    66  mv a0, s3              (loop exit → tuple span start)
    67  mv a1, s4              (tuple span length)
    70  sd a0, 64(sp)          (tuple-walk cursor spill)
    71  sd a1, 72(sp)          (tuple-walk end spill)

  plus the station-level reject shape shared by every failure path of the
  balance station (field init, find-last loop, tuple items, value capture).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC3

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Slots 66–67 (`B + 264 → B + 272`): move the last tuple's span
    `(s3, s4)` into the `rlp_walk_init` argument registers. -/
theorem bansf_loopExitMove66_spec (v19 v20 v10 v11 : Word) :
    cpsTripleWithin 2 (B + 264) (B + 272) bansfCode
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11))
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v19) ** ((.x11 : Reg) ↦ᵣ v20)) := by
  have s1 := mv_spec_gen_within .x10 .x19 v19 v10 (B + 264) (by decide)
  have s2 := mv_spec_gen_within .x11 .x20 v20 v11 (B + 268) (by decide)
  runBlock s1 s2

#print axioms bansf_loopExitMove66_spec

/-- Slots 70–71 (`B + 280 → B + 288`): spill the tuple-walk cursor and
    window end for the item units. -/
theorem bansf_tupleSpill70_spec (newSp v10 v11 : Word) :
    cpsTripleWithin 2 (B + 280) (B + 288) bansfCR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72))
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ v10) ** ((newSp + 72) ↦ₘ v11)) := by
  have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp v10 (64 : BitVec 12) (B + 280)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 280) + 4 = B + 284 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 280) bansfProg 70 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp v11 (72 : BitVec 12) (B + 284)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 284) + 4 = B + 288 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 284) bansfProg 71 (.SD .x2 .x11 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd1F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** memOwn (newSp + 72))
    (by pcf) hsd1L
  have hsd2F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ v10) ** ((newSp + 64) ↦ₘ v10))
    (by pcf) hsd2L
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hsd1F hsd2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

#print axioms bansf_tupleSpill70_spec

/-- The station-level reject shape at the epilogue entry (`B + 736`):
    every failure path of the balance station (field init, find-last loop,
    tuple items, value capture) weakens into this.  All station-scratch
    state is released to ownership; the callee-saved anchors survive. -/
def balStationRej (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) **
  memOwn oB ** memOwnU256 (oB + 8) **
  regOwn .x19 ** regOwn .x20 **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- Swap the two exits of a branch (the find-last loop reports its clean
    exit FIRST; the station convention keeps the reject exit first). -/
theorem cpsBranchWithin_swap {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    (h : cpsBranchWithin n entry cr P e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr P e2 Q2 e1 Q1 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hcase.symm⟩

#print axioms cpsBranchWithin_swap

/-!
## Balance-station assembly plan (slice 4g, `bansf_balStation_spec`)

Goal shape:
```
theorem bansf_balStation_spec (aB newSp oB : Word) (aLen off3 : Nat)
    (n3 l3 v19 v20 : Word) (acctBytes) (F) (hF hsalign hoalign hslack hover
    hvalid hovout hovalid) (hoff3 : off3 ≤ aLen)
    (hdec3 : rlpItemDecode acctBytes off3 (aB+ofNat off3) (aB+ofNat aLen) n3 l3) :
  cpsBranchWithin (98 * (aLen + 1) + 700) (B + 184) bansfCR
    (x10↦n3 ** x11↦0 ** x12↦l3 ** x19↦v19 ** x20↦v20 **
     (newSp+48)↦ₘn3 ** (newSp+56)↦ₘ(aB+ofNat aLen) ** memOwn (newSp+64/72) **
     x2↦newSp ** x8↦aB ** x9↦ofNat aLen ** x18↦oB **
     oB↦ₘ0 ** (oB+8/16/24/32)↦ₘ0 ** x0↦0 ** bytesRegion aB acctBytes ** F **
     regOwn x5 x6 x7 x28 x29 x30 x31 x1)          -- owns LAST for regOwn8 intro
    (B+736) (balStationRej aB newSp oB aLen acctBytes F)
    (B+352) (balStationPost aB newSp oB aLen ((n3-l3-aB).toNat) l3.toNat n3 acctBytes F)
```
Proof skeleton:
1. `cpsBranchWithin_of_forall_regIs_to_regOwn8` (after a weaken-perm) intros
   v5 v6 v7 v28 v29 v30 v31 vRa.
2. `rlpItemDecode_spanStart hdec3 hoff3` ⇒ hrepS (n3−l3 = aB+ofNat fOff),
   hsple, hspb (fOff + l3.toNat ≤ aLen — discharges fieldInit50's hfB).
3. spanCapture46 (liftCode bansfCode→bansfCR via union_mono_left, frameR rest,
   rw [hrepS]) ; seq_branch with fieldInit50 (fOff := (n3−l3−aB).toNat,
   fSpanW := l3, vRa-old := vRa).  Reject arm: fieldRej ** frame ⇒
   balStationRej (memIs→memOwn on 48/56/64/72 + oB cells → memOwn oB +
   hmemU-style memOwnU256 (oB+8), regIs→regOwn x19 x20 x11? note fieldRej
   owns x11/x12 already).
4. At B+208: continuation branch with pre `fun h => ∃ cOff, ((fieldInitPost
   atoms ** frame) ** ⌜FieldInitOk acctBytes fOff l3.toNat cOff⌝) h` connected
   by a pointwise rebuild lambda (ChainC2-collapse style).  exists_pre +
   pure_pre_right, then `by_cases hce : cOff = fOff + l3.toNat`:
   - EMPTY: balEmptyTaken (lift, frame all) ⇒ B+352; weaken to balStationPost
     EMPTY arm (FieldFinal.empty b hb (hok.2.1 ▸ hce); regIs→regOwn
     x10 x11 x12 x19 x20).  `cpsTripleWithin_as_cpsBranchWithin_right`.
   - NONEMPTY: balEmptyFall (hne := hce, hcle/hfle by omega from FieldInitOk
     + hspb) ; loopEntry53 ; findLastLoop1 (off0 := cOff, endOff := fOff +
     l3.toNat, j := endOff − cOff; hoff0 : cOff < endOff from hok ≤ + hce;
     flInv entry: ⟨cOff, v19', v20', …, Or.inl rfl⟩; v19'/v20' are the
     spanCapture-written x19=n3−l3, x20=l3).  Loop exits are (B+264 flExit |
     B+736 flRej) — FIRST exit continues ⇒ need the swap variant (write
     `cpsBranchWithin_swap` inline: intro/rcases/Or-swap) before chain_snd.
     flRej ⇒ balStationRej (oB cells from frame).
5. At B+264 (flExit): exists_pre n l + pure (LastItemAt).  loopExitMove66
   (lift, frame) ; `LastItemAt_decode hlast (by omega) (by omega)` ⇒
   ∃ offT ≤ endOff, decode of the last tuple; `rlpItemDecode_spanStart` on it
   ⇒ hrepT (n−l = aB+ofNat tOff), tOff + l.toNat ≤ endOff ≤ aLen (fieldInit68
   hfB ✓).  rw [hrepT]; fieldInit68 (fOff := (n−l−aB).toNat, fSpanW := l).
6. At B+280: same ∃cOff2/FieldInitOk unpack; tupleSpill70 ; tupleItem0
   (aLen-param := tOff2 + l.toNat, off := cOff2, hoffle from FieldInitOk;
   hslack' : tOff2 + l.toNat + 9 ≤ length by omega).  tupleRej ⇒
   balStationRej.
7. At B+308 (tupleOk): ∃ next len + idx-decode pure; `rlpItemDecode_advance`
   ⇒ next = aB+ofNat nOff, cOff2 < nOff ≤ tEnd2.  rw; tupleItem1 (off := nOff).
8. At B+324 (tupleValOk): ∃ vNext vLen + val-decode; balCapture (tEnd :=
   tEnd2, off := nOff, hdec := val-decode; hovout/hovalid/hoalign from
   station hyps).  balCaptureRej ⇒ balStationRej.
9. At B+352 (balCaptureOk): weaken to balStationPost FOUND arm:
   FieldFinal.last b n l vNext vLen with hb (field FieldInitOk), hne (hok ▸
   hce), hlast (flExit pure, off0 rewritten to fOff + listHeaderSize b),
   hval : TupleValueWindow = ⟨b2, hb2, next, len, idx-decode (cOff2 → tOff2 +
   listHeaderSize b2), val-decode with cursor rewritten aB+ofNat nOff → next⟩;
   vLen.toNat ≤ 32 from balCaptureOk's pure; regIs→regOwn x19 x20 (+ x10 etc.
   already own in balCaptureOk); spills 48/56 & memOwn 64/72 from frame.
Step budget per path: empty 4+84+1 = 89; found 4+84+1+2+98*(j+1)+2+84+2+93+
92+260 ≤ 98*(aLen+1)+624.  `cpsBranchWithin_mono_nSteps (by omega)` at the end.
-/

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
