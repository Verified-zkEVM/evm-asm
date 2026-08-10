/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakPad

  Pad10*1 (XOR 0x01 at rem, XOR 0x80 at 135), final CSRS, and 32-byte digest
  copy for `zkvm_keccak256`. Completes the remainder path after
  `keccakRemLoop_entry`. Outer absorb loop still blocked on the JAL→LI vs
  signedCountdownLoop BLT-hdr mismatch (coord decision pending).
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakRem
import EvmAsm.Codegen.Proofs.HashBridgeKeccakCsrs
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

private theorem signExtend12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem signExtend12_128 : signExtend12 (128 : BitVec 12) = (128 : Word) := by decide
private theorem signExtend12_135 : signExtend12 (135 : BitVec 12) = (135 : Word) := by decide

private theorem xor_zext_byte (b pad : BitVec 8) :
    (b.zeroExtend 64) ^^^ (pad.zeroExtend 64) = (b ^^^ pad).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  have hb : b.toNat < 256 := b.isLt
  have hp : pad.toNat < 256 := pad.isLt
  have hb64 : b.toNat < 2 ^ 64 := by omega
  have hp64 : pad.toNat < 2 ^ 64 := by omega
  have hx : b.toNat ^^^ pad.toNat < 256 := by
    have := (b ^^^ pad).isLt; rwa [BitVec.toNat_xor] at this
  have hx64 : b.toNat ^^^ pad.toNat < 2 ^ 64 := by omega
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt hp64, Nat.mod_eq_of_lt hx64]

private theorem truncate_xor_imm1 (b : BitVec 8) :
    ((b.zeroExtend 64) ^^^ (1 : Word)).truncate 8 = b ^^^ (1 : BitVec 8) := by
  have h1 : (1 : Word) = ((1 : BitVec 8).zeroExtend 64) := by decide
  rw [h1, xor_zext_byte, truncate_zeroExtend_byte]

private theorem truncate_xor_imm80 (b : BitVec 8) :
    ((b.zeroExtend 64) ^^^ (128 : Word)).truncate 8 = b ^^^ (0x80 : BitVec 8) := by
  have h80 : (128 : Word) = ((0x80 : BitVec 8).zeroExtend 64) := by decide
  rw [h80, xor_zext_byte, truncate_zeroExtend_byte]

/-- Pad one byte at offset `off`: LBU / XORI imm / SB. -/
theorem keccakPadByte_step (cr : CodeReq) (entry : Word)
    (scratchBase : Word) (st : List (BitVec 8)) (off : Nat)
    (imm : BitVec 12) (pad : BitVec 8) (v5 : Word)
    (himm : signExtend12 imm = pad.zeroExtend 64)
    (hst : st.length = 200) (hoff : off < 200)
    (halign : scratchBase.toNat % 8 = 0)
    (h_over : scratchBase.toNat + 200 ≤ 2 ^ 64)
    (hvalidB : isValidByteAccess (scratchBase + BitVec.ofNat 64 off) = true)
    (hmemLb : ∀ a i, CodeReq.singleton entry (.LBU .x5 .x28 0) a = some i →
      cr a = some i)
    (hmemXi : ∀ a i, CodeReq.singleton (entry + 4) (.XORI .x5 .x5 imm) a = some i →
      cr a = some i)
    (hmemSb : ∀ a i, CodeReq.singleton (entry + 8) (.SB .x28 .x5 0) a = some i →
      cr a = some i) :
    cpsTripleWithin 3 entry (entry + 12) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ v5) ** bytesRegion scratchBase st)
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (regOwn .x5) **
        bytesRegion scratchBase
          (setBytes st off [(st.getD off 0) ^^^ pad])) := by
  have hi : off < st.length := by omega
  have hover : scratchBase.toNat + off < 2 ^ 64 := by omega
  -- LBU
  have hlbu0 := cpsTripleWithin_extend_code hmemLb
    (bytesRegion_lbu_within .x5 .x28 scratchBase v5 entry st off
      (by decide) halign hi hover hvalidB)
  have hlbu : cpsTripleWithin 1 entry (entry + 4) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ v5) ** bytesRegion scratchBase st)
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ ((st[off]'hi).zeroExtend 64)) **
        bytesRegion scratchBase st) := hlbu0
  -- XORI
  have hxori0 := cpsTripleWithin_extend_code hmemXi
    (xori_spec_gen_same_within .x5 ((st[off]'hi).zeroExtend 64) imm
      (entry + 4) (by decide))
  have hxori : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      (.x5 ↦ᵣ ((st[off]'hi).zeroExtend 64))
      (.x5 ↦ᵣ (((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm)) := by
    rw [show (entry + 4 : Word) + 4 = entry + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hxori0
    exact hxori0
  have hxoriF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) ** bytesRegion scratchBase st)
    (by pcf) hxori
  have c1 : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ ((st[off]'hi).zeroExtend 64)) **
        bytesRegion scratchBase st)
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ (((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm)) **
        bytesRegion scratchBase st) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hxoriF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbu c1
  -- SB
  let vX : Word := ((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm
  have hsb0 := cpsTripleWithin_extend_code hmemSb
    (bytesRegion_sb_within .x28 .x5 scratchBase vX (entry + 8) st off
      halign hi hover hvalidB)
  have hsb : cpsTripleWithin 1 (entry + 8) (entry + 12) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ vX) ** bytesRegion scratchBase st)
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ vX) **
        bytesRegion scratchBase (st.set off (vX.truncate 8))) := by
    rw [show (entry + 8 : Word) + 4 = entry + 12 from by
      rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]]
      at hsb0
    exact hsb0
  have hset :
      st.set off (vX.truncate 8) =
        setBytes st off [(st.getD off 0) ^^^ pad] := by
    have hget : st.getD off 0 = st[off]'hi := by
      simp [List.getD, List.getElem?_eq_getElem hi]
    have htrunc : vX.truncate 8 = (st[off]'hi) ^^^ pad := by
      simp only [vX, himm]
      have hpadW : pad.zeroExtend 64 = pad.zeroExtend 64 := rfl
      -- (b.zext) ^^^ (pad.zext) = (b^^^pad).zext; truncate
      have := xor_zext_byte (st[off]'hi) pad
      rw [this, truncate_zeroExtend_byte]
    calc
      st.set off (vX.truncate 8)
          = st.set off ((st[off]'hi) ^^^ pad) := by rw [htrunc]
      _ = setBytes st off [(st[off]'hi) ^^^ pad] := (setBytes_singleton _ _ _).symm
      _ = setBytes st off [(st.getD off 0) ^^^ pad] := by rw [hget]
  have c2 : cpsTripleWithin 1 (entry + 8) (entry + 12) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ (((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm)) **
        bytesRegion scratchBase st)
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (.x5 ↦ᵣ vX) **
        bytesRegion scratchBase (setBytes st off [(st.getD off 0) ^^^ pad])) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hsb
    · simp only [vX] at hp ⊢; xperm_hyp hp
    · simp only [vX, hset] at hq ⊢; xperm_hyp hq
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2
  -- drop x5 to own
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) c012
  simp only [vX] at hq
  exact (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x5))) _ hq

/-- Full pad10*1 block (7 insn): 0x01 at rem, ADDI cursor 135, 0x80 at 135. -/
theorem keccakPadBlock_spec (cr : CodeReq) (entry : Word)
    (scratchBase : Word) (st : List (BitVec 8)) (rem : Nat) (v5 : Word)
    (hst : st.length = 200) (hrem : rem ≤ 135)
    (halign : scratchBase.toNat % 8 = 0)
    (h_over : scratchBase.toNat + 200 ≤ 2 ^ 64)
    (hvalidRem : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess (scratchBase + BitVec.ofNat 64 135) = true)
    (hmem0 : ∀ a i, CodeReq.singleton entry (.LBU .x5 .x28 0) a = some i →
      cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (entry + 4) (.XORI .x5 .x5 1) a = some i →
      cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (entry + 8) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (entry + 12) (.ADDI .x28 .x8 135) a = some i →
      cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (entry + 16) (.LBU .x5 .x28 0) a = some i →
      cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (entry + 20) (.XORI .x5 .x5 128) a = some i →
      cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (entry + 24) (.SB .x28 .x5 0) a = some i →
      cr a = some i) :
    cpsTripleWithin 7 entry (entry + 28) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x5 ↦ᵣ v5) **
        bytesRegion scratchBase st)
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) **
        bytesRegion scratchBase (keccakGuestPad st rem)) := by
  have hrem_lt : rem < 200 := by omega
  have h135_lt : (135 : Nat) < 200 := by omega
  -- pad 0x01 at rem
  have h1 := keccakPadByte_step cr entry scratchBase st rem (1 : BitVec 12)
    (1 : BitVec 8) v5 (by rw [signExtend12_1]; decide) hst hrem_lt
    halign h_over hvalidRem hmem0 hmem1 hmem2
  have h1F := cpsTripleWithin_frameR
    (.x8 ↦ᵣ scratchBase) (by pcf) h1
  have c1 : cpsTripleWithin 3 entry (entry + 12) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x5 ↦ᵣ v5) **
        bytesRegion scratchBase st)
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (regOwn .x5) **
        bytesRegion scratchBase
          (setBytes st rem [(st.getD rem 0) ^^^ (1 : BitVec 8)])) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  -- ADDI x28, x8, 135
  have hadd0 := cpsTripleWithin_extend_code hmem3
    (addi_spec_gen_within .x28 .x8 (scratchBase + BitVec.ofNat 64 rem)
      scratchBase (135 : BitVec 12) (entry + 12) (by decide))
  have hadd : cpsTripleWithin 1 (entry + 12) (entry + 16) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)))
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135))) := by
    rw [show (entry + 12 : Word) + 4 = entry + 16 from by
      rw [BitVec.add_assoc, show ((12 : Word) + 4) = (16 : Word) from by decide]]
      at hadd0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => ?_) hadd0
    have h135 :
        scratchBase + signExtend12 (135 : BitVec 12) =
          scratchBase + BitVec.ofNat 64 135 := by
      rw [signExtend12_135]
      rfl
    simpa [h135] using hq
  have haddF := cpsTripleWithin_frameR
    ((regOwn .x5) **
      bytesRegion scratchBase
        (setBytes st rem [(st.getD rem 0) ^^^ (1 : BitVec 8)]))
    (by pcf) hadd
  have c2 : cpsTripleWithin 1 (entry + 12) (entry + 16) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (regOwn .x5) **
        bytesRegion scratchBase
          (setBytes st rem [(st.getD rem 0) ^^^ (1 : BitVec 8)]))
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) **
        bytesRegion scratchBase
          (setBytes st rem [(st.getD rem 0) ^^^ (1 : BitVec 8)])) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) haddF
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 c2
  -- pad 0x80 at 135 — need concrete x5 via of_forall
  let st1 := setBytes st rem [(st.getD rem 0) ^^^ (1 : BitVec 8)]
  have hst1 : st1.length = 200 := by
    simp only [st1, length_setBytes, hst]
  have hmem5' : ∀ a i, CodeReq.singleton ((entry + 16) + 4)
      (.XORI .x5 .x5 128) a = some i → cr a = some i := by
    intro a i h
    rw [show (entry + 16 : Word) + 4 = entry + 20 from by
      rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]]
      at h
    exact hmem5 a i h
  have hmem6' : ∀ a i, CodeReq.singleton ((entry + 16) + 8)
      (.SB .x28 .x5 0) a = some i → cr a = some i := by
    intro a i h
    rw [show (entry + 16 : Word) + 8 = entry + 24 from by
      rw [BitVec.add_assoc, show ((16 : Word) + 8) = (24 : Word) from by decide]]
      at h
    exact hmem6 a i h
  have h2c (v5' : Word) :
      cpsTripleWithin 3 (entry + 16) (entry + 28) cr
        ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
          (.x5 ↦ᵣ v5') ** bytesRegion scratchBase st1)
        ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
          (regOwn .x5) **
          bytesRegion scratchBase
            (setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)])) := by
    have h := keccakPadByte_step cr (entry + 16) scratchBase st1 135
      (128 : BitVec 12) (0x80 : BitVec 8) v5'
      (by rw [signExtend12_128]; decide) hst1 h135_lt
      halign h_over hvalid135 hmem4 hmem5' hmem6'
    rw [show (entry + 16 : Word) + 12 = entry + 28 from by
      rw [BitVec.add_assoc, show ((16 : Word) + 12) = (28 : Word) from by decide]]
      at h
    exact h
  -- peel own x5 for second pad
  have h2own : cpsTripleWithin 3 (entry + 16) (entry + 28) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) ** bytesRegion scratchBase st1)
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) **
        bytesRegion scratchBase
          (setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)])) := by
    intro R hR s hcr hPR hpc
    obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
    obtain ⟨h28, hRest, hd0, hu0, hp28, hpRest⟩ := hpP
    obtain ⟨h5, hBs, hd1, hu1, hp5, hpBs⟩ := hpRest
    obtain ⟨v5', hv5⟩ := hp5
    have hPR' :
        (((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
          (.x5 ↦ᵣ v5') ** bytesRegion scratchBase st1) ** R).holdsFor s :=
      ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
        ⟨h28, hRest, hd0, hu0, hp28, ⟨h5, hBs, hd1, hu1, hv5, hpBs⟩⟩, hpR⟩
    exact h2c v5' R hR s hcr hPR' hpc
  have h2F := cpsTripleWithin_frameR
    (.x8 ↦ᵣ scratchBase) (by pcf) h2own
  have c3 : cpsTripleWithin 3 (entry + 16) (entry + 28) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) **
        bytesRegion scratchBase st1)
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) **
        bytesRegion scratchBase
          (setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)])) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 c3
  -- post = keccakGuestPad
  have hpad : setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)] =
      keccakGuestPad st rem := by
    simp only [keccakGuestPad, st1]
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) cAll
  simp only [st1, hpad] at hq ⊢
  exact hq

/-- Final permute: MV x10,x8 + CSRS (reuse absorb CSRS pattern). -/
theorem keccakFinalCsrs_spec (cr : CodeReq) (entry : Word)
    (scratchBase : Word) (st : List (BitVec 8)) (A : Assertion)
    (hA : A.pcFree) (hst : st.length = 200)
    (halign : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (v10 : Word)
    (hmemMv : ∀ a i, CodeReq.singleton entry (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (entry + 4)
        (.CSRS (2048 : BitVec 12) .x10) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 entry (entry + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ v10) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) ** A) :=
  keccakAbsorbCsrs_spec cr entry scratchBase st A hA hst halign hvalid v10
    hmemMv hmemCsrs

/-- One LD/SD pair copies dword lane `q` from state to output. -/
theorem keccakDigestDword_spec (cr : CodeReq) (entry : Word)
    (scratchBase outputBase : Word) (st out : List (BitVec 8))
    (q : Nat) (v5 : Word)
    (hst : st.length = 200) (hout : out.length = 32)
    (hq : q < 4)
    (hmemLd : ∀ a i, CodeReq.singleton entry
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * q))) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (entry + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * q))) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 entry (entry + 8) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ v5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase out)
      ((.x8 ↦ᵣ scratchBase) **
        (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion scratchBase st **
        bytesRegion outputBase
          (setBytes out (8 * q) ((st.drop (8 * q)).take 8))) := by
  have hq_st : 8 * q < st.length := by omega
  have hq_out : 8 * q + 8 ≤ out.length := by omega
  have himm : 8 * q < 2 ^ 11 := by omega
  -- LD
  have hld0 := cpsTripleWithin_extend_code hmemLd
    (bytesRegion_ld_within .x5 .x8 scratchBase v5 entry st q
      (by decide) hq_st himm)
  have hldF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out)
    (by pcf) hld0
  have c0 : cpsTripleWithin 1 entry (entry + 4) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ v5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase out)
      ((.x8 ↦ᵣ scratchBase) **
        (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion scratchBase st **
        bytesRegion outputBase out) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hldF
  -- SD
  let vD : Word := packBytes ((st.drop (8 * q)).take 8)
  have hsd0 := cpsTripleWithin_extend_code hmemSd
    (bytesRegion_sd_within .x18 .x5 outputBase vD (entry + 4) out q
      hq_out himm)
  have hsd : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      ((.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ vD) ** bytesRegion outputBase out)
      ((.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ vD) **
        bytesRegion outputBase
          (setBytes out (8 * q) (dwordBytes vD))) := by
    rw [show (entry + 4 : Word) + 4 = entry + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hsd0
    exact hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ scratchBase) ** bytesRegion scratchBase st)
    (by pcf) hsd
  have hlen : ((st.drop (8 * q)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hst]; omega
  have hdw : dwordBytes vD = (st.drop (8 * q)).take 8 := by
    simp only [vD]; exact dwordBytes_packBytes _ hlen
  have c1 : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion scratchBase st **
        bytesRegion outputBase out)
      ((.x8 ↦ᵣ scratchBase) **
        (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion scratchBase st **
        bytesRegion outputBase
          (setBytes out (8 * q) ((st.drop (8 * q)).take 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hsdF
    · simp only [vD] at hp ⊢; xperm_hyp hp
    · simp only [vD, hdw] at hq ⊢; xperm_hyp hq
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

end EvmAsm.Codegen.Proofs
