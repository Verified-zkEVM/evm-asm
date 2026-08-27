/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakTail

  Remainder-path tail after outer absorb exit (BLT taken → idx 34):
  rem setup (MV/MV) + BEQ empty-skip + rem byte loop + pad10*1 + final CSRS
  + 4× digest LD/SD + LI a0,0.

  Geometry (base = GuestAddrs.zkvm_keccak256):
    remHdr = base+136  (idx 34 MV x28,x8)
    remLoop = base+148 (idx 37 LBU)
    padHdr  = base+180 (idx 45 LBU pad 0x01)
    csrsHdr = base+208 (idx 52 MV/CSRS)
    digHdr  = base+216 (idx 54 first LD)
    li0     = base+248 (idx 62 LI a0,0)
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakAbsorb
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
    rw [h135] at hq
    exact hq
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

/-- Rem setup: MV x28,x8; MV x30,x20. -/
theorem keccakRemSetup_spec (cr : CodeReq) (hdr : Word)
    (scratchBase inputCur : Word) (v28 v30 : Word)
    (hmem0 : ∀ a i, CodeReq.singleton hdr (.MV .x28 .x8) a = some i →
      cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (hdr + 4) (.MV .x30 .x20) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 hdr (hdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30))
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur)) := by
  have h0 := cpsTripleWithin_extend_code hmem0
    (mv_spec_gen_within .x28 .x8 scratchBase v28 hdr (by decide))
  have h0F := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ inputCur) ** (.x30 ↦ᵣ v30)) (by pcf) h0
  have c0 : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30))
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ v30)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := cpsTripleWithin_extend_code hmem1
    (mv_spec_gen_within .x30 .x20 inputCur v30 (hdr + 4) (by decide))
  have h1' : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x20 ↦ᵣ inputCur) ** (.x30 ↦ᵣ v30))
      ((.x20 ↦ᵣ inputCur) ** (.x30 ↦ᵣ inputCur)) := by
    rw [show (hdr + 4 : Word) + 4 = hdr + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at h1
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ scratchBase) ** (.x28 ↦ᵣ scratchBase)) (by pcf) h1'
  have c1 : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ v30))
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- Four digest dword copies: lanes 0..3 → 32-byte output. -/
def keccakDigestCopy (st : List (BitVec 8)) : List (BitVec 8) :=
  let o0 := setBytes (List.replicate 32 (0 : BitVec 8)) 0 ((st.drop 0).take 8)
  let o1 := setBytes o0 8 ((st.drop 8).take 8)
  let o2 := setBytes o1 16 ((st.drop 16).take 8)
  setBytes o2 24 ((st.drop 24).take 8)

theorem keccakDigestCopy_length (st : List (BitVec 8)) :
    (keccakDigestCopy st).length = 32 := by
  simp only [keccakDigestCopy, length_setBytes, List.length_replicate]

private theorem tail_setBytes_at0_full (bs ns : List (BitVec 8))
    (h : ns.length = bs.length) :
    setBytes bs 0 ns = ns := by
  have hslot := setBytes_slot bs ns 0 (by omega)
  simp only [List.drop_zero] at hslot
  have hlen : (setBytes bs 0 ns).length = ns.length := by
    rw [length_setBytes, h]
  have htake : (setBytes bs 0 ns).take ns.length = setBytes bs 0 ns :=
    List.take_of_length_le (Nat.le_of_eq hlen)
  rwa [htake] at hslot

private theorem tail_take_add_eq (l : List (BitVec 8)) (m n : Nat) :
    l.take (m + n) = l.take m ++ (l.drop m).take n := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons x xs =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [show m + 1 + n = (m + n) + 1 from by omega, List.take_succ_cons]
      exact congrArg (List.cons x) (ih xs)

private theorem tail_take32_chunks (st : List (BitVec 8))
    (_hst : 32 ≤ st.length) :
    st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8 ++
        (st.drop 24).take 8 = st.take 32 := by
  have h16 : st.take 8 ++ (st.drop 8).take 8 = st.take 16 := by
    rw [show 16 = 8 + 8 from rfl, tail_take_add_eq]
  have h24 : st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8
      = st.take 24 := by
    rw [h16, show 24 = 16 + 8 from rfl, tail_take_add_eq]
  rw [h24, show 32 = 24 + 8 from rfl, tail_take_add_eq]

/-- Four successive dword splices cover all 32 output bytes, so the result
    is `st.take 32` regardless of the initial buffer contents — the fact
    that lets the digest spec take an ARBITRARY caller buffer (#12896). -/
theorem digestChain_eq_take32 (out0 st : List (BitVec 8))
    (hout0 : out0.length = 32) (hst : 32 ≤ st.length) :
    setBytes (setBytes (setBytes (setBytes out0 0 (st.take 8)) 8
        ((st.drop 8).take 8)) 16 ((st.drop 16).take 8)) 24
        ((st.drop 24).take 8)
      = st.take 32 := by
  have h0 : (st.take 8).length = 8 := by
    rw [List.length_take, min_eq_left (by omega)]
  have h8 : ((st.drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, min_eq_left (by omega)]
  have h16l : ((st.drop 16).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, min_eq_left (by omega)]
  have hchain :
      setBytes out0 0
          (st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8 ++
            (st.drop 24).take 8) =
        setBytes (setBytes (setBytes (setBytes out0 0 (st.take 8)) 8
          ((st.drop 8).take 8)) 16 ((st.drop 16).take 8)) 24
          ((st.drop 24).take 8) := by
    rw [setBytes_append, setBytes_append, setBytes_append]
    simp only [List.length_append, h0, h8, h16l, Nat.zero_add]
  rw [← hchain, tail_take32_chunks st hst, tail_setBytes_at0_full]
  rw [List.length_take, hout0, min_eq_left hst]

/-- The zero-buffer splice chain (`keccakDigestCopy`) is the same
    `st.take 32` — so the digest value is independent of the buffer the
    caller passed in. -/
theorem keccakDigestCopy_eq_chain (out0 st : List (BitVec 8))
    (hout0 : out0.length = 32) (hst : 32 ≤ st.length) :
    setBytes (setBytes (setBytes (setBytes out0 0 (st.take 8)) 8
        ((st.drop 8).take 8)) 16 ((st.drop 16).take 8)) 24
        ((st.drop 24).take 8)
      = keccakDigestCopy st := by
  rw [digestChain_eq_take32 out0 st hout0 hst]
  unfold keccakDigestCopy
  simp only [List.drop_zero]
  rw [digestChain_eq_take32 (List.replicate 32 (0 : BitVec 8)) st
    (by simp) hst]

/-- Compose 4× LD/SD digest pairs into full 32-byte copy.  The output
    buffer `out0` is ARBITRARY 32-byte caller memory (#12896): every byte
    is overwritten, so no initial-contents assumption is needed. -/
theorem keccakDigestAll_spec (cr : CodeReq) (entry : Word)
    (scratchBase outputBase : Word) (st out0 : List (BitVec 8))
    (hst : st.length = 200) (hout0 : out0.length = 32)
    (v5 : Word)
    (hmemLd0 : ∀ a i, CodeReq.singleton entry
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 0))) a = some i → cr a = some i)
    (hmemSd0 : ∀ a i, CodeReq.singleton (entry + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 0))) a = some i → cr a = some i)
    (hmemLd1 : ∀ a i, CodeReq.singleton (entry + 8)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 1))) a = some i → cr a = some i)
    (hmemSd1 : ∀ a i, CodeReq.singleton ((entry + 8) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 1))) a = some i → cr a = some i)
    (hmemLd2 : ∀ a i, CodeReq.singleton (entry + 16)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 2))) a = some i → cr a = some i)
    (hmemSd2 : ∀ a i, CodeReq.singleton ((entry + 16) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 2))) a = some i → cr a = some i)
    (hmemLd3 : ∀ a i, CodeReq.singleton (entry + 24)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 3))) a = some i → cr a = some i)
    (hmemSd3 : ∀ a i, CodeReq.singleton ((entry + 24) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 3))) a = some i → cr a = some i) :
    cpsTripleWithin 8 entry (entry + 32) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (.x5 ↦ᵣ v5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase out0)
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (keccakDigestCopy st)) := by
  -- lane 0
  have c0k := keccakDigestDword_spec cr entry scratchBase outputBase st out0 0 v5
    hst hout0 (by omega) hmemLd0 hmemSd0
  let out1 := setBytes out0 0 ((st.drop 0).take 8)
  have hout1 : out1.length = 32 := by simp only [out1, length_setBytes, hout0]
  have hpc8_8 : (entry + 8 : Word) + 8 = entry + 16 := by
    rw [BitVec.add_assoc, show ((8 : Word) + 8) = (16 : Word) from by decide]
  have c1raw := keccakDigestDword_spec cr (entry + 8) scratchBase outputBase st out1 1
    (packBytes ((st.drop 0).take 8)) hst hout1 (by omega) hmemLd1 hmemSd1
  have c1' : cpsTripleWithin 2 (entry + 8) (entry + 16) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop 0).take 8)) **
        bytesRegion scratchBase st ** bytesRegion outputBase out1)
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop 8).take 8)) **
        bytesRegion scratchBase st **
        bytesRegion outputBase
          (setBytes out1 8 ((st.drop 8).take 8))) := by
    rw [hpc8_8] at c1raw; exact c1raw
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0k c1'
  let out2 := setBytes out1 8 ((st.drop 8).take 8)
  have hout2 : out2.length = 32 := by simp only [out2, length_setBytes, hout1]
  have hpc16_8 : (entry + 16 : Word) + 8 = entry + 24 := by
    rw [BitVec.add_assoc, show ((16 : Word) + 8) = (24 : Word) from by decide]
  have c2raw := keccakDigestDword_spec cr (entry + 16) scratchBase outputBase st out2 2
    (packBytes ((st.drop 8).take 8)) hst hout2 (by omega) hmemLd2 hmemSd2
  have c2' : cpsTripleWithin 2 (entry + 16) (entry + 24) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop 8).take 8)) **
        bytesRegion scratchBase st ** bytesRegion outputBase out2)
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop 16).take 8)) **
        bytesRegion scratchBase st **
        bytesRegion outputBase
          (setBytes out2 16 ((st.drop 16).take 8))) := by
    rw [hpc16_8] at c2raw; exact c2raw
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [out1] at hp ⊢; xperm_hyp hp) c01 c2'
  let out3 := setBytes out2 16 ((st.drop 16).take 8)
  have hout3 : out3.length = 32 := by simp only [out3, length_setBytes, hout2]
  have hpc24_8 : (entry + 24 : Word) + 8 = entry + 32 := by
    rw [BitVec.add_assoc, show ((24 : Word) + 8) = (32 : Word) from by decide]
  have c3raw := keccakDigestDword_spec cr (entry + 24) scratchBase outputBase st out3 3
    (packBytes ((st.drop 16).take 8)) hst hout3 (by omega) hmemLd3 hmemSd3
  have c3' : cpsTripleWithin 2 (entry + 24) (entry + 32) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop 16).take 8)) **
        bytesRegion scratchBase st ** bytesRegion outputBase out3)
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop 24).take 8)) **
        bytesRegion scratchBase st **
        bytesRegion outputBase
          (setBytes out3 24 ((st.drop 24).take 8))) := by
    rw [hpc24_8] at c3raw; exact c3raw
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [out2] at hp ⊢; xperm_hyp hp) c012 c3'
  -- drop x5 to own + fold the splice chain to keccakDigestCopy
  have hfold : setBytes (setBytes (setBytes (setBytes out0 0
        (st.take 8)) 8 ((st.drop 8).take 8)) 16
        ((st.drop 16).take 8)) 24 ((st.drop 24).take 8)
      = keccakDigestCopy st :=
    keccakDigestCopy_eq_chain out0 st hout0 (by omega)
  refine cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      have hq1 : (
          (.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
            (.x5 ↦ᵣ packBytes ((st.drop 24).take 8)) **
            bytesRegion scratchBase st **
            bytesRegion outputBase (keccakDigestCopy st)) h := by
        simpa [out1, out2, out3, ← hfold] using hq
      -- mono x5 value → own
      refine sepConj_mono (fun _ => id)
        (sepConj_mono (fun _ => id)
          (sepConj_mono (regIs_implies_regOwn .x5)
            (fun _ => id))) h hq1)
    cAll

/-- BEQ x9,x0,+36 taken: rem = 0 → padHdr. -/
theorem keccakRemBeq_empty (cr : CodeReq) (hdr padHdr : Word)
    (hpc : hdr + signExtend13 (36 : BitVec 13) = padHdr)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x9 .x0 (36 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 hdr padHdr cr
      ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := cpsBranchWithin_extend_code hmem
    (beq_spec_gen_within .x9 .x0 (36 : BitVec 13) (0 : Word) (0 : Word) hdr)
  rw [hpc] at hbeq
  exact cpsBranchWithin_takenStripPure2 hbeq (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- BEQ x9,x0,+36 not taken: rem ≠ 0 → fallthrough rem loop. -/
theorem keccakRemBeq_nempty (cr : CodeReq) (hdr : Word) (rem : Nat)
    (hne : rem ≠ 0) (hrem64 : rem < 2 ^ 64)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x9 .x0 (36 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := cpsBranchWithin_extend_code hmem
    (beq_spec_gen_within .x9 .x0 (36 : BitVec 13)
      (BitVec.ofNat 64 rem) (0 : Word) hdr)
  rw [show hdr + 4 = hdr + 4 from rfl] at hbeq
  exact cpsBranchWithin_ntakenStripPure2 hbeq (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQt
    have heq : BitVec.ofNat 64 rem = (0 : Word) :=
      ((sepConj_pure_right _).1 hBP).2
    have h0 : (BitVec.ofNat 64 rem).toNat = 0 := by
      simpa using congrArg BitVec.toNat heq
    have : rem = 0 := by
      rw [BitVec.toNat_ofNat] at h0
      rwa [Nat.mod_eq_of_lt hrem64] at h0
    exact hne this)

/-- State after rem XOR absorb of `rem` residual bytes (or identity when rem=0). -/
def keccakRemAbsorbed (st0 : List (BitVec 8)) (inp : List (BitVec 8)) (rem : Nat) :
    List (BitVec 8) :=
  if rem = 0 then st0 else xorBytesUpTo st0 inp rem

theorem keccakRemAbsorbed_zero (st0 inp : List (BitVec 8)) :
    keccakRemAbsorbed st0 inp 0 = st0 := rfl

theorem keccakRemAbsorbed_pos (st0 inp : List (BitVec 8)) (rem : Nat)
    (hpos : 0 < rem) :
    keccakRemAbsorbed st0 inp rem = xorBytesUpTo st0 inp rem := by
  simp only [keccakRemAbsorbed, if_neg (Nat.ne_of_gt hpos)]

/-- LI a0, 0 success. -/
theorem keccakLi0_spec (cr : CodeReq) (entry : Word) (v10 : Word)
    (hmem : ∀ a i, CodeReq.singleton entry (.LI .x10 (0 : Word)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 entry (entry + 4) cr
      (.x10 ↦ᵣ v10)
      (.x10 ↦ᵣ (0 : Word)) := by
  have h := cpsTripleWithin_extend_code hmem
    (li_spec_gen_within .x10 v10 (0 : Word) entry (by decide))
  rw [show entry + 4 = entry + 4 from rfl] at h
  exact h

/-- Pad-entry ambient after rem path (cursors at rem offset; x9=0). -/
def keccakPadEntry (scratchBase inputCur : Word) (rem : Nat)
    (st : List (BitVec 8)) (inp : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x8 ↦ᵣ scratchBase) **
    (.x20 ↦ᵣ inputCur) **
    (.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
    (.x30 ↦ᵣ (inputCur + BitVec.ofNat 64 rem)) **
    (regOwn .x5) ** (regOwn .x6) **
    bytesRegion scratchBase st ** bytesRegion inputCur inp ** A

private theorem remPathFrame_pcFree (scratchBase inputCur : Word)
    (st0 inp : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
      (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
      (regOwn .x5) ** (regOwn .x6) **
      bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A).pcFree := by
  -- A is the only non-atomic; peel from the right
  exact pcFree_sepConj (by pcf)
    (pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf)
        (pcFree_sepConj (by pcf)
          (pcFree_sepConj (by pcf)
            (pcFree_sepConj (by pcf)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj (bytesRegion_pcFree _ _) hA)))))))

private theorem add_ofNat_zero (b : Word) :
    b + BitVec.ofNat 64 0 = b := by
  rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]; bv_omega

/-- rem=0 path: BEQ taken → pad with cursors at base (rem offset 0). -/
theorem keccakRemPath_zero (cr : CodeReq) (beqHdr padHdr : Word)
    (scratchBase inputCur : Word) (st0 inp : List (BitVec 8)) (A : Assertion)
    (hA : A.pcFree)
    (hpc : beqHdr + signExtend13 (36 : BitVec 13) = padHdr)
    (hmemBeq : ∀ a i, CodeReq.singleton beqHdr (.BEQ .x9 .x0 (36 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 beqHdr padHdr cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A)
      (keccakPadEntry scratchBase inputCur 0 st0 inp A) := by
  have hbr := keccakRemBeq_empty cr beqHdr padHdr hpc hmemBeq
  have hbrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
      (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
      (regOwn .x5) ** (regOwn .x6) **
      bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A)
    (remPathFrame_pcFree scratchBase inputCur st0 inp A hA) hbr
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => by
    have hq1 : (
        (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
          (.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
          (regOwn .x5) ** (regOwn .x6) **
          bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A) h := by
      xperm_hyp hq
    simpa [keccakPadEntry, add_ofNat_zero] using hq1)
    hbrF

/-- rem>0 path: BEQ ntaken + rem byte loop → pad entry. -/
theorem keccakRemPath_nonzero (cr : CodeReq) (beqHdr : Word)
    (scratchBase inputCur : Word) (st0 inp : List (BitVec 8)) (rem : Nat)
    (A : Assertion) (hA : A.pcFree)
    (hrem_pos : 1 ≤ rem) (hrem_le : rem ≤ 200) (hrem64 : rem < 2 ^ 64)
    (hst : st0.length = 200) (hinp : rem ≤ inp.length)
    (hb8s : scratchBase.toNat % 8 = 0) (hb8i : inputCur.toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      scratchBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      inputCur.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (scratchBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess (inputCur + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hmemBeq : ∀ a i, CodeReq.singleton beqHdr (.BEQ .x9 .x0 (36 : BitVec 13)) a = some i →
      cr a = some i)
    (hmemLbI : ∀ a i, CodeReq.singleton (beqHdr + 4) (.LBU .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLbS : ∀ a i, CodeReq.singleton ((beqHdr + 4) + 4) (.LBU .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton ((beqHdr + 4) + 8) (.XOR .x5 .x5 .x6) a = some i →
      cr a = some i)
    (hmemSb : ∀ a i, CodeReq.singleton ((beqHdr + 4) + 12) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton ((beqHdr + 4) + 16) (.ADDI .x28 .x28 1) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton ((beqHdr + 4) + 20) (.ADDI .x30 .x30 1) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton ((beqHdr + 4) + 24) (.ADDI .x9 .x9 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton ((beqHdr + 4) + 28) (.BNE .x9 .x0 (-28)) a = some i →
      cr a = some i) :
    cpsTripleWithin (1 + rem * 8) beqHdr ((beqHdr + 4) + 32) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A)
      (keccakPadEntry scratchBase inputCur rem (xorBytesUpTo st0 inp rem) inp A) := by
  have hne : rem ≠ 0 := Nat.ne_of_gt (Nat.lt_of_succ_le hrem_pos)
  have hbr := keccakRemBeq_nempty cr beqHdr rem hne hrem64 hmemBeq
  have hbrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
      (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
      (regOwn .x5) ** (regOwn .x6) **
      bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A)
    (remPathFrame_pcFree scratchBase inputCur st0 inp A hA) hbr
  have c0 : cpsTripleWithin 1 beqHdr (beqHdr + 4) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hbrF
  have hloop := keccakRemLoop_entry cr (beqHdr + 4) scratchBase inputCur st0 inp rem
    hrem_pos hrem_le hrem64 hst hinp hb8s hb8i hovers hoveri hvalids hvalidi
    hmemLbI hmemLbS hmemXor hmemSb hmemAddS hmemAddI hmemAddC hmemBne
  have hloopF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) ** A)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hA)) hloop
  have c1 : cpsTripleWithin (rem * 8) (beqHdr + 4) ((beqHdr + 4) + 32) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur inp ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x9 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x30 ↦ᵣ (inputCur + BitVec.ofNat 64 rem)) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp rem) **
        bytesRegion inputCur inp ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hloopF
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    have hq1 : (
        (.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
          (.x9 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
          (.x30 ↦ᵣ (inputCur + BitVec.ofNat 64 rem)) **
          (regOwn .x5) ** (regOwn .x6) **
          bytesRegion scratchBase (xorBytesUpTo st0 inp rem) **
          bytesRegion inputCur inp ** A) h := by
      xperm_hyp hq
    simpa [keccakPadEntry] using hq1)
    cAll

end EvmAsm.Codegen.Proofs
