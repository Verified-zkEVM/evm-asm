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

import EvmAsm.Codegen.Proofs.HashBridgeKeccakPad
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000

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

/-- Compose 4× LD/SD digest pairs into full 32-byte copy from zeroed out. -/
theorem keccakDigestAll_spec (cr : CodeReq) (entry : Word)
    (scratchBase outputBase : Word) (st : List (BitVec 8))
    (hst : st.length = 200)
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
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)))
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (keccakDigestCopy st)) := by
  let out0 := List.replicate 32 (0 : BitVec 8)
  have hout0 : out0.length = 32 := by simp only [out0, List.length_replicate]
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
  -- drop x5 to own + fold keccakDigestCopy
  refine cpsTripleWithin_weaken (fun _ hp => by simpa [out0] using hp)
    (fun h hq => by
      have hq1 : (
          (.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
            (.x5 ↦ᵣ packBytes ((st.drop 24).take 8)) **
            bytesRegion scratchBase st **
            bytesRegion outputBase (keccakDigestCopy st)) h := by
        simpa [out0, out1, out2, out3, keccakDigestCopy] using hq
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



