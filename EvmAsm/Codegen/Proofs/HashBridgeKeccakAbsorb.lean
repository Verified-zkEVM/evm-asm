/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakAbsorb

  One outer absorb-block body for `zkvm_keccak256`:
  setup cursors → 17-dword XOR → MV x10 → CSRS → advance input/remaining.
  Block-local input window (136 B at cursor); full-input ownership is a
  later outer-inv concern.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakCsrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Exposed temps owned across the absorb body (CSRS rest + x31 after loop). -/
def keccakAbsorbTemps : List Reg := keccakCsrsRest

private theorem absorbTemps_nodup : keccakAbsorbTemps.Nodup := by decide

/-- Post-dword state after XOR of one rate block (before permute). -/
def keccakXorAbsorbed (st0 blk : List (BitVec 8)) : List (BitVec 8) :=
  xorDwordsUpTo st0 blk 17

/-- Post-CSRS state after one full absorb block. -/
def keccakPermuteAbsorbed (st0 blk : List (BitVec 8)) : List (BitVec 8) :=
  setBytes (keccakXorAbsorbed st0 blk) 0
    (keccakBytes (keccakXorAbsorbed st0 blk) 0)

theorem keccakXorAbsorbed_length (st0 blk : List (BitVec 8))
    (hst : st0.length = 200) :
    (keccakXorAbsorbed st0 blk).length = 200 := by
  simp only [keccakXorAbsorbed, xorDwordsUpTo_length, hst]

theorem keccakPermuteAbsorbed_length (st0 blk : List (BitVec 8))
    (hst : st0.length = 200) :
    (keccakPermuteAbsorbed st0 blk).length = 200 := by
  simp only [keccakPermuteAbsorbed, length_setBytes, keccakXorAbsorbed_length st0 blk hst]

private theorem add136 (p : Word) (k : Nat) (_hk : 136 * k + 136 < 2 ^ 64) :
    p + BitVec.ofNat 64 (136 * k) + signExtend12 (136 : BitVec 12)
      = p + BitVec.ofNat 64 (136 * (k + 1)) := by
  rw [show signExtend12 (136 : BitVec 12) = (136 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((136 : Word)).toNat = 136 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem sub136 (n : Nat) (_hn : 136 ≤ n) (_hb : n < 2 ^ 64) :
    BitVec.ofNat 64 n + signExtend12 (-136 : BitVec 12)
      = BitVec.ofNat 64 (n - 136) := by
  rw [show signExtend12 (-136 : BitVec 12) = (-136 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-136 : Word)).toNat = 18446744073709551480 from rfl]
  omega

/-- Setup: MV x28,x8; MV x30,x20; LI x31,17. -/
theorem keccakAbsorbSetup_spec (cr : CodeReq) (hdr : Word)
    (scratchBase inputCur : Word) (v28 v30 v31 : Word)
    (hmemMvS : ∀ a i, CodeReq.singleton hdr (.MV .x28 .x8) a = some i → cr a = some i)
    (hmemMvI : ∀ a i, CodeReq.singleton (hdr + 4) (.MV .x30 .x20) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 8) (.LI .x31 (17 : Word)) a = some i →
      cr a = some i) :
    cpsTripleWithin 3 hdr (hdr + 12) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (.x31 ↦ᵣ (17 : Word))) := by
  -- MV focuses rd+rs; frame omits both.
  have h0 := cpsTripleWithin_extend_code hmemMvS
    (mv_spec_gen_within .x28 .x8 scratchBase v28 hdr (by decide))
  have h0F := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ inputCur) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) (by pcf) h0
  have c0 : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := cpsTripleWithin_extend_code hmemMvI
    (mv_spec_gen_within .x30 .x20 inputCur v30 (hdr + 4) (by decide))
  have h1' : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x20 ↦ᵣ inputCur) ** (.x30 ↦ᵣ v30))
      ((.x20 ↦ᵣ inputCur) ** (.x30 ↦ᵣ inputCur)) := by
    rw [show (hdr + 4 : Word) + 4 = hdr + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at h1
    exact h1
  -- MV x30,x20 focuses x30+x20; frame keeps x8/x28/x31
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ scratchBase) ** (.x28 ↦ᵣ scratchBase) ** (.x31 ↦ᵣ v31))
    (by pcf) h1'
  have c1 : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) ** (.x31 ↦ᵣ v31)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have h2 := cpsTripleWithin_extend_code hmemLi
    (li_spec_gen_within .x31 v31 (17 : Word) (hdr + 8) (by decide))
  have h2' : cpsTripleWithin 1 (hdr + 8) (hdr + 12) cr
      ((.x31 ↦ᵣ v31)) ((.x31 ↦ᵣ (17 : Word))) := by
    rw [show (hdr + 8 : Word) + 4 = hdr + 12 from by
      rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]]
      at h2
    exact h2
  have h2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
      (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur))
    (by pcf) h2'
  have c2 : cpsTripleWithin 1 (hdr + 8) (hdr + 12) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) ** (.x31 ↦ᵣ v31))
      ((.x8 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ inputCur) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (.x31 ↦ᵣ (17 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-- Advance after CSRS: ADDI x20,+136; ADDI x9,-136. -/
theorem keccakAbsorbAdvance_spec (cr : CodeReq) (hdr : Word)
    (inputCur : Word) (remaining : Nat)
    (hrem : 136 ≤ remaining) (hrem64 : remaining < 2 ^ 64)
    (hmemA20 : ∀ a i, CodeReq.singleton hdr (.ADDI .x20 .x20 (136 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemA9 : ∀ a i, CodeReq.singleton (hdr + 4) (.ADDI .x9 .x9 (-136 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 hdr (hdr + 8) cr
      ((.x20 ↦ᵣ inputCur) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining))
      ((.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136))) := by
  have h0 := cpsTripleWithin_extend_code hmemA20
    (addi_spec_gen_same_within .x20 inputCur (136 : BitVec 12) hdr (by decide))
  have h0' : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x20 ↦ᵣ inputCur))
      ((.x20 ↦ᵣ (inputCur + signExtend12 (136 : BitVec 12)))) := h0
  have h0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 remaining)) (by pcf) h0'
  have c0 : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x20 ↦ᵣ inputCur) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining))
      ((.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 remaining)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        rw [show signExtend12 (136 : BitVec 12) = (136 : Word) from by decide,
          show (136 : Word) = BitVec.ofNat 64 136 from rfl] at hq
        xperm_hyp hq) h0F
  have h1 := cpsTripleWithin_extend_code hmemA9
    (addi_spec_gen_same_within .x9 (BitVec.ofNat 64 remaining) (-136 : BitVec 12)
      (hdr + 4) (by decide))
  have h1' : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 remaining))
      ((.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136))) := by
    rw [show (hdr + 4 : Word) + 4 = hdr + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide],
      sub136 remaining hrem hrem64] at h1
    exact h1
  have h1F := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136))) (by pcf) h1'
  have c1 : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 remaining))
      ((.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- MV x10,x8 then CSRS 0x800,x10 over owned exposed rest. -/
theorem keccakAbsorbCsrs_spec (cr : CodeReq) (hdr : Word)
    (scratchBase : Word) (st : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200)
    (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (v10 : Word)
    (hmemMv : ∀ a i, CodeReq.singleton hdr (.MV .x10 .x8) a = some i → cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 4) (.CSRS 0x800 .x10) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 hdr (hdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ v10) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) ** A) := by
  -- mv focuses x8+x10; frame must omit both.
  have hmv := cpsTripleWithin_extend_code hmemMv
    (mv_spec_gen_within .x10 .x8 scratchBase v10 hdr (by decide))
  have hmvF := cpsTripleWithin_frameR
    (regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
    (pcFree_sepConj (pcFree_regOwns _)
      (pcFree_sepConj (bytesRegion_pcFree _ _) hA)) hmv
  have c0 : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ v10) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hmvF
  have hcsrs0 := csrs_keccak_x10_own_flat (hdr + 4) scratchBase st
    ((.x8 ↦ᵣ scratchBase) ** A)
    (pcFree_sepConj (by pcFree) hA) hst hb8 hvalid
  have hcsrs : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase st ** ((.x8 ↦ᵣ scratchBase) ** A))
      ((.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
        ((.x8 ↦ᵣ scratchBase) ** A)) := by
    refine cpsTripleWithin_extend_code hmemCsrs ?_
    rw [show (hdr + 4 : Word) + 4 = hdr + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hcsrs0
    exact hcsrs0
  have c1 : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcsrs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- Temps owned through the dword loop (CSRS rest minus x5/x6/x28/x30/x31). -/
def keccakDwordFrameOwns : List Reg :=
  [.x7, .x29, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem dwordFrameOwns_nodup : keccakDwordFrameOwns.Nodup := by decide

/-- Drop post-dword cursors into owns and assemble `keccakCsrsRest`. -/
theorem absorb_assemble_csrs_owns (v28 v30 v31 : Word) (R : Assertion) :
    ∀ h, ((.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) ** R) h →
    (regOwns keccakCsrsRest ** R) h := by
  intro h hs
  have hs1 :=
    sepConj_mono (regIs_implies_regOwn (r := .x28))
      (sepConj_mono (regIs_implies_regOwn (r := .x30))
        (sepConj_mono (regIs_implies_regOwn (r := .x31))
          (fun _ => id))) h hs
  simp only [regOwns, keccakCsrsRest, keccakDwordFrameOwns] at hs1 ⊢
  xperm_hyp hs1

private theorem pc_add4 (p : Word) (n k : Nat)
    (h : n + 4 = k) : p + BitVec.ofNat 64 n + 4 = p + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc, show (BitVec.ofNat 64 n + (4 : Word)) = BitVec.ofNat 64 k from by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show ((4 : Word)).toNat = 4 from rfl]
    omega]

/-- Setup framed with stable ambient through dword entry. -/
theorem keccakAbsorbSetup_framed (cr : CodeReq) (bodyHdr : Word)
    (scratchBase inputCur : Word) (remaining : Nat)
    (st0 blk : List (BitVec 8)) (v10 v28 v30 v31 : Word)
    (A : Assertion) (hA : A.pcFree)
    (hmemMvS : ∀ a i, CodeReq.singleton bodyHdr (.MV .x28 .x8) a = some i →
      cr a = some i)
    (hmemMvI : ∀ a i, CodeReq.singleton (bodyHdr + 4) (.MV .x30 .x20) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (bodyHdr + 8) (.LI .x31 (17 : Word)) a = some i →
      cr a = some i) :
    cpsTripleWithin 3 bodyHdr (bodyHdr + 12) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (.x31 ↦ᵣ (17 : Word)) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A) := by
  let F : Assertion :=
    (.x9 ↦ᵣ BitVec.ofNat 64 remaining) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ v10) ** regOwns keccakDwordFrameOwns **
      (regOwn .x5) ** (regOwn .x6) **
      bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A
  have hF : F.pcFree :=
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have h0 := keccakAbsorbSetup_spec cr bodyHdr scratchBase inputCur v28 v30 v31
    hmemMvS hmemMvI hmemLi
  have hF' := cpsTripleWithin_frameR F hF h0
  refine cpsTripleWithin_weaken (fun _ hp => by simp only [F] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by simp only [F] at hq ⊢; xperm_hyp hq) hF'

/-- Dword loop framed with stable ambient (x8/x9/x20/x10/frameOwns/A). -/
theorem keccakAbsorbDword_framed (cr : CodeReq) (dwordHdr : Word)
    (scratchBase inputCur : Word) (remaining : Nat)
    (st0 blk : List (BitVec 8)) (v10 : Word)
    (A : Assertion) (hA : A.pcFree)
    (hst : st0.length = 200) (hblk : 8 * 17 ≤ blk.length)
    (hmemLdI : ∀ a i, CodeReq.singleton dwordHdr (.LD .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton (dwordHdr + 4) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (dwordHdr + 8) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (dwordHdr + 12) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (dwordHdr + 16) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (dwordHdr + 20) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (dwordHdr + 24) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (dwordHdr + 28) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i) :
    cpsTripleWithin (17 * 8) dwordHdr (dwordHdr + 32) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (.x31 ↦ᵣ (17 : Word)) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * 17))) **
        (.x30 ↦ᵣ (inputCur + BitVec.ofNat 64 (8 * 17))) **
        (.x31 ↦ᵣ (0 : Word)) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk 17) **
        bytesRegion inputCur blk ** A) := by
  let F : Assertion :=
    (.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
      (.x20 ↦ᵣ inputCur) ** (.x10 ↦ᵣ v10) ** regOwns keccakDwordFrameOwns ** A
  have hF : F.pcFree :=
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (pcFree_regOwns _) hA
  have h0 := keccakDwordLoop_entry cr dwordHdr scratchBase inputCur st0 blk
    hst hblk hmemLdI hmemLdS hmemXor hmemSd hmemAddS hmemAddI hmemAddC hmemBne
  have hF' := cpsTripleWithin_frameR F hF h0
  refine cpsTripleWithin_weaken (fun _ hp => by simp only [F] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by simp only [F] at hq ⊢; xperm_hyp hq) hF'

/-- CSRS step after dword: drop cursors to owns then permute. -/
theorem keccakAbsorbCsrs_from_dword (cr : CodeReq) (csrsHdr : Word)
    (scratchBase inputCur : Word) (remaining : Nat)
    (stXored blk : List (BitVec 8)) (v10 : Word)
    (A : Assertion) (hA : A.pcFree)
    (hst : stXored.length = 200)
    (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (v28 v30 v31 : Word)
    (hmemMv10 : ∀ a i, CodeReq.singleton csrsHdr (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (csrsHdr + 4) (.CSRS 0x800 .x10) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 csrsHdr (csrsHdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase stXored ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes stXored 0 (keccakBytes stXored 0)) **
        bytesRegion inputCur blk ** A) := by
  let R : Assertion :=
    (.x9 ↦ᵣ BitVec.ofNat 64 remaining) ** (.x20 ↦ᵣ inputCur) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputCur blk ** A
  have hR : R.pcFree :=
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have h0 := keccakAbsorbCsrs_spec cr csrsHdr scratchBase stXored R hR
    hst hb8 hvalid v10 hmemMv10 hmemCsrs
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by
      simp only [R] at hq ⊢; xperm_hyp hq) h0
  have hpArr :
      ((.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ v10) **
          bytesRegion scratchBase stXored ** R)) h := by
    simp only [R] at hp ⊢
    xperm_hyp hp
  have hpOwn := absorb_assemble_csrs_owns v28 v30 v31
    ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ v10) **
      bytesRegion scratchBase stXored ** R) h hpArr
  simp only [R] at hpOwn ⊢
  xperm_hyp hpOwn

/-- Advance framed after CSRS. -/
theorem keccakAbsorbAdvance_framed (cr : CodeReq) (advHdr : Word)
    (scratchBase inputCur : Word) (remaining : Nat)
    (stFinal blk : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hrem : 136 ≤ remaining) (hrem64 : remaining < 2 ^ 64)
    (hmemA20 : ∀ a i, CodeReq.singleton advHdr
        (.ADDI .x20 .x20 (136 : BitVec 12)) a = some i → cr a = some i)
    (hmemA9 : ∀ a i, CodeReq.singleton (advHdr + 4)
        (.ADDI .x9 .x9 (-136 : BitVec 12)) a = some i → cr a = some i) :
    cpsTripleWithin 2 advHdr (advHdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase stFinal ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
        (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase stFinal ** bytesRegion inputCur blk ** A) := by
  let F : Assertion :=
    (.x8 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
      bytesRegion scratchBase stFinal ** bytesRegion inputCur blk ** A
  have hF : F.pcFree :=
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have h0 := keccakAbsorbAdvance_spec cr advHdr inputCur remaining
    hrem hrem64 hmemA20 hmemA9
  have hF' := cpsTripleWithin_frameR F hF h0
  refine cpsTripleWithin_weaken (fun _ hp => by simp only [F] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by simp only [F] at hq ⊢; xperm_hyp hq) hF'

/-- Bridge hmem hyps from `bodyHdr + n` to nested `bodyHdr + a + b`. -/
private theorem hmem_add_bridge {cr : CodeReq} {bodyHdr : Word} {ins : Instr}
    {n a b : Nat} (hn : a + b = n)
    (h : ∀ addr i, CodeReq.singleton (bodyHdr + BitVec.ofNat 64 n) ins addr = some i →
      cr addr = some i) :
    ∀ addr i, CodeReq.singleton (bodyHdr + BitVec.ofNat 64 a + BitVec.ofNat 64 b) ins
        addr = some i → cr addr = some i := by
  intro addr i hi
  apply h addr i
  convert hi using 2
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Full absorb body (no back-edge): setup + dword + CSRS + advance.
    `bodyHdr` = MV x28 at program index 18. Ends at the JAL PC. -/
theorem keccakAbsorbBody_spec (cr : CodeReq) (bodyHdr : Word)
    (scratchBase inputCur : Word) (remaining : Nat)
    (st0 blk : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hst : st0.length = 200)
    (hblk : blk.length = 136)
    (hrem : 136 ≤ remaining) (hrem64 : remaining < 2 ^ 64)
    (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (v10 v28 v30 v31 : Word)
    (hmemMvS : ∀ a i, CodeReq.singleton bodyHdr (.MV .x28 .x8) a = some i →
      cr a = some i)
    (hmemMvI : ∀ a i, CodeReq.singleton (bodyHdr + 4) (.MV .x30 .x20) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (bodyHdr + 8) (.LI .x31 (17 : Word)) a = some i →
      cr a = some i)
    (hmemLdI : ∀ a i, CodeReq.singleton (bodyHdr + 12) (.LD .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton (bodyHdr + 16) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (bodyHdr + 20) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (bodyHdr + 24) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (bodyHdr + 28) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (bodyHdr + 32) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (bodyHdr + 36) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (bodyHdr + 40) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i)
    (hmemMv10 : ∀ a i, CodeReq.singleton (bodyHdr + 44) (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (bodyHdr + 48) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemA20 : ∀ a i, CodeReq.singleton (bodyHdr + 52)
        (.ADDI .x20 .x20 (136 : BitVec 12)) a = some i → cr a = some i)
    (hmemA9 : ∀ a i, CodeReq.singleton (bodyHdr + 56)
        (.ADDI .x9 .x9 (-136 : BitVec 12)) a = some i → cr a = some i) :
    cpsTripleWithin (3 + 17 * 8 + 2 + 2) bodyHdr (bodyHdr + 60) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
        (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
        bytesRegion inputCur blk ** A) := by
  have hblk8 : 8 * 17 ≤ blk.length := by omega
  have c0 := keccakAbsorbSetup_framed cr bodyHdr scratchBase inputCur remaining
    st0 blk v10 v28 v30 v31 A hA hmemMvS hmemMvI hmemLi
  -- Bridge nested offsets for dwordHdr = bodyHdr+12
  have hLdS := hmem_add_bridge (a := 12) (b := 4) (n := 16) (by omega) hmemLdS
  have hXor := hmem_add_bridge (a := 12) (b := 8) (n := 20) (by omega) hmemXor
  have hSd := hmem_add_bridge (a := 12) (b := 12) (n := 24) (by omega) hmemSd
  have hAddS := hmem_add_bridge (a := 12) (b := 16) (n := 28) (by omega) hmemAddS
  have hAddI := hmem_add_bridge (a := 12) (b := 20) (n := 32) (by omega) hmemAddI
  have hAddC := hmem_add_bridge (a := 12) (b := 24) (n := 36) (by omega) hmemAddC
  have hBne := hmem_add_bridge (a := 12) (b := 28) (n := 40) (by omega) hmemBne
  have c1 := keccakAbsorbDword_framed cr (bodyHdr + 12) scratchBase inputCur remaining
    st0 blk v10 A hA hst hblk8 hmemLdI hLdS hXor hSd hAddS hAddI hAddC hBne
  have c1' : cpsTripleWithin (17 * 8) (bodyHdr + 12) (bodyHdr + 44) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputCur) **
        (.x31 ↦ᵣ (17 : Word)) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * 17))) **
        (.x30 ↦ᵣ (inputCur + BitVec.ofNat 64 (8 * 17))) **
        (.x31 ↦ᵣ (0 : Word)) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk 17) **
        bytesRegion inputCur blk ** A) := by
    rw [show (bodyHdr + 12 : Word) + 32 = bodyHdr + 44 from by
      rw [BitVec.add_assoc, show ((12 : Word) + 32) = (44 : Word) from by decide]]
      at c1
    exact c1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1'
  have hxlen : (xorDwordsUpTo st0 blk 17).length = 200 := by
    rw [xorDwordsUpTo_length st0 blk 17, hst]
  have hCsrs := hmem_add_bridge (a := 44) (b := 4) (n := 48) (by omega) hmemCsrs
  have c2 := keccakAbsorbCsrs_from_dword cr (bodyHdr + 44) scratchBase inputCur
    remaining (xorDwordsUpTo st0 blk 17) blk v10 A hA hxlen hb8 hvalid
    (scratchBase + BitVec.ofNat 64 (8 * 17))
    (inputCur + BitVec.ofNat 64 (8 * 17)) (0 : Word)
    hmemMv10 hCsrs
  have c2' : cpsTripleWithin 2 (bodyHdr + 44) (bodyHdr + 52) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * 17))) **
        (.x30 ↦ᵣ (inputCur + BitVec.ofNat 64 (8 * 17))) **
        (.x31 ↦ᵣ (0 : Word)) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk 17) **
        bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase
          (setBytes (xorDwordsUpTo st0 blk 17) 0
            (keccakBytes (xorDwordsUpTo st0 blk 17) 0)) **
        bytesRegion inputCur blk ** A) := by
    rw [show (bodyHdr + 44 : Word) + 8 = bodyHdr + 52 from by
      rw [BitVec.add_assoc, show ((44 : Word) + 8) = (52 : Word) from by decide]]
      at c2
    exact c2
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2'
  have hA9 := hmem_add_bridge (a := 52) (b := 4) (n := 56) (by omega) hmemA9
  have c3 := keccakAbsorbAdvance_framed cr (bodyHdr + 52) scratchBase inputCur remaining
    (setBytes (xorDwordsUpTo st0 blk 17) 0
      (keccakBytes (xorDwordsUpTo st0 blk 17) 0)) blk A hA hrem hrem64
    hmemA20 hA9
  have c3' : cpsTripleWithin 2 (bodyHdr + 52) (bodyHdr + 60) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase
          (setBytes (xorDwordsUpTo st0 blk 17) 0
            (keccakBytes (xorDwordsUpTo st0 blk 17) 0)) **
        bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
        (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
        bytesRegion inputCur blk ** A) := by
    rw [show (bodyHdr + 52 : Word) + 8 = bodyHdr + 60 from by
      rw [BitVec.add_assoc, show ((52 : Word) + 8) = (60 : Word) from by decide]]
      at c3
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        simp only [keccakPermuteAbsorbed, keccakXorAbsorbed] at hq ⊢
        xperm_hyp hq) c3
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3'

/-- Body fuel including the back-edge JAL (143 + 1). -/
def keccakAbsorbBodyFuel : Nat := 3 + 17 * 8 + 2 + 2 + 1

/-- Body + JAL x0,-68 back to the LI reload header.
    Geometry: `bodyHdr = liHdr + 8`; JAL at `bodyHdr+60` with imm -68 targets `liHdr`. -/
theorem keccakAbsorbBody_with_backedge (cr : CodeReq) (bodyHdr liHdr : Word)
    (scratchBase inputCur : Word) (remaining : Nat)
    (st0 blk : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hst : st0.length = 200)
    (hblk : blk.length = 136)
    (hrem : 136 ≤ remaining) (hrem64 : remaining < 2 ^ 64)
    (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (v10 v28 v30 v31 : Word)
    (_hpc_body : bodyHdr = liHdr + 8)
    (hpc_jal : bodyHdr + 60 + signExtend21 (-68 : BitVec 21) = liHdr)
    (hmemMvS : ∀ a i, CodeReq.singleton bodyHdr (.MV .x28 .x8) a = some i →
      cr a = some i)
    (hmemMvI : ∀ a i, CodeReq.singleton (bodyHdr + 4) (.MV .x30 .x20) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (bodyHdr + 8) (.LI .x31 (17 : Word)) a = some i →
      cr a = some i)
    (hmemLdI : ∀ a i, CodeReq.singleton (bodyHdr + 12) (.LD .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton (bodyHdr + 16) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (bodyHdr + 20) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (bodyHdr + 24) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (bodyHdr + 28) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (bodyHdr + 32) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (bodyHdr + 36) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (bodyHdr + 40) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i)
    (hmemMv10 : ∀ a i, CodeReq.singleton (bodyHdr + 44) (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (bodyHdr + 48) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemA20 : ∀ a i, CodeReq.singleton (bodyHdr + 52)
        (.ADDI .x20 .x20 (136 : BitVec 12)) a = some i → cr a = some i)
    (hmemA9 : ∀ a i, CodeReq.singleton (bodyHdr + 56)
        (.ADDI .x9 .x9 (-136 : BitVec 12)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (bodyHdr + 60)
        (.JAL .x0 (-68 : BitVec 21)) a = some i → cr a = some i) :
    cpsTripleWithin keccakAbsorbBodyFuel bodyHdr liHdr cr
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 remaining) **
        (.x20 ↦ᵣ inputCur) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ v28) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwns keccakDwordFrameOwns ** (regOwn .x5) ** (regOwn .x6) **
        bytesRegion scratchBase st0 ** bytesRegion inputCur blk ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
        (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
        bytesRegion inputCur blk ** A) := by
  have cBody := keccakAbsorbBody_spec cr bodyHdr scratchBase inputCur remaining
    st0 blk A hA hst hblk hrem hrem64 hb8 hvalid v10 v28 v30 v31
    hmemMvS hmemMvI hmemLi hmemLdI hmemLdS hmemXor hmemSd
    hmemAddS hmemAddI hmemAddC hmemBne hmemMv10 hmemCsrs hmemA20 hmemA9
  -- JAL x0 is emp/emp; frame the full post ambient
  have hjal0 := cpsTripleWithin_extend_code hmemJal
    (jal_x0_spec_gen_within (-68 : BitVec 21) (bodyHdr + 60))
  rw [hpc_jal] at hjal0
  let F : Assertion :=
    (.x8 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (remaining - 136)) **
      (.x20 ↦ᵣ (inputCur + BitVec.ofNat 64 136)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
      bytesRegion scratchBase (keccakPermuteAbsorbed st0 blk) **
      bytesRegion inputCur blk ** A
  have hF : F.pcFree :=
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (by pcFree) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have cJal : cpsTripleWithin 1 (bodyHdr + 60) liHdr cr F F := by
    refine cpsTripleWithin_weaken
      (fun h hp => (sepConj_emp_left _).2 hp)
      (fun h hq => (sepConj_emp_left _).1 hq)
      (cpsTripleWithin_frameR F hF hjal0)
  have s := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    cBody cJal
  simp only [keccakAbsorbBodyFuel] at s ⊢
  exact s

end EvmAsm.Codegen.Proofs
