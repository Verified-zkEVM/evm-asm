/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakDword

  Inner 17-dword XOR-absorb countdown for `zkvm_keccak256`:
  LD input; LD state; XOR; SD state; advance both cursors; ADDI ctr -1; BNE.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakZero
import EvmAsm.Rv64.SAsm.AccumLoop
import EvmAsm.Rv64.SAsm.KeccakStep
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Apply `xorDwordAt` for lanes `0..q` of a rate block. -/
def xorDwordsUpTo (st : List (BitVec 8)) (blk : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => st
  | q + 1 =>
      let st' := xorDwordsUpTo st blk q
      let v := packBytes ((blk.drop (8 * q)).take 8)
      xorDwordAt st' q v

theorem xorDwordsUpTo_length (st blk : List (BitVec 8)) (q : Nat) :
    (xorDwordsUpTo st blk q).length = st.length := by
  induction q generalizing st with
  | zero => rfl
  | succ q ih =>
    simp only [xorDwordsUpTo, xorDwordAt, length_setBytes, ih]

private theorem cursor_advance8 (p : Word) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + signExtend12 (8 : BitVec 12)
      = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((8 : Word)).toNat = 8 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem ctr_dec (n : Nat) (_hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 n := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

/-- Inv at remaining `n`: lanes `0..17-n` XOR'd; temps owned. -/
def keccakDwordInv (curS curI : Reg) (scratchBase inputBase : Word)
    (st0 blk : List (BitVec 8)) (n : Nat) : Assertion :=
  (curS ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (17 - n)))) **
  (curI ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (17 - n)))) **
  bytesRegion scratchBase (xorDwordsUpTo st0 blk (17 - n)) **
  bytesRegion inputBase blk **
  (regOwn .x5) ** (regOwn .x6)

theorem keccakDwordInv_pcFree (curS curI : Reg) (scratchBase inputBase : Word)
    (st0 blk : List (BitVec 8)) (n : Nat) :
    (keccakDwordInv curS curI scratchBase inputBase st0 blk n).pcFree := by
  unfold keccakDwordInv; pcf

/-- Peel two trailing owns. -/
private theorem of_forall2 {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 : Reg}
    (htrip : ∀ (v1 v2 : Word),
      cpsTripleWithin n entry exit cr (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2))
        (Q ** regOwn r1 ** regOwn r2)) :
    cpsTripleWithin n entry exit cr (P ** regOwn r1 ** regOwn r2)
      (Q ** regOwn r1 ** regOwn r2) := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hRest, hd0, hu0, hpP0, hpRest⟩ := hpP
  obtain ⟨hR1, hR2c, hd1, hu1, hpR1, hpR2c⟩ := hpRest
  obtain ⟨v1, hv1⟩ := hpR1
  obtain ⟨v2, hv2⟩ := hpR2c
  have hPR' :
      ((P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hRest, hd0, hu0, hpP0, ⟨hR1, hR2c, hd1, hu1, hv1, hv2⟩⟩, hpR⟩
  exact htrip v1 v2 R hR s hcr hPR' hpc

/-- Concrete-temp body step (7 insn, no BNE). -/
private theorem keccakDwordBody_step (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 blk : List (BitVec 8)) (n : Nat)
    (v5 v6 : Word)
    (hn : n < 17)
    (hst : st0.length = 200)
    (hblk : 8 * 17 ≤ blk.length)
    (hmemLdI : ∀ a i, CodeReq.singleton hdr (.LD .x5 .x30 0) a = some i → cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton (hdr + 4) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (hdr + 12) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i) :
    let k := 17 - (n + 1)
    cpsTripleWithin 7 hdr (hdr + 28) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x31 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (regOwn .x5) ** (regOwn .x6)) := by
  intro k
  have h8k_st : 8 * k + 8 ≤ (xorDwordsUpTo st0 blk k).length := by
    rw [xorDwordsUpTo_length, hst]; omega
  have h8k_st_lt : 8 * k < (xorDwordsUpTo st0 blk k).length := by omega
  have h8k_in_lt : 8 * k < blk.length := by omega
  -- LD input → x5  (focus x30/x5/blk)
  have hldI0 := cpsTripleWithin_extend_code hmemLdI
    (bytesRegion_ld_cursor_within .x5 .x30 inputBase v5 hdr blk k
      (by decide) h8k_in_lt)
  have hldI : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        (.x5 ↦ᵣ v5) ** bytesRegion inputBase blk)
      ((.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        (.x5 ↦ᵣ packBytes ((blk.drop (8 * k)).take 8)) **
        bytesRegion inputBase blk) := hldI0
  have hldIF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
      bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
      (.x6 ↦ᵣ v6))
    (by pcf) hldI
  have c0 : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ packBytes ((blk.drop (8 * k)).take 8)) ** (.x6 ↦ᵣ v6)) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hldIF
    · xperm_hyp hp
    · xperm_hyp hq
  -- LD state → x6
  have hldS0 := cpsTripleWithin_extend_code hmemLdS
    (bytesRegion_ld_cursor_within .x6 .x28 scratchBase v6 (hdr + 4)
      (xorDwordsUpTo st0 blk k) k (by decide) h8k_st_lt)
  have hldS : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase (xorDwordsUpTo st0 blk k))
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x6 ↦ᵣ packBytes (((xorDwordsUpTo st0 blk k).drop (8 * k)).take 8)) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k)) := by
    rw [show (hdr + 4 : Word) + 4 = hdr + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hldS0
    exact hldS0
  have hldSF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
      bytesRegion inputBase blk **
      (.x5 ↦ᵣ packBytes ((blk.drop (8 * k)).take 8)))
    (by pcf) hldS
  have c1 : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ packBytes ((blk.drop (8 * k)).take 8)) ** (.x6 ↦ᵣ v6))
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ packBytes ((blk.drop (8 * k)).take 8)) **
        (.x6 ↦ᵣ packBytes (((xorDwordsUpTo st0 blk k).drop (8 * k)).take 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hldSF
    · xperm_hyp hp
    · xperm_hyp hq
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  -- XOR
  let vI := packBytes ((blk.drop (8 * k)).take 8)
  let vS := packBytes (((xorDwordsUpTo st0 blk k).drop (8 * k)).take 8)
  have hxor0 := cpsTripleWithin_extend_code hmemXor
    (xor_spec_gen_rd_eq_rs1_within .x6 .x5 vS vI (hdr + 8) (by decide))
  have hxor : cpsTripleWithin 1 (hdr + 8) (hdr + 12) cr
      ((.x6 ↦ᵣ vS) ** (.x5 ↦ᵣ vI))
      ((.x6 ↦ᵣ (vS ^^^ vI)) ** (.x5 ↦ᵣ vI)) := by
    rw [show (hdr + 8 : Word) + 4 = hdr + 12 from by
      rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]]
      at hxor0
    exact hxor0
  have hxorF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
      bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
      bytesRegion inputBase blk)
    (by pcf) hxor
  have c2 : cpsTripleWithin 1 (hdr + 8) (hdr + 12) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ vS))
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hxorF
    · simp only [vI, vS] at hp ⊢; xperm_hyp hp
    · simp only [vI, vS] at hq ⊢; xperm_hyp hq
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [vI, vS] at hp ⊢; xperm_hyp hp) c01 c2
  -- SD
  have hsd0 := cpsTripleWithin_extend_code hmemSd
    (bytesRegion_sd_cursor_within .x28 .x6 scratchBase (vS ^^^ vI) (hdr + 12)
      (xorDwordsUpTo st0 blk k) k h8k_st)
  have hsd : cpsTripleWithin 1 (hdr + 12) (hdr + 16) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x6 ↦ᵣ (vS ^^^ vI)) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k))
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x6 ↦ᵣ (vS ^^^ vI)) **
        bytesRegion scratchBase
          (setBytes (xorDwordsUpTo st0 blk k) (8 * k) (dwordBytes (vS ^^^ vI)))) := by
    rw [show (hdr + 12 : Word) + 4 = hdr + 16 from by
      rw [BitVec.add_assoc, show ((12 : Word) + 4) = (16 : Word) from by decide]]
      at hsd0
    exact hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
      bytesRegion inputBase blk **
      (.x5 ↦ᵣ vI))
    (by pcf) hsd
  have hxor_set :
      setBytes (xorDwordsUpTo st0 blk k) (8 * k) (dwordBytes (vS ^^^ vI))
        = xorDwordsUpTo st0 blk (k + 1) := by
    simp only [xorDwordsUpTo, xorDwordAt, vI, vS]
  have c3 : cpsTripleWithin 1 (hdr + 12) (hdr + 16) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk k) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI)))
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hsdF
    · simp only [vI, vS] at hp ⊢; xperm_hyp hp
    · simp only [vI, vS, hxor_set] at hq ⊢; xperm_hyp hq
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3
  -- ADDI x28 +8
  have haddS0 := cpsTripleWithin_extend_code hmemAddS
    (addi_spec_gen_same_within .x28 (scratchBase + BitVec.ofNat 64 (8 * k)) 8
      (hdr + 16) (by decide))
  have haddS : cpsTripleWithin 1 (hdr + 16) (hdr + 20) cr
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k)))
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k) +
        signExtend12 (8 : BitVec 12))) := by
    rw [show (hdr + 16 : Word) + 4 = hdr + 20 from by
      rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]]
      at haddS0
    exact haddS0
  have haddSF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
      bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
      bytesRegion inputBase blk **
      (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI)))
    (by pcf) haddS
  have c4 : cpsTripleWithin 1 (hdr + 16) (hdr + 20) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * k))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI)))
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) haddSF
    · simp only [vI, vS] at hp ⊢; xperm_hyp hp
    · simp only [vI, vS, cursor_advance8] at hq ⊢; xperm_hyp hq
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 c4
  -- ADDI x30 +8
  have haddI0 := cpsTripleWithin_extend_code hmemAddI
    (addi_spec_gen_same_within .x30 (inputBase + BitVec.ofNat 64 (8 * k)) 8
      (hdr + 20) (by decide))
  have haddI : cpsTripleWithin 1 (hdr + 20) (hdr + 24) cr
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k)))
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k) +
        signExtend12 (8 : BitVec 12))) := by
    rw [show (hdr + 20 : Word) + 4 = hdr + 24 from by
      rw [BitVec.add_assoc, show ((20 : Word) + 4) = (24 : Word) from by decide]]
      at haddI0
    exact haddI0
  have haddIF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
      bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
      bytesRegion inputBase blk **
      (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI)))
    (by pcf) haddI
  have c5 : cpsTripleWithin 1 (hdr + 20) (hdr + 24) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * k))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI)))
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) haddIF
    · simp only [vI, vS] at hp ⊢; xperm_hyp hp
    · simp only [vI, vS, cursor_advance8] at hq ⊢; xperm_hyp hq
  have c012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01234 c5
  -- ADDI x31 -1
  have haddC0 := cpsTripleWithin_extend_code hmemAddC
    (addi_spec_gen_same_within .x31 (BitVec.ofNat 64 (n + 1)) (-1) (hdr + 24)
      (by decide))
  have haddC : cpsTripleWithin 1 (hdr + 24) (hdr + 28) cr
      (.x31 ↦ᵣ BitVec.ofNat 64 (n + 1))
      (.x31 ↦ᵣ (BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12))) := by
    rw [show (hdr + 24 : Word) + 4 = hdr + 28 from by
      rw [BitVec.add_assoc, show ((24 : Word) + 4) = (28 : Word) from by decide]]
      at haddC0
    exact haddC0
  have haddCF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (k + 1)))) **
      bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
      bytesRegion inputBase blk **
      (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI)))
    (by pcf) haddC
  have hn64 : n + 1 < 2 ^ 64 := by omega
  have c6 : cpsTripleWithin 1 (hdr + 24) (hdr + 28) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI)))
      ((.x31 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (k + 1)))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk (k + 1)) **
        bytesRegion inputBase blk **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ (vS ^^^ vI))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) haddCF
    · simp only [vI, vS] at hp ⊢; xperm_hyp hp
    · simp only [vI, vS, ctr_dec n hn64] at hq ⊢; xperm_hyp hq
  have c0123456 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012345 c6
  -- Drop temps to owns
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) c0123456
  exact
    (sepConj_mono (fun _ => id)
      (sepConj_mono (fun _ => id)
        (sepConj_mono (fun _ => id)
          (sepConj_mono (fun _ => id)
            (sepConj_mono (fun _ => id)
              (sepConj_mono (fun _ => id)
                (sepConj_mono (regIs_implies_regOwn (r := .x5))
                  (regIs_implies_regOwn (r := .x6))))))))) _ hq

/-- Body under owns (for loop). -/
theorem keccakDwordBody_spec (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 blk : List (BitVec 8)) (n : Nat)
    (hn : n < 17)
    (hst : st0.length = 200)
    (hblk : 8 * 17 ≤ blk.length)
    (hmemLdI : ∀ a i, CodeReq.singleton hdr (.LD .x5 .x30 0) a = some i → cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton (hdr + 4) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (hdr + 12) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i) :
    cpsTripleWithin 7 hdr (hdr + 28) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakDwordInv .x28 .x30 scratchBase inputBase st0 blk (n + 1))
      ((.x31 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakDwordInv .x28 .x30 scratchBase inputBase st0 blk n) := by
  let P : Assertion :=
    (.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (17 - (n + 1))))) **
    (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (17 - (n + 1))))) **
    bytesRegion scratchBase (xorDwordsUpTo st0 blk (17 - (n + 1))) **
    bytesRegion inputBase blk
  let Q : Assertion :=
    (.x31 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * (17 - n)))) **
    (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * (17 - n)))) **
    bytesRegion scratchBase (xorDwordsUpTo st0 blk (17 - n)) **
    bytesRegion inputBase blk
  have hforall := of_forall2 (P := P) (Q := Q) (r1 := .x5) (r2 := .x6)
    (fun v1 v2 => by
      have h :=
        keccakDwordBody_step cr hdr scratchBase inputBase st0 blk n v1 v2
          hn hst hblk hmemLdI hmemLdS hmemXor hmemSd hmemAddS hmemAddI hmemAddC
      have hk1 : 17 - (n + 1) + 1 = 17 - n := by omega
      refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h
      · simp only [P] at hp ⊢; xperm_hyp hp
      · simp only [Q, hk1] at hq ⊢; xperm_hyp hq)
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hforall
  · simp only [keccakDwordInv, P] at hp ⊢; xperm_hyp hp
  · simp only [keccakDwordInv, Q] at hq ⊢; xperm_hyp hq

/-- Full 17-step dword XOR loop. -/
theorem keccakDwordLoop_full (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 blk : List (BitVec 8))
    (hst : st0.length = 200)
    (hblk : 8 * 17 ≤ blk.length)
    (hmemLdI : ∀ a i, CodeReq.singleton hdr (.LD .x5 .x30 0) a = some i → cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton (hdr + 4) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (hdr + 12) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 28) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i) :
    cpsTripleWithin (17 * 8) hdr (hdr + 32) cr
      ((.x31 ↦ᵣ (17 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakDwordInv .x28 .x30 scratchBase inputBase st0 blk 17)
      ((.x31 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakDwordInv .x28 .x30 scratchBase inputBase st0 blk 0) := by
  have hbody : ∀ n, n < 17 →
      cpsTripleWithin 7 hdr (hdr + 28) cr
        ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          keccakDwordInv .x28 .x30 scratchBase inputBase st0 blk (n + 1))
        ((.x31 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
          keccakDwordInv .x28 .x30 scratchBase inputBase st0 blk n) :=
    fun n hn =>
      keccakDwordBody_spec cr hdr scratchBase inputBase st0 blk n hn hst hblk
        hmemLdI hmemLdS hmemXor hmemSd hmemAddS hmemAddI hmemAddC
  have hloop := countdownLoopBottom_spec cr hdr (hdr + 28) .x31
    (-28 : BitVec 13) 7 17
    (keccakDwordInv .x28 .x30 scratchBase inputBase st0 blk)
    (by decide) (by decide) (by decide)
    (by
      rw [show signExtend13 (-28 : BitVec 13) = (-28 : Word) from by decide]
      bv_omega)
    (fun n => keccakDwordInv_pcFree .x28 .x30 scratchBase inputBase st0 blk n)
    hmemBne hbody
  rw [show hdr + 28 + 4 = hdr + 32 from by
    rw [BitVec.add_assoc, show ((28 : Word) + 4) = (32 : Word) from by decide]]
    at hloop
  exact hloop

/-- Entry form: cursors at bases, state at entry, ctr=17. -/
theorem keccakDwordLoop_entry (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 blk : List (BitVec 8))
    (hst : st0.length = 200)
    (hblk : 8 * 17 ≤ blk.length)
    (hmemLdI : ∀ a i, CodeReq.singleton hdr (.LD .x5 .x30 0) a = some i → cr a = some i)
    (hmemLdS : ∀ a i, CodeReq.singleton (hdr + 4) (.LD .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x6 .x6 .x5) a = some i →
      cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (hdr + 12) (.SD .x28 .x6 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 8) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 8) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x31 .x31 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 28) (.BNE .x31 .x0 (-28)) a = some i →
      cr a = some i) :
    cpsTripleWithin (17 * 8) hdr (hdr + 32) cr
      ((.x31 ↦ᵣ (17 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputBase) **
        bytesRegion scratchBase st0 ** bytesRegion inputBase blk **
        (regOwn .x5) ** (regOwn .x6))
      ((.x31 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (8 * 17))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (8 * 17))) **
        bytesRegion scratchBase (xorDwordsUpTo st0 blk 17) **
        bytesRegion inputBase blk **
        (regOwn .x5) ** (regOwn .x6)) := by
  have hfull :=
    keccakDwordLoop_full cr hdr scratchBase inputBase st0 blk hst hblk
      hmemLdI hmemLdS hmemXor hmemSd hmemAddS hmemAddI hmemAddC hmemBne
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hfull
  · -- goal is hfull pre (inv 17); hp is entry form
    unfold keccakDwordInv
    rw [show 17 - 17 = 0 from by omega,
      show scratchBase + BitVec.ofNat 64 (8 * 0) = scratchBase from by
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]; bv_omega,
      show inputBase + BitVec.ofNat 64 (8 * 0) = inputBase from by
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]; bv_omega,
      show xorDwordsUpTo st0 blk 0 = st0 from rfl]
    xperm_hyp hp
  · -- goal is entry post; hq is hfull post (inv 0)
    unfold keccakDwordInv at hq
    rw [show 17 - 0 = 17 from by omega] at hq
    xperm_hyp hq

end EvmAsm.Codegen.Proofs
