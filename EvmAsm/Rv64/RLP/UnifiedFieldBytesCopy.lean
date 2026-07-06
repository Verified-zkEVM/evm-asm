/-
  EvmAsm.Rv64.RLP.UnifiedFieldBytesCopy

  EL.3 / Phase 5 — leaf byte-array field copy. Given a decoded `.bytes` field's payload
  pointer (`x13`, the single-item decoder's output convention) and a fixed length `N`
  (20-byte address / 32-byte hash), copy the `N` payload bytes into the output struct
  region at byte offset `di0`. The byte-array analog of `unified_field_scalar_read`
  (which BE-reads the payload into a register); here we byte-copy it into the output.

  Layout (program base `base`; output pointer register `rOut` holding `outBase`):
      base       ADDI x14, rOut, fieldImm        ; x14 := outBase + di0  (dst pointer)
      base+4     < N copy blocks, 20*N bytes >   ; output[di0 .. di0+N) := src[off .. off+N)
      base+4+20N (exit)
-/

import EvmAsm.Rv64.RLP.ByteCopyChainGen
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- `pcFree` for separating conjunctions whose leaves may include `bytesRegion`. -/
local macro "pcfree_region" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_emp
    | apply pcFree_sepConj)

/-- A singleton before the chain (`a` strictly below `bw`, no wrap) is disjoint from the
    whole copy chain. -/
theorem singleton_disjoint_byteCopyChainCR (a bw : Word) (i : Instr) (N : Nat)
    (hsep : a.toNat + 4 ≤ bw.toNat) (hov : bw.toNat + 20 * N < 2 ^ 64) :
    (CodeReq.singleton a i).Disjoint (byteCopyChainCR bw N) := by
  induction N generalizing bw with
  | zero => simpa [byteCopyChainCR] using CodeReq.Disjoint.empty_right (CodeReq.singleton a i)
  | succ k ih =>
    rw [byteCopyChainCR]
    refine CodeReq.Disjoint.union_right ?_ ?_
    · intro a'
      by_cases ha : a' = a
      · subst ha; exact Or.inr (copyIterCR_none bw a' (fun k2 hk2 => by bv_omega))
      · exact Or.inl (CodeReq.singleton_miss (by simpa using ha))
    · exact ih (bw + 20)
        (by have : (bw + 20).toNat = bw.toNat + 20 := by
              have : bw.toNat + 20 < 2 ^ 64 := by omega
              bv_omega
            omega)
        (by have : (bw + 20).toNat = bw.toNat + 20 := by
              have : bw.toNat + 20 < 2 ^ 64 := by omega
              bv_omega
            omega)

set_option maxRecDepth 8000 in
/-- **Leaf byte-array field copy.** From `x13 = regionBase + ofNat off` (a decoded
    `.bytes` payload pointer) copy `N` bytes into the output struct region at byte offset
    `di0` (set up by `ADDI x14, rOut, fieldImm` where `signExtend12 fieldImm = ofNat di0`).
    The output region's bytes `[di0, di0+N)` become `src[off .. off+N)`. -/
theorem unified_field_bytes_copy
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (srcBytes outBytes : List (BitVec 8)) (off di0 N : Nat) (v12Old v14Old cnt : Word)
    (hsalign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hsover : regionBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsrc : off + N ≤ srcBytes.length) (hdst : di0 + N ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (4 + 20 * N) < 2 ^ 64)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0) :
    cpsTripleWithin (1 + 5 * N) base (base + 4 + BitVec.ofNat 64 (20 * N))
      ((CodeReq.singleton base (.ADDI .x14 rOut fieldImm)).union (byteCopyChainCR (base + 4) N))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ cnt) ** (rOut ↦ᵣ outBase) **
       bytesRegion regionBase srcBytes ** bytesRegion outBase outBytes)
      ((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + N))) **
       (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + N))) ** (regOwn .x15) ** (rOut ↦ᵣ outBase) **
       bytesRegion regionBase srcBytes **
       bytesRegion outBase (copyRangeGen outBytes srcBytes off di0 N)) := by
  -- ADDI x14, rOut, fieldImm : x14 := outBase + ofNat di0.
  have addi := addi_spec_gen_within .x14 rOut v14Old outBase fieldImm base (by decide)
  rw [hImm] at addi
  have s_addi : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x14 rOut fieldImm))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ cnt) ** (rOut ↦ᵣ outBase) **
       bytesRegion regionBase srcBytes ** bytesRegion outBase outBytes)
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di0)) ** (.x15 ↦ᵣ cnt) ** (rOut ↦ᵣ outBase) **
       bytesRegion regionBase srcBytes ** bytesRegion outBase outBytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) ** (.x15 ↦ᵣ cnt) **
         bytesRegion regionBase srcBytes ** bytesRegion outBase outBytes) (by pcfree_region) addi)
  -- The copy chain at base+4.
  have chain := rlp_copy_chain_gen_spec regionBase outBase srcBytes hsalign hdalign hsover hsvalid
    N off di0 cnt v12Old outBytes (base + 4) hsrc hdst hdov hdval
    (by have h4 : (base + 4).toNat = base.toNat + 4 := by bv_omega
        omega)
  -- Frame rOut through the chain.
  have chain' := cpsTripleWithin_frameR (rOut ↦ᵣ outBase) (by pcFree) chain
  have hd : (CodeReq.singleton base (.ADDI .x14 rOut fieldImm)).Disjoint
      (byteCopyChainCR (base + 4) N) :=
    singleton_disjoint_byteCopyChainCR base (base + 4) (.ADDI .x14 rOut fieldImm) N
      (by have : (base + 4).toNat = base.toNat + 4 := by bv_omega
          omega)
      (by have : (base + 4).toNat = base.toNat + 4 := by bv_omega
          omega)
  refine cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) s_addi)
      chain')

end EvmAsm.Rv64.RLP
