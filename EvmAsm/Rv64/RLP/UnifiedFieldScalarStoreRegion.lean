/-
  EvmAsm.Rv64.RLP.UnifiedFieldScalarStoreRegion

  EL.3 / Phase 5 — leaf scalar store into the output struct region. Given a decoded u64
  field value in `x11`, set up the destination pointer (`ADDI x14, rOut, fieldImm`) and
  spill the value's `N` bytes (little-endian, `N = 8` for a full u64) into the unified
  output-struct `bytesRegion` at byte offset `di0`. The spill analog of
  `unified_field_bytes_copy` — lets decoded scalar fields write into the same whole-struct
  region the address/hash fields use.

      base       ADDI x14, rOut, fieldImm        ; x14 := outBase + di0  (dst pointer)
      base+4     < N spill blocks, 12*N bytes >  ; output[di0 .. di0+N) := value (LE)
      base+4+12N (exit)
-/

import EvmAsm.Rv64.RLP.ScalarSpillChain
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

local macro "pcfree_region" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_emp
    | apply pcFree_sepConj)

/-- A singleton before the spill chain is disjoint from it. -/
theorem singleton_disjoint_spillChainCR (a bw : Word) (i : Instr) (N : Nat)
    (hsep : a.toNat + 4 ≤ bw.toNat) (hov : bw.toNat + 12 * N < 2 ^ 64) :
    (CodeReq.singleton a i).Disjoint (spillChainCR bw N) := by
  induction N generalizing bw with
  | zero => simpa [spillChainCR] using CodeReq.Disjoint.empty_right (CodeReq.singleton a i)
  | succ k ih =>
    rw [spillChainCR]
    refine CodeReq.Disjoint.union_right ?_ ?_
    · intro a'
      by_cases ha : a' = a
      · subst ha; exact Or.inr (spillIterCR_none bw a' (fun k2 hk2 => by bv_omega))
      · exact Or.inl (CodeReq.singleton_miss (by simpa using ha))
    · exact ih (bw + 12)
        (by have : (bw + 12).toNat = bw.toNat + 12 := by
              have : bw.toNat + 12 < 2 ^ 64 := by omega
              bv_omega
            omega)
        (by have : (bw + 12).toNat = bw.toNat + 12 := by
              have : bw.toNat + 12 < 2 ^ 64 := by omega
              bv_omega
            omega)

set_option maxRecDepth 8000 in
/-- **Leaf scalar store into region.** Set up `x14 := outBase + di0` (via `ADDI x14, rOut,
    fieldImm` with `signExtend12 fieldImm = ofNat di0`) and spill the value `x11 = v` (its
    `N` little-endian bytes) into the output region; `output[di0 .. di0+N)` becomes `v`'s
    LE bytes. -/
theorem unified_field_scalar_store_region
    (base : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (outBytes : List (BitVec 8)) (di0 N : Nat) (v v14Old : Word)
    (hdalign : outBase.toNat % 8 = 0)
    (hdst : di0 + N ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (4 + 12 * N) < 2 ^ 64)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0) :
    cpsTripleWithin (1 + 3 * N) base (base + 4 + BitVec.ofNat 64 (12 * N))
      ((CodeReq.singleton base (.ADDI .x14 rOut fieldImm)).union (spillChainCR (base + 4) N))
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ v14Old) ** (rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
      ((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + N))) ** (rOut ↦ᵣ outBase) **
       bytesRegion outBase (spillRange outBytes v di0 N)) := by
  -- ADDI x14, rOut, fieldImm : x14 := outBase + di0.
  have addi := addi_spec_gen_within .x14 rOut v14Old outBase fieldImm base (by decide)
  rw [hImm] at addi
  have s_addi : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x14 rOut fieldImm))
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ v14Old) ** (rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di0)) ** (rOut ↦ᵣ outBase) **
       bytesRegion outBase outBytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ v) ** bytesRegion outBase outBytes) (by pcfree_region) addi)
  -- The spill chain at base+4.
  have chain := rlp_spill_chain_spec outBase hdalign N di0 v outBytes (base + 4) hdst hdov hdval
    (by have h4 : (base + 4).toNat = base.toNat + 4 := by bv_omega
        omega)
  -- Frame rOut through the chain.
  have chain' := cpsTripleWithin_frameR (rOut ↦ᵣ outBase) (by pcFree) chain
  have hd : (CodeReq.singleton base (.ADDI .x14 rOut fieldImm)).Disjoint (spillChainCR (base + 4) N) :=
    singleton_disjoint_spillChainCR base (base + 4) (.ADDI .x14 rOut fieldImm) N
      (by have : (base + 4).toNat = base.toNat + 4 := by bv_omega
          omega)
      (by have : (base + 4).toNat = base.toNat + 4 := by bv_omega
          omega)
  refine cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) s_addi)
      chain')

end EvmAsm.Rv64.RLP
