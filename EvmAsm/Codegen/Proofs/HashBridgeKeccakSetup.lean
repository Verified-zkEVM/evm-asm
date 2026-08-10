/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSetup

  Body-entry setup for `zkvm_keccak256` (idx 5..15):
    MV x20,a0; MV x9,a1; MV x18,a2; la x8,zk3_state; MV x28,x8; LI x29,25
    + 25-dword zero loop → outer LI header (idx 16).
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakZero
import EvmAsm.Codegen.Proofs.HashBridgeKeccakFrame
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Guest entry PC (concrete). -/
private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256

/-- Shared sponge BSS. -/
private abbrev Zk3 : Word := BitVec.ofNat 64 GuestAddrs.zk3_state

/-- Unfold Program → List Instr so GetElem works. -/
private abbrev keccakProgL : List Instr := zkvmKeccak256_prog

private theorem keccakProgL_len : keccakProgL.length = 69 := by
  simp only [keccakProgL, zkvmKeccak256_prog, zkvmKeccak256_prog_of]
  decide

private theorem keccakProgL_bound : 4 * keccakProgL.length < 2 ^ 64 := by
  rw [keccakProgL_len]; norm_num

private abbrev keccakCr : CodeReq := CodeReq.ofProg B keccakProgL

/-- Singleton at index `k` ⊆ ofProg. -/
private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < keccakProgL.length)
    (hins : keccakProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → keccakCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A keccakProgL k ins hA hk hins keccakProgL_bound a i h

/-- Bridge Codegen.laHi (Nat) → Rv64.laHi (Word) at la site idx 8 = B+32. -/
private theorem la_zk3_hi :
    Codegen.laHi GuestAddrs.zk3_state (GuestAddrs.zkvm_keccak256 + 32) =
      Rv64.laHi (B + 32) Zk3 := by
  decide

private theorem la_zk3_lo :
    Codegen.laLo GuestAddrs.zk3_state (GuestAddrs.zkvm_keccak256 + 32) =
      Rv64.laLo (B + 32) Zk3 := by
  decide

private theorem la_zk3_range : laInRange (B + 32) Zk3 := by
  decide

/-- Three ABI moves: bodyEntry B+20 → B+32. -/
theorem keccakSetupMoves_spec (inputBase lenW outputBase : Word)
    (v20 v9 v18 : Word) :
    cpsTripleWithin 3 (B + 20) (B + 32) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ v20) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase)) := by
  -- MV focuses rd+rs; frame MUST omit both.
  have h0 := mv_spec_gen_within .x20 .x10 inputBase v20 (B + 20) (by decide)
  rw [show (B + 20 : Word) + 4 = B + 24 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 5 (.MV .x20 .x10) (B + 20) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl)) h0
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18)) (by pcf) l0
  have c0 : cpsTripleWithin 1 (B + 20) (B + 24) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ v20) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := mv_spec_gen_within .x9 .x11 lenW v9 (B + 24) (by decide)
  rw [show (B + 24 : Word) + 4 = B + 28 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 6 (.MV .x9 .x11) (B + 24) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl)) h1
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x12 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ inputBase) ** (.x18 ↦ᵣ v18)) (by pcf) l1
  have c1 : cpsTripleWithin 1 (B + 24) (B + 28) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ v18)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have h2 := mv_spec_gen_within .x18 .x12 outputBase v18 (B + 28) (by decide)
  rw [show (B + 28 : Word) + 4 = B + 32 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (mem_at 7 (.MV .x18 .x12) (B + 28) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl)) h2
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) **
      (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW)) (by pcf) l2
  have c2 : cpsTripleWithin 1 (B + 28) (B + 32) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-- `la x8, zk3_state` at B+32. -/
theorem keccakSetupLa_spec (v8 : Word) :
    cpsTripleWithin 2 (B + 32) (B + 40) keccakCr
      (.x8 ↦ᵣ v8) (.x8 ↦ᵣ Zk3) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 32)
        (.AUIPC .x8 (Rv64.laHi (B + 32) Zk3)) a = some i →
        keccakCr a = some i := by
    intro a i hi
    have hmem := mem_at 8
      (.AUIPC .x8 (Codegen.laHi GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256 + 32)))
      (B + 32) (by decide) (by rw [keccakProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_zk3_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 32) + 4)
        (.ADDI .x8 .x8 (Rv64.laLo (B + 32) Zk3)) a = some i →
        keccakCr a = some i := by
    intro a i hi
    have hmem := mem_at 9
      (.ADDI .x8 .x8 (Codegen.laLo GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256 + 32)))
      (B + 36) (by decide) (by rw [keccakProgL_len]; decide) (by rfl)
    have hpc : (B + 32 : Word) + 4 = B + 36 := by decide
    rw [hpc, ← la_zk3_lo] at hi
    exact hmem a i hi
  have h := la_materialize_within .x8 v8 (B + 32) Zk3
    (by decide) la_zk3_range hau had
  rwa [show (B + 32 : Word) + 8 = B + 40 from by decide] at h

/-- MV x28,x8; LI x29,25. B+40 → B+48. -/
theorem keccakSetupZeroPrep_spec (v28 v29 : Word) :
    cpsTripleWithin 2 (B + 40) (B + 48) keccakCr
      ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29))
      ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3) ** (.x29 ↦ᵣ BitVec.ofNat 64 25)) := by
  -- MV x28,x8 focuses x28+x8
  have h0 := mv_spec_gen_within .x28 .x8 Zk3 v28 (B + 40) (by decide)
  rw [show (B + 40 : Word) + 4 = B + 44 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 10 (.MV .x28 .x8) (B + 40) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl)) h0
  have h0F := cpsTripleWithin_frameR (.x29 ↦ᵣ v29) (by pcf) l0
  have c0 : cpsTripleWithin 1 (B + 40) (B + 44) keccakCr
      ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29))
      ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3) ** (.x29 ↦ᵣ v29)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  -- LI focuses only x29; imm must match BitVec.ofNat form used by zero loop
  have h1 := li_spec_gen_within .x29 v29 (BitVec.ofNat 64 25) (B + 44) (by decide)
  rw [show (B + 44 : Word) + 4 = B + 48 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 11 (.LI .x29 (BitVec.ofNat 64 25)) (B + 44) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl)) h1
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3)) (by pcf) l1
  have c1 : cpsTripleWithin 1 (B + 44) (B + 48) keccakCr
      ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3) ** (.x29 ↦ᵣ v29))
      ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3) ** (.x29 ↦ᵣ BitVec.ofNat 64 25)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- Zero loop framed under ABI ambient. B+48 → B+64 (outer LI). Fuel 100. -/
theorem keccakZeroLoop_framed (os : List (BitVec 8))
    (inputBase lenW outputBase : Word) (A : Assertion) (hA : A.pcFree)
    (hlen : os.length = 200)
    (halign : Zk3.toNat % 8 = 0)
    (hover : Zk3.toNat + 200 < 2 ^ 64) :
    cpsTripleWithin 100 (B + 48) (B + 64) keccakCr
      ((.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3) ** (.x29 ↦ᵣ BitVec.ofNat 64 25) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        bytesRegion Zk3 os ** A)
      ((.x8 ↦ᵣ Zk3) **
        (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x29 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        bytesRegion Zk3 keccakZeroStateBytes ** A) := by
  have hloop := keccakZeroLoop_spec keccakCr (B + 48) .x28 .x29 Zk3 os
    (by decide) (by decide) hlen halign hover
    (mem_at 12 (.SD .x28 .x0 0) (B + 48) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl))
    (mem_at 13 (.ADDI .x28 .x28 (8 : BitVec 12)) (B + 52) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl))
    (mem_at 14 (.ADDI .x29 .x29 (-1 : BitVec 12)) (B + 56) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl))
    (mem_at 15 (.BNE .x29 .x0 (-12 : BitVec 13)) (B + 60) (by decide)
      (by rw [keccakProgL_len]; decide) (by rfl))
  rw [show (B + 48 : Word) + 16 = B + 64 from by decide] at hloop
  have hloopF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ Zk3) ** (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ outputBase) ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) hA) hloop
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hloopF

/-- Full setup bodyEntry→outer LI. Fuel 107 = 3+2+2+100. -/
theorem keccakSetupToOuter_spec (inputBase lenW outputBase : Word)
    (v20 v9 v18 v8 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hlen : os.length = 200)
    (halign : Zk3.toNat % 8 = 0)
    (hover : Zk3.toNat + 200 < 2 ^ 64) :
    cpsTripleWithin 107 (B + 20) (B + 64) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ v20) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x8 ↦ᵣ v8) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) **
        (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x29 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion Zk3 keccakZeroStateBytes ** A) := by
  -- moves
  have cMv0 := keccakSetupMoves_spec inputBase lenW outputBase v20 v9 v18
  have cMvF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ v8) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) cMv0
  have cMv : cpsTripleWithin 3 (B + 20) (B + 32) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ v20) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x8 ↦ᵣ v8) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) cMvF
  -- la
  have hla := keccakSetupLa_spec v8
  have hlaF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) hla
  have cLa : cpsTripleWithin 2 (B + 32) (B + 40) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlaF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) cMv cLa
  -- zero prep
  have hprep := keccakSetupZeroPrep_spec v28 v29
  have hprepF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) hprep
  have cPrep : cpsTripleWithin 2 (B + 40) (B + 48) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3) ** (.x29 ↦ᵣ BitVec.ofNat 64 25) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hprepF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 cPrep
  -- zero loop
  have cZ := keccakZeroLoop_framed os inputBase lenW outputBase A hA
    hlen halign hover
  have cZF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase))
    (by pcf) cZ
  have cZ' : cpsTripleWithin 100 (B + 48) (B + 64) keccakCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) ** (.x28 ↦ᵣ Zk3) ** (.x29 ↦ᵣ BitVec.ofNat 64 25) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ inputBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ Zk3) **
        (.x28 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x29 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion Zk3 keccakZeroStateBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) cZF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 cZ'

end EvmAsm.Codegen.Proofs
