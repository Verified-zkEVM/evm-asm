/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegmentsPrelude

  Setup slice for the linked `zkvm_keccak256_segments` routine.

  The segment entry is the machine side consumed by the signing-hash
  contracts.  This module contains the linked-program setup and descriptor
  table facts; the companion proof keeps the byte-loop work tied to the same
  `CodeReq` so that the eventual top-level triple cannot silently prove a
  different program.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakZero
import EvmAsm.Codegen.Proofs.HashBridgeKeccakAbsorb
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256_segments
private abbrev Zk3 : Word := BitVec.ofNat 64 GuestAddrs.zk3_state
private abbrev segmentsProgL : List Instr := zkvmKeccak256Segments_prog
private abbrev segmentsCr : CodeReq := CodeReq.ofProg B segmentsProgL

private theorem segmentsProgL_len : segmentsProgL.length = 70 := by
  simp only [segmentsProgL, zkvmKeccak256Segments_prog,
    zkvmKeccak256Segments_prog_of]
  decide

private theorem segmentsProgL_bound : 4 * segmentsProgL.length < 2 ^ 64 := by
  rw [segmentsProgL_len]
  norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < segmentsProgL.length)
    (hins : segmentsProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → segmentsCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A segmentsProgL k ins hA hk hins
      segmentsProgL_bound a i h

private theorem la_zk3_hi :
    Codegen.laHi GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256_segments + 48) =
      Rv64.laHi (B + 48) Zk3 := by
  decide

private theorem la_zk3_lo :
    Codegen.laLo GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256_segments + 48) =
      Rv64.laLo (B + 48) Zk3 := by
  decide

private theorem la_zk3_range : laInRange (B + 48) Zk3 := by
  decide

private theorem segmentsSetupMoves_spec
    (inputBase countW outputBase : Word)
    (v8 v9 v18 : Word) :
    cpsTripleWithin 3 (B + 36) (B + 48) segmentsCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase)) := by
  have h0 := mv_spec_gen_within .x8 .x10 inputBase v8 (B + 36) (by decide)
  rw [show (B + 36 : Word) + 4 = B + 40 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 9 (.MV .x8 .x10) (B + 36) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) h0
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18)) (by pcf) l0
  have c0 : cpsTripleWithin 1 (B + 36) (B + 40) segmentsCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := mv_spec_gen_within .x9 .x11 countW v9 (B + 40) (by decide)
  rw [show (B + 40 : Word) + 4 = B + 44 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 10 (.MV .x9 .x11) (B + 40) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) h1
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ inputBase) ** (.x18 ↦ᵣ v18)) (by pcf) l1
  have c1 : cpsTripleWithin 1 (B + 40) (B + 44) segmentsCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ v18)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c0 c1
  have h2 := mv_spec_gen_within .x18 .x12 outputBase v18 (B + 44) (by decide)
  rw [show (B + 44 : Word) + 4 = B + 48 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (mem_at 11 (.MV .x18 .x12) (B + 44) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) h2
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) **
      (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW)) (by pcf) l2
  have c2 : cpsTripleWithin 1 (B + 44) (B + 48) segmentsCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

private theorem segmentsSetupLa_spec (v19 : Word) :
    cpsTripleWithin 2 (B + 48) (B + 56) segmentsCr
      (.x19 ↦ᵣ v19) (.x19 ↦ᵣ Zk3) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 48)
        (.AUIPC .x19 (Rv64.laHi (B + 48) Zk3)) a = some i →
        segmentsCr a = some i := by
    intro a i hi
    have hmem := mem_at 12
      (.AUIPC .x19 (Codegen.laHi GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256_segments + 48)))
      (B + 48) (by decide) (by rw [segmentsProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_zk3_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 48) + 4)
        (.ADDI .x19 .x19 (Rv64.laLo (B + 48) Zk3)) a = some i →
        segmentsCr a = some i := by
    intro a i hi
    have hmem := mem_at 13
      (.ADDI .x19 .x19 (Codegen.laLo GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256_segments + 48)))
      (B + 52) (by decide) (by rw [segmentsProgL_len]; decide) (by rfl)
    have hpc : (B + 48 : Word) + 4 = B + 52 := by decide
    rw [hpc, ← la_zk3_lo] at hi
    exact hmem a i hi
  have h := la_materialize_within .x19 v19 (B + 48) Zk3
    (by decide) la_zk3_range hau had
  rwa [show (B + 48 : Word) + 8 = B + 56 from by decide] at h

private theorem segmentsSetupZeroPrep_spec (v5 v6 : Word) :
    cpsTripleWithin 2 (B + 56) (B + 64) segmentsCr
      ((.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ Zk3) **
        (.x6 ↦ᵣ BitVec.ofNat 64 25)) := by
  have h0 := mv_spec_gen_within .x5 .x19 Zk3 v5 (B + 56) (by decide)
  rw [show (B + 56 : Word) + 4 = B + 60 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mem_at 14 (.MV .x5 .x19) (B + 56) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) h0
  have h0F := cpsTripleWithin_frameR (.x6 ↦ᵣ v6) (by pcf) l0
  have c0 : cpsTripleWithin 1 (B + 56) (B + 60) segmentsCr
      ((.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ Zk3) ** (.x6 ↦ᵣ v6)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := li_spec_gen_within .x6 v6 (BitVec.ofNat 64 25) (B + 60) (by decide)
  rw [show (B + 60 : Word) + 4 = B + 64 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mem_at 15 (.LI .x6 (BitVec.ofNat 64 25)) (B + 60) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) h1
  have h1F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ Zk3)) (by pcf) l1
  have c1 : cpsTripleWithin 1 (B + 60) (B + 64) segmentsCr
      ((.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ Zk3) ** (.x6 ↦ᵣ v6))
      ((.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ Zk3) **
        (.x6 ↦ᵣ BitVec.ofNat 64 25)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

private theorem segmentsSetupZeroLoop_spec (os : List (BitVec 8))
    (hOs : os.length = 200)
    (hAlign : Zk3.toNat % 8 = 0)
    (hOver : Zk3.toNat + 200 < 2 ^ 64) :
    cpsTripleWithin 100 (B + 64) (B + 80) segmentsCr
      ((.x5 ↦ᵣ Zk3) ** (.x6 ↦ᵣ BitVec.ofNat 64 25) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os)
      ((.x5 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x6 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion Zk3 keccakZeroStateBytes) := by
  have h := keccakZeroLoop_spec segmentsCr (B + 64) .x5 .x6 Zk3 os
    (by decide) (by decide) hOs hAlign hOver
    (mem_at 16 (.SD .x5 .x0 0) (B + 64) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl))
    (mem_at 17 (.ADDI .x5 .x5 (8 : BitVec 12)) (B + 68) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl))
    (mem_at 18 (.ADDI .x6 .x6 (-1 : BitVec 12)) (B + 72) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl))
    (mem_at 19 (.BNE .x6 .x0 (-12 : BitVec 13)) (B + 76) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl))
  simpa only [show (B + 64 : Word) + 16 = B + 80 by decide] using h

theorem zkvmKeccak256Segments_setup_spec
    (inputBase countW outputBase : Word) (v8 v9 v18 v19 v5 v6 v20 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hOs : os.length = 200)
    (hAlign : Zk3.toNat % 8 = 0)
    (hOver : Zk3.toNat + 200 < 2 ^ 64) :
    cpsTripleWithin 109 (B + 36) (B + 84) segmentsCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase) **
        (.x19 ↦ᵣ Zk3) **
        (.x5 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x6 ↦ᵣ BitVec.ofNat 64 0) ** (.x20 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 keccakZeroStateBytes ** A) := by
  have hMoves := segmentsSetupMoves_spec inputBase countW outputBase v8 v9 v18
  have hMovesF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ v19) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os)
    (by pcf) hMoves
  have hLa := segmentsSetupLa_spec v19
  have hLaF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os)
    (by pcf) hLa
  have hZeroPrep := segmentsSetupZeroPrep_spec v5 v6
  have hZeroPrepF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os)
    (by pcf) hZeroPrep
  have hZero := segmentsSetupZeroLoop_spec os hOs hAlign hOver
  have hZeroF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase) **
      (.x19 ↦ᵣ Zk3) ** (.x20 ↦ᵣ v20))
    (by pcf) hZero
  have hLi := li_spec_gen_within .x20 v20 (0 : Word) (B + 80) (by decide)
  have hLi' := cpsTripleWithin_extend_code
    (mem_at 20 (.LI .x20 (0 : Word)) (B + 80) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) hLi
  rw [show (B + 80 : Word) + 4 = B + 84 from by decide] at hLi'
  have hLiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase) **
      (.x19 ↦ᵣ Zk3) ** (.x5 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
      (.x6 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion Zk3 keccakZeroStateBytes)
    (by pcf) hLi'
  have c0 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hMovesF hLaF
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c0 hZeroPrepF
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c1 hZeroF
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c2 hLiF
  have c3A := cpsTripleWithin_frameR A hA c3
  have c3A' := cpsTripleWithin_mono_nSteps
    (nSteps' := 109) (by omega) c3A
  have c3A'' : cpsTripleWithin 109 (B + 36) (B + 84) segmentsCr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 os ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ countW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ inputBase) ** (.x9 ↦ᵣ countW) ** (.x18 ↦ᵣ outputBase) **
        (.x19 ↦ᵣ Zk3) **
        (.x5 ↦ᵣ (Zk3 + BitVec.ofNat 64 200)) **
        (.x6 ↦ᵣ BitVec.ofNat 64 0) ** (.x20 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion Zk3 keccakZeroStateBytes ** A) := by
    exact cpsTripleWithin_weaken (P' := _) (Q' := _)
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c3A'
  exact c3A''

/-! ## Descriptor table surface

The linked entry consumes three `(ptr,len)` dword pairs.  Keeping the table
bytes explicit makes the zero-length legacy descriptor an ordinary instance:
the source region may be empty, while the table itself remains a 48-byte
read-only region.
-/

def segmentsTableBytes (p0 n0 p1 n1 p2 n2 : Word) : List (BitVec 8) :=
  dwordBytes p0 ++ dwordBytes n0 ++ dwordBytes p1 ++ dwordBytes n1 ++
    dwordBytes p2 ++ dwordBytes n2

theorem segmentsTableBytes_length (p0 n0 p1 n1 p2 n2 : Word) :
    (segmentsTableBytes p0 n0 p1 n1 p2 n2).length = 48 := by
  simp only [segmentsTableBytes, length_dwordBytes, List.length_append]

private theorem segmentsTableBytes_first (p0 n0 p1 n1 p2 n2 : Word) :
    packBytes ((segmentsTableBytes p0 n0 p1 n1 p2 n2).drop 0 |>.take 8) = p0 := by
  change packBytes ((dwordBytes p0 ++ dwordBytes n0 ++ dwordBytes p1 ++
      dwordBytes n1 ++ dwordBytes p2 ++ dwordBytes n2).take 8) = p0
  calc
    _ = packBytes (dwordBytes p0) := congrArg packBytes
      (take8_dword_append p0
        (dwordBytes n0 ++ dwordBytes p1 ++ dwordBytes n1 ++
          dwordBytes p2 ++ dwordBytes n2))
    _ = p0 := packBytes_dwordBytes p0

private theorem segmentsTableBytes_second (p0 n0 p1 n1 p2 n2 : Word) :
    packBytes ((segmentsTableBytes p0 n0 p1 n1 p2 n2).drop 8 |>.take 8) = n0 := by
  change packBytes ((dwordBytes n0 ++ dwordBytes p1 ++ dwordBytes n1 ++
      dwordBytes p2 ++ dwordBytes n2).take 8) = n0
  calc
    _ = packBytes (dwordBytes n0) := congrArg packBytes
      (take8_dword_append n0
        (dwordBytes p1 ++ dwordBytes n1 ++ dwordBytes p2 ++ dwordBytes n2))
    _ = n0 := packBytes_dwordBytes n0

theorem zkvmKeccak256Segments_load_descriptor0_spec
    (table p0 n0 p1 n1 p2 n2 : Word) (v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 4 (B + 88) (B + 104) segmentsCr
      ((.x8 ↦ᵣ table) ** (.x9 ↦ᵣ BitVec.ofNat 64 3) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        bytesRegion table (segmentsTableBytes p0 n0 p1 n1 p2 n2) ** A)
      ((.x8 ↦ᵣ (table + BitVec.ofNat 64 16)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 2) ** (.x21 ↦ᵣ p0) ** (.x22 ↦ᵣ n0) **
        bytesRegion table (segmentsTableBytes p0 n0 p1 n1 p2 n2) ** A) := by
  have hlen := segmentsTableBytes_length p0 n0 p1 n1 p2 n2
  have hld0 := bytesRegion_ld_within .x21 .x8 table v21 (B + 88)
    (segmentsTableBytes p0 n0 p1 n1 p2 n2) 0 (by decide) (by omega) (by decide)
  rw [segmentsTableBytes_first] at hld0
  have hld0' := cpsTripleWithin_extend_code
    (mem_at 22 (.LD .x21 .x8 0) (B + 88) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) hld0
  have hld0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 3) ** (.x22 ↦ᵣ v22))
    (by pcf) hld0'
  have hld1 := bytesRegion_ld_within .x22 .x8 table v22 (B + 92)
    (segmentsTableBytes p0 n0 p1 n1 p2 n2) 1 (by decide) (by omega) (by decide)
  rw [segmentsTableBytes_second] at hld1
  have hld1' := cpsTripleWithin_extend_code
    (mem_at 23 (.LD .x22 .x8 8) (B + 92) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) hld1
  have hld1F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 3) ** (.x21 ↦ᵣ p0))
    (by pcf) hld1'
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by sep_perm hp) hld0F hld1F
  have ha8 := addi_spec_gen_same_within .x8 table
    (16 : BitVec 12) (B + 96) (by decide)
  have hptr8 : table + signExtend12 (16 : BitVec 12) =
      table + BitVec.ofNat 64 16 := by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) by decide]
    exact congrArg (fun x : Word => table + x) (by decide)
  rw [hptr8, show (B + 96 : Word) + 4 = B + 100 by decide] at ha8
  have ha8' := cpsTripleWithin_extend_code
    (mem_at 24 (.ADDI .x8 .x8 (16 : BitVec 12)) (B + 96) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) ha8
  have ha8F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ p0) ** (.x22 ↦ᵣ n0) **
      (.x9 ↦ᵣ BitVec.ofNat 64 3) **
      bytesRegion table (segmentsTableBytes p0 n0 p1 n1 p2 n2))
    (by pcf) ha8'
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by sep_perm hp) c01 ha8F
  have ha9 := addi_spec_gen_same_within .x9
    (BitVec.ofNat 64 3) (-1 : BitVec 12) (B + 100) (by decide)
  rw [show BitVec.ofNat 64 3 + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 2 by decide,
    show (B + 100 : Word) + 4 = B + 104 by decide] at ha9
  have ha9' := cpsTripleWithin_extend_code
    (mem_at 25 (.ADDI .x9 .x9 (-1 : BitVec 12)) (B + 100) (by decide)
      (by rw [segmentsProgL_len]; decide) (by rfl)) ha9
  have ha9F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ (table + BitVec.ofNat 64 16)) ** (.x21 ↦ᵣ p0) **
      (.x22 ↦ᵣ n0) **
      bytesRegion table (segmentsTableBytes p0 n0 p1 n1 p2 n2))
    (by pcf) ha9'
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by sep_perm hp) c2 ha9F
  have c3A := cpsTripleWithin_frameR A hA c3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c3A
