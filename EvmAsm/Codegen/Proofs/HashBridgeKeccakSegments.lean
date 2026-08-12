/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegments

  Proof boundary for the linked `zkvm_keccak256_segments` routine.

  The segment entry is the machine side consumed by the signing-hash
  contracts.  This file starts with the concrete setup slice; the remaining
  descriptor/byte-loop proof is kept in the same linked `CodeReq` so that the
  eventual top-level triple cannot silently prove a different program.
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

/-! ## One-byte segment body

The byte body is deliberately stated independently of the two control
branches around it.  The header tests the segment remainder, while the
following `BNE x20,x5` tests the rate offset; keeping both tests outside this
lemma prevents the two counters from being accidentally conflated.
-/

def xorBytesAt (st inp : List (BitVec 8)) (off : Nat) : Nat → List (BitVec 8)
  | 0 => st
  | q + 1 =>
      let st' := xorBytesAt st inp off q
      let b := (inp.getD q 0) ^^^ (st'.getD (off + q) 0)
      setBytes st' (off + q) [b]

theorem xorBytesAt_length (st inp : List (BitVec 8)) (off q : Nat) :
    (xorBytesAt st inp off q).length = st.length := by
  induction q generalizing st with
  | zero => rfl
  | succ q ih =>
    simp only [xorBytesAt, length_setBytes, ih]

private theorem xorBytesAt_succ (st inp : List (BitVec 8)) (off k : Nat)
    (hkState : off + k < (xorBytesAt st inp off k).length)
    (hkInp : k < inp.length) :
    xorBytesAt st inp off (k + 1) =
      setBytes (xorBytesAt st inp off k) (off + k)
        [(inp[k]'hkInp) ^^^ (xorBytesAt st inp off k).getD (off + k) 0] := by
  rw [show k + 1 = Nat.succ k by omega]
  simp only [xorBytesAt, setBytes_singleton]
  have hinpD : inp.getD k 0 = inp[k]'hkInp := by
    simp [List.getD_eq_getElem?_getD, hkInp]
  have hstD : (xorBytesAt st inp off k).getD (off + k) 0 =
      (xorBytesAt st inp off k)[off + k]'hkState := by
    simp [List.getD_eq_getElem?_getD, hkState]
  rw [hinpD, hstD]

private def segmentsByteStep (st inp : List (BitVec 8)) (off cursor : Nat) :
    List (BitVec 8) :=
  setBytes st off [(inp.getD cursor 0) ^^^ (st.getD off 0)]

private theorem segmentsByteStep_eq_xor (st inp : List (BitVec 8))
    (off cursor : Nat) :
    segmentsByteStep st inp off cursor =
      xorBytesAt st (inp.drop cursor) off 1 := by
  simp [segmentsByteStep, xorBytesAt, List.getD_eq_getElem?_getD]

private def segmentsStateFold (st inp : List (BitVec 8))
    (off cursor q : Nat) : List (BitVec 8) :=
  match q with
  | 0 => st
  | q + 1 =>
      let st' := segmentsByteStep st inp off cursor
      if off + 1 = 136 then
        segmentsStateFold (setBytes st' 0 (keccakBytes st' 0)) inp 0 (cursor + 1) q
      else
        segmentsStateFold st' inp (off + 1) (cursor + 1) q

private theorem segmentsStateFold_succ (st inp : List (BitVec 8))
    (off cursor q : Nat) :
    segmentsStateFold st inp off cursor (q + 1) =
      let st' := segmentsByteStep st inp off cursor
      if off + 1 = 136 then
        segmentsStateFold (setBytes st' 0 (keccakBytes st' 0)) inp 0 (cursor + 1) q
      else
        segmentsStateFold st' inp (off + 1) (cursor + 1) q := by
  rfl

private theorem segmentsStateFold_nonrate_step (st inp : List (BitVec 8))
    (off cursor : Nat) (hneq : off + 1 ≠ 136) :
    segmentsStateFold st inp off cursor 1 =
      segmentsByteStep st inp off cursor := by
  simp [segmentsStateFold, hneq]

private theorem segmentsStateFold_rate_boundary (st inp : List (BitVec 8))
    (cursor : Nat) :
    segmentsStateFold st inp 135 cursor 1 =
      setBytes (segmentsByteStep st inp 135 cursor) 0
        (keccakBytes (segmentsByteStep st inp 135 cursor) 0) := by
  simp [segmentsStateFold]

private theorem segments_cursor_advance (p : Word) (k : Nat)
    (_hk : k + 1 < 2 ^ 64) :
    p + BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12) =
      p + BitVec.ofNat 64 (k + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem segments_counter_decrement (n k : Nat)
    (_hk : k + 1 ≤ n) (_hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - k) + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (n - (k + 1)) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  have hklt : n - k < 2 ^ 64 := by omega
  have hpos : n - k ≥ 1 := by omega
  omega

private theorem segments_byte_xor (a b : BitVec 8) :
    ((a.zeroExtend 64) ^^^ (b.zeroExtend 64)).truncate 8 = a ^^^ b := by
  have h1 : (a.zeroExtend 64) ^^^ (b.zeroExtend 64) =
      (a ^^^ b).zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    have ha : a.toNat < 256 := a.isLt
    have hb : b.toNat < 256 := b.isLt
    have ha64 : a.toNat < 2 ^ 64 := by omega
    have hb64 : b.toNat < 2 ^ 64 := by omega
    have hx : a.toNat ^^^ b.toNat < 2 ^ 64 := by
      have := (a ^^^ b).isLt
      have hx8 : a.toNat ^^^ b.toNat < 256 := by rwa [BitVec.toNat_xor] at this
      omega
    simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt hx]
  rw [h1, truncate_zeroExtend_byte]

private theorem segments_values_to_owns3 {P : Assertion} {v5 v6 v7 : Word} :
    ∀ h, (P ** ((.x5 ↦ᵣ v5) ** ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7)))) h →
      (P ** (regOwn .x5 ** (regOwn .x6 ** regOwn .x7))) h := by
  intro h hp
  exact sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
        (regIs_implies_regOwn .x7))) h hp

private theorem segments_byte_body_step (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 inp : List (BitVec 8))
    (off n k : Nat) (v5 v6 v7 : Word)
    (hk : k < n) (hoff : off + k < 136)
    (hst : st0.length = 200) (hinp : n ≤ inp.length)
    (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + (off + k) < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (off + k)) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hmemIn : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i →
      cr a = some i)
    (hmemAdd : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i →
      cr a = some i)
    (hmemState : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i →
      cr a = some i)
    (hmemStore : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i →
      cr a = some i)
    (hmemInputStep : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i →
      cr a = some i)
    (hmemCountStep : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i →
      cr a = some i)
    (hmemOffsetStep : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i →
      cr a = some i) :
    cpsTripleWithin 8 hdr (hdr + 32) cr
      ((.x19 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7))
      ((.x19 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k + 1))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off (k + 1)) **
        bytesRegion inputBase inp **
        (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7)) := by
  have hk_in : k < inp.length := Nat.lt_of_lt_of_le hk hinp
  have hk_state : off + k < (xorBytesAt st0 inp off k).length := by
    rw [xorBytesAt_length, hst]
    omega
  have hst_next : (xorBytesAt st0 inp off (k + 1)).length = 200 := by
    rw [xorBytesAt_length, hst]
  have hlbuIn := cpsTripleWithin_extend_code hmemIn
    (bytesRegion_lbu_within .x5 .x21 inputBase v5 hdr inp k
      (by decide) hb8i hk_in hbaseI hvalidI)
  have hlbuInF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 (off + k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase (xorBytesAt st0 inp off k) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7)) (by pcf) hlbuIn
  have c0 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hlbuInF
  have hAdd := cpsTripleWithin_extend_code hmemAdd
    (add_spec_gen_within .x6 .x19 .x20 scratchBase
      (BitVec.ofNat 64 (off + k)) v6 (hdr + 4) (by decide))
  rw [show (hdr + 4 : Word) + 4 = hdr + 8 by
    rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]] at hAdd
  have hAddF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase (xorBytesAt st0 inp off k) **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ ((inp[k]'hk_in).zeroExtend 64)) **
      (.x7 ↦ᵣ v7)) (by pcf) hAdd
  have c1 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hAddF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have hstate := cpsTripleWithin_extend_code hmemState
    (bytesRegion_lbu_within .x7 .x6 scratchBase v7 (hdr + 8)
      (xorBytesAt st0 inp off k) (off + k) (by decide) hb8s hk_state
      hbaseS hvalidS)
  rw [show (hdr + 8 : Word) + 4 = hdr + 12 by
    rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]] at hstate
  have hstateF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 (off + k)) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) ** bytesRegion inputBase inp **
      (.x5 ↦ᵣ ((inp[k]'hk_in).zeroExtend 64))) (by pcf) hstate
  have c2 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hstateF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2
  let vState : Word := ((xorBytesAt st0 inp off k)[off + k]'hk_state).zeroExtend 64
  let vInput : Word := (inp[k]'hk_in).zeroExtend 64
  have hx := cpsTripleWithin_extend_code hmemXor
    (xor_spec_gen_rd_eq_rs1_within .x7 .x5 vState vInput
      (hdr + 12) (by decide))
  rw [show (hdr + 12 : Word) + 4 = hdr + 16 by
    rw [BitVec.add_assoc, show ((12 : Word) + 4) = (16 : Word) from by decide]] at hx
  have hxF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 (off + k)) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase (xorBytesAt st0 inp off k) **
      bytesRegion inputBase inp ** (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 (off + k)))) (by pcf) hx
  have c3 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hxF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3
  let vX : Word := vState ^^^ vInput
  let st1 : List (BitVec 8) :=
    (xorBytesAt st0 inp off k).set (off + k) (vX.truncate 8)
  have hstore := cpsTripleWithin_extend_code hmemStore
    (bytesRegion_sb_within .x6 .x7 scratchBase vX (hdr + 16)
      (xorBytesAt st0 inp off k) (off + k) hb8s hk_state hbaseS hvalidS)
  rw [show (hdr + 16 : Word) + 4 = hdr + 20 by
    rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]] at hstore
  have hstoreF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 (off + k)) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ ((inp[k]'hk_in).zeroExtend 64))) (by pcf) hstore
  have c4 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hstoreF
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by sep_perm hp) c0123 c4
  have hi := cpsTripleWithin_extend_code hmemInputStep
    (addi_spec_gen_same_within .x21 (inputBase + BitVec.ofNat 64 k)
      (1 : BitVec 12) (hdr + 20) (by decide))
  rw [show (hdr + 20 : Word) + 4 = hdr + 24 by
    rw [BitVec.add_assoc, show ((20 : Word) + 4) = (24 : Word) from by decide]] at hi
  have hk64 : k + 1 < 2 ^ 64 := by omega
  rw [segments_cursor_advance inputBase k hk64] at hi
  have hiF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ BitVec.ofNat 64 (off + k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase st1 **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ vInput) **
      (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 (off + k))) ** (.x7 ↦ᵣ vX))
    (by pcf) hi
  have c5 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hiF
  have c012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01234 c5
  have hc := cpsTripleWithin_extend_code hmemCountStep
    (addi_spec_gen_same_within .x22 (BitVec.ofNat 64 (n - k))
      (-1 : BitVec 12) (hdr + 24) (by decide))
  rw [show (hdr + 24 : Word) + 4 = hdr + 28 by
    rw [BitVec.add_assoc, show ((24 : Word) + 4) = (28 : Word) from by decide]] at hc
  rw [segments_counter_decrement n k (by omega) hn64] at hc
  have hcF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ BitVec.ofNat 64 (off + k)) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      bytesRegion scratchBase st1 **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ vInput) **
      (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 (off + k))) ** (.x7 ↦ᵣ vX))
    (by pcf) hc
  have c6 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hcF
  have c0123456 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012345 c6
  have ho := cpsTripleWithin_extend_code hmemOffsetStep
    (addi_spec_gen_same_within .x20 (BitVec.ofNat 64 (off + k))
      (1 : BitVec 12) (hdr + 28) (by decide))
  rw [show (hdr + 28 : Word) + 4 = hdr + 32 by
    rw [BitVec.add_assoc, show ((28 : Word) + 4) = (32 : Word) from by decide]] at ho
  have hoff_step : BitVec.ofNat 64 (off + k) + signExtend12 (1 : BitVec 12) =
      BitVec.ofNat 64 (off + k + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hoff_step] at ho
  have hoF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - (k + 1))) **
      bytesRegion scratchBase st1 **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ vInput) **
      (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 (off + k))) ** (.x7 ↦ᵣ vX))
    (by pcf) ho
  have c7 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hoF
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123456 c7
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h_state hq => ?_) c
  · rw [show (off + k + 1) = off + (k + 1) by omega]
    have hxor := xorBytesAt_succ st0 inp off k hk_state hk_in
    rw [hxor]
    have hbyte : (xorBytesAt st0 inp off k)[off + k]'hk_state =
        (xorBytesAt st0 inp off k).getD (off + k) 0 := by simp [List.getD_eq_getElem?_getD, hk_state]
    have hbyteval : vX.truncate 8 =
        (inp[k]'hk_in) ^^^ (xorBytesAt st0 inp off k).getD (off + k) 0 := by
      dsimp [vX, vState, vInput]
      change
        ((((xorBytesAt st0 inp off k)[off + k]'hk_state).zeroExtend 64) ^^^
            ((inp[k]'hk_in).zeroExtend 64)).truncate 8 =
          (inp[k]'hk_in) ^^^ (xorBytesAt st0 inp off k).getD (off + k) 0
      calc
        _ = (xorBytesAt st0 inp off k)[off + k]'hk_state ^^^ (inp[k]'hk_in) :=
          segments_byte_xor _ _
        _ = (inp[k]'hk_in) ^^^ (xorBytesAt st0 inp off k)[off + k]'hk_state :=
          BitVec.xor_comm _ _
        _ = (inp[k]'hk_in) ^^^ (xorBytesAt st0 inp off k).getD (off + k) 0 := by
          rw [hbyte]
    have hst1 : st1 = xorBytesAt st0 inp off (k + 1) := by
      unfold st1
      rw [hbyteval, hxor, setBytes_singleton]
    rw [hst1] at hq
    rw [hxor] at hq
    rw [show off + k + 1 = off + (k + 1) by omega] at hq
    let Pseg : Assertion :=
      (.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 (off + (k + 1))) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - (k + 1))) **
      bytesRegion scratchBase
        (setBytes (xorBytesAt st0 inp off k) (off + k)
          [((inp[k]'hk_in) ^^^
            (xorBytesAt st0 inp off k).getD (off + k) 0)]) **
      bytesRegion inputBase inp
    have hq0 :
        (Pseg ** (.x5 ↦ᵣ vInput) **
          (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 (off + k))) **
          (.x7 ↦ᵣ vX)) h_state := by
      have hq1 :
          (((.x19 ↦ᵣ scratchBase) **
            (.x20 ↦ᵣ BitVec.ofNat 64 (off + (k + 1))) **
            (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ BitVec.ofNat 64 (n - (k + 1))) **
            bytesRegion scratchBase
              (setBytes (xorBytesAt st0 inp off k) (off + k)
                [((inp[k]'hk_in) ^^^
                  (xorBytesAt st0 inp off k).getD (off + k) 0)]) **
            bytesRegion inputBase inp **
            (.x5 ↦ᵣ vInput) **
            (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 (off + k))) **
            (.x7 ↦ᵣ vX))) h_state := by
        xperm_hyp hq
      simpa only [Pseg, sepConj_assoc'] using hq1
    simpa only [Pseg, sepConj_assoc'] using
      (segments_values_to_owns3 (P := Pseg)
        (v5 := vInput) (v6 := scratchBase + BitVec.ofNat 64 (off + k))
        (v7 := vX) h_state hq0)

private theorem segments_rate_test_spec (cr : CodeReq) (hdr vOffset : Word)
    (A : Assertion) (hA : A.pcFree)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i →
      cr a = some i) :
    cpsBranchWithin 2 (hdr + 32) cr
      ((regOwn .x5) ** (.x20 ↦ᵣ vOffset) ** A)
      (hdr + 36 + signExtend13 (-40 : BitVec 13))
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset ≠ (136 : Word)⌝) ** A)
      (hdr + 40)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset = (136 : Word)⌝) ** A) := by
  have hli := cpsTripleWithin_extend_code hmemLi
    (li_spec_gen_own_within .x5 (136 : Word) (hdr + 32) (by decide))
  rw [show (hdr + 32 : Word) + 4 = hdr + 36 by
    rw [BitVec.add_assoc, show ((32 : Word) + 4) = (36 : Word) from by decide]] at hli
  have hliF := cpsTripleWithin_frameR ((.x20 ↦ᵣ vOffset) ** A)
    (pcFree_sepConj (by pcf) hA) hli
  have hb := cpsBranchWithin_extend_code hmemBne
    (bne_spec_gen_within .x20 .x5 (-40 : BitVec 13) vOffset
      (136 : Word) (hdr + 36))
  have hbF := cpsBranchWithin_frameR A hA hb
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hbF
  rw [show (hdr + 36 : Word) + 4 = hdr + 40 by
    rw [BitVec.add_assoc, show ((36 : Word) + 4) = (40 : Word) from by decide]] at hseq
  exact hseq

private theorem segments_absorb_spec (cr : CodeReq) (hdr scratchBase v10 : Word)
    (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmemMv : ∀ a i, CodeReq.singleton hdr (.MV .x10 .x19) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 4) (.CSRS 0x800 .x10) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 hdr (hdr + 8) cr
      ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      ((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) ** A) := by
  have hmv := cpsTripleWithin_extend_code hmemMv
    (mv_spec_gen_within .x10 .x19 scratchBase v10 hdr (by decide))
  rw [show (hdr : Word) + 4 = hdr + 4 by rfl] at hmv
  have hmvF := cpsTripleWithin_frameR
    (regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
    (pcFree_sepConj (pcFree_regOwns _)
      (pcFree_sepConj (bytesRegion_pcFree _ _) hA)) hmv
  have hcsrs := csrs_keccak_x10_own_flat (hdr + 4) scratchBase st
    ((.x19 ↦ᵣ scratchBase) ** A)
    (pcFree_sepConj (by pcf) hA) hst hb8 hvalid
  rw [show (hdr + 4 : Word) + 4 = hdr + 8 by
    rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]] at hcsrs
  have hcsrs' := cpsTripleWithin_extend_code hmemCsrs hcsrs
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmvF hcsrs'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

private theorem segments_rate_continuation_spec
    (cr : CodeReq) (hdr scratchBase v10 : Word)
    (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i →
      cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i →
      cr a = some i) :
    cpsTripleWithin 4 (hdr + 40) (hdr - 4) cr
      ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st **
        (.x20 ↦ᵣ (136 : Word)) ** A)
      ((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
        (.x20 ↦ᵣ (0 : Word)) ** A) := by
  have hmemCsrs' : ∀ a i,
      CodeReq.singleton ((hdr + 40) + 4) (.CSRS 0x800 .x10) a = some i →
        cr a = some i := by
    intro a i h
    rw [show (hdr + 40 : Word) + 4 = hdr + 44 by
      rw [BitVec.add_assoc, show ((40 : Word) + 4) = (44 : Word) from by decide]] at h
    exact hmemCsrs a i h
  have hAbs := segments_absorb_spec cr (hdr + 40) scratchBase v10 st
    ((.x20 ↦ᵣ (136 : Word)) ** A)
    (pcFree_sepConj (by pcf) hA) hst hb8 hvalid hmemMv hmemCsrs'
  rw [show (hdr + 40 : Word) + 8 = hdr + 48 by
    rw [BitVec.add_assoc, show ((40 : Word) + 8) = (48 : Word) from by decide]] at hAbs
  have hLi := cpsTripleWithin_extend_code hmemLi
    (li_spec_gen_within .x20 (136 : Word) (0 : Word) (hdr + 48) (by decide))
  rw [show (hdr + 48 : Word) + 4 = hdr + 52 by
    rw [BitVec.add_assoc, show ((48 : Word) + 4) = (52 : Word) from by decide]] at hLi
  let T : Assertion :=
    (.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
      regOwns keccakCsrsRest **
      bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) ** A
  have hT : T.pcFree := by
    simp only [T]
    exact pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf)
        (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj (bytesRegion_pcFree _ _) hA)))
  have hLiF := cpsTripleWithin_frameR T hT hLi
  let Pzero : Assertion := (.x20 ↦ᵣ (0 : Word)) ** T
  have hPzero : Pzero.pcFree := by
    simp only [Pzero]
    exact pcFree_sepConj (by pcf) hT
  have hJal0 := jal0_spec_pcFree (-56 : BitVec 21) (hdr + 52) (P := Pzero) hPzero
  have hJal := cpsTripleWithin_extend_code hmemJal hJal0
  rw [show (hdr + 52 : Word) + signExtend21 (-56 : BitVec 21) = hdr - 4 by
    rw [show signExtend21 (-56 : BitVec 21) = (-56 : Word) from by decide]
    bv_omega] at hJal
  have hTail := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hLiF hJal
  have hAll := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [T] at hp ⊢; xperm_hyp hp) hAbs hTail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by simp only [Pzero, T] at hq ⊢; xperm_hyp hq) hAll

private theorem segments_rate_branch_spec
    (cr : CodeReq) (hdr scratchBase v10 vOffset : Word)
    (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i →
      cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i →
      cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i →
      cr a = some i) :
    cpsBranchWithin 6 (hdr + 32) cr
      ((regOwn .x5) ** (.x20 ↦ᵣ vOffset) ** (.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      (hdr - 4)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset ≠ (136 : Word)⌝) **
          ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
            regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A))
      (hdr - 4)
        (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
          (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
          (⌜vOffset = (136 : Word)⌝ ** A)) := by
  let Arate : Assertion :=
    (.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
      bytesRegion scratchBase st ** A
  have hArate : Arate.pcFree := by
    simp only [Arate]
    exact pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf)
        (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj (bytesRegion_pcFree _ _) hA)))
  have hRate := segments_rate_test_spec cr hdr vOffset Arate hArate hmemLi hmemBne
  have hRate' : cpsBranchWithin 2 (hdr + 32) cr
      ((regOwn .x5) ** (.x20 ↦ᵣ vOffset) ** Arate)
      (hdr - 4)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset ≠ (136 : Word)⌝) ** Arate)
      (hdr + 40)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset = (136 : Word)⌝) ** Arate) := by
    simpa only [Arate, show (hdr + 36 : Word) + signExtend13 (-40 : BitVec 13) = hdr - 4 by
      rw [show signExtend13 (-40 : BitVec 13) = (-40 : Word) from by decide]
      bv_omega] using hRate
  have hCont := segments_rate_continuation_spec cr hdr scratchBase v10 st
    ((.x5 ↦ᵣ (136 : Word)) ** (⌜vOffset = (136 : Word)⌝ ** A))
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hA))
    hst hb8 hvalid hmemMv hmemCsrs hmemLi0 hmemJal
  have hCont' : cpsTripleWithin 4 (hdr + 40) (hdr - 4) cr
      (((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase st ** (.x20 ↦ᵣ (136 : Word)) **
        (.x5 ↦ᵣ (136 : Word))) ** (⌜vOffset = (136 : Word)⌝ ** A))
      (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
        (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
        (⌜vOffset = (136 : Word)⌝ ** A)) := by
    simpa only [sepConj_assoc'] using hCont
  have hperm : ∀ h,
      (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
        ⌜vOffset = (136 : Word)⌝) ** Arate) h →
      (((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase st ** (.x20 ↦ᵣ (136 : Word)) **
        (.x5 ↦ᵣ (136 : Word))) ** (⌜vOffset = (136 : Word)⌝ ** A)) h := by
    intro h hp
    have hp' :
        ((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) ** Arate **
          ⌜vOffset = (136 : Word)⌝) h := by
      simpa only [Arate] using (by
        have := hp
        xperm_hyp this)
    have heq : vOffset = (136 : Word) := by
      have hp'''' :
          (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) ** Arate) **
            ⌜vOffset = (136 : Word)⌝) h := by
        xperm_hyp hp'
      have hinner := (sepConj_pure_right (P :=
        (.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) ** Arate) h).1 hp''''
      exact hinner.2
    have hp''' :
        ((.x20 ↦ᵣ (136 : Word)) ** (.x5 ↦ᵣ (136 : Word)) ** Arate **
          ⌜vOffset = (136 : Word)⌝) h := by
      simpa only [heq] using hp'
    have hp'''' :
        ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
          bytesRegion scratchBase st ** (.x20 ↦ᵣ (136 : Word)) **
          (.x5 ↦ᵣ (136 : Word)) ** ⌜vOffset = (136 : Word)⌝ ** A) h := by
      simp only [Arate] at hp''' ⊢
      xperm_hyp hp'''
    simpa only [sepConj_assoc'] using hp''''
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    hRate' hperm hCont' (fun h hp => by
      simp only [Arate] at hp ⊢
      xperm_hyp hp)

private theorem segments_of_forall3 {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 r3 : Reg}
    (h : ∀ (v1 v2 v3 : Word),
      cpsTripleWithin nSteps entry exit_ cr
        (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** (regOwn r1) ** (regOwn r2) ** (regOwn r3)) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨h3, h4, hd2, hu2, hP3, hOwn⟩ := hPP
  obtain ⟨h5, h6, hd3, hu3, ⟨v1, hv1⟩, hOwn23⟩ := hOwn
  obtain ⟨h7, h8, hd4, hu4, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hOwn23
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨h3, h4, hd2, hu2, hP3,
        ⟨h5, h6, hd3, hu3, hv1,
          ⟨h7, h8, hd4, hu4, hv2, hv3⟩⟩⟩, hRb⟩ hpc

private theorem segments_nonrate_boundary (off k : Nat) (hnext : off + k + 1 < 136) :
    BitVec.ofNat 64 (off + k + 1) ≠ (136 : Word) := by
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  have h136 : BitVec.toNat (136 : Word) = 136 := by decide
  rw [h136] at hnat
  have hlt64 : off + k + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt64] at hnat
  omega

private theorem segments_byte_round_spec
    (cr : CodeReq) (hdr scratchBase inputBase : Word) (v10 : Word)
    (st0 inp : List (BitVec 8)) (off n k : Nat) (A : Assertion)
    (hA : A.pcFree) (hk : k < n) (hoff : off + k < 136)
    (hst : st0.length = 200) (hinp : n ≤ inp.length) (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + (off + k) < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (off + k)) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmem0 : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i → cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i → cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i → cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i → cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i → cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i → cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i → cr a = some i)
    (hmem7 : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i → cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i → cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i → cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i → cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i → cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i → cr a = some i) :
    cpsBranchWithin 14 hdr cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off k) ** bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A)
      (hdr - 4) (fun h =>
        (((.x20 ↦ᵣ (BitVec.ofNat 64 (off + k + 1))) **
          (.x5 ↦ᵣ (136 : Word)) **
          ⌜BitVec.ofNat 64 (off + k + 1) ≠ (136 : Word)⌝) **
          ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
            regOwns keccakCsrsRest **
            bytesRegion scratchBase (xorBytesAt st0 inp off (k + 1)) **
            (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 ** A)) h)
      (hdr - 4) (fun h =>
        (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase
            (setBytes (xorBytesAt st0 inp off (k + 1)) 0
              (keccakBytes (xorBytesAt st0 inp off (k + 1)) 0)) **
          (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
          ((.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 **
            (⌜BitVec.ofNat 64 (off + k + 1) = (136 : Word)⌝ ** A))) h) := by
  let F : Assertion := (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A
  have hF : F.pcFree := by
    simp only [F]
    exact pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regOwns _) hA)
  have hbodyVals : ∀ v5 v6 v7,
      cpsTripleWithin 8 hdr (hdr + 32) cr
        ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
          bytesRegion scratchBase (xorBytesAt st0 inp off k) ** bytesRegion inputBase inp **
          F ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7))
        ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k + 1))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion scratchBase (xorBytesAt st0 inp off (k + 1)) **
          bytesRegion inputBase inp ** F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) := by
    intro v5 v6 v7
    have h := segments_byte_body_step cr hdr scratchBase inputBase st0 inp off n k
      v5 v6 v7 hk hoff hst hinp hn64 hb8s hb8i hbaseS hbaseI hvalidS hvalidI
      hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6 hmem7
    have hF' := cpsTripleWithin_frameR F hF h
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF'
  have hbody : cpsTripleWithin 8 hdr (hdr + 32) cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off k) ** bytesRegion inputBase inp **
        F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k + 1))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off (k + 1)) **
        bytesRegion inputBase inp ** F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [F] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [F] at hq ⊢
        xperm_hyp hq)
      (segments_of_forall3
      (P :=
        (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
          bytesRegion scratchBase (xorBytesAt st0 inp off k) **
          bytesRegion inputBase inp ** F)
      (Q :=
        (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k + 1))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion scratchBase (xorBytesAt st0 inp off (k + 1)) **
          bytesRegion inputBase inp ** F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (fun v5 v6 v7 => by
        refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => hq)
          (hbodyVals v5 v6 v7)
        simp only [F] at hp ⊢
        xperm_hyp hp))
  let A0 : Assertion :=
    (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
      bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 ** A
  have hA0 : A0.pcFree := by
    simp only [A0]
    exact pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf)
      (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hA))))
  have hRate := segments_rate_branch_spec cr hdr scratchBase v10
    (BitVec.ofNat 64 (off + k + 1))
    (xorBytesAt st0 inp off (k + 1)) A0 hA0
    (by simp [xorBytesAt_length, hst]) hb8s hvalid hmemLi hmemBne
    hmemMv hmemCsrs hmemLi0 hmemJal
  have hSeq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by simp only [F, A0] at hp ⊢; xperm_hyp hp) hbody hRate
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [A0] at hq ⊢
      xperm_hyp hq)
    (fun _ hq => by
      simp only [A0] at hq ⊢
      xperm_hyp hq) hSeq

private theorem segments_byte_round_nonrate_spec
    (cr : CodeReq) (hdr scratchBase inputBase : Word) (v10 : Word)
    (st0 inp : List (BitVec 8)) (off n k : Nat) (A : Assertion)
    (hA : A.pcFree) (hk : k < n) (hnext : off + k + 1 < 136)
    (hst : st0.length = 200) (hinp : n ≤ inp.length) (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + (off + k) < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (off + k)) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmem0 : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i → cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i → cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i → cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i → cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i → cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i → cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i → cr a = some i)
    (hmem7 : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i → cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i → cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i → cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i → cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i → cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i → cr a = some i) :
    cpsTripleWithin 14 hdr (hdr - 4) cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off k) ** bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A)
      (((.x20 ↦ᵣ (BitVec.ofNat 64 (off + k + 1))) **
          (.x5 ↦ᵣ (136 : Word)) **
          ⌜BitVec.ofNat 64 (off + k + 1) ≠ (136 : Word)⌝) **
        ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase (xorBytesAt st0 inp off (k + 1)) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 ** A)) := by
  have hround := segments_byte_round_spec cr hdr scratchBase inputBase v10 st0 inp off n k A
    hA hk (by omega) hst hinp hn64 hb8s hb8i hbaseS hbaseI hvalidS hvalidI hvalid
    hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6 hmem7 hmemLi hmemBne hmemMv hmemCsrs
    hmemLi0 hmemJal
  apply cpsBranchWithin_takenPath hround
  intro hp hq
  extract_pure_deep hq
  obtain ⟨heq, _⟩ := hq
  exact segments_nonrate_boundary off k hnext heq

private theorem segments_byte_round_rate_spec
    (cr : CodeReq) (hdr scratchBase inputBase : Word) (v10 : Word)
    (st0 inp : List (BitVec 8)) (off n k : Nat) (A : Assertion)
    (hA : A.pcFree) (hk : k < n) (hoff : off + k < 136)
    (hrate : off + k + 1 = 136)
    (hst : st0.length = 200) (hinp : n ≤ inp.length) (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + (off + k) < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (off + k)) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmem0 : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i → cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i → cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i → cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i → cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i → cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i → cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i → cr a = some i)
    (hmem7 : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i → cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i → cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i → cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i → cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i → cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i → cr a = some i) :
    cpsTripleWithin 14 hdr (hdr - 4) cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off k) ** bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A)
      (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase
            (setBytes (xorBytesAt st0 inp off (k + 1)) 0
              (keccakBytes (xorBytesAt st0 inp off (k + 1)) 0)) **
          (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
        ((.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 **
          (⌜BitVec.ofNat 64 (off + k + 1) = (136 : Word)⌝ ** A))) := by
  have hround := segments_byte_round_spec cr hdr scratchBase inputBase v10 st0 inp off n k A
    hA hk hoff hst hinp hn64 hb8s hb8i hbaseS hbaseI hvalidS hvalidI hvalid
    hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6 hmem7 hmemLi hmemBne hmemMv hmemCsrs
    hmemLi0 hmemJal
  apply cpsBranchWithin_ntakenPath hround
  intro hp hq
  extract_pure_deep hq
  obtain ⟨hne, _⟩ := hq
  apply hne
  rw [hrate]
  rfl

/-! The descriptor counter's control shape is separate from the byte-state
    invariant.  A nonzero descriptor count takes the fall-through byte round
    and returns to the header; exhaustion takes the header branch to the next
    descriptor gate.  Keeping this combinator explicit prevents the eventual
    state invariant from silently changing the branch geometry. -/

private theorem segments_descriptor_loop_spec
    (cr : CodeReq) (hdr exitA : Word) (n : Nat)
    (inv : Nat → Assertion) (QA Q : Assertion)
    (hiterBranch : ∀ j, j < n →
      cpsBranchWithin 1 hdr cr (inv j) exitA QA (hdr + 4) (inv j))
    (hround : ∀ j, j < n →
      cpsTripleWithin 14 (hdr + 4) hdr cr (inv j) (inv (j + 1)))
    (hfinal : cpsTripleWithin 1 hdr exitA cr (inv n) Q) :
    cpsBranchWithin (n * 15 + 1) hdr cr (inv 0) exitA QA exitA Q := by
  apply twoExitRetLoop_spec n 15 1 inv
  · intro j hj
    exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
      (hiterBranch j hj)
      (fun _ hp => by xperm_hyp hp)
      (hround j hj)
      (fun _ hp => by xperm_hyp hp)
  · exact hfinal

private theorem segments_descriptor_header_spec
    (cr : CodeReq) (hdr exitA v : Word) (P : Assertion) (hP : P.pcFree)
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsBranchWithin 1 hdr cr
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      exitA (((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) ** ⌜v = (0 : Word)⌝)
      (hdr + 4) (((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) ** ⌜v ≠ (0 : Word)⌝) := by
  have hbr := cpsBranchWithin_extend_code hmem
    (beq_spec_gen_within .x22 .x0 (-20 : BitVec 13) v (0 : Word) hdr)
  rw [haddr] at hbr
  have hbrF := cpsBranchWithin_frameR P hP hbr
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by xperm_hyp hq)
    hbrF

private theorem segments_descriptor_header_nonzero_spec
    (cr : CodeReq) (hdr exitA v : Word) (P QA : Assertion) (hP : P.pcFree)
    (hv : v ≠ (0 : Word))
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsBranchWithin 1 hdr cr
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      exitA QA
      (hdr + 4) ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hbr := segments_descriptor_header_spec cr hdr exitA v P hP haddr hmem
  exact cpsBranchWithin_weaken
    (fun _ hp => hp)
    (fun h hq => by
      have heq := ((sepConj_pure_right (P :=
        (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).2
      exact (hv heq).elim)
    (fun h hq => by
      exact ((sepConj_pure_right (P :=
        (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).1)
    hbr

private theorem segments_descriptor_header_zero_spec
    (cr : CodeReq) (hdr exitA v : Word) (P : Assertion) (hP : P.pcFree)
    (hv : v = (0 : Word))
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 hdr exitA cr
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hbr := segments_descriptor_header_spec cr hdr exitA v P hP haddr hmem
  have htaken := cpsBranchWithin_takenPath hbr (fun h hq => by
    have hne := ((sepConj_pure_right (P :=
      (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).2
    exact hne hv)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hq => ((sepConj_pure_right (P :=
      (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).1)
    htaken

private theorem segments_descriptor_loop_with_header
    (cr : CodeReq) (hdr exitA : Word) (n : Nat)
    (payload : Nat → Assertion) (QA Q : Assertion)
    (hpayload : ∀ j, (payload j).pcFree)
    (hn64 : n < 2 ^ 64)
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i)
    (hround : ∀ j, j < n →
      cpsTripleWithin 14 (hdr + 4) hdr cr
        ((.x22 ↦ᵣ (BitVec.ofNat 64 (n - j))) ** (.x0 ↦ᵣ (0 : Word)) ** payload j)
        ((.x22 ↦ᵣ (BitVec.ofNat 64 (n - (j + 1)))) ** (.x0 ↦ᵣ (0 : Word)) **
          payload (j + 1)))
    (hfinal : cpsTripleWithin 1 hdr exitA cr
      ((.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** payload n) Q) :
    cpsBranchWithin (n * 15 + 1) hdr cr
      ((.x22 ↦ᵣ (BitVec.ofNat 64 n)) ** (.x0 ↦ᵣ (0 : Word)) ** payload 0)
      exitA QA exitA Q := by
  apply segments_descriptor_loop_spec cr hdr exitA n
    (fun j => (.x22 ↦ᵣ (BitVec.ofNat 64 (n - j))) **
      (.x0 ↦ᵣ (0 : Word)) ** payload j) QA Q
  · intro j hj
    have hne : BitVec.ofNat 64 (n - j) ≠ (0 : Word) := by
      intro heq
      have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat] at hnat
      have hsub : n - j < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hsub] at hnat
      have hzero : BitVec.toNat (0 : Word) = 0 := by decide
      rw [hzero] at hnat
      omega
    simpa using segments_descriptor_header_nonzero_spec cr hdr exitA
      (BitVec.ofNat 64 (n - j)) (payload j) QA (hpayload j) hne haddr hmem
  · exact hround
  · simpa using hfinal

end EvmAsm.Codegen.Proofs
