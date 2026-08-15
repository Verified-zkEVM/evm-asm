/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Setup

  The straight-line ABI setup of `zkvm_sha256`.  This is intentionally kept
  separate from the compression/padding loops: the four moves are a useful
  proof boundary in their own right and pin the exact register contract of the
  generated wrapper.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Frame
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev ShaState : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_state
private abbrev ShaInput : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_input
private abbrev ShaIv : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_iv
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]
  norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins sha256ProgL_bound a i h

private theorem mv_at (k : Nat) (rd rs : Reg) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = .MV rd rs) :
    ∀ a i, CodeReq.singleton A (.MV rd rs) a = some i → sha256Cr a = some i :=
  mem_at k (.MV rd rs) A hA hk hins

private theorem la_state_hi :
    Codegen.laHi GuestAddrs.sha256_w_state (GuestAddrs.zkvm_sha256 + 28) =
      Rv64.laHi (B + 28) ShaState := by decide

private theorem la_state_lo :
    Codegen.laLo GuestAddrs.sha256_w_state (GuestAddrs.zkvm_sha256 + 28) =
      Rv64.laLo (B + 28) ShaState := by decide

private theorem la_input_hi :
    Codegen.laHi GuestAddrs.sha256_w_input (GuestAddrs.zkvm_sha256 + 52) =
      Rv64.laHi (B + 52) ShaInput := by decide

private theorem la_input_lo :
    Codegen.laLo GuestAddrs.sha256_w_input (GuestAddrs.zkvm_sha256 + 52) =
      Rv64.laLo (B + 52) ShaInput := by decide

private theorem la_iv_hi :
    Codegen.laHi GuestAddrs.sha256_w_iv (GuestAddrs.zkvm_sha256 + 60) =
      Rv64.laHi (B + 60) ShaIv := by decide

private theorem la_iv_lo :
    Codegen.laLo GuestAddrs.sha256_w_iv (GuestAddrs.zkvm_sha256 + 60) =
      Rv64.laLo (B + 60) ShaIv := by decide

private theorem la_state_range : laInRange (B + 28) ShaState := by decide
private theorem la_input_range : laInRange (B + 52) ShaInput := by decide
private theorem la_iv_range : laInRange (B + 60) ShaIv := by decide

theorem sha256SetupLaState_spec (v8 : Word) :
    cpsTripleWithin 2 (B + 28) (B + 36) sha256Cr
      (.x8 ↦ᵣ v8) (.x8 ↦ᵣ ShaState) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 28)
        (.AUIPC .x8 (Rv64.laHi (B + 28) ShaState)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 7
      (.AUIPC .x8 (Codegen.laHi GuestAddrs.sha256_w_state
        (GuestAddrs.zkvm_sha256 + 28))) (B + 28) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_state_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 28) + 4)
        (.ADDI .x8 .x8 (Rv64.laLo (B + 28) ShaState)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 8
      (.ADDI .x8 .x8 (Codegen.laLo GuestAddrs.sha256_w_state
        (GuestAddrs.zkvm_sha256 + 28))) (B + 32) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    have hpc : (B + 28 : Word) + 4 = B + 32 := by decide
    rw [hpc, ← la_state_lo] at hi
    exact hmem a i hi
  exact la_materialize_within .x8 v8 (B + 28) ShaState
    (by decide) la_state_range hau had

theorem sha256SetupLaInput_spec (v21 : Word) :
    cpsTripleWithin 2 (B + 52) (B + 60) sha256Cr
      (.x21 ↦ᵣ v21) (.x21 ↦ᵣ ShaInput) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 52)
        (.AUIPC .x21 (Rv64.laHi (B + 52) ShaInput)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 13
      (.AUIPC .x21 (Codegen.laHi GuestAddrs.sha256_w_input
        (GuestAddrs.zkvm_sha256 + 52))) (B + 52) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_input_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 52) + 4)
        (.ADDI .x21 .x21 (Rv64.laLo (B + 52) ShaInput)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 14
      (.ADDI .x21 .x21 (Codegen.laLo GuestAddrs.sha256_w_input
        (GuestAddrs.zkvm_sha256 + 52))) (B + 56) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    have hpc : (B + 52 : Word) + 4 = B + 56 := by decide
    rw [hpc, ← la_input_lo] at hi
    exact hmem a i hi
  exact la_materialize_within .x21 v21 (B + 52) ShaInput
    (by decide) la_input_range hau had

theorem sha256SetupLaIv_spec (v5 : Word) :
    cpsTripleWithin 2 (B + 60) (B + 68) sha256Cr
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ ShaIv) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 60)
        (.AUIPC .x5 (Rv64.laHi (B + 60) ShaIv)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 15
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.sha256_w_iv
        (GuestAddrs.zkvm_sha256 + 60))) (B + 60) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_iv_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 60) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo (B + 60) ShaIv)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 16
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.sha256_w_iv
        (GuestAddrs.zkvm_sha256 + 60))) (B + 64) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    have hpc : (B + 60 : Word) + 4 = B + 64 := by decide
    rw [hpc, ← la_iv_lo] at hi
    exact hmem a i hi
  exact la_materialize_within .x5 v5 (B + 60) ShaIv
    (by decide) la_iv_range hau had

/- Four ABI setup instructions: MV x9,a0; MV x18,a1; MV x19,a2;
   SLLI x20,a1,3. -/
theorem sha256SetupMoves_spec (inputBase lenW outputBase : Word)
    (v9 v18 v19 v20 : Word) :
    cpsTripleWithin 4 (B + 36) (B + 52) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x19 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ (lenW <<< 3))) := by
  have h0 := mv_spec_gen_within .x9 .x10 inputBase v9 (B + 36) (by decide)
  rw [show (B + 36 : Word) + 4 = B + 40 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (mv_at 9 .x9 .x10 (B + 36) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h0
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20)) (by pcf) l0
  have c0 : cpsTripleWithin 1 (B + 36) (B + 40) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := mv_spec_gen_within .x18 .x11 lenW v18 (B + 40) (by decide)
  rw [show (B + 40 : Word) + 4 = B + 44 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (mv_at 10 .x18 .x11 (B + 40) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h1
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x12 ↦ᵣ outputBase) **
      (.x9 ↦ᵣ inputBase) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20)) (by pcf) l1
  have c1 : cpsTripleWithin 1 (B + 40) (B + 44) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have h2 := mv_spec_gen_within .x19 .x12 outputBase v19 (B + 44) (by decide)
  rw [show (B + 44 : Word) + 4 = B + 48 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (mv_at 11 .x19 .x12 (B + 44) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h2
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) **
      (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x20 ↦ᵣ v20)) (by pcf) l2
  have c2 : cpsTripleWithin 1 (B + 44) (B + 48) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ v20)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  have h3 := slli_spec_gen_within .x20 .x11 v20 lenW (3 : BitVec 6)
    (B + 48) (by decide)
  rw [show (B + 48 : Word) + 4 = B + 52 from by decide] at h3
  have l3 := cpsTripleWithin_extend_code
    (mem_at 12 (.SLLI .x20 .x11 (3 : BitVec 6)) (B + 48) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h3
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x12 ↦ᵣ outputBase) **
      (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x19 ↦ᵣ outputBase)) (by pcf) l3
  have c3 : cpsTripleWithin 1 (B + 48) (B + 52) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x19 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) ** (.x19 ↦ᵣ outputBase) **
        (.x20 ↦ᵣ (lenW <<< 3))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h3F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 c3))

/-- One IV dword copy.  The four copies in the wrapper are instances of this
    same read-then-write boundary; keeping the chunk theorem separate avoids
    hiding the source/destination region obligations in the later composition.
-/
theorem sha256InitDword_spec (cr : CodeReq) (entry : Word)
    (ivBase stateBase : Word) (iv state : List (BitVec 8))
    (q : Nat) (v6 : Word)
    (hiv : iv.length = 32) (hstate : state.length = 32)
    (hq : q < 4)
    (hmemLd : ∀ a i, CodeReq.singleton entry
        (.LD .x6 .x5 (BitVec.ofNat 12 (8 * q))) a = some i → cr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (entry + 4)
        (.SD .x8 .x6 (BitVec.ofNat 12 (8 * q))) a = some i → cr a = some i) :
    cpsTripleWithin 2 entry (entry + 8) cr
      ((.x5 ↦ᵣ ivBase) ** (.x8 ↦ᵣ stateBase) ** (.x6 ↦ᵣ v6) **
        bytesRegion ivBase iv ** bytesRegion stateBase state)
      ((.x5 ↦ᵣ ivBase) ** (.x8 ↦ᵣ stateBase) **
        (.x6 ↦ᵣ packBytes ((iv.drop (8 * q)).take 8)) **
        bytesRegion ivBase iv **
        bytesRegion stateBase (setBytes state (8 * q)
          ((iv.drop (8 * q)).take 8))) := by
  have hq_iv : 8 * q < iv.length := by rw [hiv]; omega
  have hq_state : 8 * q + 8 ≤ state.length := by rw [hstate]; omega
  have himm : 8 * q < 2 ^ 11 := by omega
  have hld0 := cpsTripleWithin_extend_code hmemLd
    (bytesRegion_ld_within .x6 .x5 ivBase v6 entry iv q
      (by decide) hq_iv himm)
  have hldF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ stateBase) ** bytesRegion stateBase state)
    (by pcf) hld0
  have c0 : cpsTripleWithin 1 entry (entry + 4) cr
      ((.x5 ↦ᵣ ivBase) ** (.x8 ↦ᵣ stateBase) ** (.x6 ↦ᵣ v6) **
        bytesRegion ivBase iv ** bytesRegion stateBase state)
      ((.x5 ↦ᵣ ivBase) ** (.x8 ↦ᵣ stateBase) **
        (.x6 ↦ᵣ packBytes ((iv.drop (8 * q)).take 8)) **
        bytesRegion ivBase iv ** bytesRegion stateBase state) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq' => by xperm_hyp hq') hldF
  let vD : Word := packBytes ((iv.drop (8 * q)).take 8)
  have hsd0 := cpsTripleWithin_extend_code hmemSd
    (bytesRegion_sd_within .x8 .x6 stateBase vD (entry + 4) state q
      hq_state himm)
  have hsd : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      ((.x8 ↦ᵣ stateBase) ** (.x6 ↦ᵣ vD) ** bytesRegion stateBase state)
      ((.x8 ↦ᵣ stateBase) ** (.x6 ↦ᵣ vD) **
        bytesRegion stateBase (setBytes state (8 * q) (dwordBytes vD))) := by
    rw [show (entry + 4 : Word) + 4 = entry + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hsd0
    exact hsd0
  have hlen : ((iv.drop (8 * q)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hiv]
    omega
  have hdw : dwordBytes vD = (iv.drop (8 * q)).take 8 := by
    simp only [vD]
    exact dwordBytes_packBytes _ hlen
  have hsdF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ ivBase) ** bytesRegion ivBase iv) (by pcf) hsd
  have c1 : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      ((.x5 ↦ᵣ ivBase) ** (.x8 ↦ᵣ stateBase) **
        (.x6 ↦ᵣ packBytes ((iv.drop (8 * q)).take 8)) **
        bytesRegion ivBase iv ** bytesRegion stateBase state)
      ((.x5 ↦ᵣ ivBase) ** (.x8 ↦ᵣ stateBase) **
        (.x6 ↦ᵣ packBytes ((iv.drop (8 * q)).take 8)) **
        bytesRegion ivBase iv ** bytesRegion stateBase
          (setBytes state (8 * q) ((iv.drop (8 * q)).take 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [vD] at hp ⊢
      xperm_hyp hp) (fun _ hq' => by
      simp only [vD, hdw] at hq' ⊢
      xperm_hyp hq') hsdF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-! ## IV dword copy (B+68 → B+100) and Setup→Outer compose -/

private abbrev sha256IvCopyProg : List Instr :=
  dwordCopyProgFrom .x5 .x8 .x6 0 4

private abbrev sha256IvCopyPrefix : List Instr := sha256ProgL.take 17
private abbrev sha256IvCopySuffix : List Instr := sha256ProgL.drop 25

private theorem sha256IvCopy_split :
    sha256ProgL = sha256IvCopyPrefix ++ sha256IvCopyProg ++ sha256IvCopySuffix := by
  simp only [sha256ProgL, sha256IvCopyPrefix, sha256IvCopyProg, sha256IvCopySuffix,
    zkvmSha256_prog, zkvmSha256_prog_of, dwordCopyProgFrom]
  decide

private theorem sha256IvCopyPrefix_len : sha256IvCopyPrefix.length = 17 := by
  simp only [sha256IvCopyPrefix, sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256IvCopySuffix_len : sha256IvCopySuffix.length = 96 := by
  simp only [sha256IvCopySuffix, sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256IvCopy_mem :
    ∀ a i, CodeReq.ofProg (B + 68) sha256IvCopyProg a = some i →
      sha256Cr a = some i := by
  intro a i h
  have hleft := ofProg_mono_left (base := B + 68)
    (p1 := sha256IvCopyProg) (p2 := sha256IvCopySuffix) a i h
  have haddr : B + BitVec.ofNat 64 (4 * sha256IvCopyPrefix.length) = B + 68 := by
    rw [sha256IvCopyPrefix_len]
    decide
  have hright := ofProg_mono_right
    (base := B) (p1 := sha256IvCopyPrefix)
    (p2 := sha256IvCopyProg ++ sha256IvCopySuffix)
    (by simp only [List.length_append, sha256IvCopyPrefix_len,
        sha256IvCopySuffix_len, dwordCopyProgFrom_length]
        norm_num) a i (by
      rw [haddr]
      exact hleft)
  change CodeReq.ofProg B sha256ProgL a = some i
  rw [sha256IvCopy_split]
  exact hright

/-- Four IV dword copies into the state BSS. Fuel 8. Ends at outer LI (B+100).
    Post state bytes = `iv` via `copyDwords_covers`. -/
theorem sha256InitIv_spec (iv state : List (BitVec 8)) (v6 : Word)
    (hiv : iv.length = 32) (hstate : state.length = 32) :
    cpsTripleWithin 8 (B + 68) (B + 100) sha256Cr
      ((.x5 ↦ᵣ ShaIv) ** (.x8 ↦ᵣ ShaState) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaIv iv ** bytesRegion ShaState state)
      ((.x5 ↦ᵣ ShaIv) ** (.x8 ↦ᵣ ShaState) ** regOwn .x6 **
        bytesRegion ShaIv iv ** bytesRegion ShaState iv) := by
  have hcopy := selectedDwordCopy_spec .x5 .x8 .x6
    (by decide) ShaIv ShaState v6 iv state 0 4
    (by omega) (by omega) (by omega) (B + 68)
  have hcopy' := cpsTripleWithin_extend_code sha256IvCopy_mem hcopy
  have hpc : (B + 68 : Word) + BitVec.ofNat 64 (4 * (2 * 4)) = B + 100 := by
    decide
  rw [hpc] at hcopy'
  have hcover : copyDwords iv state 0 4 = iv := by
    exact copyDwords_covers iv state 4 hiv hstate
  rw [hcover] at hcopy'
  exact hcopy'

/-- Body entry → outer-loop header (B+28 → B+100). Fuel 18 = 2+4+2+2+8.
    Posts OuterInv-ready concrete regs/BSS: x8=ShaState, x21=ShaInput,
    x9=inputBase, x18=lenW, state BSS = IV bytes; x5 demoted to `regOwn`
    (LI at B+100 overwrites). Ambient `A` frames scratch/params/input/etc.

    **Adapter gap vs `sha256OuterLoop_spec` entry** (reshape at seq site):
    1. Flat atoms here vs packaged `sha256OuterInv … N N` / `sha256OuterAmb`
       (cursor = inputBase, absorbed = iv / `sha256AbsorbedState iv input 0`).
    2. Extra concrete ABI/setup regs (`x10/x11/x12/x19/x20`, IV region, `x5`
       already owned) must be framed/demoted; Outer only needs
       `x18`, `regOwn x5`, OuterInv, `x10↦v10`, scratch bytes.
    3. Bases are concrete `ShaState`/`ShaInput`; Outer quantifies them —
       instantiate at the seq site. -/
theorem sha256SetupToOuter_spec (inputBase lenW outputBase : Word)
    (v8 v9 v18 v19 v20 v21 v5 v6 : Word)
    (st0 iv : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st0.length = 32) (hiv : iv.length = 32) :
    cpsTripleWithin 18 (B + 28) (B + 100) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ ShaInput) **
        (regOwn .x5) ** (regOwn .x6) **
        bytesRegion ShaState iv ** bytesRegion ShaIv iv ** A) := by
  -- LA state
  have cLaS0 := sha256SetupLaState_spec v8
  have cLaSF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) cLaS0
  have cLaS : cpsTripleWithin 2 (B + 28) (B + 36) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) cLaSF
  -- Moves
  have cMv0 := sha256SetupMoves_spec inputBase lenW outputBase v9 v18 v19 v20
  have cMvF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ ShaState) ** (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) cMv0
  have cMv : cpsTripleWithin 4 (B + 36) (B + 52) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) cMvF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) cLaS cMv
  -- LA input (scratch BSS)
  have cLaI0 := sha256SetupLaInput_spec v21
  have cLaIF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) cLaI0
  have cLaI : cpsTripleWithin 2 (B + 52) (B + 60) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ ShaInput) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) cLaIF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 cLaI
  -- LA IV
  have cLaV0 := sha256SetupLaIv_spec v5
  have cLaVF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
      (.x21 ↦ᵣ ShaInput) ** (.x6 ↦ᵣ v6) **
      bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) cLaV0
  have cLaV : cpsTripleWithin 2 (B + 60) (B + 68) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ ShaInput) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ ShaInput) ** (.x5 ↦ᵣ ShaIv) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) cLaVF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 cLaV
  -- IV → state dword copy
  have cIv0 := sha256InitIv_spec iv st0 v6 hiv hst
  have cIvF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
      (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
      (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
      (.x21 ↦ᵣ ShaInput) ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) hA) cIv0
  have cIv : cpsTripleWithin 8 (B + 68) (B + 100) sha256Cr
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ ShaInput) ** (.x5 ↦ᵣ ShaIv) ** (.x6 ↦ᵣ v6) **
        bytesRegion ShaState st0 ** bytesRegion ShaIv iv ** A)
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ ShaInput) ** (.x5 ↦ᵣ ShaIv) ** (regOwn .x6) **
        bytesRegion ShaState iv ** bytesRegion ShaIv iv ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) cIvF
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 cIv
  -- Demote x5↦ShaIv → regOwn (OuterLoop entry shape)
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) cAll
  have hq' :
      ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
        (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
        (.x21 ↦ᵣ ShaInput) ** (.x5 ↦ᵣ ShaIv) ** (regOwn .x6) **
        bytesRegion ShaState iv ** bytesRegion ShaIv iv ** A) h := hq
  -- Rotate x5 to the front of the trailing own-block and demote.
  have hq2 :
      (((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
          (.x8 ↦ᵣ ShaState) ** (.x9 ↦ᵣ inputBase) ** (.x18 ↦ᵣ lenW) **
          (.x19 ↦ᵣ outputBase) ** (.x20 ↦ᵣ (lenW <<< 3)) **
          (.x21 ↦ᵣ ShaInput) ** (regOwn .x6) **
          bytesRegion ShaState iv ** bytesRegion ShaIv iv ** A) **
        (.x5 ↦ᵣ ShaIv)) h := by
    xperm_hyp hq'
  have hq3 := sepConj_mono_right (regIs_to_regOwn .x5 ShaIv) h hq2
  xperm_hyp hq3

/-- External-memory CSR seam used by SHA's wrapper.  The parameter block,
    state buffer and message block are three distinct regions (unlike the
    original window-local `csrs_sha256Compress_spec_within` contract).  The
    semantic guard is deliberately explicit: callers must prove both the
    accelerator validity bit and the exact state-buffer write target/payload.
-/
theorem sha256ExternalCsrs_spec_within
    (base : Word) (rf : RegFile) (paramsBase stateBase inputBase : Word)
    (params state input : List (BitVec 8)) (payload : List Word)
    (_hparams : params.length = 16) (hstate : state.length = 32)
    (_hinput : input.length = 64) (hpayload : payload.length = 4)
    (_hstate_fit : 8 * payload.length ≤ state.length)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((regFileIs rf) ** bytesRegion paramsBase params **
        bytesRegion stateBase state ** bytesRegion inputBase input) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS 0x805 .x10))
      ((regFileIs rf) ** bytesRegion paramsBase params **
        bytesRegion stateBase state ** bytesRegion inputBase input)
      ((regFileIs rf) ** bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion inputBase input) := by
  intro R hR s hcr hPR hpcs
  subst hpcs
  have hfetch : s.code s.pc = some (.CSRS 0x805 .x10) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  obtain ⟨hvalidCsrs, hwriteCsrs⟩ := hsem R s hPR
  simp only [sepConj_assoc'] at hPR
  have hMem :
      ((bytesRegion stateBase state) **
        ((regFileIs rf) ** bytesRegion paramsBase params **
          bytesRegion inputBase input ** R)).holdsFor s := by
    sep_perm hPR
  have hW := holdsFor_bytesRegion_writeWords payload state s 0 hMem
    (by simp) (by omega)
  have hstep : step s = some (execInstrBr s (.CSRS 0x805 .x10)) :=
    step_csrs hfetch hvalidCsrs
  have hwrite : s.execCsrs 0x805 .x10 =
      s.writeWords stateBase payload := by
    show s.writeWords (s.csrsWrite 0x805 .x10).1
      (s.csrsWrite 0x805 .x10).2 = _
    rw [hwriteCsrs]
  refine ⟨1, Nat.le_refl 1,
    ((s.execCsrs 0x805 .x10).setPC (s.pc + 4)), ?_, ?_, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep]
    rfl
  · rfl
  · have hpcf :
        ((bytesRegion paramsBase params **
          bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
          bytesRegion inputBase input) ** ((regFileIs rf) ** R)).pcFree := by
      have hmemFree :
          (bytesRegion paramsBase params **
            bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
            bytesRegion inputBase input).pcFree :=
        pcFree_sepConj (bytesRegion_pcFree _ _)
          (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
      exact pcFree_sepConj hmemFree (pcFree_sepConj (pcFree_regFileIs _) hR)
    have hW' :
        ((bytesRegion paramsBase params **
          bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
          bytesRegion inputBase input) ** ((regFileIs rf) ** R)).holdsFor
          (s.writeWords (stateBase + 0#64) payload) := by
      sep_perm hW
    have hzero : stateBase + 0#64 = stateBase := by simp
    rw [hzero] at hW'
    have hfin := holdsFor_pcFree_setPC (v := s.pc + 4) hpcf hW'
    rw [← hwrite] at hfin
    sep_perm hfin

end EvmAsm.Codegen.Proofs
