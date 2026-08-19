/-
  K67 `header_validate_post_merge` — post-loop compare chains.

  After the field-scan loop exits clean at `K + 116` (see
  `HeaderValidatePostMergeRound.lean`), the routine checks the nonce field
  (field 14, content length 8, all-zero bytes) and the ommers-hash field
  (field 1, content length 32, equal to the pinned `empty_ommers_hash`
  constant in `.data`).  This file proves those two compare chains:

  * `k67LbuRegion` — an offset-generic `LBU` spec reading `bs[i]` straight
    out of a `bytesRegion` (the `MemRegion.bytesRegion_lbu_within` pattern,
    but with a nonzero instruction offset).
  * `k67NoncePairClean` / `k67NonceCleanRun` — one clean (LBU+BNE-not-taken)
    nonce pair, and an induction folding `k ≤ 8` clean pairs.
  * `k67OmmersTripleClean` / `k67OmmersCleanRun` — the same for the
    three-instruction ommers blocks (two loads + branch).

  The phase theorems and the merged `cpsNBranchWithin` over the whole
  post-loop region live at the bottom of the file.
-/
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeRound

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## Offset-generic `LBU` from a `bytesRegion` -/

/-- `LBU rd, off(rs1)` where `rs1` holds `v_addr` and
    `v_addr + signExtend12 off` lands on byte `i` of a `bytesRegion`: the load
    reads `bs[i]`.  This is `MemRegion.bytesRegion_lbu_within` generalized to a
    nonzero instruction offset (the K67 compare chains index with `LBU x7, k(x6)`). -/
theorem k67LbuRegion (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12)
    (pc regionBase : Word) (bs : List (BitVec 8)) (i : Nat)
    (hrd : rd ≠ .x0)
    (haddr : v_addr + signExtend12 off = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 pc (pc + 4) (CodeReq.singleton pc (.LBU rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ v_addr) **
        (rd ↦ᵣ ((bs[i]'hi).zeroExtend 64)) ** bytesRegion regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegion_dword_at regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hda
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (v_addr + signExtend12 off) = dwordAddr := by
    rw [haddr]
    exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' : isValidByteAccess (v_addr + signExtend12 off) = true := by
    rw [haddr]; exact hvalid
  have lbu := generic_lbu_spec_within rd rs1 v_addr vOld off pc dwordAddr
    wordVal hrd halign' hvalid'
  have hbyte : extractByte wordVal
      (byteOffset (v_addr + signExtend12 off)) = bs[i]'hi := by
    rw [haddr, byteOffset_add_ofNat_of_aligned halign hover, hwv,
      extractByte_packBytes _ _ (by omega)
        (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu; rw [heq]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

/-! ## Nonce compare: one clean pair and the clean-run fold -/

/-- One clean nonce-compare pair at byte `j`: `LBU x7, j(x6)` loads a zero
    byte (per `hzero`) and `BNE x7, x0` falls through.  The ambient state `F`
    (every other register and both memory regions) is framed through. -/
theorem k67NoncePairClean (cs old7 : Word) (base : Word)
    (bytes : List (BitVec 8)) (csIdx j : Nat) (F : Assertion) (hF : F.pcFree)
    (haddr : cs + signExtend12 (BitVec.ofNat 12 j) =
      base + BitVec.ofNat 64 (csIdx + j))
    (halign : base.toNat % 8 = 0) (hi : csIdx + j < bytes.length)
    (hover : base.toNat + (csIdx + j) < 2 ^ 64)
    (hvalid : isValidByteAccess (base + BitVec.ofNat 64 (csIdx + j)) = true)
    (hzero : bytes[csIdx + j]'hi = (0 : BitVec 8))
    (hj : j < 8) (off : BitVec 13)
    (hlookLBU : k67Prog.get ⟨32 + 2 * j, by rw [k67_length]; omega⟩ =
      Instr.LBU .x7 .x6 (BitVec.ofNat 12 j))
    (hlookBNE : k67Prog.get ⟨33 + 2 * j, by rw [k67_length]; omega⟩ =
      Instr.BNE .x7 .x0 off) :
    cpsTripleWithin 2 (K + BitVec.ofNat 64 (128 + 8 * j))
      (K + BitVec.ofNat 64 (128 + 8 * j) + 8) fullCode
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F) := by
  -- The load.
  have hlbu := k67LbuRegion .x7 .x6 cs old7 (BitVec.ofNat 12 j)
    (K + BitVec.ofNat 64 (128 + 8 * j)) base bytes (csIdx + j)
    (by decide) haddr halign hi hover hvalid
  rw [hzero] at hlbu
  rw [show ((0 : BitVec 8).zeroExtend 64) = (0 : Word) from by decide] at hlbu
  have hmem1 : (CodeReq.ofProg K k67Prog) (K + BitVec.ofNat 64 (128 + 8 * j)) =
      some (Instr.LBU .x7 .x6 (BitVec.ofNat 12 j)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (32 + 2 * j)
      (K + BitVec.ofNat 64 (128 + 8 * j)) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide)
      (by unfold K; congr 1; congr 1; omega)).trans (congrArg some hlookLBU)
  have hlbuC : cpsTripleWithin 1 (K + BitVec.ofNat 64 (128 + 8 * j))
      (K + BitVec.ofNat 64 (128 + 8 * j) + 4) fullCode
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** F)
          (pcFree_sepConj pcFree_regIs hF) hlbu))
  -- The branch (not taken: both sides are 0).
  have hbne := bne_spec_gen_within .x7 .x0 off
    (0 : Word) (0 : Word)
    (K + BitVec.ofNat 64 (128 + 8 * j) + 4)
  rw [show K + BitVec.ofNat 64 (128 + 8 * j) + 4 + 4 =
      K + BitVec.ofNat 64 (128 + 8 * j) + 8 from by bv_omega] at hbne
  have hmem2 : (CodeReq.ofProg K k67Prog)
      (K + BitVec.ofNat 64 (128 + 8 * j) + 4) =
      some (Instr.BNE .x7 .x0 off) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (33 + 2 * j)
      (K + BitVec.ofNat 64 (128 + 8 * j) + 4) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide)
      (by unfold K; bv_omega)).trans (congrArg some hlookBNE)
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h)) hbne
  have hntake := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hBP).2 (by decide))
  have hntakeF : cpsTripleWithin 1
      (K + BitVec.ofNat 64 (128 + 8 * j) + 4)
      (K + BitVec.ofNat 64 (128 + 8 * j) + 8) fullCode
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR ((.x6 ↦ᵣ cs) ** bytesRegion base bytes ** F)
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (bytesRegion_pcFree _ _) hF)) hntake)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlbuC hntakeF

/-- A clean run of `k` consecutive nonce byte-compare pairs, starting at pair
    `j` (so the last pair checked is `j + k - 1`): every loaded byte was `0`,
    and `x7` after the run holds the zero byte of the last pair. -/
theorem k67NonceCleanRun (cs old7 : Word) (base : Word)
    (bytes : List (BitVec 8)) (csIdx j k : Nat)
    (F : Assertion) (hF : F.pcFree) (offs : Nat → BitVec 13)
    (hk0 : 0 < k) (hjk : j + k ≤ 8)
    (haddr : ∀ j', j' < 8 → cs + signExtend12 (BitVec.ofNat 12 j') =
      base + BitVec.ofNat 64 (csIdx + j'))
    (halign : base.toNat % 8 = 0) (hib : csIdx + 8 ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (hzero : ∀ (j' : Nat) (hj' : j' < 8),
      bytes[csIdx + j']'(by omega) = (0 : BitVec 8))
    (hlookLBU : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨32 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookBNE : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨33 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x0 (offs j')) :
    cpsTripleWithin (2 * k) (K + BitVec.ofNat 64 (128 + 8 * j))
      (K + BitVec.ofNat 64 (128 + 8 * (j + k))) fullCode
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F) := by
  induction k with
  | zero => exact absurd hk0 (Nat.lt_irrefl 0)
  | succ k ih =>
    obtain rfl | hk0' : k = 0 ∨ 0 < k := by omega
    · rw [show K + BitVec.ofNat 64 (128 + 8 * (j + (0 + 1))) =
          K + BitVec.ofNat 64 (128 + 8 * j) + 8 from by bv_omega]
      exact k67NoncePairClean cs old7 base bytes csIdx j F hF
        (haddr j (by omega)) halign (by omega) (by omega)
        (hvalid _ (by omega)) (hzero j (by omega)) (by omega) (offs j)
        (hlookLBU j (by omega)) (hlookBNE j (by omega))
    · have hih := ih hk0' (by omega) hzero hlookLBU hlookBNE
      have hpair := k67NoncePairClean cs (0 : Word) base bytes csIdx (j + k) F
        hF (haddr (j + k) (by omega)) halign (by omega) (by omega)
        (hvalid _ (by omega)) (hzero (j + k) (by omega)) (by omega)
        (offs (j + k))
        (hlookLBU (j + k) (by omega)) (hlookBNE (j + k) (by omega))
      rw [show 2 * (k + 1) = 2 * k + 2 from by omega,
        show K + BitVec.ofNat 64 (128 + 8 * (j + (k + 1))) =
          K + BitVec.ofNat 64 (128 + 8 * (j + k)) + 8 from by bv_omega]
      exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hih hpair

