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

/-! ## Ommers compare: one clean triple and the clean-run fold -/

/-- One clean ommers-compare triple at byte `j`: `LBU x7, j(x6)` loads the
    header byte (equal to the pinned constant per `hmatch`), `LBU x28, j(x5)`
    loads constant byte `j`, and `BNE x7, x28` falls through.  Both memory
    regions are exposed so the loads can resolve. -/
theorem k67OmmersTripleClean (cs omC old7 old28 : Word) (base omConst : Word)
    (bytes : List (BitVec 8)) (csIdx j : Nat)
    (F : Assertion) (hF : F.pcFree)
    (haddr : cs + signExtend12 (BitVec.ofNat 12 j) =
      base + BitVec.ofNat 64 (csIdx + j))
    (hom : omC + signExtend12 (BitVec.ofNat 12 j) =
      omConst + BitVec.ofNat 64 j)
    (halign : base.toNat % 8 = 0) (hi : csIdx + j < bytes.length)
    (hover : base.toNat + (csIdx + j) < 2 ^ 64)
    (hvalid : isValidByteAccess (base + BitVec.ofNat 64 (csIdx + j)) = true)
    (homalign : omConst.toNat % 8 = 0) (hi2 : j < k67OmBytes.length)
    (hover2 : omConst.toNat + j < 2 ^ 64)
    (hvalid2 : isValidByteAccess (omConst + BitVec.ofNat 64 j) = true)
    (hmatch : bytes[csIdx + j]'hi = k67OmBytes[j]'hi2)
    (hj : j < 32) (off : BitVec 13)
    (hlookLBU1 : k67Prog.get ⟨53 + 3 * j, by rw [k67_length]; omega⟩ =
      Instr.LBU .x7 .x6 (BitVec.ofNat 12 j))
    (hlookLBU2 : k67Prog.get ⟨54 + 3 * j, by rw [k67_length]; omega⟩ =
      Instr.LBU .x28 .x5 (BitVec.ofNat 12 j))
    (hlookBNE : k67Prog.get ⟨55 + 3 * j, by rw [k67_length]; omega⟩ =
      Instr.BNE .x7 .x28 off) :
    cpsTripleWithin 3 (K + BitVec.ofNat 64 (212 + 12 * j))
      (K + BitVec.ofNat 64 (212 + 12 * j) + 12) fullCode
      (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x7 ↦ᵣ old7) ** (.x28 ↦ᵣ old28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        bytesRegion omConst k67OmBytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) **
        (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
        (.x28 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        bytesRegion omConst k67OmBytes) ** F) := by
  -- LBU x7, j(x6): the header byte, rewritten to the constant via `hmatch`.
  have hmem1 : (CodeReq.ofProg K k67Prog)
      (K + BitVec.ofNat 64 (212 + 12 * j)) =
      some (Instr.LBU .x7 .x6 (BitVec.ofNat 12 j)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (53 + 3 * j)
      (K + BitVec.ofNat 64 (212 + 12 * j)) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by unfold K; bv_omega)).trans
      (congrArg some hlookLBU1)
  have hlbu1 := k67LbuRegion .x7 .x6 cs old7 (BitVec.ofNat 12 j)
    (K + BitVec.ofNat 64 (212 + 12 * j)) base bytes (csIdx + j)
    (by decide) haddr halign hi hover hvalid
  rw [hmatch] at hlbu1
  have hF1 : ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion omConst k67OmBytes ** F).pcFree :=
    pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF)))
  have hlbu1F :
      cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * j))
        (K + BitVec.ofNat 64 (212 + 12 * j) + 4)
        (CodeReq.singleton (K + BitVec.ofNat 64 (212 + 12 * j))
          (Instr.LBU .x7 .x6 (BitVec.ofNat 12 j)))
        (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** bytesRegion base bytes) **
          ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion omConst k67OmBytes ** F))
        (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          bytesRegion base bytes) **
          ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion omConst k67OmBytes ** F)) :=
    cpsTripleWithin_frameR _ hF1 hlbu1
  have hlbu1C :
      cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * j))
        (K + BitVec.ofNat 64 (212 + 12 * j) + 4) fullCode
        (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** bytesRegion base bytes) **
          ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion omConst k67OmBytes ** F))
        (((.x6 ↦ᵣ cs) **
          (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          bytesRegion base bytes) **
          ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion omConst k67OmBytes ** F)) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) hlbu1F)
  -- LBU x28, j(x5): the constant byte.
  have hmem2 : (CodeReq.ofProg K k67Prog)
      (K + BitVec.ofNat 64 (212 + 12 * j) + 4) =
      some (Instr.LBU .x28 .x5 (BitVec.ofNat 12 j)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (54 + 3 * j)
      (K + BitVec.ofNat 64 (212 + 12 * j) + 4) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by unfold K; bv_omega)).trans
      (congrArg some hlookLBU2)
  have hlbu2 := k67LbuRegion .x28 .x5 omC old28 (BitVec.ofNat 12 j)
    (K + BitVec.ofNat 64 (212 + 12 * j) + 4) omConst k67OmBytes j
    (by decide) hom homalign hi2 hover2 hvalid2
  rw [show K + BitVec.ofNat 64 (212 + 12 * j) + 4 + 4 =
    K + BitVec.ofNat 64 (212 + 12 * j) + 8 from by bv_omega] at hlbu2
  have hF2 : ((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F).pcFree :=
    pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF)))
  have hlbu2F :
      cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * j) + 4)
        (K + BitVec.ofNat 64 (212 + 12 * j) + 8)
        (CodeReq.singleton (K + BitVec.ofNat 64 (212 + 12 * j) + 4)
          (Instr.LBU .x28 .x5 (BitVec.ofNat 12 j)))
        (((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) **
          bytesRegion omConst k67OmBytes) **
          ((.x6 ↦ᵣ cs) **
            (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F))
        (((.x5 ↦ᵣ omC) **
          (.x28 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          bytesRegion omConst k67OmBytes) **
          ((.x6 ↦ᵣ cs) **
            (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F)) :=
    cpsTripleWithin_frameR _ hF2 hlbu2
  have hlbu2C :
      cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * j) + 4)
        (K + BitVec.ofNat 64 (212 + 12 * j) + 8) fullCode
        (((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) **
          bytesRegion omConst k67OmBytes) **
          ((.x6 ↦ᵣ cs) **
            (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F))
        (((.x5 ↦ᵣ omC) **
          (.x28 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          bytesRegion omConst k67OmBytes) **
          ((.x6 ↦ᵣ cs) **
            (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F)) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h))
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) hlbu2F)
  -- BNE x7, x28: both pins hold the same constant byte, so not taken.
  have hbne := bne_spec_gen_within .x7 .x28 off
    ((k67OmBytes[j]'hi2).zeroExtend 64) ((k67OmBytes[j]'hi2).zeroExtend 64)
    (K + BitVec.ofNat 64 (212 + 12 * j) + 8)
  rw [show (K + BitVec.ofNat 64 (212 + 12 * j) + 8) + 4 =
    K + BitVec.ofNat 64 (212 + 12 * j) + 12 from by bv_omega] at hbne
  have hmem3 : (CodeReq.ofProg K k67Prog)
      (K + BitVec.ofNat 64 (212 + 12 * j) + 8) =
      some (Instr.BNE .x7 .x28 off) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (55 + 3 * j)
      (K + BitVec.ofNat 64 (212 + 12 * j) + 8) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by unfold K; bv_omega)).trans
      (congrArg some hlookBNE)
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem3 a' i h)) hbne
  have hntake := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)
  have hF3 : ((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion base bytes ** bytesRegion omConst k67OmBytes ** F).pcFree :=
    pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))
  have hntakeF :
      cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * j) + 8)
        (K + BitVec.ofNat 64 (212 + 12 * j) + 12) fullCode
        (((.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          (.x28 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64))) **
          ((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion base bytes ** bytesRegion omConst k67OmBytes ** F))
        (((.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          (.x28 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64))) **
          ((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion base bytes ** bytesRegion omConst k67OmBytes ** F)) :=
    cpsTripleWithin_frameR _ hF3 hntake
  have hntakeC :
      cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * j) + 8)
        (K + BitVec.ofNat 64 (212 + 12 * j) + 12) fullCode
        (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) **
          (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          (.x28 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
          bytesRegion omConst k67OmBytes) ** F)
        (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) **
          (.x7 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          (.x28 ↦ᵣ ((k67OmBytes[j]'hi2).zeroExtend 64)) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
          bytesRegion omConst k67OmBytes) ** F) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hntakeF
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbu1C hlbu2C
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) (cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) h12 hntakeC)

/-- A clean run of `k` consecutive ommers-compare triples, starting at triple
    `j`: every compared byte pair was equal, so after the run `x7`/`x28` hold
    the last constant byte `k67OmBytes[j + k - 1]`. -/
theorem k67OmmersCleanRun (cs omC : Word) (base omConst : Word)
    (bytes : List (BitVec 8)) (csIdx j k : Nat)
    (old7 old28 : Word)
    (F : Assertion) (hF : F.pcFree) (offs : Nat → BitVec 13)
    (hk0 : 0 < k) (hjk : j + k ≤ 32)
    (haddr : ∀ (j' : Nat) (_hj' : j' < 32),
      cs + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (csIdx + j'))
    (hom : ∀ (j' : Nat) (_hj' : j' < 32),
      omC + signExtend12 (BitVec.ofNat 12 j') =
        omConst + BitVec.ofNat 64 j')
    (halign : base.toNat % 8 = 0) (hib : csIdx + 32 ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (homalign : omConst.toNat % 8 = 0)
    (hover2 : omConst.toNat + 32 < 2 ^ 64)
    (hvalid2 : ∀ (j' : Nat) (_hj' : j' < 32),
      isValidByteAccess (omConst + BitVec.ofNat 64 j') = true)
    (hmatch : ∀ (j' : Nat) (hj' : j' < 32),
      bytes[csIdx + j']'(by omega) =
        k67OmBytes[j']'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega))
    (hlookLBU1 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨53 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookLBU2 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨54 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x28 .x5 (BitVec.ofNat 12 j'))
    (hlookBNE : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨55 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x28 (offs j')) :
    cpsTripleWithin (3 * k) (K + BitVec.ofNat 64 (212 + 12 * j))
      (K + BitVec.ofNat 64 (212 + 12 * (j + k))) fullCode
      (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x7 ↦ᵣ old7) ** (.x28 ↦ᵣ old28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        bytesRegion omConst k67OmBytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) **
        (.x7 ↦ᵣ ((k67OmBytes[j + k - 1]'(by
          rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend
            64)) **
        (.x28 ↦ᵣ ((k67OmBytes[j + k - 1]'(by
          rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend
            64)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        bytesRegion omConst k67OmBytes) ** F) := by
  induction k with
  | zero => exact absurd hk0 (Nat.lt_irrefl 0)
  | succ k ih =>
    obtain rfl | hk0' : k = 0 ∨ 0 < k := by omega
    · rw [show 3 * (0 + 1) = 3 from by omega,
        show K + BitVec.ofNat 64 (212 + 12 * (j + (0 + 1))) =
          K + BitVec.ofNat 64 (212 + 12 * j) + 12 from by bv_omega]
      exact k67OmmersTripleClean cs omC old7 old28 base omConst bytes csIdx j
        F hF (haddr j (by omega)) (hom j (by omega)) halign (by omega)
        (by omega) (hvalid _ (by omega)) homalign
        (by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega) (by omega)
        (hvalid2 j (by omega)) (hmatch j (by omega)) (by omega) (offs j)
        (hlookLBU1 j (by omega)) (hlookLBU2 j (by omega))
        (hlookBNE j (by omega))
    · have hih := ih hk0' (by omega) hmatch hlookLBU1 hlookLBU2 hlookBNE
      have htri := k67OmmersTripleClean cs omC
        ((k67OmBytes[j + k - 1]'(by
          rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend
            64)
        ((k67OmBytes[j + k - 1]'(by
          rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend
            64)
        base omConst bytes csIdx (j + k) F hF
        (haddr (j + k) (by omega)) (hom (j + k) (by omega)) halign (by omega)
        (by omega) (hvalid _ (by omega)) homalign
        (by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega) (by omega)
        (hvalid2 (j + k) (by omega)) (hmatch (j + k) (by omega)) (by omega)
        (offs (j + k))
        (hlookLBU1 (j + k) (by omega)) (hlookLBU2 (j + k) (by omega))
        (hlookBNE (j + k) (by omega))
      rw [show 3 * (k + 1) = 3 * k + 3 from by omega,
        show K + BitVec.ofNat 64 (212 + 12 * (j + (k + 1))) =
          K + BitVec.ofNat 64 (212 + 12 * (j + k)) + 12 from by bv_omega]
      exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hih htri

