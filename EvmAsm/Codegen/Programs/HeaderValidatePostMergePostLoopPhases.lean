/-
  K67 `header_validate_post_merge` — post-loop phase theorems.

  Builds on `HeaderValidatePostMergePostLoop.lean`'s clean-run inductions to
  prove the six post-loop outcomes:

  * nonce length gate (`k67NonceLenFail`): `x12 ≠ 8` branches to the status-2
    stub at `K + 612`;
  * nonce byte failure (`k67NonceByteFail`): byte `k` of the nonce content is
    nonzero, so the `k`-th pair's `BNE x7, x0` fires to `K + 612`;
  * nonce pass (`k67NoncePass`): all 8 nonce bytes are zero, fall through to
    the ommers gate at `K + 192`;
  * ommers length gate (`k67OmmersLenFail`): `x9 ≠ 32` branches to the
    status-3 stub at `K + 620`;
  * ommers byte failure (`k67OmmersByteFail`): byte `k` differs from the
    pinned `empty_ommers_hash` constant, branch to `K + 620`;
  * ommers pass (`k67OmmersPass`): all 32 bytes match, fall through to the
    status-0 stub at `K + 596`.

  and the merged `k67PostLoop` `cpsNBranchWithin` with exits
  `[(K+596, Q0), (K+620, Q3), (K+612, Q2)]`.
-/
import EvmAsm.Codegen.Programs.HeaderValidatePostMergePostLoop
import EvmAsm.Evm64.Stack

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## The post-loop pre-state -/

/-- The register/memory state at `K + 116` (loop cleanly exited): the
    `k67LoopExit`-post shape.  `next14`/`len14` are the nonce field's
    content-end cursor and content length; `omEndW`/`omLenW` are the ommers
    field's captured content-end cursor and length. -/
def k67PLPre (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) : Assertion :=
  (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (15 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
  (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
  (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
  (.x21 ↦ᵣ v21) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
  frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
  bytesRegion base bytes ** bytesRegion omConst k67OmBytes

/-! ## Nonce phase -/

/-- Nonce length gate, failing: `x12 ≠ 8` branches to the status-2 stub at
    `K + 612` (2 instructions: `LI x5, 8`; `BNE x12, x5`, taken). -/
theorem k67NonceLenFail (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word)
    (hne : len14 ≠ (8 : Word)) :
    cpsTripleWithin 2 (K + 116) (K + 612) fullCode
      (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v6 v7 v28 v29 v30 v31 v21 svals)
      (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ len14) ** (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
        (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
        (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) := by
  have hli := li_spec_gen_within .x5 (15 : Word) (8 : Word) (K + 116)
    (by decide)
  have hmem1 : (CodeReq.ofProg K k67Prog) (K + 116) =
      some (Instr.LI .x5 (8 : Word)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 29 (K + 116)
      (by rw [k67_length]; decide) (by rw [k67_length]; decide)
      (by unfold K; bv_omega)).trans (congrArg some (by decide))
  let F1 : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next14) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) ** (.x8 ↦ᵣ omEndW) **
    (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) **
    (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 **
    regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion base bytes ** bytesRegion omConst k67OmBytes
  have hF1 : F1.pcFree := by
    dsimp only [F1]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  have hliF : cpsTripleWithin 1 (K + 116) (K + 116 + 4) fullCode
      ((.x5 ↦ᵣ (15 : Word)) ** F1) ((.x5 ↦ᵣ (8 : Word)) ** F1) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      (cpsTripleWithin_frameR F1 hF1 hli)
  rw [show K + 116 + 4 = K + 120 from by
    rw [BitVec.add_assoc,
      show (116 : Word) + (4 : Word) = (120 : Word) from by decide]] at hliF
  have hbne := bne_spec_gen_within .x12 .x5 (492 : BitVec 13)
    len14 (8 : Word) (K + 120)
  rw [show (K + 120 : Word) + 4 = K + 124 from by
      rw [BitVec.add_assoc,
        show (120 : Word) + (4 : Word) = (124 : Word) from by decide],
    show (K + 120 : Word) + signExtend13 (492 : BitVec 13) = K + 612 from by
      rw [show signExtend13 (492 : BitVec 13) = (492 : Word) from by decide,
        BitVec.add_assoc,
        show (120 : Word) + (492 : Word) = (612 : Word) from by decide]]
    at hbne
  have hmem2 : (CodeReq.ofProg K k67Prog) (K + 120) =
      some (Instr.BNE .x12 .x5 (492 : BitVec 13)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 30 (K + 120)
      (by rw [k67_length]; decide) (by rw [k67_length]; decide)
      (by unfold K; bv_omega)).trans (congrArg some (by decide))
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h)) hbne
  have htake := cpsBranchWithin_takenStripPure2 hbneC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hBP).2 hne)
  let F2 : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next14) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
    (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
    (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
    (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion base bytes ** bytesRegion omConst k67OmBytes
  have hF2 : F2.pcFree := by
    dsimp only [F2]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  have hbneF : cpsTripleWithin 1 (K + 120) (K + 612) fullCode
      (((.x12 ↦ᵣ len14) ** (.x5 ↦ᵣ (8 : Word))) ** F2)
      (((.x12 ↦ᵣ len14) ** (.x5 ↦ᵣ (8 : Word))) ** F2) :=
    cpsTripleWithin_frameR F2 hF2 htake
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold k67PLPre at hp; dsimp only [F1]; xperm_hyp hp)
    (fun _ hq => by dsimp only [F2] at hq; xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by dsimp only [F1, F2] at hp; xperm_hyp hp) hliF hbneF)

/-- One failing nonce-compare pair at byte `k`: `LBU x7, k(x6)` loads a
    nonzero byte (per `hbyte`) and `BNE x7, x0` is taken to the status-2 stub
    at `K + 612`.  The branch offset stays an opaque parameter (the byte index
    is symbolic); callers discharge `htaken`/`hlookBNE` by case-splitting the
    index. -/
theorem k67NoncePairFail (cs old7 : Word) (base : Word)
    (bytes : List (BitVec 8)) (csIdx k : Nat) (F : Assertion) (hF : F.pcFree)
    (haddr : cs + signExtend12 (BitVec.ofNat 12 k) =
      base + BitVec.ofNat 64 (csIdx + k))
    (halign : base.toNat % 8 = 0) (hi : csIdx + k < bytes.length)
    (hover : base.toNat + (csIdx + k) < 2 ^ 64)
    (hvalid : isValidByteAccess (base + BitVec.ofNat 64 (csIdx + k)) = true)
    (hbyte : bytes[csIdx + k]'hi ≠ (0 : BitVec 8))
    (hk : k < 8) (off : BitVec 13)
    (htaken : (K + BitVec.ofNat 64 (132 + 8 * k)) + signExtend13 off =
      K + 612)
    (hlookLBU : k67Prog.get ⟨32 + 2 * k, by rw [k67_length]; omega⟩ =
      Instr.LBU .x7 .x6 (BitVec.ofNat 12 k))
    (hlookBNE : k67Prog.get ⟨33 + 2 * k, by rw [k67_length]; omega⟩ =
      Instr.BNE .x7 .x0 off) :
    cpsTripleWithin 2 (K + BitVec.ofNat 64 (128 + 8 * k)) (K + 612) fullCode
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion base bytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((bytes[csIdx + k]'hi).zeroExtend 64)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes) ** F) := by
  have hmem1 : (CodeReq.ofProg K k67Prog) (K + BitVec.ofNat 64 (128 + 8 * k)) =
      some (Instr.LBU .x7 .x6 (BitVec.ofNat 12 k)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (32 + 2 * k)
      (K + BitVec.ofNat 64 (128 + 8 * k)) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by unfold K; bv_omega)).trans
      (congrArg some hlookLBU)
  have hlbu := k67LbuRegion .x7 .x6 cs old7 (BitVec.ofNat 12 k)
    (K + BitVec.ofNat 64 (128 + 8 * k)) base bytes (csIdx + k) (by decide)
    haddr halign hi hover hvalid
  have hN : ((.x0 ↦ᵣ (0 : Word)) ** F).pcFree :=
    pcFree_sepConj pcFree_regIs hF
  have hlbuF : cpsTripleWithin 1 (K + BitVec.ofNat 64 (128 + 8 * k))
      (K + BitVec.ofNat 64 (128 + 8 * k) + 4)
      (CodeReq.singleton (K + BitVec.ofNat 64 (128 + 8 * k))
        (.LBU .x7 .x6 (BitVec.ofNat 12 k)))
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** bytesRegion base bytes) **
        ((.x0 ↦ᵣ (0 : Word)) ** F))
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((bytes[csIdx + k]'hi).zeroExtend 64)) **
        bytesRegion base bytes) ** ((.x0 ↦ᵣ (0 : Word)) ** F)) :=
    cpsTripleWithin_frameR _ hN hlbu
  have hlbuC : cpsTripleWithin 1 (K + BitVec.ofNat 64 (128 + 8 * k))
      (K + BitVec.ofNat 64 (128 + 8 * k) + 4) fullCode
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** bytesRegion base bytes) **
        ((.x0 ↦ᵣ (0 : Word)) ** F))
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((bytes[csIdx + k]'hi).zeroExtend 64)) **
        bytesRegion base bytes) ** ((.x0 ↦ᵣ (0 : Word)) ** F)) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      hlbuF
  rw [show K + BitVec.ofNat 64 (128 + 8 * k) + 4 =
      K + BitVec.ofNat 64 (132 + 8 * k) from by bv_omega] at hlbuC
  have hbne := bne_spec_gen_within .x7 .x0 off
    ((bytes[csIdx + k]'hi).zeroExtend 64) (0 : Word)
    (K + BitVec.ofNat 64 (132 + 8 * k))
  rw [show (K + BitVec.ofNat 64 (132 + 8 * k) : Word) + 4 =
      K + BitVec.ofNat 64 (136 + 8 * k) from by bv_omega, htaken] at hbne
  have hmem2 : (CodeReq.ofProg K k67Prog)
      (K + BitVec.ofNat 64 (132 + 8 * k)) = some (Instr.BNE .x7 .x0 off) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (33 + 2 * k)
      (K + BitVec.ofNat 64 (132 + 8 * k)) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by unfold K; bv_omega)).trans
      (congrArg some hlookBNE)
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h)) hbne
  have htake := cpsBranchWithin_takenStripPure2 hbneC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    have hz := ((sepConj_pure_right _).1 hBP).2
    have hz' : bytes[csIdx + k]'hi = (0 : BitVec 8) := by bv_omega
    exact absurd hz' hbyte)
  have hM : (((.x6 ↦ᵣ cs) ** bytesRegion base bytes) ** F).pcFree :=
    pcFree_sepConj (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) hF
  have hbneF : cpsTripleWithin 1 (K + BitVec.ofNat 64 (132 + 8 * k))
      (K + 612) fullCode
      (((.x7 ↦ᵣ ((bytes[csIdx + k]'hi).zeroExtend 64)) **
        (.x0 ↦ᵣ (0 : Word))) ** (((.x6 ↦ᵣ cs) ** bytesRegion base bytes) ** F))
      (((.x7 ↦ᵣ ((bytes[csIdx + k]'hi).zeroExtend 64)) **
        (.x0 ↦ᵣ (0 : Word))) ** (((.x6 ↦ᵣ cs) ** bytesRegion base bytes) ** F)) :=
    cpsTripleWithin_frameR _ hM htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      hlbuC hbneF)

/-- The nonce-compare preamble when the length gate passes (`len14 = 8`):
    `LI x5, 8`; `BNE x12, x5` not taken; `SUB x6, x10, x12` — three
    instructions from the post-loop entry `K + 116` to the first compare pair
    at `K + 128`, with `x6` left holding the nonce content start. -/
theorem k67NonceFront (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word)
    (hlen : len14 = (8 : Word)) :
    cpsTripleWithin 3 (K + 116) (K + 128) fullCode
      (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v6 v7 v28 v29 v30 v31 v21 svals)
      (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x6 ↦ᵣ (next14 - len14)) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next14) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) ** (.x8 ↦ᵣ omEndW) **
        (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 **
        regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) := by
  have hli := li_spec_gen_within .x5 (15 : Word) (8 : Word) (K + 116)
    (by decide)
  have hmem1 : (CodeReq.ofProg K k67Prog) (K + 116) =
      some (Instr.LI .x5 (8 : Word)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 29 (K + 116)
      (by rw [k67_length]; decide) (by rw [k67_length]; decide)
      (by unfold K; bv_omega)).trans (congrArg some (by decide))
  let F1 : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next14) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) ** (.x8 ↦ᵣ omEndW) **
    (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) **
    (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 **
    regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion base bytes ** bytesRegion omConst k67OmBytes
  have hF1 : F1.pcFree := by
    dsimp only [F1]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  have hliF : cpsTripleWithin 1 (K + 116) (K + 116 + 4) fullCode
      ((.x5 ↦ᵣ (15 : Word)) ** F1) ((.x5 ↦ᵣ (8 : Word)) ** F1) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      (cpsTripleWithin_frameR F1 hF1 hli)
  rw [show K + 116 + 4 = K + 120 from by
    rw [BitVec.add_assoc,
      show (116 : Word) + (4 : Word) = (120 : Word) from by decide]] at hliF
  have hbne := bne_spec_gen_within .x12 .x5 (492 : BitVec 13)
    len14 (8 : Word) (K + 120)
  rw [show (K + 120 : Word) + 4 = K + 124 from by
    rw [BitVec.add_assoc,
      show (120 : Word) + (4 : Word) = (124 : Word) from by decide]] at hbne
  have hmem2 : (CodeReq.ofProg K k67Prog) (K + 120) =
      some (Instr.BNE .x12 .x5 (492 : BitVec 13)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 30 (K + 120)
      (by rw [k67_length]; decide) (by rw [k67_length]; decide)
      (by unfold K; bv_omega)).trans (congrArg some (by decide))
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h)) hbne
  have hntk := cpsBranchWithin_ntakenStripPure2 hbneC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    exact absurd hlen ((sepConj_pure_right _).1 hBP).2)
  let F2 : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next14) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
    (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
    (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
    (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion base bytes ** bytesRegion omConst k67OmBytes
  have hF2 : F2.pcFree := by
    dsimp only [F2]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  have hbneF : cpsTripleWithin 1 (K + 120) (K + 124) fullCode
      (((.x12 ↦ᵣ len14) ** (.x5 ↦ᵣ (8 : Word))) ** F2)
      (((.x12 ↦ᵣ len14) ** (.x5 ↦ᵣ (8 : Word))) ** F2) :=
    cpsTripleWithin_frameR F2 hF2 hntk
  have hsub := sub_spec_gen_within .x6 .x10 .x12 next14 len14 v6 (K + 124)
    (by decide)
  rw [show K + 124 + 4 = K + 128 from by
    rw [BitVec.add_assoc,
      show (124 : Word) + (4 : Word) = (128 : Word) from by decide]] at hsub
  have hmem3 : (CodeReq.ofProg K k67Prog) (K + 124) =
      some (Instr.SUB .x6 .x10 .x12) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 31 (K + 124)
      (by rw [k67_length]; decide) (by rw [k67_length]; decide)
      (by unfold K; bv_omega)).trans (congrArg some (by decide))
  have hsubC := cpsTripleWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem3 a' i h)) hsub
  let F3 : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
    (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
    (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
    (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion base bytes ** bytesRegion omConst k67OmBytes
  have hF3 : F3.pcFree := by
    dsimp only [F3]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  have hsubF : cpsTripleWithin 1 (K + 124) (K + 128) fullCode
      (((.x10 ↦ᵣ next14) ** (.x12 ↦ᵣ len14) ** (.x6 ↦ᵣ v6)) ** F3)
      (((.x10 ↦ᵣ next14) ** (.x12 ↦ᵣ len14) **
        (.x6 ↦ᵣ (next14 - len14))) ** F3) :=
    cpsTripleWithin_frameR F3 hF3 hsubC
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold k67PLPre at hp; dsimp only [F1]; xperm_hyp hp)
    (fun _ hq => by dsimp only [F3] at hq; xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by dsimp only [F1, F2] at hp; xperm_hyp hp)
      hliF (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by dsimp only [F2, F3] at hp; xperm_hyp hp)
        hbneF hsubF))

/-- Nonce compare, failing at byte `k`: the length gate passes, bytes
    `csIdx + 0 … csIdx + k - 1` are zero (`hpre`), and byte `csIdx + k` is
    nonzero (`hbyte`), so the walk is `LI/BNE/SUB` (3), `k` clean pairs
    (`2 * k`), and the failing `LBU + BNE-taken` pair (2) into the status-2
    stub at `K + 612`. -/
theorem k67NonceByteFail (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) (k csIdx : Nat)
    (hlen : len14 = (8 : Word))
    (hcsE : next14 - len14 = base + BitVec.ofNat 64 csIdx)
    (hib : csIdx + 8 ≤ bytes.length)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (hk : k < 8)
    (hpre : ∀ (j' : Nat) (hj' : j' < k),
      bytes[csIdx + j']'(by omega) = (0 : BitVec 8))
    (hbyte : bytes[csIdx + k]'(by omega) ≠ (0 : BitVec 8))
    (offs : Nat → BitVec 13)
    (haddr8 : ∀ (j' : Nat) (_hj' : j' < 8),
      next14 - (8 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (csIdx + j'))
    (htaken : ∀ (j' : Nat) (_hj' : j' < 8),
      (K + BitVec.ofNat 64 (132 + 8 * j')) + signExtend13 (offs j') =
        K + 612)
    (hlookLBU : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨32 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookBNE : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨33 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x0 (offs j')) :
    cpsTripleWithin (3 + (2 * k + 2)) (K + 116) (K + 612) fullCode
      (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v6 v7 v28 v29 v30 v31 v21 svals)
      (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x6 ↦ᵣ (next14 - len14)) **
        (.x7 ↦ᵣ ((bytes[csIdx + k]'(by omega)).zeroExtend 64)) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
        (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) := by
  subst hlen
  have hfront := k67NonceFront sp0 base omConst endPtr bytes next14 8
    omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals rfl
  let F : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x10 ↦ᵣ next14) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (8 : Word)) ** (.x8 ↦ᵣ omEndW) **
    (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) **
    (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 **
    regOwn .x14 ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion omConst k67OmBytes
  have hF : F.pcFree := by
    dsimp only [F]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  by_cases hk0 : k = 0
  · subst hk0
    have hpair := k67NoncePairFail (next14 - (8 : Word)) v7 base bytes csIdx 0
      F hF (haddr8 0 (by omega)) halign (by omega) (by omega)
      (hvalid _ (by omega)) hbyte (by omega) (offs 0) (htaken 0 (by omega))
      (hlookLBU 0 (by omega)) (hlookBNE 0 (by omega))
    rw [show K + 128 = K + BitVec.ofNat 64 (128 + 8 * 0) from by
      rw [show BitVec.ofNat 64 (128 + 8 * 0) = (128 : Word) from by decide]]
      at hfront
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by dsimp only [F] at hq; xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by dsimp only [F]; xperm_hyp hp) hfront hpair)
  · have hk0' : 0 < k := by omega
    have hclean := k67NonceCleanRun (next14 - (8 : Word)) v7 base bytes
      csIdx 0 k F hF offs hk0' (by omega)
      (fun j' hj' => haddr8 j' (by omega)) halign hib hover hvalid
      (fun j' hj' => hpre j' (by omega))
      (fun j' hj' => hlookLBU j' (by omega))
      (fun j' hj' => hlookBNE j' (by omega))
    rw [show K + BitVec.ofNat 64 (128 + 8 * 0) = K + 128 from by
      rw [show BitVec.ofNat 64 (128 + 8 * 0) = (128 : Word) from by decide],
      Nat.zero_add k]
      at hclean
    have hpair := k67NoncePairFail (next14 - (8 : Word)) (0 : Word) base bytes
      csIdx k F hF (haddr8 k (by omega)) halign (by omega) (by omega)
      (hvalid _ (by omega)) hbyte hk (offs k) (htaken k (by omega))
      (hlookLBU k (by omega)) (hlookBNE k (by omega))
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by dsimp only [F] at hq; xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by dsimp only [F]; xperm_hyp hp) hfront
        (cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by dsimp only [F] at hp ⊢; xperm_hyp hp) hclean hpair))

/-- Nonce compare, all eight bytes zero: the preamble plus a full clean run
    lands at the ommers length gate `K + 192` (19 instructions). -/
theorem k67NoncePass (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) (csIdx : Nat)
    (hlen : len14 = (8 : Word))
    (hcsE : next14 - len14 = base + BitVec.ofNat 64 csIdx)
    (hib : csIdx + 8 ≤ bytes.length)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (hzero8 : ∀ (j' : Nat) (hj' : j' < 8),
      bytes[csIdx + j']'(by omega) = (0 : BitVec 8))
    (offs : Nat → BitVec 13)
    (haddr8 : ∀ (j' : Nat) (_hj' : j' < 8),
      next14 - (8 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (csIdx + j'))
    (hlookLBU : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨32 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookBNE : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨33 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x0 (offs j')) :
    cpsTripleWithin (3 + 2 * 8) (K + 116) (K + 192) fullCode
      (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v6 v7 v28 v29 v30 v31 v21 svals)
      (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x6 ↦ᵣ (next14 - len14)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
        (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) := by
  subst hlen
  have hfront := k67NonceFront sp0 base omConst endPtr bytes next14 8
    omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals rfl
  let F : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x10 ↦ᵣ next14) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (8 : Word)) ** (.x8 ↦ᵣ omEndW) **
    (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) **
    (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 **
    regOwn .x14 ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion omConst k67OmBytes
  have hF : F.pcFree := by
    dsimp only [F]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  have hclean := k67NonceCleanRun (next14 - (8 : Word)) v7 base bytes
    csIdx 0 8 F hF offs (by omega) (by omega) haddr8 halign hib hover hvalid
    hzero8 hlookLBU hlookBNE
  rw [show K + BitVec.ofNat 64 (128 + 8 * 0) = K + 128 from by
    rw [show BitVec.ofNat 64 (128 + 8 * 0) = (128 : Word) from by decide],
    show K + BitVec.ofNat 64 (128 + 8 * (0 + 8)) = K + 192 from by
      rw [show BitVec.ofNat 64 (128 + 8 * (0 + 8)) = (192 : Word) from by
        decide]] at hclean
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by dsimp only [F] at hq; xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by dsimp only [F]; xperm_hyp hp) hfront hclean)

/-! ## Ommers phase -/

/-- The ommers-phase pre-state at `K + 192` (nonce phase passed): the
    `k67PLPre` shape with `x5` free (the nonce pass leaves `x5 = 8`). -/
def k67PLPreO (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v5o v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) : Assertion :=
  (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5o) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
  (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
  (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
  (.x21 ↦ᵣ v21) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
  frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
  bytesRegion base bytes ** bytesRegion omConst k67OmBytes

/-- Ommers length gate, failing: `x9 ≠ 32` branches to the status-3 stub at
    `K + 620` (2 instructions: `LI x5, 32`; `BNE x9, x5`, taken). -/
theorem k67OmmersLenFail (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v5o v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) (hne : omLenW ≠ 32) :
    cpsTripleWithin 2 (K + 192) (K + 620) fullCode
      (k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v5o v6 v7 v28 v29 v30 v31 v21 svals)
      ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
        (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
        (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes) := by
  have hmem1 : (CodeReq.ofProg K k67Prog) (K + 192) =
      some (Instr.LI .x5 (32 : Word)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 48 (K + 192)
      (by rw [k67_length]; omega) (by rw [k67_length]; decide)
      (by rw [show BitVec.ofNat 64 (4 * 48) = (192 : Word) from by decide])).trans
      (congrArg some (by decide))
  have hli := li_spec_gen_within .x5 v5o (32 : Word) (K + 192) (by decide)
  have hliF : cpsTripleWithin 1 (K + 192) (K + 192 + 4) fullCode
      (((.x5 ↦ᵣ v5o) ** ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
        (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
        (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)))
      (((.x5 ↦ᵣ (32 : Word)) ** ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
        (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
        (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes))) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      (cpsTripleWithin_frameR _
        (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
          | exact bytesRegion_pcFree _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | apply pcFree_sepConj) hli)
  rw [show K + 192 + 4 = K + 196 from by
    rw [BitVec.add_assoc,
      show (192 : Word) + (4 : Word) = (196 : Word) from by decide]] at hliF
  have hbne := bne_spec_gen_within .x9 .x5
    (brOff (GuestAddrs.header_validate_post_merge + 620)
      (GuestAddrs.header_validate_post_merge + 196))
    omLenW (32 : Word) (K + 196)
  rw [show K + 196 + 4 = K + 200 from by
    rw [BitVec.add_assoc,
      show (196 : Word) + (4 : Word) = (200 : Word) from by decide],
    show (K + 196 : Word) + signExtend13
        (brOff (GuestAddrs.header_validate_post_merge + 620)
          (GuestAddrs.header_validate_post_merge + 196)) = K + 620 from by
      rw [show brOff (GuestAddrs.header_validate_post_merge + 620)
          (GuestAddrs.header_validate_post_merge + 196) =
          (424 : BitVec 13) from by decide,
        show signExtend13 (424 : BitVec 13) = (424 : Word) from by decide,
        BitVec.add_assoc,
        show (196 : Word) + (424 : Word) = (620 : Word) from by decide]] at hbne
  have hmem2 : (CodeReq.ofProg K k67Prog) (K + 196) =
      some (Instr.BNE .x9 .x5
        (brOff (GuestAddrs.header_validate_post_merge + 620)
          (GuestAddrs.header_validate_post_merge + 196))) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 49 (K + 196)
      (by rw [k67_length]; omega) (by rw [k67_length]; decide)
      (by rw [show BitVec.ofNat 64 (4 * 49) = (196 : Word) from by decide])).trans
      (congrArg some (by decide))
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h)) hbne
  have htake := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)
  have hbneF : cpsTripleWithin 1 (K + 196) (K + 620) fullCode
      (((.x9 ↦ᵣ omLenW) ** (.x5 ↦ᵣ (32 : Word))) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x8 ↦ᵣ omEndW) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes))
      (((.x9 ↦ᵣ omLenW) ** (.x5 ↦ᵣ (32 : Word))) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x8 ↦ᵣ omEndW) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) :=
    cpsTripleWithin_frameR _
      (by repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_frameSlotsSaved _ _ _
        | apply pcFree_sepConj) htake
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold k67PLPreO at hp; xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      hliF hbneF)

/-- Ommers front, passing the length gate: `LI x5, 32`; `BNE x9, x5` not
    taken; `SUB x6, x8, x9` (ommers content start); `la x5, empty_ommers_hash`
    (5 instructions, `K+192 → K+212`). -/
theorem k67OmmersFront (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v5o v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) (hlen : omLenW = 32) :
    cpsTripleWithin 5 (K + 192) (K + 212) fullCode
      (k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v5o v6 v7 v28 v29 v30 v31 v21 svals)
      ((.x1 ↦ᵣ (K + 68)) **
        (.x5 ↦ᵣ ((GuestAddrs.empty_ommers_hash : Word))) **
        (.x6 ↦ᵣ (omEndW - omLenW)) ** (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
        (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
        (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes) := by
  subst hlen
  have hmem1 : (CodeReq.ofProg K k67Prog) (K + 192) =
      some (Instr.LI .x5 (32 : Word)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 48 (K + 192)
      (by rw [k67_length]; omega) (by rw [k67_length]; decide)
      (by rw [show BitVec.ofNat 64 (4 * 48) = (192 : Word) from by decide])).trans
      (congrArg some (by decide))
  have hli := li_spec_gen_within .x5 v5o (32 : Word) (K + 192) (by decide)
  have hliF : cpsTripleWithin 1 (K + 192) (K + 192 + 4) fullCode
      (((.x5 ↦ᵣ v5o) ** ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) **
        (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
        (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)))
      (((.x5 ↦ᵣ (32 : Word)) ** ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) **
        (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
        (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes))) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      (cpsTripleWithin_frameR _
        (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
          | exact bytesRegion_pcFree _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | apply pcFree_sepConj) hli)
  rw [show K + 192 + 4 = K + 196 from by
    rw [BitVec.add_assoc,
      show (192 : Word) + (4 : Word) = (196 : Word) from by decide]] at hliF
  have hbne := bne_spec_gen_within .x9 .x5
    (brOff (GuestAddrs.header_validate_post_merge + 620)
      (GuestAddrs.header_validate_post_merge + 196))
    (32 : Word) (32 : Word) (K + 196)
  rw [show K + 196 + 4 = K + 200 from by
    rw [BitVec.add_assoc,
      show (196 : Word) + (4 : Word) = (200 : Word) from by decide]] at hbne
  have hmem2 : (CodeReq.ofProg K k67Prog) (K + 196) =
      some (Instr.BNE .x9 .x5
        (brOff (GuestAddrs.header_validate_post_merge + 620)
          (GuestAddrs.header_validate_post_merge + 196))) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 49 (K + 196)
      (by rw [k67_length]; omega) (by rw [k67_length]; decide)
      (by rw [show BitVec.ofNat 64 (4 * 49) = (196 : Word) from by decide])).trans
      (congrArg some (by decide))
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h)) hbne
  have hntake := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hBP).2 (by decide))
  have hbneF : cpsTripleWithin 1 (K + 196) (K + 200) fullCode
      (((.x9 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ (32 : Word))) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x8 ↦ᵣ omEndW) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes))
      (((.x9 ↦ᵣ (32 : Word)) ** (.x5 ↦ᵣ (32 : Word))) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x8 ↦ᵣ omEndW) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) :=
    cpsTripleWithin_frameR _
      (by repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | exact pcFree_frameSlotsSaved _ _ _
        | apply pcFree_sepConj) hntake
  have hmem3 : (CodeReq.ofProg K k67Prog) (K + 200) =
      some (Instr.SUB .x6 .x8 .x9) :=
    (CodeReq.ofProg_lookup_addr K k67Prog 50 (K + 200)
      (by rw [k67_length]; omega) (by rw [k67_length]; decide)
      (by rw [show BitVec.ofNat 64 (4 * 50) = (200 : Word) from by decide])).trans
      (congrArg some (by decide))
  have hsub := sub_spec_gen_within .x6 .x8 .x9 omEndW (32 : Word) v6 (K + 200)
    (by decide)
  have hsubF : cpsTripleWithin 1 (K + 200) (K + 204) fullCode
      (((.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ v6)) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes))
      (((.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) **
        (.x6 ↦ᵣ (omEndW - (32 : Word)))) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem3 a' i h))
      (cpsTripleWithin_frameR _
        (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
          | exact bytesRegion_pcFree _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | apply pcFree_sepConj) hsub)
  have hau := CodeReq.ofProg_mem_at K (K + 204) k67Prog 51
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.empty_ommers_hash
      (GuestAddrs.header_validate_post_merge + 204)))
    (by rw [show BitVec.ofNat 64 (4 * 51) = (204 : Word) from by decide])
    (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)
  have had := CodeReq.ofProg_mem_at K (K + 208) k67Prog 52
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.empty_ommers_hash
      (GuestAddrs.header_validate_post_merge + 204)))
    (by rw [show BitVec.ofNat 64 (4 * 52) = (208 : Word) from by decide])
    (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)
  have hla := EvmAsm.Rv64.la_materialize_within (cr := k67Code) .x5
    (32 : Word) (K + 204) ((GuestAddrs.empty_ommers_hash : Word))
    (by decide) (by decide) hau had
  have hlaF : cpsTripleWithin 2 (K + 204) (K + 204 + 8) fullCode
      (((.x5 ↦ᵣ (32 : Word))) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ (omEndW - (32 : Word))) **
          (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes))
      (((.x5 ↦ᵣ ((GuestAddrs.empty_ommers_hash : Word)))) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ (omEndW - (32 : Word))) **
          (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
          (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) **
          (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
          (.x21 ↦ᵣ v21) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
            svals **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) :=
    cpsTripleWithin_extend_code k67_mono
      (cpsTripleWithin_frameR _
        (by repeat' first
          | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
          | exact bytesRegion_pcFree _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | apply pcFree_sepConj) hla)
  rw [show K + 204 + 8 = K + 212 from by
    rw [BitVec.add_assoc,
      show (204 : Word) + (8 : Word) = (212 : Word) from by decide]] at hlaF
  exact cpsTripleWithin_weaken
    (fun _ hp => by unfold k67PLPreO at hp; xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
          hliF hbneF)
        hsubF)
      hlaF)

/-- One failing ommers-compare triple at byte `k`: the header byte and the
    constant byte load into `x7`/`x28`, and `BNE x7, x28` is taken (the bytes
    differ, per `hbyte`), branching to the status-3 station `K + 620`. -/
theorem k67OmmersPairFail (cs omC old7 old28 : Word) (base omConst : Word)
    (bytes : List (BitVec 8)) (omIdx k : Nat) (F : Assertion) (hF : F.pcFree)
    (haddr : cs + signExtend12 (BitVec.ofNat 12 k) =
      base + BitVec.ofNat 64 (omIdx + k))
    (hom : omC + signExtend12 (BitVec.ofNat 12 k) =
      omConst + BitVec.ofNat 64 k)
    (halign : base.toNat % 8 = 0) (hi : omIdx + k < bytes.length)
    (hover : base.toNat + (omIdx + k) < 2 ^ 64)
    (hvalid : isValidByteAccess (base + BitVec.ofNat 64 (omIdx + k)) = true)
    (homalign : omConst.toNat % 8 = 0) (hi2 : k < k67OmBytes.length)
    (hover2 : omConst.toNat + k < 2 ^ 64)
    (hvalid2 : isValidByteAccess (omConst + BitVec.ofNat 64 k) = true)
    (hbyte : bytes[omIdx + k]'hi ≠ k67OmBytes[k]'hi2)
    (hk : k < 32) (off : BitVec 13)
    (htaken : (K + BitVec.ofNat 64 (212 + 12 * k) + 8) + signExtend13 off =
      K + 620)
    (hlookLBU1 : k67Prog.get ⟨53 + 3 * k, by rw [k67_length]; omega⟩ =
      Instr.LBU .x7 .x6 (BitVec.ofNat 12 k))
    (hlookLBU2 : k67Prog.get ⟨54 + 3 * k, by rw [k67_length]; omega⟩ =
      Instr.LBU .x28 .x5 (BitVec.ofNat 12 k))
    (hlookBNE : k67Prog.get ⟨55 + 3 * k, by rw [k67_length]; omega⟩ =
      Instr.BNE .x7 .x28 off) :
    cpsTripleWithin 3 (K + BitVec.ofNat 64 (212 + 12 * k)) (K + 620) fullCode
      (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x7 ↦ᵣ old7) ** (.x28 ↦ᵣ old28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        bytesRegion omConst k67OmBytes) ** F)
      (((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) **
        (.x7 ↦ᵣ ((bytes[omIdx + k]'hi).zeroExtend 64)) **
        (.x28 ↦ᵣ ((k67OmBytes[k]'hi2).zeroExtend 64)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        bytesRegion omConst k67OmBytes) ** F) := by
  have hmem1 : (CodeReq.ofProg K k67Prog) (K + BitVec.ofNat 64 (212 + 12 * k)) =
      some (Instr.LBU .x7 .x6 (BitVec.ofNat 12 k)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (53 + 3 * k)
      (K + BitVec.ofNat 64 (212 + 12 * k)) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by
        rw [show BitVec.ofNat 64 (4 * (53 + 3 * k)) =
          BitVec.ofNat 64 (212 + 12 * k) from by congr 1; omega]))
      |>.trans (congrArg some hlookLBU1)
  have hlbu1 := k67LbuRegion .x7 .x6 cs old7 (BitVec.ofNat 12 k)
    (K + BitVec.ofNat 64 (212 + 12 * k)) base bytes (omIdx + k)
    (by decide) haddr halign hi hover hvalid
  have hN : ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion omConst k67OmBytes ** F).pcFree :=
    pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF)))
  have hlbu1C : cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * k))
      (K + BitVec.ofNat 64 (212 + 12 * k) + 4) fullCode
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ old7) ** bytesRegion base bytes) **
        ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion omConst k67OmBytes ** F))
      (((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((bytes[omIdx + k]'hi).zeroExtend 64)) **
        bytesRegion base bytes) **
        ((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion omConst k67OmBytes ** F)) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem1 a' i h))
      (cpsTripleWithin_frameR _ hN hlbu1)
  have hmem2 : (CodeReq.ofProg K k67Prog)
      (K + BitVec.ofNat 64 (212 + 12 * k) + 4) =
      some (Instr.LBU .x28 .x5 (BitVec.ofNat 12 k)) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (54 + 3 * k)
      (K + BitVec.ofNat 64 (212 + 12 * k) + 4) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by unfold K; bv_omega))
      |>.trans (congrArg some hlookLBU2)
  have hlbu2 := k67LbuRegion .x28 .x5 omC old28 (BitVec.ofNat 12 k)
    (K + BitVec.ofNat 64 (212 + 12 * k) + 4) omConst k67OmBytes k
    (by decide) hom homalign hi2 hover2 hvalid2
  rw [show K + BitVec.ofNat 64 (212 + 12 * k) + 4 + 4 =
      K + BitVec.ofNat 64 (212 + 12 * k) + 8 from by bv_omega] at hlbu2
  have hM : ((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((bytes[omIdx + k]'hi).zeroExtend 64)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F).pcFree :=
    pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF)))
  have hlbu2C : cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * k) + 4)
      (K + BitVec.ofNat 64 (212 + 12 * k) + 8) fullCode
      (((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ old28) ** bytesRegion omConst k67OmBytes) **
        ((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((bytes[omIdx + k]'hi).zeroExtend 64)) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F))
      (((.x5 ↦ᵣ omC) ** (.x28 ↦ᵣ ((k67OmBytes[k]'hi2).zeroExtend 64)) **
        bytesRegion omConst k67OmBytes) **
        ((.x6 ↦ᵣ cs) ** (.x7 ↦ᵣ ((bytes[omIdx + k]'hi).zeroExtend 64)) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes ** F)) :=
    cpsTripleWithin_extend_code
      (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem2 a' i h))
      (cpsTripleWithin_frameR _ hM hlbu2)
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbu1C hlbu2C
  have hbne := bne_spec_gen_within .x7 .x28 off
    ((bytes[omIdx + k]'hi).zeroExtend 64) ((k67OmBytes[k]'hi2).zeroExtend 64)
    (K + BitVec.ofNat 64 (212 + 12 * k) + 8)
  rw [show K + BitVec.ofNat 64 (212 + 12 * k) + 8 + 4 =
      K + BitVec.ofNat 64 (212 + 12 * k) + 12 from by bv_omega, htaken]
    at hbne
  have hmem3 : (CodeReq.ofProg K k67Prog)
      (K + BitVec.ofNat 64 (212 + 12 * k) + 8) =
      some (Instr.BNE .x7 .x28 off) :=
    (CodeReq.ofProg_lookup_addr K k67Prog (55 + 3 * k)
      (K + BitVec.ofNat 64 (212 + 12 * k) + 8) (by rw [k67_length]; omega)
      (by rw [k67_length]; decide) (by unfold K; bv_omega))
      |>.trans (congrArg some hlookBNE)
  have hbneC := cpsBranchWithin_extend_code
    (fun a' i h => k67_mono a' i (CodeReq.singleton_mono hmem3 a' i h)) hbne
  have htake := cpsBranchWithin_takenStripPure2 hbneC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    have hz := ((sepConj_pure_right _).1 hBP).2
    have hz' : bytes[omIdx + k]'hi = k67OmBytes[k]'hi2 := by bv_omega
    exact absurd hz' hbyte)
  have hG : ((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion base bytes ** bytesRegion omConst k67OmBytes ** F).pcFree :=
    pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))
  have htakeF : cpsTripleWithin 1 (K + BitVec.ofNat 64 (212 + 12 * k) + 8)
      (K + 620) fullCode
      (((.x7 ↦ᵣ ((bytes[omIdx + k]'hi).zeroExtend 64)) **
          (.x28 ↦ᵣ ((k67OmBytes[k]'hi2).zeroExtend 64))) **
        ((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes ** F))
      (((.x7 ↦ᵣ ((bytes[omIdx + k]'hi).zeroExtend 64)) **
          (.x28 ↦ᵣ ((k67OmBytes[k]'hi2).zeroExtend 64))) **
        ((.x6 ↦ᵣ cs) ** (.x5 ↦ᵣ omC) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion base bytes ** bytesRegion omConst k67OmBytes ** F)) :=
    cpsTripleWithin_frameR _ hG htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      h12 htakeF)

/-- Ommers compare, first mismatch at byte `k`: the preamble (length gate,
    content-start `SUB`, `la`), a clean run of `k` triples, and the failing
    triple land at the status-3 station `K + 620` (`5 + (3 * k + 3)`
    instructions). -/
theorem k67OmmersByteFail (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (omIdx k : Nat)
    (v5o v6 v7 v28 v29 v30 v31 v21 : Word) (svals : Reg → Word)
    (hlen : omLenW = (32 : Word))
    (homC : omConst = (GuestAddrs.empty_ommers_hash : Word))
    (_hcsE : omEndW - (32 : Word) = base + BitVec.ofNat 64 omIdx)
    (hib : omIdx + 32 ≤ bytes.length)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (hvalid2 : ∀ (j' : Nat) (_hj' : j' < 32),
      isValidByteAccess (omConst + BitVec.ofNat 64 j') = true)
    (hk : k < 32)
    (hpre : ∀ (j' : Nat) (hj' : j' < k),
      bytes[omIdx + j']'(by omega) =
        k67OmBytes[j']'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega))
    (hbyte : bytes[omIdx + k]'(by omega) ≠
      k67OmBytes[k]'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega))
    (offs : Nat → BitVec 13)
    (haddr32 : ∀ (j' : Nat) (_hj' : j' < 32),
      omEndW - (32 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (omIdx + j'))
    (htaken : ∀ (j' : Nat) (_hj' : j' < 32),
      (K + BitVec.ofNat 64 (212 + 12 * j') + 8) + signExtend13 (offs j') =
        K + 620)
    (hlookLBU1 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨53 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookLBU2 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨54 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x28 .x5 (BitVec.ofNat 12 j'))
    (hlookBNE : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨55 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x28 (offs j')) :
    cpsTripleWithin (5 + (3 * k + 3)) (K + 192) (K + 620) fullCode
      (k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v5o v6 v7 v28 v29 v30 v31 v21 svals)
      (((.x1 ↦ᵣ (K + 68)) **
        (.x5 ↦ᵣ ((GuestAddrs.empty_ommers_hash : Word))) **
        (.x6 ↦ᵣ (omEndW - omLenW)) **
        (.x7 ↦ᵣ ((bytes[omIdx + k]'(by omega)).zeroExtend 64)) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
        (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ ((k67OmBytes[k]'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend 64)) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) := by
  subst hlen; subst homC
  have hfront := k67OmmersFront sp0 base
    (GuestAddrs.empty_ommers_hash : Word) endPtr bytes next14 len14 omEndW 32
    v5o v6 v7 v28 v29 v30 v31 v21 svals rfl
  let F : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ len14) ** (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) **
    (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
    (.x21 ↦ᵣ v21) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    regOwn .x13 ** regOwn .x14 **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
  have hF : F.pcFree := by
    dsimp only [F]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  by_cases hk0 : k = 0
  · subst hk0
    have hpair := k67OmmersPairFail (omEndW - (32 : Word))
      (GuestAddrs.empty_ommers_hash : Word) v7 v28 base
      (GuestAddrs.empty_ommers_hash : Word) bytes omIdx 0 F hF
      (haddr32 0 (by omega))
      (by rw [EvmAsm.Evm64.signExtend12_ofNat_small (by omega)])
      halign (by omega) (by omega) (hvalid _ (by omega))
      (by decide) (by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)
      (by decide) (hvalid2 0 (by omega)) hbyte (by omega) (offs 0)
      (htaken 0 (by omega)) (hlookLBU1 0 (by omega)) (hlookLBU2 0 (by omega))
      (hlookBNE 0 (by omega))
    rw [show K + 212 = K + BitVec.ofNat 64 (212 + 12 * 0) from by
      rw [show BitVec.ofNat 64 (212 + 12 * 0) = (212 : Word) from by decide]]
      at hfront
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by dsimp only [F] at hq; xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by dsimp only [F]; xperm_hyp hp) hfront hpair)
  · have hk0' : 0 < k := by omega
    have hclean := k67OmmersCleanRun (omEndW - (32 : Word))
      (GuestAddrs.empty_ommers_hash : Word) base
      (GuestAddrs.empty_ommers_hash : Word) bytes omIdx 0 k v7 v28 F hF offs
      hk0' (by omega)
      (fun j' hj' => haddr32 j' (by omega))
      (fun j' _hj' => by rw [EvmAsm.Evm64.signExtend12_ofNat_small (by omega)])
      halign hib hover hvalid (by decide) (by decide)
      (fun j' hj' => hvalid2 j' (by omega))
      (fun j' hj' => hpre j' (by omega))
      (fun j' hj' => hlookLBU1 j' (by omega))
      (fun j' hj' => hlookLBU2 j' (by omega))
      (fun j' hj' => hlookBNE j' (by omega))
    rw [show K + BitVec.ofNat 64 (212 + 12 * 0) = K + 212 from by
      rw [show BitVec.ofNat 64 (212 + 12 * 0) = (212 : Word) from by decide],
      show (212 + 12 * (0 + k) : Nat) = 212 + 12 * k from by omega]
      at hclean
    have hpair := k67OmmersPairFail (omEndW - (32 : Word))
      (GuestAddrs.empty_ommers_hash : Word)
      ((k67OmBytes[0 + k - 1]'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend 64)
      ((k67OmBytes[0 + k - 1]'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend 64)
      base (GuestAddrs.empty_ommers_hash : Word) bytes omIdx k F hF
      (haddr32 k (by omega))
      (by rw [EvmAsm.Evm64.signExtend12_ofNat_small (by omega)])
      halign (by omega) (by omega) (hvalid _ (by omega))
      (by decide) (by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)
      (by
        have h32 : (GuestAddrs.empty_ommers_hash : Word).toNat + 32 < 2 ^ 64 :=
          by decide
        omega) (hvalid2 k (by omega)) hbyte hk (offs k)
      (htaken k (by omega)) (hlookLBU1 k (by omega)) (hlookLBU2 k (by omega))
      (hlookBNE k (by omega))
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by dsimp only [F] at hq; xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by dsimp only [F]; xperm_hyp hp) hfront
        (cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by dsimp only [F] at hp ⊢; xperm_hyp hp) hclean hpair))

/-- Ommers compare, all 32 bytes matching the pinned `empty_ommers_hash`
    constant: the preamble plus a full clean run lands at the status-0 stub
    `K + 596` (101 instructions). -/
theorem k67OmmersPass (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (omIdx : Nat)
    (v5o v6 v7 v28 v29 v30 v31 v21 : Word) (svals : Reg → Word)
    (hlen : omLenW = (32 : Word))
    (homC : omConst = (GuestAddrs.empty_ommers_hash : Word))
    (_hcsE : omEndW - (32 : Word) = base + BitVec.ofNat 64 omIdx)
    (hib : omIdx + 32 ≤ bytes.length)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (hvalid2 : ∀ (j' : Nat) (_hj' : j' < 32),
      isValidByteAccess (omConst + BitVec.ofNat 64 j') = true)
    (hmatch32 : ∀ (j' : Nat) (hj' : j' < 32),
      bytes[omIdx + j']'(by omega) =
        k67OmBytes[j']'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega))
    (offs : Nat → BitVec 13)
    (haddr32 : ∀ (j' : Nat) (_hj' : j' < 32),
      omEndW - (32 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (omIdx + j'))
    (hlookLBU1 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨53 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookLBU2 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨54 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x28 .x5 (BitVec.ofNat 12 j'))
    (hlookBNE : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨55 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x28 (offs j')) :
    cpsTripleWithin (5 + 3 * 32) (K + 192) (K + 596) fullCode
      (k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v5o v6 v7 v28 v29 v30 v31 v21 svals)
      (((.x1 ↦ᵣ (K + 68)) **
        (.x5 ↦ᵣ ((GuestAddrs.empty_ommers_hash : Word))) **
        (.x6 ↦ᵣ (omEndW - omLenW)) **
        (.x7 ↦ᵣ ((k67OmBytes[0 + 32 - 1]'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend 64)) **
        (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
        (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
        (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x28 ↦ᵣ ((k67OmBytes[0 + 32 - 1]'(by rw [show k67OmBytes.length = 32 from ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]; omega)).zeroExtend 64)) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
          svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes)) := by
  subst hlen; subst homC
  have hfront := k67OmmersFront sp0 base
    (GuestAddrs.empty_ommers_hash : Word) endPtr bytes next14 len14 omEndW 32
    v5o v6 v7 v28 v29 v30 v31 v21 svals rfl
  let F : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ len14) ** (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ (32 : Word)) **
    (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
    (.x21 ↦ᵣ v21) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    regOwn .x13 ** regOwn .x14 **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
  have hF : F.pcFree := by
    dsimp only [F]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | apply pcFree_sepConj
  have hclean := k67OmmersCleanRun (omEndW - (32 : Word))
    (GuestAddrs.empty_ommers_hash : Word) base
    (GuestAddrs.empty_ommers_hash : Word) bytes omIdx 0 32 v7 v28 F hF offs
    (by omega) (by omega) haddr32
    (fun j' _hj' => by rw [EvmAsm.Evm64.signExtend12_ofNat_small (by omega)])
    halign hib hover hvalid (by decide) (by decide)
    (fun j' hj' => hvalid2 j' (by omega)) hmatch32 hlookLBU1 hlookLBU2 hlookBNE
  rw [show K + BitVec.ofNat 64 (212 + 12 * 0) = K + 212 from by
    rw [show BitVec.ofNat 64 (212 + 12 * 0) = (212 : Word) from by decide],
    show K + BitVec.ofNat 64 (212 + 12 * (0 + 32)) = K + 596 from by
      rw [show BitVec.ofNat 64 (212 + 12 * (0 + 32)) = (596 : Word) from by
        decide]] at hclean
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by dsimp only [F] at hq; xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by dsimp only [F]; xperm_hyp hp) hfront hclean)

/-! ## Merged post-loop N-branch -/

/-- Post-loop success post at the status-0 stub `K + 596`: the full
    pass-through state with the compare-scratch registers pinned to their
    final values, plus the semantic payload — nonce is eight zero bytes and
    the ommers hash content matches `k67OmBytes` (all in `getD` form, which is
    what the SpecRef bridge consumes). -/
def k67QOk (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (csIdx omIdx : Nat)
    (v29 v30 v31 v21 : Word) (svals : Reg → Word) : Assertion :=
  (((.x1 ↦ᵣ (K + 68)) **
    (.x5 ↦ᵣ ((GuestAddrs.empty_ommers_hash : Word))) **
    (.x6 ↦ᵣ (omEndW - omLenW)) **
    (.x7 ↦ᵣ ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64)) **
    (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
    (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
    (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
    (.x28 ↦ᵣ ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64)) **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
  ⌜len14 = (8 : Word) ∧
    (∀ (k : Nat), k < 8 → bytes.getD (csIdx + k) (0 : BitVec 8) = 0) ∧
    omLenW = (32 : Word) ∧
    (∀ (k : Nat), k < 32 → bytes.getD (omIdx + k) (0 : BitVec 8) =
      k67OmBytes.getD k (0 : BitVec 8))⌝)

/-- Post-loop nonce-failure post at the status-2 stub `K + 612`:
    pass-through state with the scratch registers existentialized, plus the
    failure witness (bad length or a nonzero byte). -/
def k67QNonceFail (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (csIdx _omIdx : Nat)
    (v28 v29 v30 v31 v21 : Word) (svals : Reg → Word) : Assertion := fun h =>
  ∃ v5 v6 v7 : Word,
    (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
      (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
      (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
    ⌜len14 ≠ (8 : Word) ∨
      ∃ (k : Nat), k < 8 ∧ bytes.getD (csIdx + k) (0 : BitVec 8) ≠ 0⌝) h

/-- Ommers-failure station post (`K + 620`): the ommers length gate failed or
    some ommers byte mismatched the pinned constant.  The clobbered registers
    are existential (`x28` included: the byte-fail path loads the constant into
    it, the length-gate path leaves it untouched). -/
def k67QOmmersFail (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (_csIdx omIdx : Nat)
    (v29 v30 v31 v21 : Word) (svals : Reg → Word) : Assertion := fun h =>
  ∃ v5 v6 v7 v28o : Word,
    (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
      (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
      (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28o) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
    ⌜omLenW ≠ (32 : Word) ∨
      ∃ (k : Nat), k < 32 ∧ bytes.getD (omIdx + k) (0 : BitVec 8) ≠
        k67OmBytes.getD k (0 : BitVec 8)⌝) h

/-! ## Merged post-loop N-branch -/

theorem k67_getD_eq {bytes : List (BitVec 8)} {dflt : BitVec 8} {n : Nat}
    (hn : n < bytes.length) : bytes.getD n dflt = bytes[n]'hn := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rfl

/-- The whole post-loop region as one N-branch: from the loop-exit state at
    `K + 116`, control reaches the success station `K + 596`, the ommers
    station `K + 620`, or the nonce station `K + 612` within 124 instructions,
    with each station post carrying the semantic fact its exit test
    established. -/
theorem k67PostLoop (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) (csIdx omIdx : Nat)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (hcsE14 : next14 - len14 = base + BitVec.ofNat 64 csIdx)
    (hib14 : csIdx + 8 ≤ bytes.length)
    (hib1 : omIdx + 32 ≤ bytes.length)
    (hcsE1 : omEndW - (32 : Word) = base + BitVec.ofNat 64 omIdx)
    (hvalid2 : ∀ (j' : Nat) (_hj' : j' < 32),
      isValidByteAccess (omConst + BitVec.ofNat 64 j') = true)
    (homC : omConst = ((GuestAddrs.empty_ommers_hash : Word)))
    (haddr8 : ∀ (j' : Nat) (_hj' : j' < 8),
      next14 - (8 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (csIdx + j'))
    (haddr32 : ∀ (j' : Nat) (_hj' : j' < 32),
      omEndW - (32 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (omIdx + j'))
    (offsN offsO : Nat → BitVec 13)
    (htakenN : ∀ (j' : Nat) (_hj' : j' < 8),
      (K + BitVec.ofNat 64 (132 + 8 * j')) + signExtend13 (offsN j') =
        K + 612)
    (htakenO : ∀ (j' : Nat) (_hj' : j' < 32),
      (K + BitVec.ofNat 64 (212 + 12 * j') + 8) + signExtend13 (offsO j') =
        K + 620)
    (hlookLBUN : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨32 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookBNEN : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨33 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x0 (offsN j'))
    (hlookLBU1 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨53 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookLBU2 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨54 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x28 .x5 (BitVec.ofNat 12 j'))
    (hlookBNEO : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨55 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x28 (offsO j')) :
    cpsNBranchWithin 124 (K + 116) fullCode
      (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v6 v7 v28 v29 v30 v31 v21 svals)
      [(K + 596, k67QOk sp0 base omConst endPtr bytes next14 len14 omEndW
          omLenW csIdx omIdx v29 v30 v31 v21 svals),
        (K + 620, k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
          omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals),
        (K + 612, k67QNonceFail sp0 base omConst endPtr bytes next14 len14
          omEndW omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)] := by
  by_cases hlen : len14 = (8 : Word)
  · by_cases hz : ∀ k', k' < 8 →
        bytes.getD (csIdx + k') (0 : BitVec 8) = (0 : BitVec 8)
    · -- nonce clean: phase 1 into the K+192 gate, then phase 2.
      have hzero8 : ∀ (j' : Nat) (hj' : j' < 8),
          bytes[csIdx + j']'(by omega) = (0 : BitVec 8) := by
        intro j' hj'
        have h1 := hz j' hj'
        rw [k67_getD_eq (by omega)] at h1
        exact h1
      have hpass := k67NoncePass sp0 base omConst endPtr bytes next14 len14
        omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals csIdx hlen hcsE14 hib14
        halign hover hvalid hzero8 offsN haddr8 hlookLBUN hlookBNEN
      have h1 : cpsNBranchWithin (3 + 2 * 8) (K + 116) fullCode
          (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
            v6 v7 v28 v29 v30 v31 v21 svals)
          [(K + 192, k67PLPreO sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW (8 : Word) (next14 - len14) (0 : Word) v28 v29 v30
              v31 v21 svals),
            (K + 612, k67QNonceFail sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)] := by
        apply cpsNBranchWithin_of_triple
          (Q := k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW
            omLenW (8 : Word) (next14 - len14) (0 : Word) v28 v29 v30 v31 v21
            svals)
          (by apply List.Mem.head)
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (fun _ hq => by unfold k67PLPreO; xperm_hyp hq) hpass
      have h2 : cpsNBranchWithin 101 (K + 192) fullCode
          (k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
            (8 : Word) (next14 - len14) (0 : Word) v28 v29 v30 v31 v21 svals)
          [(K + 596, k67QOk sp0 base omConst endPtr bytes next14 len14 omEndW
              omLenW csIdx omIdx v29 v30 v31 v21 svals),
            (K + 620, k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals)] := by
        by_cases hlen1 : omLenW = (32 : Word)
        · by_cases hm : ∀ k', k' < 32 → bytes.getD (omIdx + k') (0 : BitVec 8) =
              k67OmBytes.getD k' (0 : BitVec 8)
          · -- all 32 ommers bytes match
            have hmatch32 : ∀ (j' : Nat) (hj' : j' < 32),
                bytes[omIdx + j']'(by omega) =
                  k67OmBytes[j']'(by
                    rw [show k67OmBytes.length = 32 from
                      ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                    omega) := by
              intro j' hj'
              have h1 := hm j' hj'
              rw [k67_getD_eq (by omega)] at h1
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)] at h1
              exact h1
            have hpassO := k67OmmersPass sp0 base omConst endPtr bytes next14
              len14 omEndW omLenW omIdx (8 : Word) (next14 - len14) (0 : Word)
              v28 v29 v30 v31 v21 svals hlen1 homC hcsE1 hib1 halign hover
              hvalid hvalid2 hmatch32 offsO haddr32
              hlookLBU1 hlookLBU2 hlookBNEO
            apply cpsNBranchWithin_mono_nSteps (show 5 + 3 * 32 ≤ 101 by omega)
            apply cpsNBranchWithin_of_triple
              (Q := k67QOk sp0 base omConst endPtr bytes next14 len14 omEndW
                omLenW csIdx omIdx v29 v30 v31 v21 svals)
              (by apply List.Mem.head)
            refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hpassO
            intro h hq
            have hconv : ((k67OmBytes[0 + 32 - 1]'(by
                  rw [show k67OmBytes.length = 32 from
                    ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                  omega)).zeroExtend 64) =
                ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64) := by
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)]
            rw [hconv] at hq
            refine (sepConj_pure_right _).2 ⟨?_, hlen, hz, hlen1, hm⟩
            xperm_hyp hq
          · -- some ommers byte mismatches: take the minimal one
            haveI : DecidablePred (fun k' => k' < 32 ∧
                bytes.getD (omIdx + k') (0 : BitVec 8) ≠
                  k67OmBytes.getD k' (0 : BitVec 8)) := inferInstance
            obtain ⟨kw, hkw32, hwm⟩ : ∃ k', k' < 32 ∧
                bytes.getD (omIdx + k') (0 : BitVec 8) ≠
                  k67OmBytes.getD k' (0 : BitVec 8) := by
              have h1 := Classical.not_forall.mp hm
              obtain ⟨w, hw⟩ := h1
              have ⟨hw32, hwne⟩ := Classical.not_imp.mp hw
              exact ⟨w, hw32, hwne⟩
            have hW : ∃ k', k' < 32 ∧ bytes.getD (omIdx + k') (0 : BitVec 8) ≠
                k67OmBytes.getD k' (0 : BitVec 8) := ⟨kw, hkw32, hwm⟩
            let n := Nat.find hW
            have hnspec := Nat.find_spec hW
            have hn32 : n < 32 := hnspec.1
            have hpre : ∀ (j' : Nat) (hj' : j' < n),
                bytes[omIdx + j']'(by omega) =
                  k67OmBytes[j']'(by
                    rw [show k67OmBytes.length = 32 from
                      ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                    omega) := by
              intro j' hj'
              have hmin := Nat.find_min hW hj'
              have heq : bytes.getD (omIdx + j') (0 : BitVec 8) =
                  k67OmBytes.getD j' (0 : BitVec 8) :=
                of_not_not (fun hb => hmin ⟨by omega, hb⟩)
              rw [k67_getD_eq (by omega)] at heq
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)] at heq
              exact heq
            have hbyte' : bytes[omIdx + n]'(by omega) ≠
                k67OmBytes[n]'(by
                  rw [show k67OmBytes.length = 32 from
                    ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                  omega) := by
              have h1 := hnspec.2
              rw [k67_getD_eq (by omega)] at h1
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)] at h1
              exact h1
            have hbf := k67OmmersByteFail sp0 base omConst endPtr bytes next14
              len14 omEndW omLenW omIdx n (8 : Word) (next14 - len14)
              (0 : Word) v28 v29 v30 v31 v21 svals hlen1 homC hcsE1 hib1
              halign hover hvalid hvalid2 hn32 hpre hbyte' offsO haddr32
              htakenO hlookLBU1 hlookLBU2 hlookBNEO
            apply cpsNBranchWithin_mono_nSteps
              (show 5 + (3 * n + 3) ≤ 101 by omega)
            apply cpsNBranchWithin_of_triple
              (Q := k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
                omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals)
              (by apply List.Mem.tail; apply List.Mem.head)
            refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hbf
            intro h hq
            refine ⟨((GuestAddrs.empty_ommers_hash : Word)), omEndW - omLenW,
              ((bytes[omIdx + n]'(by omega)).zeroExtend 64),
              ((k67OmBytes[n]'(by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)).zeroExtend 64), ?_⟩
            refine (sepConj_pure_right _).2 ⟨?_,
              (Or.inr ⟨n, hnspec⟩ : omLenW ≠ (32 : Word) ∨
                ∃ (k : Nat), k < 32 ∧ bytes.getD (omIdx + k) (0 : BitVec 8) ≠
                  k67OmBytes.getD k (0 : BitVec 8))⟩
            xperm_hyp hq
        · -- ommers length gate fails
          have hlf := k67OmmersLenFail sp0 base omConst endPtr bytes next14
            len14 omEndW omLenW (8 : Word) (next14 - len14) (0 : Word) v28 v29
            v30 v31 v21 svals hlen1
          apply cpsNBranchWithin_mono_nSteps (show 2 ≤ 101 by omega)
          apply cpsNBranchWithin_of_triple
            (Q := k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals)
            (by apply List.Mem.tail; apply List.Mem.head)
          refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hlf
          intro h hq
          refine ⟨(32 : Word), next14 - len14, (0 : Word), v28, ?_⟩
          refine (sepConj_pure_right _).2 ⟨?_, Or.inl hlen1⟩
          xperm_hyp hq
      exact cpsNBranchWithin_mono_nSteps (show 3 + 2 * 8 + 101 ≤ 124 by omega)
        (cpsNBranchWithin_extend_head_nbranch h1 h2)
    · -- nonce length OK but some nonce byte nonzero: minimal witness.
      haveI : DecidablePred (fun k' => k' < 8 ∧
          bytes.getD (csIdx + k') (0 : BitVec 8) ≠ (0 : BitVec 8)) :=
        inferInstance
      obtain ⟨kw, hkw8, hwm⟩ : ∃ k', k' < 8 ∧
          bytes.getD (csIdx + k') (0 : BitVec 8) ≠ (0 : BitVec 8) := by
        have h1 := Classical.not_forall.mp hz
        obtain ⟨w, hw⟩ := h1
        have ⟨hw8, hwne⟩ := Classical.not_imp.mp hw
        exact ⟨w, hw8, hwne⟩
      have hW : ∃ k', k' < 8 ∧ bytes.getD (csIdx + k') (0 : BitVec 8) ≠
          (0 : BitVec 8) := ⟨kw, hkw8, hwm⟩
      let n := Nat.find hW
      have hnspec := Nat.find_spec hW
      have hn8 : n < 8 := hnspec.1
      have hpre : ∀ (j' : Nat) (hj' : j' < n),
          bytes[csIdx + j']'(by omega) = (0 : BitVec 8) := by
        intro j' hj'
        have hmin := Nat.find_min hW hj'
        have heq : bytes.getD (csIdx + j') (0 : BitVec 8) = (0 : BitVec 8) :=
          of_not_not (fun hb => hmin ⟨by omega, hb⟩)
        rw [k67_getD_eq (by omega)] at heq
        exact heq
      have hbyte' : bytes[csIdx + n]'(by omega) ≠ (0 : BitVec 8) := by
        have h1 := hnspec.2
        rw [k67_getD_eq (by omega)] at h1
        exact h1
      have hbf := k67NonceByteFail sp0 base omConst endPtr bytes next14 len14
        omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals n csIdx hlen hcsE14 hib14
        halign hover hvalid hn8 hpre hbyte' offsN haddr8 htakenN hlookLBUN
        hlookBNEN
      apply cpsNBranchWithin_mono_nSteps (show 3 + (2 * n + 2) ≤ 124 by omega)
      apply cpsNBranchWithin_of_triple
        (Q := k67QNonceFail sp0 base omConst endPtr bytes next14 len14 omEndW
          omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)
        (by apply List.Mem.tail; apply List.Mem.tail; apply List.Mem.head)
      refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hbf
      intro h hq
      refine ⟨(8 : Word), next14 - len14,
        ((bytes[csIdx + n]'(by omega)).zeroExtend 64), ?_⟩
      refine (sepConj_pure_right _).2 ⟨?_,
        (Or.inr ⟨n, hnspec⟩ : len14 ≠ (8 : Word) ∨
          ∃ (k : Nat), k < 8 ∧ bytes.getD (csIdx + k) (0 : BitVec 8) ≠ 0)⟩
      xperm_hyp hq
  · -- nonce length gate fails immediately
    have hlf := k67NonceLenFail sp0 base omConst endPtr bytes next14 len14
      omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals hlen
    apply cpsNBranchWithin_mono_nSteps (show 2 ≤ 124 by omega)
    apply cpsNBranchWithin_of_triple
      (Q := k67QNonceFail sp0 base omConst endPtr bytes next14 len14 omEndW
        omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)
      (by apply List.Mem.tail; apply List.Mem.tail; apply List.Mem.head)
    refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hlf
    intro h hq
    refine ⟨(8 : Word), v6, v7, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, Or.inl hlen⟩
    xperm_hyp hq

end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
