/-
  The 32-byte hash length-check + copy-setup blocks of
  `headerExtendedDecode_prog` (`Programs/HeaderDecode.lean`, PR-K39):
  parent_hash ([17]-[21]) and state_root ([43]-[47]).

  Each is a five-instruction guard at `S = HB + 4·k`:

    [k]   LI  x5, 32               [k+1] BNE x12, x5, →fail
    [k+2] SUB x28, x10, x12        [k+3] MV/ADDI x29, x18(, 32)
    [k+4] LI  x5, 32

  The `BNE` rejects a wrong-length field (`len ≠ 32`) to `HB + 664`; on the
  32-byte path the block leaves the byte-copy cursors ready (`x28` = content
  pointer, `x29` = output slot, `x5` = 32) for `hedCopyLoop`.  The differing
  `x29` setup (`MV` for parent_hash at struct+0, `ADDI …, 32` for state_root at
  struct+32) is abstracted as the `hDst` triple hypothesis, so one theorem
  serves both blocks.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeCall
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-- The length-check ok post at `S + 20`: the field was exactly 32 bytes, so the
    byte-copy cursors are set (`x28` = content ptr `adv − len`, `x29` = the
    struct slot `dstAddr`, `x5` = 32), the reported length stays in `x12`, and
    the advanced cursor in `x10`. -/
def hedLenOk (adv len outBase dstAddr : Word) (Extra : Assertion) : Assertion :=
  (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x28 : Reg) ↦ᵣ (adv - len)) **
    ((.x29 : Reg) ↦ᵣ dstAddr) ** ((.x12 : Reg) ↦ᵣ len) ** ((.x10 : Reg) ↦ᵣ adv) **
    ((.x18 : Reg) ↦ᵣ outBase) ** Extra) **
   ⌜len = (32 : Word)⌝

/-- The length-check fail post at `HB + 664`: the field was not 32 bytes.  Only
    the first `LI x5, 32` executed, so the surrounding registers are untouched. -/
def hedLenFail (adv len outBase v28 v29 : Word) (Extra : Assertion) : Assertion :=
  (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x12 : Reg) ↦ᵣ len) ** ((.x10 : Reg) ↦ᵣ adv) **
    ((.x18 : Reg) ↦ᵣ outBase) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** Extra) **
   ⌜len ≠ (32 : Word)⌝

set_option maxRecDepth 8000 in
/-- **32-byte length check + copy-setup.**  Given the `LI`/`BNE`/`SUB`/`LI`
    membership witnesses, the taken-target tie (`BNE → HB + 664`), and the `x29`
    setup triple `hDst` (`MV x29, x18` for parent_hash, `ADDI x29, x18, 32` for
    state_root), the block is a branch: fail (`len ≠ 32`) → `HB + 664`
    (`hedLenFail`), ok (`len = 32`) → `S + 20` (`hedLenOk`). -/
theorem hedLenCheck {Extra : Assertion}
    (S adv len outBase dstAddr v5 v28 v29 : Word) (boff : BitVec 13)
    (hExtra : Extra.pcFree)
    (htgt : (S + 4) + signExtend13 boff = HB + 664)
    (hLI0 : ∀ a i, CodeReq.singleton S (.LI .x5 (32 : Word)) a = some i → fullCode a = some i)
    (hBNE : ∀ a i, CodeReq.singleton (S + 4) (.BNE .x12 .x5 boff) a = some i → fullCode a = some i)
    (hSUB : ∀ a i, CodeReq.singleton (S + 8) (.SUB .x28 .x10 .x12) a = some i → fullCode a = some i)
    (hLI1 : ∀ a i, CodeReq.singleton (S + 16) (.LI .x5 (32 : Word)) a = some i → fullCode a = some i)
    (hDst : cpsTripleWithin 1 (S + 12) (S + 16) fullCode
      (((.x18 : Reg) ↦ᵣ outBase) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x18 : Reg) ↦ᵣ outBase) ** ((.x29 : Reg) ↦ᵣ dstAddr))) :
    cpsBranchWithin 5 S fullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x12 : Reg) ↦ᵣ len) ** ((.x10 : Reg) ↦ᵣ adv) **
        ((.x18 : Reg) ↦ᵣ outBase) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** Extra)
      (HB + 664) (hedLenFail adv len outBase v28 v29 Extra)
      (S + 20) (hedLenOk adv len outBase dstAddr Extra) := by
  -- [S] LI x5, 32
  have hli0 := li_spec_gen_within .x5 v5 (32 : Word) S (by decide)
  have hli0L := cpsTripleWithin_extend_code hLI0 hli0
  have hli0F := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ len) ** ((.x10 : Reg) ↦ᵣ adv) ** ((.x18 : Reg) ↦ᵣ outBase) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact hExtra | apply pcFree_sepConj) hli0L
  -- [S+4] BNE x12, x5, →fail
  have hbne := bne_spec_gen_within .x12 .x5 boff len (32 : Word) (S + 4)
  rw [htgt, show (S + 4) + 4 = S + 8 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code hBNE hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ adv) ** ((.x18 : Reg) ↦ᵣ outBase) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact hExtra | apply pcFree_sepConj) hbneL
  -- tail triple [S+8]-[S+16]: SUB ; dst ; LI  (S+8 → S+20)
  have hsub := sub_spec_gen_within .x28 .x10 .x12 adv len v28 (S + 8) (by decide)
  rw [show (S + 8) + 4 = S + 12 from by bv_omega] at hsub
  have hsubL := cpsTripleWithin_extend_code hSUB hsub
  have hsubF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x18 : Reg) ↦ᵣ outBase) **
     ((.x29 : Reg) ↦ᵣ v29) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact hExtra | apply pcFree_sepConj) hsubL
  have hdstF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ adv) ** ((.x12 : Reg) ↦ᵣ len) **
     ((.x28 : Reg) ↦ᵣ (adv - len)) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact hExtra | apply pcFree_sepConj) hDst
  have hli1 := li_spec_gen_within .x5 (32 : Word) (32 : Word) (S + 16) (by decide)
  rw [show (S + 16) + 4 = S + 20 from by bv_omega] at hli1
  have hli1L := cpsTripleWithin_extend_code hLI1 hli1
  have hli1F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ adv) ** ((.x12 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (adv - len)) **
     ((.x29 : Reg) ↦ᵣ dstAddr) ** ((.x18 : Reg) ↦ᵣ outBase) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact hExtra | apply pcFree_sepConj) hli1L
  have hsd1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsubF hdstF
  have htail0 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsd1 hli1F
  -- attach the ⌜len = 32⌝ carried from the BNE not-taken exit.
  have htail : cpsTripleWithin 3 (S + 8) (S + 20) fullCode
      ((((.x10 : Reg) ↦ᵣ adv) ** ((.x12 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28) **
        ((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x18 : Reg) ↦ᵣ outBase) **
        ((.x29 : Reg) ↦ᵣ v29) ** Extra) ** ⌜len = (32 : Word)⌝)
      (hedLenOk adv len outBase dstAddr Extra) := by
    have htailF := cpsTripleWithin_frameR (⌜len = (32 : Word)⌝) (by pcFree) htail0
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htailF
    -- hq : (post ** ⌜len = 32⌝) ; hedLenOk = regs ** ⌜len = 32⌝
    unfold hedLenOk
    obtain ⟨hreg, hlen⟩ := (sepConj_pure_right _).1 hq
    exact (sepConj_pure_right _).2 ⟨by xperm_hyp hreg, hlen⟩
  -- BNE branch ;; tail  (S+4 → HB+664 fail / S+20 ok)
  have hbr := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr hbneF
    (fun h hp => by xperm_hyp hp) htail
    (fun h hq => (by unfold hedLenFail; xperm_hyp hq :
      hedLenFail adv len outBase v28 v29 Extra h))
  -- weaken the composite pre to the LI0-post order, then prepend LI0.
  have hbr' := cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ x => x) (fun _ x => x) hbr
    (P' := ((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x12 : Reg) ↦ᵣ len) ** ((.x10 : Reg) ↦ᵣ adv) **
      ((.x18 : Reg) ↦ᵣ outBase) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** Extra)
  exact cpsTripleWithin_seq_branch_same_cr hli0F hbr'

#print axioms hedLenCheck

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
