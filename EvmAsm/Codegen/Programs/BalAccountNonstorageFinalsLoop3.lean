/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsLoop3

  Station-3 find-last-tuple loop of `bal_account_nonstorage_finals`
  (header `B + 592`), instantiated from the verified station-1 stack
  in `BalAccountNonstorageFinalsLoop.lean` via the concrete address table —
  the slice-1 `#guard`s pin the three station shapes literally identical
  (bead evm-asm-4ch8f.43.5, slice 2c).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsLoop

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-! ## §2  The parse-failure arm

    After `rlp_walk_next` returns a non-zero status, the `bne a1, x0` at
    `B + 616` jumps to the shared reject stub (`B + 732`, `li a0, 1`) and
    falls into the epilogue entry (`B + 736`). -/

/-- Any non-zero-status arm of the callee post routes to the reject exit. -/
theorem fl3_failArm (aB newSp cursor v19 v20 raOld k : Word)
    (acctBytes : List (BitVec 8)) (endOff : Nat) (F : Assertion)
    (hF : F.pcFree) (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 616) (B + 736) bansfCR
      (((.x10 : Reg) ↦ᵣ cursor) ** ((.x11 : Reg) ↦ᵣ k) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) **
       bytesRegion aB acctBytes **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ cursor) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)
      (flRej aB newSp acctBytes F) := by
  -- the BNE at slot 61: taken (status ≠ 0) to the reject stub
  have hbne := bne_spec_gen_within .x11 .x0 (116 : BitVec 13) k (0 : Word) (B + 616)
  rw [show (B + 616) + signExtend13 (116 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (116 : BitVec 13) = (116 : Word) from by decide]
        bv_omega,
      show (B + 616) + 4 = B + 620 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 616) bansfProg 154 (.BNE .x11 .x0 (116 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ cursor) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion aB acctBytes **
     ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)
    (by pcf; exact hF) hbneL
  have htaken := cpsBranchWithin_takenPath hbneF
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact hk (((sepConj_pure_right _).1 h_pure).2))
  -- the reject stub at B + 732 sets a0 := 1 and falls into the epilogue
  have hrej := liftCode (cr' := bansfCR)
    (bansf_rejectTail_spec B cursor (by decide))
    (fun a i h => CodeReq.union_mono_left a i h)
  have hrejF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x12 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion aB acctBytes **
     ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)
    (by pcf; exact hF) hrej
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2)
    htaken hrejF
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
  unfold flRej
  have hq2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x11)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono (regIs_implies_regOwn .x1)
                    (sepConj_mono (fun _ x => x)
                      (sepConj_mono (fun _ x => x)
                        (sepConj_mono memIs_implies_memOwn
                          (sepConj_mono memIs_implies_memOwn
                            (sepConj_mono (regIs_implies_regOwn .x19)
                              (sepConj_mono (regIs_implies_regOwn .x20)
                                (fun _ x => x))))))))))))))))))
    h hq
  xperm_hyp hq2


/-! ## §3  The accept arm: spill the advanced cursor, capture the span -/

/-- The zero-status continuation: `bne` falls through, the advanced cursor
    is spilled, `s3`/`s4` capture the item's `(next - len, len)`, and the
    back edge returns to the header. -/
theorem fl3_okArm (aB newSp cursorOld v19 v20 next len raVal : Word)
    (acctBytes : List (BitVec 8)) (endOff : Nat) (F : Assertion)
    (hF : F.pcFree) :
    cpsTripleWithin 5 (B + 616) (B + 592) bansfCR
      (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
       bytesRegion aB acctBytes **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ cursorOld) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)
      (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
       bytesRegion aB acctBytes **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ next) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
       ((.x19 : Reg) ↦ᵣ (next - len)) ** ((.x20 : Reg) ↦ᵣ len) ** F) := by
  -- BNE at B+244: status 0 = 0, never taken
  have hbne := bne_spec_gen_within .x11 .x0 (116 : BitVec 13) (0 : Word) (0 : Word) (B + 616)
  rw [show (B + 616) + 4 = B + 620 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 616) bansfProg 154 (.BNE .x11 .x0 (116 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  -- SD a0, 64(sp) at B+248
  have hsd := sd_spec_gen_within .x2 .x10 newSp next cursorOld (64 : BitVec 12) (B + 620)
  rw [se64, show (B + 620) + 4 = B + 624 from by bv_omega] at hsd
  have hsdL := liftCode (cr' := bansfCR) hsd
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 620) bansfProg 155 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- SUB s3, a0, a2 at B+252
  have hsub := sub_spec_gen_within .x19 .x10 .x12 next len v19 (B + 624) (by decide)
  rw [show (B + 624) + 4 = B + 628 from by bv_omega] at hsub
  have hsubL := liftCode (cr' := bansfCR) hsub
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 624) bansfProg 156 (.SUB .x19 .x10 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- MV s4, a2 at B+256
  have hmv := mv_spec_gen_within .x20 .x12 len v20 (B + 628) (by decide)
  rw [show (B + 628) + 4 = B + 632 from by bv_omega] at hmv
  have hmvL := liftCode (cr' := bansfCR) hmv
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 628) bansfProg 157 (.MV .x20 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- J -40 at B+260 back to the header
  have hjal := jal_x0_spec_gen_within (-40 : BitVec 21) (B + 632)
  rw [show (B + 632) + signExtend21 (-40 : BitVec 21) = B + 592 from by
        rw [show signExtend21 (-40 : BitVec 21) = (-40 : Word) from by decide]
        bv_omega] at hjal
  have hjalL := liftCode (cr' := bansfCR) hjal
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 632) bansfProg 158 (.JAL .x0 (-40 : BitVec 21))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- frames
  have hfallF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ next) ** ((.x12 : Reg) ↦ᵣ len) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion aB acctBytes **
     ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursorOld) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)
    (by pcf; exact hF) hfall
  have hsdF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ len) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
     bytesRegion aB acctBytes **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)
    (by pcf; exact hF) hsdL
  have hsubF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
     bytesRegion aB acctBytes **
     ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ next) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x20 : Reg) ↦ᵣ v20) ** F)
    (by pcf; exact hF) hsubL
  have hmvF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
     bytesRegion aB acctBytes **
     ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ next) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ (next - len)) ** F)
    (by pcf; exact hF) hmvL
  have hjalF := cpsTripleWithin_frameL
    (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
     ((.x12 : Reg) ↦ᵣ len) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
     bytesRegion aB acctBytes **
     ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ next) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ (next - len)) ** ((.x20 : Reg) ↦ᵣ len) ** F)
    (by pcf; exact hF) hjalL
  rw [sepConj_emp_right'] at hjalF
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2)
    hfallF hsdF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hsubF
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2 hmvF
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3 hjalF
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) c4


/-! ## §4  The loop head: reload the spills, test for the window end -/

def fl3HeadPre (newSp cursor endW : Word) : Assertion :=
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((newSp + 64) ↦ₘ cursor) ** ((newSp + 72) ↦ₘ endW) **
  regOwn .x5 ** regOwn .x6

def fl3HeadPost (newSp cursor endW : Word) : Assertion :=
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((newSp + 64) ↦ₘ cursor) ** ((newSp + 72) ↦ₘ endW) **
  ((.x5 : Reg) ↦ᵣ cursor) ** ((.x6 : Reg) ↦ᵣ endW)

/-- The two spill loads (`B+220`, `B+224`), before the head test. -/
private theorem fl3_headLoads (newSp cursor endW : Word) :
    cpsTripleWithin 2 (B + 592) (B + 600) bansfCR
      (fl3HeadPre newSp cursor endW) (fl3HeadPost newSp cursor endW) := by
  have core : cpsTripleWithin 2 (B + 592) (B + 600) bansfCR
      (((((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
         ((newSp + 72) ↦ₘ endW)) ** regOwn .x5 ** regOwn .x6))
      (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
       ((newSp + 72) ↦ₘ endW) ** ((.x5 : Reg) ↦ᵣ cursor) **
       ((.x6 : Reg) ↦ᵣ endW)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v5 v6 => ?_)
    have hld1 := ld_spec_gen_within .x5 .x2 newSp v5 cursor (64 : BitVec 12) (B + 592)
      (by decide)
    rw [se64, show (B + 592) + 4 = B + 596 from by bv_omega] at hld1
    have hld1L := liftCode (cr' := bansfCR) hld1
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 592) bansfProg 148 (.LD .x5 .x2 (64 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    have hld2 := ld_spec_gen_within .x6 .x2 newSp v6 endW (72 : BitVec 12) (B + 596)
      (by decide)
    rw [se72, show (B + 596) + 4 = B + 600 from by bv_omega] at hld2
    have hld2L := liftCode (cr' := bansfCR) hld2
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 596) bansfProg 149 (.LD .x6 .x2 (72 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    have hld1F := cpsTripleWithin_frameR
      (((newSp + 72) ↦ₘ endW) ** ((.x6 : Reg) ↦ᵣ v6))
      (by pcf) hld1L
    have hld2F := cpsTripleWithin_frameR
      (((newSp + 64) ↦ₘ cursor) ** ((.x5 : Reg) ↦ᵣ cursor))
      (by pcf) hld2L
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hld1F hld2F
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq) c1
  exact cpsTripleWithin_weaken
    (fun h hp => by unfold fl3HeadPre at hp; xperm_hyp hp)
    (fun h hq => by unfold fl3HeadPost; xperm_hyp hq) core

/-- Head, exit case (`cursor = end`): the `beq` takes to `B + 636`. -/
theorem fl3_headExit (newSp cursor endW : Word) (heq : cursor = endW) :
    cpsTripleWithin 3 (B + 592) (B + 636) bansfCR
      (fl3HeadPre newSp cursor endW) (fl3HeadPost newSp cursor endW) := by
  have hbeq := beq_spec_gen_within .x5 .x6 (36 : BitVec 13) cursor endW (B + 600)
  rw [show (B + 600) + signExtend13 (36 : BitVec 13) = B + 636 from by
        rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]
        bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 600) bansfProg 150 (.BEQ .x5 .x6 (36 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbeq
  have htaken := cpsBranchWithin_takenPath hbeqL
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd heq (((sepConj_pure_right _).1 h_pure).2))
  have htakenF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) ** ((newSp + 72) ↦ₘ endW))
    (by pcf) htaken
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by unfold fl3HeadPost at hp; xperm_hyp hp)
    (fl3_headLoads newSp cursor endW) htakenF
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hchain
  unfold fl3HeadPost
  have hq2 := sepConj_mono_left (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq2

/-- Head, continue case (`cursor ≠ end`): the `beq` falls through to
    `B + 604`. -/
theorem fl3_headFall (newSp cursor endW : Word) (hne : cursor ≠ endW) :
    cpsTripleWithin 3 (B + 592) (B + 604) bansfCR
      (fl3HeadPre newSp cursor endW) (fl3HeadPost newSp cursor endW) := by
  have hbeq := beq_spec_gen_within .x5 .x6 (36 : BitVec 13) cursor endW (B + 600)
  rw [show (B + 600) + 4 = B + 604 from by bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 600) bansfProg 150 (.BEQ .x5 .x6 (36 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbeq
  have hfall := cpsBranchWithin_ntakenPath hbeqL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hne)
  have hfallF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) ** ((newSp + 72) ↦ₘ endW))
    (by pcf) hfall
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by unfold fl3HeadPost at hp; xperm_hyp hp)
    (fl3_headLoads newSp cursor endW) hfallF
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hchain
  unfold fl3HeadPost
  have hq2 := sepConj_mono_left (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq2


/-! ## §5  The call block: `mv a0/a1`, `jal rlp_walk_next` -/

/-- From `B + 604` (head fall-through) to the callee return (`B + 616`):
    the two argument moves and the verified `rlp_walk_next` call.  All
    clobbered registers enter PINNED (the round introduces the owned values);
    the post is the callee's six-outcome dispatch, framed. -/
theorem fl3_callBlock (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off endOff : Nat) (v19 v20 v7 v10 v11 v12 v28 v29 v30 v31 vRa : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoffe : off < endOff) :
    cpsTripleWithin 90 (B + 604) (B + 616) bansfCR
      (((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
       ((.x7 : Reg) ↦ᵣ v7) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x1 : Reg) ↦ᵣ vRa) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** F)
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ (B + 612 + 4)) ** bytesRegion aB acctBytes) **
        (fun h =>
          rlpWalkNextOk (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff)
            acctBytes off h ∨
          ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ (2 : Word)) **
            ((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff) = true⌝) h) ∨
          ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ (3 : Word)) **
            ((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
              (aB + BitVec.ofNat 64 endOff) next len⌝) h) ∨
          ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ (4 : Word)) **
            ((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
              (aB + BitVec.ofNat 64 endOff) next len⌝) h) ∨
          ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ (5 : Word)) **
            ((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
              (aB + BitVec.ofNat 64 endOff) next len⌝) h) ∨
          ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ (6 : Word)) **
            ((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
              (aB + BitVec.ofNat 64 endOff) next len⌝) h))) **
       (((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
        ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)) := by
  have hoffb : off < acctBytes.length := by omega
  -- MV a0, t0 at B+232
  have hmv1 := mv_spec_gen_within .x10 .x5 (aB + BitVec.ofNat 64 off) v10 (B + 604)
    (by decide)
  rw [show (B + 604) + 4 = B + 608 from by bv_omega] at hmv1
  have hmv1L := liftCode (cr' := bansfCR) hmv1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 604) bansfProg 151 (.MV .x10 .x5)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- MV a1, t1 at B+236
  have hmv2 := mv_spec_gen_within .x11 .x6 (aB + BitVec.ofNat 64 endOff) v11 (B + 608)
    (by decide)
  rw [show (B + 608) + 4 = B + 612 from by bv_omega] at hmv2
  have hmv2L := liftCode (cr' := bansfCR) hmv2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 608) bansfProg 152 (.MV .x11 .x6)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- the callee triple at its entry, with ra = B + 612 + 4
  have hwn := rlp_walk_next_spec_within WN aB (aB + BitVec.ofNat 64 endOff)
    (B + 612 + 4) v12 (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff) v7
    v28 v29 v30 v31 acctBytes off hsalign hoffb (by omega)
    (hvalid off hoffb)
    (fun h80 hb8 _ _ => ⟨by omega, by omega, hvalid _ (by omega)⟩)
    (fun hb8 hc0 _ => by
      have hlo : ((acctBytes[off]'hoffb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        have h1 := ult_lt hc0
        have h2 := not_ult_le hb8
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
    (fun hf8 _ => by
      have hlo : ((acctBytes[off]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[off]'hoffb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
  -- reorder the callee pre into the adapter's (ra ** Prest) shape
  have hwn' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwn
    (P' := ((.x1 : Reg) ↦ᵣ (B + 612 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  -- the call through the site-60 adapter
  have hcall := bansf_callSite153_walk_next (n := 87) vRa (by pcf) hwn'
  rw [show (B + 612) + 4 = B + 616 from by bv_omega] at hcall
  -- frame the untouched context through the call
  have hcallF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F)
    (by pcf; exact hF) hcall
  -- frames for the moves
  have hmv1F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
     ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x1 : Reg) ↦ᵣ vRa) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hmv1L
  have hmv2F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
     ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
     ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x12 : Reg) ↦ᵣ v12) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x1 : Reg) ↦ᵣ vRa) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hmv2L
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hmv1F hmv2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hcallF
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq) c2


/-! ## §6  The dispatch: consume the six-outcome post -/

/-- Shorthand for the callee-common frame at the return site. -/
def fl3CF (aB : Word) (acctBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x1 : Reg) ↦ᵣ (B + 612 + 4)) ** bytesRegion aB acctBytes

/-- Shorthand for the framed extras at the return site. -/
def fl3Ex (aB newSp : Word) (off endOff : Nat) (v19 v20 : Word)
    (F : Assertion) : Assertion :=
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
  ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
  ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F

/-- A fail arm (status `k ≠ 0`), packaged against the §5 post shape. -/
private theorem fl3_dispatchFail (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 off endOff : Nat) (v19 v20 k : Word) (junk : Prop) (F : Assertion)
    (hF : F.pcFree) (hk : k ≠ (0 : Word)) (j : Nat) :
    cpsBranchWithin 5 (B + 616) bansfCR
      ((fl3CF aB acctBytes **
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ k) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ⌜junk⌝)) **
       fl3Ex aB newSp off endOff v19 v20 F)
      (B + 736) (flRej aB newSp acctBytes F)
      (B + 592) (fun h => ∃ j', j' < j ∧
        flInv aB newSp acctBytes off0 endOff F j' h) := by
  have hfa := fl3_failArm aB newSp (aB + BitVec.ofNat 64 off) v19 v20 (B + 612 + 4) k
    acctBytes endOff F hF hk
  have ht := cpsTripleWithin_weaken (P' := ((fl3CF aB acctBytes **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ k) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ⌜junk⌝)) **
      fl3Ex aB newSp off endOff v19 v20 F))
    (fun h hp => by
      have hp2 : ((fl3CF aB acctBytes **
          (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ k) **
           ((.x12 : Reg) ↦ᵣ (0 : Word)))) **
          fl3Ex aB newSp off endOff v19 v20 F) h := by
        refine sepConj_mono_left (sepConj_mono_right (fun h' hp' => ?_)) h hp
        obtain ⟨h1, h2, hd, hu, h10, hrest⟩ := hp'
        obtain ⟨h3, h4, hd2, hu2, h11, hrest2⟩ := hrest
        obtain ⟨hP, _⟩ := (sepConj_pure_right h4).1 hrest2
        exact ⟨h1, h2, hd, hu, h10, h3, h4, hd2, hu2, h11, hP⟩
      unfold fl3CF fl3Ex at hp2
      xperm_hyp hp2)
    (fun _ hq => hq) hfa
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsTripleWithin_as_cpsBranchWithin_left _ _ ht)

/-- The accept arm: the decode advances the cursor; the continuation
    re-establishes the invariant at the strictly smaller measure. -/
private theorem fl3_dispatchOk (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 off endOff : Nat) (v19 v20 : Word) (F : Assertion)
    (hF : F.pcFree)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hb1 : off0 ≤ off) (hb2 : off ≤ endOff) (hoffe : off < endOff)
    (hstate : off = off0 ∨ ∃ n l : Word,
      WalkPrefix acctBytes aB (aB + BitVec.ofNat 64 endOff) off0 off n l ∧
      n = aB + BitVec.ofNat 64 off ∧ v19 = n - l ∧ v20 = l)
    (j : Nat) (hj : j = endOff - off) :
    cpsBranchWithin 5 (B + 616) bansfCR
      ((fl3CF aB acctBytes **
        rlpWalkNextOk (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff)
          acctBytes off) **
       fl3Ex aB newSp off endOff v19 v20 F)
      (B + 736) (flRej aB newSp acctBytes F)
      (B + 592) (fun h => ∃ j', j' < j ∧
        flInv aB newSp acctBytes off0 endOff F j' h) := by
  -- expose the existential next/len and the decode fact
  refine cpsBranchWithin_weaken (P := fun h => ∃ next : Word, ∃ len : Word,
      (((fl3CF aB acctBytes **
         (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len))) **
        fl3Ex aB newSp off endOff v19 v20 F) **
       ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
         (aB + BitVec.ofNat 64 endOff) next len⌝) h)
    (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq) ?_
  · -- pointwise: pull the ∃/pure out of the callee-post arm
    obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ⟨next, len, hpins⟩⟩, hEx⟩ := hp
    obtain ⟨h5, h6, hd3, hu3, h10, hrest⟩ := hpins
    obtain ⟨h7, h8, hd4, hu4, h11, hrest2⟩ := hrest
    obtain ⟨hP12, hdec⟩ := (sepConj_pure_right h8).1 hrest2
    refine ⟨next, len, ?_⟩
    have hbody : ((fl3CF aB acctBytes **
        (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ len))) **
        fl3Ex aB newSp off endOff v19 v20 F) h :=
      ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, h5, h6, hd3, hu3, h10,
        h7, h8, hd4, hu4, h11, hP12⟩, hEx⟩
    exact (sepConj_pure_right h).2 ⟨hbody, hdec⟩
  refine cpsBranchWithin_exists_pre (fun next => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
  -- the decode strictly advances the cursor inside the window
  have hadv := rlpItemDecode_advance (bytes := acctBytes) (base := aB)
    (off := off) (endOff := endOff) hdec hb2 (by omega)
  obtain ⟨hrep, hlt, hle⟩ := hadv
  refine cpsTripleWithin_as_cpsBranchWithin_right _ _ ?_
  have hok := fl3_okArm aB newSp (aB + BitVec.ofNat 64 off) v19 v20 next len
    (B + 612 + 4) acctBytes endOff F hF
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hok
  · unfold fl3CF fl3Ex at hp
    xperm_hyp hp
  · -- rebuild the invariant at the smaller measure
    refine ⟨endOff - (next - aB).toNat, by omega, ?_⟩
    unfold flInv
    refine ⟨(next - aB).toNat, next - len, len, ?_⟩
    have hq2 := sepConj_mono
      (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
                  (sepConj_mono (regIs_implies_regOwn .x1)
                    (fun _ x => x))))))))))))
      h hq
    have hatoms : ((((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ next) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
        ((.x19 : Reg) ↦ᵣ (next - len)) ** ((.x20 : Reg) ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hq2
    rw [← hrep]
    refine (sepConj_pure_right h).2 ⟨hatoms, rfl, by omega, hle, Or.inr ⟨next, len, ?_, rfl, rfl, rfl⟩⟩
    -- extend the chain
    rcases hstate with hA | ⟨n, l, hch, hrepn, _, _⟩
    · subst hA
      exact WalkPrefix.one off next len hdec
    · refine WalkPrefix.snoc hch ?_ hdec
      rw [hrepn]
      intro hc
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat] at this
      omega


/-! ## §7  The round: one full pass from the header -/

/-- One loop round: from `flInv j` at the header, reach the clean exit, the
    reject exit, or the header again with a strictly smaller measure. -/
theorem fl3_round (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 endOff : Nat) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoff0 : off0 < endOff) (j : Nat) :
    cpsNBranchWithin 98 (B + 592) bansfCR
      (flInv aB newSp acctBytes off0 endOff F j)
      [(B + 636, flExit aB newSp acctBytes off0 endOff F),
       (B + 736, flRej aB newSp acctBytes F),
       (B + 592, fun h => ∃ j', j' < j ∧
         flInv aB newSp acctBytes off0 endOff F j' h)] := by
  unfold flInv
  refine cpsNBranchWithin_exists_pre (fun off => ?_)
  refine cpsNBranchWithin_exists_pre (fun v19 => ?_)
  refine cpsNBranchWithin_exists_pre (fun v20 => ?_)
  refine cpsNBranchWithin_pure_pre (fun hfacts => ?_)
  obtain ⟨hj, hb1, hb2, hstate⟩ := hfacts
  by_cases hoe : off = endOff
  · -- ===== clean exit: the head BEQ takes =====
    subst hoe
    have hchainD : ∃ n l : Word,
        WalkPrefix acctBytes aB (aB + BitVec.ofNat 64 off) off0 off n l ∧
        n = aB + BitVec.ofNat 64 off ∧ v19 = n - l ∧ v20 = l := by
      rcases hstate with hA | hB
      · exact absurd hA (by omega)
      · exact hB
    obtain ⟨n, l, hch, hrepn, hv19, hv20⟩ := hchainD
    have hlast := WalkPrefix.toLastItemAt hch hrepn
    have hheF := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF)
      (fl3_headExit newSp (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 off) rfl)
    refine cpsNBranchWithin_of_triple (List.mem_cons_self ..)
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken
          (fun h hp => by unfold fl3HeadPre; xperm_hyp hp)
          (fun h hq => ?_) hheF))
    unfold fl3HeadPost at hq
    unfold flExit
    refine ⟨n, l, ?_⟩
    rw [hv19, hv20] at hq
    have hq2 : ((((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l) **
        ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** regOwn .x7 **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hq
    exact (sepConj_pure_right h).2 ⟨hq2, hlast⟩
  · -- ===== continue: fall through into the call block =====
    have hoffe : off < endOff := Nat.lt_of_le_of_ne hb2 hoe
    have hne' : aB + BitVec.ofNat 64 off ≠ aB + BitVec.ofNat 64 endOff := by
      intro hc
      apply hoe
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat] at this
      omega
    -- expose the nine call-clobbered registers
    refine cpsNBranchWithin3_weaken
      (P := ((((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
        ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
        regOwn .x5 ** regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F) **
        regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x1))
      (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x) (fun _ x => x) ?_
    refine cpsNBranchWithin_of_forall_regIs_to_regOwn9
      (fun v7 v10 v11 v12 v28 v29 v30 v31 vRa => ?_)
    -- head fall-through
    have t1 := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x7 : Reg) ↦ᵣ v7) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x1 : Reg) ↦ᵣ vRa) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF)
      (fl3_headFall newSp (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff) hne')
    have t2 := fl3_callBlock aB newSp acctBytes off endOff v19 v20 v7 v10 v11 v12
      v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid hoffe
    have t12 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by unfold fl3HeadPost at hp; xperm_hyp hp) t1 t2
    -- the six dispatch arms, recombined
    have harms := cpsBranchWithin_pre_or
      (fl3_dispatchOk aB newSp acctBytes off0 off endOff v19 v20 F hF hslack hover
        hb1 hb2 hoffe hstate j hj)
      (cpsBranchWithin_pre_or
        (fl3_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (2 : Word)
          (¬ BitVec.ult (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff) = true)
          F hF (by decide) j)
        (cpsBranchWithin_pre_or
          (fl3_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (3 : Word)
            (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
              (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)
          (cpsBranchWithin_pre_or
            (fl3_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (4 : Word)
              (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
                (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)
            (cpsBranchWithin_pre_or
              (fl3_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (5 : Word)
                (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
                  (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)
              (fl3_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (6 : Word)
                (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
                  (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)))))
    -- distribute the callee post into the six arm preconditions and chain
    refine cpsNBranchWithin_of_branch_mem (by simp) (by simp [flInv])
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsBranchWithin_weaken
          (fun h hp => by unfold fl3HeadPre; xperm_hyp hp)
          (fun _ x => x) (fun _ x => x)
          (cpsTripleWithin_seq_branch_same_cr t12
            (cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x) harms))))
    -- pointwise or-distribution
    obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, hor⟩, hEx⟩ := hp
    rcases hor with a1 | a2 | a3 | a4 | a5 | a6
    · exact Or.inl ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, a1⟩, hEx⟩
    · exact Or.inr (Or.inl ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, a2⟩, hEx⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, a3⟩, hEx⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, a4⟩, hEx⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, a5⟩, hEx⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, a6⟩, hEx⟩))))


/-! ## §8  The folded loop -/

/-- **The find-last-tuple loop, folded** (station 1, header `B + 592`):
    from the invariant at measure `j`, the loop reaches either the clean
    exit (`B + 636`) with the LAST item's span and the genuine `LastItemAt`
    derivation, or the shared reject epilogue entry (`B + 736`) with
    `a0 = 1` — within `98 * (j + 1)` steps. -/
theorem bansf_findLastLoop3_spec (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 endOff : Nat) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoff0 : off0 < endOff) (j : Nat) :
    cpsBranchWithin (98 * (j + 1)) (B + 592) bansfCR
      (flInv aB newSp acctBytes off0 endOff F j)
      (B + 636) (flExit aB newSp acctBytes off0 endOff F)
      (B + 736) (flRej aB newSp acctBytes F) :=
  cpsBranchWithin_of_nBranch2
    (measureTwoExitLoop_spec 98 (flInv aB newSp acctBytes off0 endOff F)
      (fun j' => fl3_round aB newSp acctBytes off0 endOff F hF hsalign hslack
        hover hvalid hoff0 j') j)


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
