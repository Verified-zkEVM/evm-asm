/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsLoop

  The FIRST find-last-tuple loop of `bal_account_nonstorage_finals`
  (slots 55–65, station 1 / balance_changes), verified end-to-end
  (bead evm-asm-4ch8f.43.5, slice 2b).

  Loop shape (byte offsets from `B = GuestAddrs.bal_account_nonstorage_finals`):

    B+220  ld   t0, 64(sp)        (cursor spill)
    B+224  ld   t1, 72(sp)        (window-end spill)
    B+228  beq  t0, t1, +36 → B+264   (clean exit: cursor = end)
    B+232  mv   a0, t0
    B+236  mv   a1, t1
    B+240  jal  rlp_walk_next     (verified callee, 6-outcome post)
    B+244  bne  a1, x0, +488 → B+732  (parse failure → reject stub → B+736)
    B+248  sd   a0, 64(sp)        (cursor := next)
    B+252  sub  s3, a0, a2        (s3 := next - len, the last item's span start)
    B+256  mv   s4, a2            (s4 := len)
    B+260  j    -40  → B+220      (back edge)

  Fold: `measureTwoExitLoop_spec` with measure `j = endOff - off`
  (strict decrease by `rlpItemDecode_advance`).  The invariant carries the
  `WalkPrefix` chain; the clean exit converts it to the `LastItemAt`
  semantics via `WalkPrefix.toLastItemAt`.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsWalk

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

theorem se64 : signExtend12 (64 : BitVec 12) = (64 : Word) := by decide
theorem se72 : signExtend12 (72 : BitVec 12) = (72 : Word) := by decide

/-! ## §1  Invariant and exits -/

/-- The loop invariant at the header (`B + 220`), indexed by the remaining
    byte gap `j = endOff - off`.  `off` is the cursor offset (spilled at
    `64(sp)`); after at least one iteration `s3`/`s4` hold the last decoded
    item's `(next - len, len)` with the `WalkPrefix` chain recorded. -/
def flInv (aB newSp : Word) (acctBytes : List (BitVec 8)) (off0 endOff : Nat)
    (F : Assertion) (j : Nat) : Assertion :=
  fun h => ∃ off : Nat, ∃ v19 v20 : Word,
    ((((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
      ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aB acctBytes ** F) **
     ⌜j = endOff - off ∧ off0 ≤ off ∧ off ≤ endOff ∧
       (off = off0 ∨ ∃ n l : Word,
         WalkPrefix acctBytes aB (aB + BitVec.ofNat 64 endOff) off0 off n l ∧
         n = aB + BitVec.ofNat 64 off ∧ v19 = n - l ∧ v20 = l)⌝) h

/-- The clean exit (`B + 264`): the cursor reached the window end; `s3`/`s4`
    hold the LAST item's span with the genuine `LastItemAt` derivation. -/
def flExit (aB newSp : Word) (acctBytes : List (BitVec 8)) (off0 endOff : Nat)
    (F : Assertion) : Assertion :=
  fun h => ∃ n l : Word,
    ((((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
      ((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l) **
      ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
      ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aB acctBytes ** F) **
     ⌜LastItemAt acctBytes aB (aB + BitVec.ofNat 64 endOff) off0 n l⌝) h

/-- The reject exit (`B + 736`, the shared epilogue entry after the reject
    stub): `a0 = 1`, everything the loop touched released to ownership. -/
def flRej (aB newSp : Word) (acctBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
  regOwn .x31 ** regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion aB acctBytes ** F

/-! ## §2  The parse-failure arm

    After `rlp_walk_next` returns a non-zero status, the `bne a1, x0` at
    `B + 244` jumps to the shared reject stub (`B + 732`, `li a0, 1`) and
    falls into the epilogue entry (`B + 736`). -/

/-- Any non-zero-status arm of the callee post routes to the reject exit. -/
theorem fl_failArm (aB newSp cursor v19 v20 raOld k : Word)
    (acctBytes : List (BitVec 8)) (endOff : Nat) (F : Assertion)
    (hF : F.pcFree) (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 244) (B + 736) bansfCR
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
  have hbne := bne_spec_gen_within .x11 .x0 (488 : BitVec 13) k (0 : Word) (B + 244)
  rw [show (B + 244) + signExtend13 (488 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (488 : BitVec 13) = (488 : Word) from by decide]
        bv_omega,
      show (B + 244) + 4 = B + 248 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 244) bansfProg 61 (.BNE .x11 .x0 (488 : BitVec 13))
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
theorem fl_okArm (aB newSp cursorOld v19 v20 next len raVal : Word)
    (acctBytes : List (BitVec 8)) (endOff : Nat) (F : Assertion)
    (hF : F.pcFree) :
    cpsTripleWithin 5 (B + 244) (B + 220) bansfCR
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
  have hbne := bne_spec_gen_within .x11 .x0 (488 : BitVec 13) (0 : Word) (0 : Word) (B + 244)
  rw [show (B + 244) + 4 = B + 248 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 244) bansfProg 61 (.BNE .x11 .x0 (488 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  -- SD a0, 64(sp) at B+248
  have hsd := sd_spec_gen_within .x2 .x10 newSp next cursorOld (64 : BitVec 12) (B + 248)
  rw [se64, show (B + 248) + 4 = B + 252 from by bv_omega] at hsd
  have hsdL := liftCode (cr' := bansfCR) hsd
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 248) bansfProg 62 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- SUB s3, a0, a2 at B+252
  have hsub := sub_spec_gen_within .x19 .x10 .x12 next len v19 (B + 252) (by decide)
  rw [show (B + 252) + 4 = B + 256 from by bv_omega] at hsub
  have hsubL := liftCode (cr' := bansfCR) hsub
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 252) bansfProg 63 (.SUB .x19 .x10 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- MV s4, a2 at B+256
  have hmv := mv_spec_gen_within .x20 .x12 len v20 (B + 256) (by decide)
  rw [show (B + 256) + 4 = B + 260 from by bv_omega] at hmv
  have hmvL := liftCode (cr' := bansfCR) hmv
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 256) bansfProg 64 (.MV .x20 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- J -40 at B+260 back to the header
  have hjal := jal_x0_spec_gen_within (-40 : BitVec 21) (B + 260)
  rw [show (B + 260) + signExtend21 (-40 : BitVec 21) = B + 220 from by
        rw [show signExtend21 (-40 : BitVec 21) = (-40 : Word) from by decide]
        bv_omega] at hjal
  have hjalL := liftCode (cr' := bansfCR) hjal
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 260) bansfProg 65 (.JAL .x0 (-40 : BitVec 21))
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

def flHeadPre (newSp cursor endW : Word) : Assertion :=
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((newSp + 64) ↦ₘ cursor) ** ((newSp + 72) ↦ₘ endW) **
  regOwn .x5 ** regOwn .x6

def flHeadPost (newSp cursor endW : Word) : Assertion :=
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((newSp + 64) ↦ₘ cursor) ** ((newSp + 72) ↦ₘ endW) **
  ((.x5 : Reg) ↦ᵣ cursor) ** ((.x6 : Reg) ↦ᵣ endW)

/-- The two spill loads (`B+220`, `B+224`), before the head test. -/
private theorem fl_headLoads (newSp cursor endW : Word) :
    cpsTripleWithin 2 (B + 220) (B + 228) bansfCR
      (flHeadPre newSp cursor endW) (flHeadPost newSp cursor endW) := by
  have core : cpsTripleWithin 2 (B + 220) (B + 228) bansfCR
      (((((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
         ((newSp + 72) ↦ₘ endW)) ** regOwn .x5 ** regOwn .x6))
      (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
       ((newSp + 72) ↦ₘ endW) ** ((.x5 : Reg) ↦ᵣ cursor) **
       ((.x6 : Reg) ↦ᵣ endW)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v5 v6 => ?_)
    have hld1 := ld_spec_gen_within .x5 .x2 newSp v5 cursor (64 : BitVec 12) (B + 220)
      (by decide)
    rw [se64, show (B + 220) + 4 = B + 224 from by bv_omega] at hld1
    have hld1L := liftCode (cr' := bansfCR) hld1
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 220) bansfProg 55 (.LD .x5 .x2 (64 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    have hld2 := ld_spec_gen_within .x6 .x2 newSp v6 endW (72 : BitVec 12) (B + 224)
      (by decide)
    rw [se72, show (B + 224) + 4 = B + 228 from by bv_omega] at hld2
    have hld2L := liftCode (cr' := bansfCR) hld2
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 224) bansfProg 56 (.LD .x6 .x2 (72 : BitVec 12))
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
    (fun h hp => by unfold flHeadPre at hp; xperm_hyp hp)
    (fun h hq => by unfold flHeadPost; xperm_hyp hq) core

/-- Head, exit case (`cursor = end`): the `beq` takes to `B + 264`. -/
theorem fl_headExit (newSp cursor endW : Word) (heq : cursor = endW) :
    cpsTripleWithin 3 (B + 220) (B + 264) bansfCR
      (flHeadPre newSp cursor endW) (flHeadPost newSp cursor endW) := by
  have hbeq := beq_spec_gen_within .x5 .x6 (36 : BitVec 13) cursor endW (B + 228)
  rw [show (B + 228) + signExtend13 (36 : BitVec 13) = B + 264 from by
        rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]
        bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 228) bansfProg 57 (.BEQ .x5 .x6 (36 : BitVec 13))
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
    (fun h hp => by unfold flHeadPost at hp; xperm_hyp hp)
    (fl_headLoads newSp cursor endW) htakenF
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hchain
  unfold flHeadPost
  have hq2 := sepConj_mono_left (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq2

/-- Head, continue case (`cursor ≠ end`): the `beq` falls through to
    `B + 232`. -/
theorem fl_headFall (newSp cursor endW : Word) (hne : cursor ≠ endW) :
    cpsTripleWithin 3 (B + 220) (B + 232) bansfCR
      (flHeadPre newSp cursor endW) (flHeadPost newSp cursor endW) := by
  have hbeq := beq_spec_gen_within .x5 .x6 (36 : BitVec 13) cursor endW (B + 228)
  rw [show (B + 228) + 4 = B + 232 from by bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 228) bansfProg 57 (.BEQ .x5 .x6 (36 : BitVec 13))
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
    (fun h hp => by unfold flHeadPost at hp; xperm_hyp hp)
    (fl_headLoads newSp cursor endW) hfallF
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hchain
  unfold flHeadPost
  have hq2 := sepConj_mono_left (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq2


/-! ## §5  The call block: `mv a0/a1`, `jal rlp_walk_next` -/

/-- From `B + 232` (head fall-through) to the callee return (`B + 244`):
    the two argument moves and the verified `rlp_walk_next` call.  All
    clobbered registers enter PINNED (the round introduces the owned values);
    the post is the callee's six-outcome dispatch, framed. -/
theorem fl_callBlock (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off endOff : Nat) (v19 v20 v7 v10 v11 v12 v28 v29 v30 v31 vRa : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoffe : off < endOff) :
    cpsTripleWithin 90 (B + 232) (B + 244) bansfCR
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
         ((.x1 : Reg) ↦ᵣ (B + 240 + 4)) ** bytesRegion aB acctBytes) **
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
  have hmv1 := mv_spec_gen_within .x10 .x5 (aB + BitVec.ofNat 64 off) v10 (B + 232)
    (by decide)
  rw [show (B + 232) + 4 = B + 236 from by bv_omega] at hmv1
  have hmv1L := liftCode (cr' := bansfCR) hmv1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 232) bansfProg 58 (.MV .x10 .x5)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- MV a1, t1 at B+236
  have hmv2 := mv_spec_gen_within .x11 .x6 (aB + BitVec.ofNat 64 endOff) v11 (B + 236)
    (by decide)
  rw [show (B + 236) + 4 = B + 240 from by bv_omega] at hmv2
  have hmv2L := liftCode (cr' := bansfCR) hmv2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 236) bansfProg 59 (.MV .x11 .x6)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  -- the callee triple at its entry, with ra = B + 240 + 4
  have hwn := rlp_walk_next_spec_within WN aB (aB + BitVec.ofNat 64 endOff)
    (B + 240 + 4) v12 (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff) v7
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
    (P' := ((.x1 : Reg) ↦ᵣ (B + 240 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  -- the call through the site-60 adapter
  have hcall := bansf_callSite60_walk_next (n := 87) vRa (by pcf) hwn'
  rw [show (B + 240) + 4 = B + 244 from by bv_omega] at hcall
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
def flCF (aB : Word) (acctBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x1 : Reg) ↦ᵣ (B + 240 + 4)) ** bytesRegion aB acctBytes

/-- Shorthand for the framed extras at the return site. -/
def flEx (aB newSp : Word) (off endOff : Nat) (v19 v20 : Word)
    (F : Assertion) : Assertion :=
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
  ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
  ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) ** F

/-- A fail arm (status `k ≠ 0`), packaged against the §5 post shape. -/
private theorem fl_dispatchFail (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 off endOff : Nat) (v19 v20 k : Word) (junk : Prop) (F : Assertion)
    (hF : F.pcFree) (hk : k ≠ (0 : Word)) (j : Nat) :
    cpsBranchWithin 5 (B + 244) bansfCR
      ((flCF aB acctBytes **
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ k) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ⌜junk⌝)) **
       flEx aB newSp off endOff v19 v20 F)
      (B + 736) (flRej aB newSp acctBytes F)
      (B + 220) (fun h => ∃ j', j' < j ∧
        flInv aB newSp acctBytes off0 endOff F j' h) := by
  have hfa := fl_failArm aB newSp (aB + BitVec.ofNat 64 off) v19 v20 (B + 240 + 4) k
    acctBytes endOff F hF hk
  have ht := cpsTripleWithin_weaken (P' := ((flCF aB acctBytes **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ k) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ⌜junk⌝)) **
      flEx aB newSp off endOff v19 v20 F))
    (fun h hp => by
      have hp2 : ((flCF aB acctBytes **
          (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x11 : Reg) ↦ᵣ k) **
           ((.x12 : Reg) ↦ᵣ (0 : Word)))) **
          flEx aB newSp off endOff v19 v20 F) h := by
        refine sepConj_mono_left (sepConj_mono_right (fun h' hp' => ?_)) h hp
        obtain ⟨h1, h2, hd, hu, h10, hrest⟩ := hp'
        obtain ⟨h3, h4, hd2, hu2, h11, hrest2⟩ := hrest
        obtain ⟨hP, _⟩ := (sepConj_pure_right h4).1 hrest2
        exact ⟨h1, h2, hd, hu, h10, h3, h4, hd2, hu2, h11, hP⟩
      unfold flCF flEx at hp2
      xperm_hyp hp2)
    (fun _ hq => hq) hfa
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsTripleWithin_as_cpsBranchWithin_left _ _ ht)

/-- The accept arm: the decode advances the cursor; the continuation
    re-establishes the invariant at the strictly smaller measure. -/
private theorem fl_dispatchOk (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 off endOff : Nat) (v19 v20 : Word) (F : Assertion)
    (hF : F.pcFree)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hb1 : off0 ≤ off) (hb2 : off ≤ endOff) (hoffe : off < endOff)
    (hstate : off = off0 ∨ ∃ n l : Word,
      WalkPrefix acctBytes aB (aB + BitVec.ofNat 64 endOff) off0 off n l ∧
      n = aB + BitVec.ofNat 64 off ∧ v19 = n - l ∧ v20 = l)
    (j : Nat) (hj : j = endOff - off) :
    cpsBranchWithin 5 (B + 244) bansfCR
      ((flCF aB acctBytes **
        rlpWalkNextOk (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff)
          acctBytes off) **
       flEx aB newSp off endOff v19 v20 F)
      (B + 736) (flRej aB newSp acctBytes F)
      (B + 220) (fun h => ∃ j', j' < j ∧
        flInv aB newSp acctBytes off0 endOff F j' h) := by
  -- expose the existential next/len and the decode fact
  refine cpsBranchWithin_weaken (P := fun h => ∃ next : Word, ∃ len : Word,
      (((flCF aB acctBytes **
         (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len))) **
        flEx aB newSp off endOff v19 v20 F) **
       ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
         (aB + BitVec.ofNat 64 endOff) next len⌝) h)
    (fun h hp => ?_) (fun _ hq => hq) (fun _ hq => hq) ?_
  · -- pointwise: pull the ∃/pure out of the callee-post arm
    obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ⟨next, len, hpins⟩⟩, hEx⟩ := hp
    obtain ⟨h5, h6, hd3, hu3, h10, hrest⟩ := hpins
    obtain ⟨h7, h8, hd4, hu4, h11, hrest2⟩ := hrest
    obtain ⟨hP12, hdec⟩ := (sepConj_pure_right h8).1 hrest2
    refine ⟨next, len, ?_⟩
    have hbody : ((flCF aB acctBytes **
        (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ len))) **
        flEx aB newSp off endOff v19 v20 F) h :=
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
  have hok := fl_okArm aB newSp (aB + BitVec.ofNat 64 off) v19 v20 next len
    (B + 240 + 4) acctBytes endOff F hF
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hok
  · unfold flCF flEx at hp
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
theorem fl_round (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 endOff : Nat) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoff0 : off0 < endOff) (j : Nat) :
    cpsNBranchWithin 98 (B + 220) bansfCR
      (flInv aB newSp acctBytes off0 endOff F j)
      [(B + 264, flExit aB newSp acctBytes off0 endOff F),
       (B + 736, flRej aB newSp acctBytes F),
       (B + 220, fun h => ∃ j', j' < j ∧
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
      (fl_headExit newSp (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 off) rfl)
    refine cpsNBranchWithin_of_triple (List.mem_cons_self ..)
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken
          (fun h hp => by unfold flHeadPre; xperm_hyp hp)
          (fun h hq => ?_) hheF))
    unfold flHeadPost at hq
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
      (fl_headFall newSp (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff) hne')
    have t2 := fl_callBlock aB newSp acctBytes off endOff v19 v20 v7 v10 v11 v12
      v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid hoffe
    have t12 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by unfold flHeadPost at hp; xperm_hyp hp) t1 t2
    -- the six dispatch arms, recombined
    have harms := cpsBranchWithin_pre_or
      (fl_dispatchOk aB newSp acctBytes off0 off endOff v19 v20 F hF hslack hover
        hb1 hb2 hoffe hstate j hj)
      (cpsBranchWithin_pre_or
        (fl_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (2 : Word)
          (¬ BitVec.ult (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 endOff) = true)
          F hF (by decide) j)
        (cpsBranchWithin_pre_or
          (fl_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (3 : Word)
            (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
              (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)
          (cpsBranchWithin_pre_or
            (fl_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (4 : Word)
              (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
                (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)
            (cpsBranchWithin_pre_or
              (fl_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (5 : Word)
                (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
                  (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)
              (fl_dispatchFail aB newSp acctBytes off0 off endOff v19 v20 (6 : Word)
                (¬ ∃ next len, rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
                  (aB + BitVec.ofNat 64 endOff) next len) F hF (by decide) j)))))
    -- distribute the callee post into the six arm preconditions and chain
    refine cpsNBranchWithin_of_branch_mem (by simp) (by simp [flInv])
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsBranchWithin_weaken
          (fun h hp => by unfold flHeadPre; xperm_hyp hp)
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

/-- **The find-last-tuple loop, folded** (station 1, header `B + 220`):
    from the invariant at measure `j`, the loop reaches either the clean
    exit (`B + 264`) with the LAST item's span and the genuine `LastItemAt`
    derivation, or the shared reject epilogue entry (`B + 736`) with
    `a0 = 1` — within `98 * (j + 1)` steps. -/
theorem bansf_findLastLoop1_spec (aB newSp : Word) (acctBytes : List (BitVec 8))
    (off0 endOff : Nat) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoff0 : off0 < endOff) (j : Nat) :
    cpsBranchWithin (98 * (j + 1)) (B + 220) bansfCR
      (flInv aB newSp acctBytes off0 endOff F j)
      (B + 264) (flExit aB newSp acctBytes off0 endOff F)
      (B + 736) (flRej aB newSp acctBytes F) :=
  cpsBranchWithin_of_nBranch2
    (measureTwoExitLoop_spec 98 (flInv aB newSp acctBytes off0 endOff F)
      (fun j' => fl_round aB newSp acctBytes off0 endOff F hF hsalign hslack
        hover hvalid hoff0 j') j)


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
