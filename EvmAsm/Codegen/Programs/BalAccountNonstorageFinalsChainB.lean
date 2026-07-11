/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainB

  The OUTER chain of `bal_account_nonstorage_finals` (bead evm-asm-4ch8f.43.5,
  slice 3a): body entry (`B + 28`, slot 7) through the balance-station
  boundary (`B + 184`, slot 46) —

    7–9    mv s0,a0 ; mv s1,a1 ; mv s2,a2
    10–19  sd x0 → 0/40/56/64/72/8/16/24/32/48(s2)   (zero the out block)
    20–21  mv a0,s0 ; mv a1,s1
    22     jal rlp_walk_init            (AccountChanges outer list; 9 outcomes)
    23     bnez a2 → reject
    24–25  sd a0→48(sp) ; sd a1→56(sp)
    26–27  ld a0←48(sp) ; ld a1←56(sp)
    28     jal rlp_walk_next            (item 0 = address)      29 bnez → reject
    30     sd a0→48(sp)
    31–33  ld ; ld ; jal rlp_walk_next  (item 1)                34 bnez ; 35 sd
    36–38  ld ; ld ; jal rlp_walk_next  (item 2)                39 bnez ; 40 sd
    41–43  ld ; ld ; jal rlp_walk_next  (item 3 = balance_changes)  44 bnez
    45     sd a0→48(sp)

  Success carries the unified `ListWindowOk` header fact for the outer list
  plus the four-item `rlpItemDecode` chain; every failure status routes to
  the shared reject epilogue entry (`B + 736`) with `a0 = 1`.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsLoop3

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

private theorem se48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

/-- The routine's own bytes as an abbrev (`runBlock`'s CodeReq delta-unfolder
    needs a named head; a bare `ofProg` head gets wrongly unfolded). -/
abbrev bansfCode : CodeReq := CodeReq.ofProg B bansfProg

/-! ## §1  The unified list-header fact

    `rlp_walk_init`'s two success arms (short / long list) normalize to one
    header-decode fact tied to the §2 `listHeaderSize` semantics of the spec
    file: the content cursor sits `listHeaderSize b` past the window start,
    and the header + declared content exactly fill the window. -/

/-- The window `[off, off + spanN)` of `bytes` is an RLP LIST whose content
    starts at `off + listHeaderSize b` — the pure residue of a successful
    `rlp_walk_init` on the window. -/
def ListWindowOk (bytes : List (BitVec 8)) (off spanN : Nat) : Prop :=
  ∃ b, bytes[off]? = some b ∧ 0xc0 ≤ b.toNat ∧
    listHeaderSize b ≤ spanN

/-- Content-start offset of a `ListWindowOk` window. -/
noncomputable def listContentOff (bytes : List (BitVec 8)) (off : Nat) : Nat :=
  off + listHeaderSize (bytes.getD off 0)

/-! ## §2  The prologue: argument moves + out-block zeroing (slots 7–21) -/

theorem bansf_prologue_spec (aB aLenW oB v8 v9 v18 : Word) :
    cpsTripleWithin 15 (B + 28) (B + 88) bansfCode
      (((.x10 : Reg) ↦ᵣ aB) ** ((.x11 : Reg) ↦ᵣ aLenW) ** ((.x12 : Reg) ↦ᵣ oB) **
       ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       memOwn oB ** memOwn (oB + 40) ** memOwn (oB + 56) **
       memOwn (oB + 64) ** memOwn (oB + 72) ** memOwn (oB + 8) **
       memOwn (oB + 16) ** memOwn (oB + 24) ** memOwn (oB + 32) **
       memOwn (oB + 48))
      (((.x10 : Reg) ↦ᵣ aB) ** ((.x11 : Reg) ↦ᵣ aLenW) ** ((.x12 : Reg) ↦ᵣ oB) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ aLenW) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
       ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
       ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word))) := by
  have s1 := mv_spec_gen_within .x8 .x10 aB v8 (B + 28) (by decide)
  have s2 := mv_spec_gen_within .x9 .x11 aLenW v9 (B + 32) (by decide)
  have s3 := mv_spec_gen_within .x18 .x12 oB v18 (B + 36) (by decide)
  have s4 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (0 : BitVec 12) (B + 40)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show oB + (0 : Word) = oB from by bv_omega] at s4
  have s5 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (40 : BitVec 12) (B + 44)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at s5
  have s6 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (56 : BitVec 12) (B + 48)
  rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide] at s6
  have s7 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (64 : BitVec 12) (B + 52)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide] at s7
  have s8 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (72 : BitVec 12) (B + 56)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide] at s8
  have s9 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (8 : BitVec 12) (B + 60)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at s9
  have s10 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (16 : BitVec 12) (B + 64)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at s10
  have s11 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (24 : BitVec 12) (B + 68)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at s11
  have s12 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (32 : BitVec 12) (B + 72)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at s12
  have s13 := sd_spec_gen_own_within .x18 .x0 oB (0 : Word) (48 : BitVec 12) (B + 76)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at s13
  have s14 := mv_spec_gen_within .x10 .x8 aB aB (B + 80) (by decide)
  have s15 := mv_spec_gen_within .x11 .x9 aLenW aLenW (B + 84) (by decide)
  runBlock s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15

#print axioms bansf_prologue_spec

/-! ## §3  The outer `rlp_walk_init` call and status dispatch (slots 22–23)

    Nine callee outcomes: seven failure statuses route through the `bne` to
    the shared reject epilogue entry; the two success arms (short / long
    list header) unify into the `listHeaderSize`-anchored content cursor. -/

/-- The reject-routing helper at the outer status check (`B + 92`,
    `bne a2, x0, +640 → B+732`). -/
private theorem outerFail (aB cur endW k : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 92) (B + 736) bansfCR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       ((.x12 : Reg) ↦ᵣ k) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 88 + 4)) **
       bytesRegion aB acctBytes ** F)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) **
       regOwn .x11 ** regOwn .x12 **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes ** F) := by
  have hbne := bne_spec_gen_within .x12 .x0 (640 : BitVec 13) k (0 : Word) (B + 92)
  rw [show (B + 92) + signExtend13 (640 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (640 : BitVec 13) = (640 : Word) from by decide]
        bv_omega,
      show (B + 92) + 4 = B + 96 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 92) bansfProg 23 (.BNE .x12 .x0 (640 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 88 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hbneL
  have htaken := cpsBranchWithin_takenPath hbneF
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact hk (((sepConj_pure_right _).1 h_pure).2))
  have hrej := liftCode (cr' := bansfCR)
    (bansf_rejectTail_spec B cur (by decide))
    (fun a i h => CodeReq.union_mono_left a i h)
  have hrejF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x11 : Reg) ↦ᵣ endW) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 88 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hrej
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2)
    htaken hrejF
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
  have hq2 := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x11)
          (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono (regIs_implies_regOwn .x1)
                    (fun _ x => x))))))))))))
    h hq
  xperm_hyp hq2

#print axioms outerFail

/-- The pure residue of a successful outer `rlp_walk_init`: the content
    cursor offset is `listHeaderSize` of the window's first byte. -/
def OuterInitOk (bytes : List (BitVec 8)) (aLen cOff : Nat) : Prop :=
  ∃ b0, bytes[0]? = some b0 ∧ cOff = listHeaderSize b0 ∧ 1 ≤ cOff ∧ cOff ≤ aLen

/-- The unified continue-state after the outer init status check
    (`B + 96`). -/
def outerInitPost (aB : Word) (aLen : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  fun h => ∃ cOff : Nat,
    ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
      ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
      ((.x12 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜OuterInitOk acctBytes aLen cOff⌝) h

/-- The reject-side post shared by every outer-chain failure. -/
def outerRej (aB : Word) (acctBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/- The outer `rlp_walk_init` dispatch (slot 22 call + slot 23 status check
   ⇒ `outerRej` / `outerInitPost`) is the next slice: the nine callee arms
   need explicit per-arm branch lemmas (seven `outerFail` instantiations +
   the two success arms unified into `OuterInitOk` via the short/long
   `listHeaderSize` bridges), recombined with `cpsBranchWithin_pre_or` as in
   `fl_round`.  The interfaces above are final. -/

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
