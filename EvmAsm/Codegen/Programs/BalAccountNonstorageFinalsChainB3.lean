/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainB3

  SEG-B assembly for `bal_account_nonstorage_finals` (bead
  evm-asm-4ch8f.43.5, slice 3d): body entry (`B + 28`) through the
  balance-station boundary (`B + 184`) as ONE two-exit branch — the
  prologue, the outer `rlp_walk_init` dispatch, the cursor/end spills, and
  the four outer item units, with the reject exits threaded to the shared
  epilogue entry and the success exit carrying the accumulated
  `rlpItemDecode` chain for items 0–3.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainB2

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

private theorem se48' : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se56' : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

/-- The SEG-B grand reject: everything the outer chain touches, with the
    prologue's stable state (`s0/s1/s2`, the zeroed out block) still pinned. -/
def chainRejB (aB newSp oB : Word) (aLen : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) **
  (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
  ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
  ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
  ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
  ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- The item-0-ready state (`B + 104`): outer header consumed, cursor and
    window end spilled. -/
def chainMidB (aB newSp oB : Word) (aLen : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  fun h => ∃ c : Nat,
    ((((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 c)) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 c)) **
      ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
      ((.x12 : Reg) ↦ᵣ (0 : Word)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) **
      (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
      ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
      ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜OuterInitOk acctBytes aLen c⌝) h

/-- Part A of SEG-B: body entry (`B + 28`) through the spilled outer
    cursor (`B + 104`): prologue, outer `rlp_walk_init` dispatch, and the
    two spill stores. -/
theorem bansf_chainA_spec (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (v8 v9 v18 : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin 101 (B + 28) bansfCR
      (((.x10 : Reg) ↦ᵣ aB) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x12 : Reg) ↦ᵣ oB) **
       ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 48) ** memOwn (newSp + 56) **
       memOwn oB ** memOwn (oB + 40) ** memOwn (oB + 56) **
       memOwn (oB + 64) ** memOwn (oB + 72) ** memOwn (oB + 8) **
       memOwn (oB + 16) ** memOwn (oB + 24) ** memOwn (oB + 32) **
       memOwn (oB + 48) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes ** F)
      (B + 736) (chainRejB aB newSp oB aLen acctBytes F)
      (B + 104) (chainMidB aB newSp oB aLen acctBytes F) := by
  -- expose the eight owned scratch registers for the init call
  refine cpsBranchWithin_weaken
    (P := ((((.x10 : Reg) ↦ᵣ aB) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x12 : Reg) ↦ᵣ oB) **
       ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 48) ** memOwn (newSp + 56) **
       memOwn oB ** memOwn (oB + 40) ** memOwn (oB + 56) **
       memOwn (oB + 64) ** memOwn (oB + 72) ** memOwn (oB + 8) **
       memOwn (oB + 16) ** memOwn (oB + 24) ** memOwn (oB + 32) **
       memOwn (oB + 48) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** F) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
    (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x) ?_
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  -- prologue triple (B+28 → B+88), framed
  have hpro := liftCode (cr' := bansfCR)
    (bansf_prologue_spec aB (BitVec.ofNat 64 aLen) oB v8 v9 v18)
    (fun a i h => CodeReq.union_mono_left a i h)
  have hproF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     memOwn (newSp + 48) ** memOwn (newSp + 56) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hpro
  -- outer init dispatch (B+88), with the prologue's stable state framed
  have hinit := bansf_outerInit_spec aB aLen acctBytes v5 v6 v7 oB v28 v29 v30 v31
    vRa
    (((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     ((.x2 : Reg) ↦ᵣ newSp) **
     memOwn (newSp + 48) ** memOwn (newSp + 56) **
     (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
     ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
     ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
     ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
     ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** F)
    (by pcf; exact hF) hsalign hslack hover hvalid
  -- glue: SD a0, 48(sp) ; SD a1, 56(sp)  (slots 24–25, B+96 → B+104)
  have hglue : ∀ c : Nat, cpsTripleWithin 2 (B + 96) (B + 104) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 c)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 48) ** memOwn (newSp + 56))
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 c)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 c)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen))) := by
    intro c
    have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp (aB + BitVec.ofNat 64 c)
      (48 : BitVec 12) (B + 96)
    rw [se48', show (B + 96) + 4 = B + 100 from by bv_omega] at hsd1
    have hsd1L := liftCode (cr' := bansfCR) hsd1
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 96) bansfProg 24 (.SD .x2 .x10 (48 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp (aB + BitVec.ofNat 64 aLen)
      (56 : BitVec 12) (B + 100)
    rw [se56', show (B + 100) + 4 = B + 104 from by bv_omega] at hsd2
    have hsd2L := liftCode (cr' := bansfCR) hsd2
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 100) bansfProg 25 (.SD .x2 .x11 (56 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    have hsd1F := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) ** memOwn (newSp + 56))
      (by pcf) hsd1L
    have hsd2F := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 c)) **
       ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 c)))
      (by pcf) hsd2L
    have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
      hsd1F hsd2F
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq) hchain
  -- the post-init continuation: eliminate the ∃c, run the glue, restate
  have hcont : cpsBranchWithin 2 (B + 96) bansfCR
      (outerInitPost aB aLen acctBytes
        (((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         memOwn (newSp + 48) ** memOwn (newSp + 56) **
         (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
         ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
         ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** F))
      (B + 736) (chainRejB aB newSp oB aLen acctBytes F)
      (B + 104) (chainMidB aB newSp oB aLen acctBytes F) := by
    unfold outerInitPost
    refine cpsBranchWithin_exists_pre (fun c => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hg := hglue c
    have hgF := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
       ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
       ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hg
    have hout : cpsTripleWithin 2 (B + 96) (B + 104) bansfCR
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 c)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
         bytesRegion aB acctBytes **
         (((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          memOwn (newSp + 48) ** memOwn (newSp + 56) **
          (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
          ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
          ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
          ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
          ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) ** F))
        (chainMidB aB newSp oB aLen acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hgF
      unfold chainMidB
      refine ⟨c, ?_⟩
      have hq2 : ((((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 c)) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 c)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) **
          (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
          ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
          ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
          ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
          ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hq
      exact (sepConj_pure_right h).2 ⟨hq2, hok⟩
    exact cpsTripleWithin_as_cpsBranchWithin_right _ _ hout
  -- assemble: prologue ; init-dispatch(+reject weaken) ; glue
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_seq_branch_same_cr hproF
        (cpsBranchWithin_chain_snd
          (cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
            (fun h hq => ?_) (fun _ x => x) hinit)
          hcont)))
  -- the init reject, weakened into the grand SEG-B reject
  unfold outerRej at hq
  unfold chainRejB
  have hq2 : ((((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) **
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 48) ** memOwn (newSp + 56) **
       (oB ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
       ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
       ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       regOwn .x11 ** regOwn .x12 **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes ** F))) h := by
    xperm_hyp hq
  xperm_hyp hq2


/-! ## §2  The four-item chain (B + 104 → B + 184) -/

def acc0 (aB newSp : Word) (aLen off0 : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  fun h => ∃ n0 l0 : Word,
    ((((newSp + 48) ↦ₘ n0) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x10 : Reg) ↦ᵣ n0) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ l0) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜((rlpItemDecode acctBytes off0 (aB + BitVec.ofNat 64 off0)
        (aB + BitVec.ofNat 64 aLen) n0 l0)) ∧
      (n0 - aB).toNat ≤ aLen⌝) h

def acc1 (aB newSp : Word) (aLen off0 : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  fun h => ∃ n0 l0 n1 l1 : Word,
    ((((newSp + 48) ↦ₘ n1) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x10 : Reg) ↦ᵣ n1) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ l1) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜((rlpItemDecode acctBytes off0 (aB + BitVec.ofNat 64 off0)
        (aB + BitVec.ofNat 64 aLen) n0 l0) ∧
      (rlpItemDecode acctBytes ((n0 - aB).toNat) (aB + BitVec.ofNat 64 ((n0 - aB).toNat))
        (aB + BitVec.ofNat 64 aLen) n1 l1)) ∧
      (n1 - aB).toNat ≤ aLen⌝) h

def acc2 (aB newSp : Word) (aLen off0 : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  fun h => ∃ n0 l0 n1 l1 n2 l2 : Word,
    ((((newSp + 48) ↦ₘ n2) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x10 : Reg) ↦ᵣ n2) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ l2) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜(((rlpItemDecode acctBytes off0 (aB + BitVec.ofNat 64 off0)
        (aB + BitVec.ofNat 64 aLen) n0 l0) ∧
      (rlpItemDecode acctBytes ((n0 - aB).toNat) (aB + BitVec.ofNat 64 ((n0 - aB).toNat))
        (aB + BitVec.ofNat 64 aLen) n1 l1)) ∧
      (rlpItemDecode acctBytes ((n1 - aB).toNat) (aB + BitVec.ofNat 64 ((n1 - aB).toNat))
        (aB + BitVec.ofNat 64 aLen) n2 l2)) ∧
      (n2 - aB).toNat ≤ aLen⌝) h

def acc3 (aB newSp : Word) (aLen off0 : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  fun h => ∃ n0 l0 n1 l1 n2 l2 n3 l3 : Word,
    ((((newSp + 48) ↦ₘ n3) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x10 : Reg) ↦ᵣ n3) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ l3) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜((((rlpItemDecode acctBytes off0 (aB + BitVec.ofNat 64 off0)
        (aB + BitVec.ofNat 64 aLen) n0 l0) ∧
      (rlpItemDecode acctBytes ((n0 - aB).toNat) (aB + BitVec.ofNat 64 ((n0 - aB).toNat))
        (aB + BitVec.ofNat 64 aLen) n1 l1)) ∧
      (rlpItemDecode acctBytes ((n1 - aB).toNat) (aB + BitVec.ofNat 64 ((n1 - aB).toNat))
        (aB + BitVec.ofNat 64 aLen) n2 l2)) ∧
      (rlpItemDecode acctBytes ((n2 - aB).toNat) (aB + BitVec.ofNat 64 ((n2 - aB).toNat))
        (aB + BitVec.ofNat 64 aLen) n3 l3)) ∧
      (n3 - aB).toNat ≤ aLen⌝) h

/-- Items 0–3 chained (`B + 104 → B + 184`), from the item-0-ready state at
    offset `off0`, accumulating the outer `rlpItemDecode` chain. -/
theorem bansf_chainItems_spec (aB newSp : Word) (aLen off0 : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoff0le : off0 ≤ aLen) :
    cpsBranchWithin 372 (B + 104) bansfCR
      (((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off0)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off0)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes ** F)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 184) (acc3 aB newSp aLen off0 acctBytes F) := by
  have hover9 : aB.toNat + aLen + 9 < 2 ^ 64 := by omega
  -- ===== item 0 =====
  have hstep0 : cpsBranchWithin 93 (B + 104) bansfCR
      (((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off0)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off0)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes ** F)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 124) (acc0 aB newSp aLen off0 acctBytes F) := by
    refine cpsBranchWithin_weaken
      (Q_f := itemOk aB newSp aLen off0 acctBytes F)
      (P := ((((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off0)) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off0)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
      (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun h hq => ?_) ?_
    · unfold itemOk at hq
      obtain ⟨next, len, hqq⟩ := hq
      obtain ⟨hA, hdec⟩ := (sepConj_pure_right h).1 hqq
      have hadv := rlpItemDecode_advance (bytes := acctBytes) (base := aB)
        (off := off0) (endOff := aLen) hdec hoff0le hover9
      refine ⟨next, len, ?_⟩
      have hA' : ((((newSp + 48) ↦ₘ next) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hA
      exact (sepConj_pure_right h).2 ⟨hA', hdec, hadv.2.2⟩
    · refine cpsBranchWithin_of_forall_regIs_to_regOwn8
        (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
      exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ x => x) (fun _ x => x)
        (bansf_item0_spec aB newSp aLen off0 acctBytes
          v5 v6 v7 (aB + BitVec.ofNat 64 off0) (aB + BitVec.ofNat 64 aLen) (0 : Word)
          v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid hoff0le)
  -- ===== item 1 at the advanced cursor =====
  have hstep1 : cpsBranchWithin 93 (B + 124) bansfCR
      (acc0 aB newSp aLen off0 acctBytes F)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 144) (acc1 aB newSp aLen off0 acctBytes F) := by
    unfold acc0
    refine cpsBranchWithin_exists_pre (fun n0 => ?_)
    refine cpsBranchWithin_exists_pre (fun l0 => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdecs => ?_)
    obtain ⟨hchain, hbound⟩ := hdecs
    have hrep : n0 = aB + BitVec.ofNat 64 ((n0 - aB).toNat) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    refine cpsBranchWithin_weaken
      (Q_f := itemOk aB newSp aLen ((n0 - aB).toNat) acctBytes F)
      (P := ((((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 ((n0 - aB).toNat))) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n0 - aB).toNat))) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ l0) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
      (fun h hp => by rw [← hrep]; xperm_hyp hp)
      (fun _ x => x) (fun h hq => ?_) ?_
    · -- accumulate the new decode and its bound
      unfold itemOk at hq
      obtain ⟨next, len, hqq⟩ := hq
      obtain ⟨hA, hdnew⟩ := (sepConj_pure_right h).1 hqq
      have hadv := rlpItemDecode_advance (bytes := acctBytes) (base := aB)
        (off := ((n0 - aB).toNat)) (endOff := aLen) hdnew hbound hover9
      refine ⟨n0, l0, next, len, ?_⟩
      have hA' : ((((newSp + 48) ↦ₘ next) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hA
      exact (sepConj_pure_right h).2 ⟨hA', ⟨hchain, hdnew⟩, hadv.2.2⟩
    · refine cpsBranchWithin_of_forall_regIs_to_regOwn8
        (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
      exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ x => x) (fun _ x => x)
        (bansf_item1_spec aB newSp aLen ((n0 - aB).toNat) acctBytes
          v5 v6 v7 (aB + BitVec.ofNat 64 ((n0 - aB).toNat)) (0 : Word) l0
          v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid hbound)
  -- ===== item 2 at the advanced cursor =====
  have hstep2 : cpsBranchWithin 93 (B + 144) bansfCR
      (acc1 aB newSp aLen off0 acctBytes F)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 164) (acc2 aB newSp aLen off0 acctBytes F) := by
    unfold acc1
    refine cpsBranchWithin_exists_pre (fun n0 => ?_)
    refine cpsBranchWithin_exists_pre (fun l0 => ?_)
    refine cpsBranchWithin_exists_pre (fun n1 => ?_)
    refine cpsBranchWithin_exists_pre (fun l1 => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdecs => ?_)
    obtain ⟨hchain, hbound⟩ := hdecs
    have hrep : n1 = aB + BitVec.ofNat 64 ((n1 - aB).toNat) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    refine cpsBranchWithin_weaken
      (Q_f := itemOk aB newSp aLen ((n1 - aB).toNat) acctBytes F)
      (P := ((((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 ((n1 - aB).toNat))) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n1 - aB).toNat))) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ l1) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
      (fun h hp => by rw [← hrep]; xperm_hyp hp)
      (fun _ x => x) (fun h hq => ?_) ?_
    · -- accumulate the new decode and its bound
      unfold itemOk at hq
      obtain ⟨next, len, hqq⟩ := hq
      obtain ⟨hA, hdnew⟩ := (sepConj_pure_right h).1 hqq
      have hadv := rlpItemDecode_advance (bytes := acctBytes) (base := aB)
        (off := ((n1 - aB).toNat)) (endOff := aLen) hdnew hbound hover9
      refine ⟨n0, l0, n1, l1, next, len, ?_⟩
      have hA' : ((((newSp + 48) ↦ₘ next) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hA
      exact (sepConj_pure_right h).2 ⟨hA', ⟨hchain, hdnew⟩, hadv.2.2⟩
    · refine cpsBranchWithin_of_forall_regIs_to_regOwn8
        (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
      exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ x => x) (fun _ x => x)
        (bansf_item2_spec aB newSp aLen ((n1 - aB).toNat) acctBytes
          v5 v6 v7 (aB + BitVec.ofNat 64 ((n1 - aB).toNat)) (0 : Word) l1
          v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid hbound)
  -- ===== item 3 at the advanced cursor =====
  have hstep3 : cpsBranchWithin 93 (B + 164) bansfCR
      (acc2 aB newSp aLen off0 acctBytes F)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 184) (acc3 aB newSp aLen off0 acctBytes F) := by
    unfold acc2
    refine cpsBranchWithin_exists_pre (fun n0 => ?_)
    refine cpsBranchWithin_exists_pre (fun l0 => ?_)
    refine cpsBranchWithin_exists_pre (fun n1 => ?_)
    refine cpsBranchWithin_exists_pre (fun l1 => ?_)
    refine cpsBranchWithin_exists_pre (fun n2 => ?_)
    refine cpsBranchWithin_exists_pre (fun l2 => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdecs => ?_)
    obtain ⟨hchain, hbound⟩ := hdecs
    have hrep : n2 = aB + BitVec.ofNat 64 ((n2 - aB).toNat) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    refine cpsBranchWithin_weaken
      (Q_f := itemOk aB newSp aLen ((n2 - aB).toNat) acctBytes F)
      (P := ((((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 ((n2 - aB).toNat))) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n2 - aB).toNat))) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ l2) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
      (fun h hp => by rw [← hrep]; xperm_hyp hp)
      (fun _ x => x) (fun h hq => ?_) ?_
    · -- accumulate the new decode and its bound
      unfold itemOk at hq
      obtain ⟨next, len, hqq⟩ := hq
      obtain ⟨hA, hdnew⟩ := (sepConj_pure_right h).1 hqq
      have hadv := rlpItemDecode_advance (bytes := acctBytes) (base := aB)
        (off := ((n2 - aB).toNat)) (endOff := aLen) hdnew hbound hover9
      refine ⟨n0, l0, n1, l1, n2, l2, next, len, ?_⟩
      have hA' : ((((newSp + 48) ↦ₘ next) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hA
      exact (sepConj_pure_right h).2 ⟨hA', ⟨hchain, hdnew⟩, hadv.2.2⟩
    · refine cpsBranchWithin_of_forall_regIs_to_regOwn8
        (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
      exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ x => x) (fun _ x => x)
        (bansf_item3_spec aB newSp aLen ((n2 - aB).toNat) acctBytes
          v5 v6 v7 (aB + BitVec.ofNat 64 ((n2 - aB).toNat)) (0 : Word) l2
          v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid hbound)
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_chain_snd hstep0
      (cpsBranchWithin_chain_snd hstep1
        (cpsBranchWithin_chain_snd hstep2 hstep3)))


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
