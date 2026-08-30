import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Rv64.RLP.WalkNextStrict
import EvmAsm.Rv64.CPSCall
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame

namespace EvmAsm.Codegen.RlpWalkNextStrictTie

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-- Guest entry of the strict wrapper's shared body. -/
abbrev S : Word := (GuestAddrs.rlp_walk_next_shared : Word)

/-- Guest entry of the lenient 412-byte core. -/
abbrev C : Word := (GuestAddrs.rlp_walk_next_core : Word)

/-! Code requirements are parameterized by the same depth cap consumed by the
    shared program.  The default alias is the linked Amsterdam instantiation;
    cap-sensitive contracts use `sharedCodeWithCap` directly. -/
def sharedCodeWithCap (depthCap : Word) : CodeReq :=
  CodeReq.ofProg S (rlpWalkNextShared_prog_with_cap depthCap)

/- Keep the historical default requirement directly tied to the default Program
   so existing fixed-address block proofs continue to reduce cheaply.  Generic
   cap-sensitive contracts use `sharedCodeWithCap` above. -/
abbrev sharedCode : CodeReq := CodeReq.ofProg S rlpWalkNextShared_prog

/-- `pcf` closes `P.pcFree` for the atoms used in this module. -/
local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

theorem shared_length : rlpWalkNextShared_prog.length = 52 := rfl

theorem shared_length_with_cap (depthCap : Word) :
    (rlpWalkNextShared_prog_with_cap depthCap).length = 52 := rfl

/-- The Codegen transcription of the core is literally the verified core body. -/
theorem core_prog_eq : rlpWalkNextCore_prog = rlp_walk_next_prog := rfl

/-! ## Epilogue block (indices 46..51): reload the saved outputs and return. -/

theorem tail_block (sp raVal w1 w10 w11 w12 v10 v11 v12 : Word) :
    cpsTripleWithin 6 (S + 184) (raVal &&& ~~~1) sharedCode
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ w10) ** (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ w12) ** (.x1 ↦ᵣ w1) **
       ((sp + 24) ↦ₘ v10) ** ((sp + 32) ↦ₘ v11) ** ((sp + 40) ↦ₘ v12) ** (sp ↦ₘ raVal))
      ((.x2 ↦ᵣ (sp + 64)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x1 ↦ᵣ raVal) **
       ((sp + 24) ↦ₘ v10) ** ((sp + 32) ↦ₘ v11) ** ((sp + 40) ↦ₘ v12) ** (sp ↦ₘ raVal)) := by
  have h46 := ld_spec_gen_within .x10 .x2 sp w10 v10 (24 : BitVec 12) (S + 184) (by decide)
  have h47 := ld_spec_gen_within .x11 .x2 sp w11 v11 (32 : BitVec 12) (S + 188) (by decide)
  have h48 := ld_spec_gen_within .x12 .x2 sp w12 v12 (40 : BitVec 12) (S + 192) (by decide)
  have h49 := ld_spec_gen_within .x1 .x2 sp w1 raVal (0 : BitVec 12) (S + 196) (by decide)
  have h50 := addi_spec_gen_same_within .x2 sp (64 : BitVec 12) (S + 200) (by decide)
  have h51 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (S + 204)
  runBlock h46 h47 h48 h49 h50 h51

/-! ## Prologue block (indices 0..3): open the 64-byte frame and spill ra/a0/a1. -/

theorem prologue_block (sp raVal cursor endPtr : Word) :
    cpsTripleWithin 4 S (S + 16) sharedCode
      ((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ raVal) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16))
      ((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ raVal) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
       (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ cursor) ** ((sp + 16) ↦ₘ endPtr)) := by
  have h0 := addi_spec_gen_same_within .x2 (sp + 64) (-64 : BitVec 12) S (by decide)
  rw [show (sp + 64) + signExtend12 (-64 : BitVec 12) = sp from by
        rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide]; bv_omega] at h0
  have h1 := sd_spec_gen_own_within .x2 .x1 sp raVal (0 : BitVec 12) (S + 4)
  have h2 := sd_spec_gen_own_within .x2 .x10 sp cursor (8 : BitVec 12) (S + 8)
  have h3 := sd_spec_gen_own_within .x2 .x11 sp endPtr (16 : BitVec 12) (S + 12)
  runBlock h0 h1 h2 h3

/-! ## Spill block (indices 5..7): save the core's `a0/a1/a2` into the frame. -/

theorem spill_block (sp a0 a1 a2 : Word) :
    cpsTripleWithin 3 (S + 20) (S + 32) sharedCode
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40))
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
       ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2)) := by
  have h5 := sd_spec_gen_own_within .x2 .x10 sp a0 (24 : BitVec 12) (S + 20)
  have h6 := sd_spec_gen_own_within .x2 .x11 sp a1 (32 : BitVec 12) (S + 24)
  have h7 := sd_spec_gen_own_within .x2 .x12 sp a2 (40 : BitVec 12) (S + 28)
  runBlock h5 h6 h7

/-! ## Status branch (index 8): a nonzero core status short-circuits to the epilogue. -/

theorem status_branch (status : Word) :
    cpsBranchWithin 1 (S + 32) sharedCode
      ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)))
      (S + 184) ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status ≠ 0⌝)
      (S + 36) ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status = 0⌝) := by
  have h := bne_spec_gen_within .x11 .x0 (152 : BitVec 13) status (0 : Word) (S + 32)
  rw [show (S + 32) + signExtend13 (152 : BitVec 13) = S + 184 from by
        rw [show signExtend13 (152 : BitVec 13) = (152 : Word) from by decide]; bv_omega,
      show S + 32 + 4 = S + 36 from by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr S rlpWalkNextShared_prog 8 (S + 32)
      (by rw [shared_length]; norm_num) (by rw [shared_length]; norm_num) (by bv_omega))) h

/-! ## Recursion-budget branch (index 10) and prefix-class branch (index 15). -/

theorem budget_branch (budget v5 : Word) :
    cpsBranchWithin 1 (S + 40) sharedCode
      ((.x8 ↦ᵣ budget) ** (.x5 ↦ᵣ v5))
      (S + 168) ((.x8 ↦ᵣ budget) ** (.x5 ↦ᵣ v5) ** ⌜BitVec.ult budget v5⌝)
      (S + 44) ((.x8 ↦ᵣ budget) ** (.x5 ↦ᵣ v5) ** ⌜¬ BitVec.ult budget v5⌝) := by
  have h := bltu_spec_gen_within .x8 .x5 (128 : BitVec 13) budget v5 (S + 40)
  rw [show (S + 40) + signExtend13 (128 : BitVec 13) = S + 168 from by
        rw [show signExtend13 (128 : BitVec 13) = (128 : Word) from by decide]; bv_omega,
      show S + 40 + 4 = S + 44 from by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr S rlpWalkNextShared_prog 10 (S + 40)
      (by rw [shared_length]; norm_num) (by rw [shared_length]; norm_num) (by bv_omega))) h

theorem prefix_branch (pfx v7 : Word) :
    cpsBranchWithin 1 (S + 60) sharedCode
      ((.x6 ↦ᵣ pfx) ** (.x7 ↦ᵣ v7))
      (S + 184) ((.x6 ↦ᵣ pfx) ** (.x7 ↦ᵣ v7) ** ⌜BitVec.ult pfx v7⌝)
      (S + 64) ((.x6 ↦ᵣ pfx) ** (.x7 ↦ᵣ v7) ** ⌜¬ BitVec.ult pfx v7⌝) := by
  have h := bltu_spec_gen_within .x6 .x7 (124 : BitVec 13) pfx v7 (S + 60)
  rw [show (S + 60) + signExtend13 (124 : BitVec 13) = S + 184 from by
        rw [show signExtend13 (124 : BitVec 13) = (124 : Word) from by decide]; bv_omega,
      show S + 60 + 4 = S + 64 from by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr S rlpWalkNextShared_prog 15 (S + 60)
      (by rw [shared_length]; norm_num) (by rw [shared_length]; norm_num) (by bv_omega))) h

/-! ## `LI t0, 2` (index 9). -/

theorem li2_block (v5 : Word) :
    cpsTripleWithin 1 (S + 36) (S + 40) sharedCode ((.x5 ↦ᵣ v5)) ((.x5 ↦ᵣ (2 : Word))) := by
  have h := li_spec_gen_within .x5 v5 (2 : Word) (S + 36) (by decide)
  runBlock h

theorem li2_block_own :
    cpsTripleWithin 1 (S + 36) (S + 40) sharedCode (regOwn .x5) ((.x5 ↦ᵣ (2 : Word))) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn_single li2_block

/-! ## Reload-and-classify block (indices 11..14): decrement the recursion budget,
    reload the item cursor from the frame, and load the item's prefix byte. -/

theorem classify_block (sp srcBase budget v6 v7 : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin 4 (S + 44) (S + 60) sharedCode
      ((.x8 ↦ᵣ budget) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) **
       ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
       bytesRegion srcBase srcBytes ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7))
      ((.x8 ↦ᵣ (budget - 2)) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) ** (.x7 ↦ᵣ (192 : Word)) **
       ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
       bytesRegion srcBase srcBytes) := by
  have h11 := addi_spec_gen_same_within .x8 budget (-2 : BitVec 12) (S + 44) (by decide)
  rw [show budget + signExtend12 (-2 : BitVec 12) = budget - 2 from by
        rw [show signExtend12 (-2 : BitVec 12) = (-2 : Word) from by decide]; bv_omega] at h11
  have h12 := ld_spec_gen_within .x5 .x2 sp (2 : Word) (srcBase + BitVec.ofNat 64 srcOff)
    (8 : BitVec 12) (S + 48) (by decide)
  have h13 := bytesRegion_lbu_within .x6 .x5 srcBase v6 (S + 52) srcBytes srcOff (by decide)
    hsalign hoff hover hvalid
  have h14 := li_spec_gen_within .x7 v7 (192 : Word) (S + 56) (by decide)
  runBlock h11 h12 h13 h14

theorem classify_block_own (sp srcBase budget : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin 4 (S + 44) (S + 60) sharedCode
      ((.x8 ↦ᵣ budget) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) **
       ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
       bytesRegion srcBase srcBytes ** regOwn .x6 ** regOwn .x7)
      ((.x8 ↦ᵣ (budget - 2)) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) ** (.x7 ↦ᵣ (192 : Word)) **
       ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
       bytesRegion srcBase srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x8 ↦ᵣ budget) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) **
        ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
        bytesRegion srcBase srcBytes ** regOwn .x6)
      (r := .x7) (fun v7 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x8 ↦ᵣ budget) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) **
        ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
        bytesRegion srcBase srcBytes ** (.x7 ↦ᵣ v7))
      (r := .x6) (fun v6 => ?_))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (classify_block sp srcBase budget v6 v7 srcBytes srcOff hsalign hoff hover hvalid)

/-! ## The two-program code requirement: wrapper body plus lenient core. -/

/-! `coreCode` is deliberately built from the production Codegen Program.  The
    verified core is obtained only through the theorem immediately below; this
    keeps the caller-side CPS code requirement anchored to the emitted body
    instead of silently selecting the retired/offline validator Program. -/
abbrev coreCode : CodeReq := CodeReq.ofProg C rlpWalkNextCore_prog

abbrev fullCode : CodeReq := sharedCode.union coreCode

theorem shared_core_disjoint : sharedCode.Disjoint coreCode :=
  CodeReq.ofProg_disjoint_range_len S rlpWalkNextShared_prog 52 C rlpWalkNextCore_prog 103
    shared_length (by decide) (by
      intro k1 k2 h1 h2 heq
      have hS : S.toNat = GuestAddrs.rlp_walk_next_shared := by decide
      have hC : C.toNat = GuestAddrs.rlp_walk_next_core := by decide
      simp only [GuestAddrs.rlp_walk_next_shared, GuestAddrs.rlp_walk_next_core] at hS hC
      have h := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hS, hC] at h
      omega)

theorem shared_sub : ∀ a i, sharedCode a = some i → fullCode a = some i :=
  CodeReq.union_mono_left

theorem core_sub : ∀ a i, coreCode a = some i → fullCode a = some i := by
  intro a i h
  rcases shared_core_disjoint a with h1 | h2
  · simp only [fullCode, CodeReq.union, h1, h]
  · rw [h2] at h; exact absurd h (by simp)

/-! ## Production core adapter

`coreCode` is the linked production Program, not the retired validator
Program.  Keep this adapter at the Codegen boundary so callers can lift the
verified core triple into their enclosing production `CodeReq` without
reintroducing the offline `rlpValidatePayloadOffline_prog` at `C`.  The
`rlpWalkNextCoreCode_eq_verified` tie is deliberately symbolic: it identifies
the Codegen Program with the verified body at the production `GuestAddrs`
entry, while the separate image gates establish the Program/image relation. -/

theorem coreCode_eq_verified :
    coreCode = EvmAsm.Rv64.RLP.rlp_walk_next_code C := by
  exact EvmAsm.Codegen.rlpWalkNextCoreCode_eq_verified

theorem production_core_code_lift
    {n : Nat} {exit_ : Word} {wholeCode : CodeReq} {P Q : Assertion}
    (hsub : ∀ a i, coreCode a = some i → wholeCode a = some i)
    (hcore : cpsTripleWithin n C exit_ coreCode P Q) :
    cpsTripleWithin n C exit_ wholeCode P Q :=
  cpsTripleWithin_extend_code hsub hcore

theorem rlp_walk_next_core_production_spec_within
    (srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true →
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)) = (1 : Word) →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin 87 C (raVal &&& ~~~1) coreCode
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
              (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
              (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
              (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
         (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
              (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h))) := by
  rw [coreCode_eq_verified]
  exact EvmAsm.Rv64.RLP.rlp_walk_next_spec_within
    C srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    srcBytes srcOff hsalign hoff hover hvalid hss hls hll

/-! ## Call block (index 4): `jal ra, rlp_walk_next_core`. -/

theorem call_core {n : Nat} {Prest Q : Assertion} (oldRa : Word)
    (h_pre : Prest.pcFree)
    (h_callee : cpsTripleWithin n C ((S + 20) &&& ~~~(1 : Word))
      coreCode ((.x1 ↦ᵣ (S + 20)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (S + 16) (S + 20) fullCode ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  rw [show (S + 20 : Word) = S + 16 + 4 from by bv_omega] at h_callee ⊢
  have h_call := WP.cpsCallWithin
    (nSteps := n) (callerPC := S + 16) (calleeEntry := C) (vOld := oldRa)
    (calleeCode := coreCode) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next_core (GuestAddrs.rlp_walk_next_shared + 16))
    (by decide) (by decide) h_pre
    (CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len C rlpWalkNextCore_prog 103 (S + 16)
        (by decide) (by
          intro k hk heq
          have hS16 : (S + 16).toNat = GuestAddrs.rlp_walk_next_shared + 16 := by decide
          have hC : C.toNat = GuestAddrs.rlp_walk_next_core := by decide
          simp only [GuestAddrs.rlp_walk_next_shared, GuestAddrs.rlp_walk_next_core] at hS16 hC
          have h := congrArg BitVec.toNat heq
          rw [hS16] at h
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hC] at h
          omega))) h_callee
  refine cpsTripleWithin_extend_code (CodeReq.union_split_mono ?_ core_sub) h_call
  exact fun a i h_code => shared_sub a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr S rlpWalkNextShared_prog 4 (S + 16)
      (by rw [shared_length]; norm_num) (by rw [shared_length]; norm_num) (by bv_omega))
      a i h_code)

/-! ## Error continuation: a nonzero core status is returned unchanged. -/

theorem contErr (sp raVal a0 a1 a2 : Word) (ha1 : a1 ≠ 0) :
    cpsTripleWithin 10 (S + 20) (raVal &&& ~~~1) sharedCode
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) ** (sp ↦ₘ raVal))
      ((.x2 ↦ᵣ (sp + 64)) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** (sp ↦ₘ raVal)) := by
  have h1 := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) ** (sp ↦ₘ raVal)) (by pcf)
    (spill_block sp a0 a1 a2)
  have hbr0 := cpsBranchWithin_takenPath (status_branch a1)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      exact ha1 ((sepConj_pure_right _).1 hpure).2)
  have hbr := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) hbr0
  have h2 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x1 ↦ᵣ (S + 20)) **
     ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** (sp ↦ₘ raVal))
    (by pcf) hbr
  have h3 := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf)
    (tail_block sp raVal (S + 20) a0 a1 a2 a0 a1 a2)
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1 h2
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 h3
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h123)

/-! ## Accept continuation for a NON-LIST item.

    The core reported status `0`; the wrapper reloads the item cursor, re-reads the
    prefix byte from the input region and finds it below `0xc0`, so the branch at
    index 15 jumps straight to the epilogue — `rlp_validate_payload` is never
    entered and no recursion happens on this path. -/

def contOkCorePre (sp raVal srcBase endPtr budget a0 len : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
   (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) ** (.x8 ↦ᵣ budget) **
   regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
   (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
   ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes)

def contOkCorePost (sp raVal srcBase endPtr budget a0 len : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hoff : srcOff < srcBytes.length) : Assertion :=
  ((.x2 ↦ᵣ (sp + 64)) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
   (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ (budget - 2)) **
   (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
   (.x6 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) **
   (.x7 ↦ᵣ (192 : Word)) **
   ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
   (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
   ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes)

theorem contOk (sp raVal srcBase endPtr budget a0 len : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hbudget : ¬ BitVec.ult budget (2 : Word))
    (hpfx : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word)) :
    cpsTripleWithin 17 (S + 20) (raVal &&& ~~~1) sharedCode
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) ** (.x8 ↦ᵣ budget) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x13 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes)
      ((.x2 ↦ᵣ (sp + 64)) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ (budget - 2)) **
       (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       regOwn .x9 ** regOwn .x13 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 **
       (.x6 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) ** (.x7 ↦ᵣ (192 : Word)) **
       ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
       (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes) := by
  let clobberRest : Assertion :=
    regOwn .x9 ** regOwn .x13 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31
  have hclobber : clobberRest.pcFree := by
    simp only [clobberRest]
    pcf
  suffices hbase : cpsTripleWithin 17 (S + 20) (raVal &&& ~~~1) sharedCode
      (contOkCorePre sp raVal srcBase endPtr budget a0 len srcBytes srcOff)
      (contOkCorePost sp raVal srcBase endPtr budget a0 len srcBytes srcOff hoff) by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [clobberRest, contOkCorePre] at hp ⊢
        xperm_hyp hp)
      (fun _ hp => by
        simp only [clobberRest, contOkCorePost] at hp ⊢
        xperm_hyp hp)
      (cpsTripleWithin_frameR clobberRest hclobber hbase)
  simp only [contOkCorePre, contOkCorePost]
  -- index 5..7
  have h1 := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) ** (.x8 ↦ᵣ budget) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (sp ↦ₘ raVal) **
     ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
     bytesRegion srcBase srcBytes) (by pcf) (spill_block sp a0 (0 : Word) len)
  -- index 8 (not taken: status is 0)
  have hstat0 := cpsBranchWithin_ntakenPath (status_branch (0 : Word))
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      exact ((sepConj_pure_right _).1 hpure).2 rfl)
  have hstat := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) hstat0
  have h2 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (S + 20)) **
     (.x8 ↦ᵣ budget) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
     (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes) (by pcf) hstat
  -- index 9
  have h3 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) ** (.x8 ↦ᵣ budget) **
     regOwn .x6 ** regOwn .x7 **
     ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
     (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes) (by pcf) li2_block_own
  -- index 10 (not taken: the recursion budget is at least 2)
  have hbud0 := cpsBranchWithin_ntakenPath (budget_branch budget (2 : Word))
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      exact hbudget ((sepConj_pure_right _).1 hpure).2)
  have hbud := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) hbud0
  have h4 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) ** regOwn .x6 ** regOwn .x7 **
     ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
     (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes) (by pcf) hbud
  -- index 11..14
  have h5 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) **
     ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
     (sp ↦ₘ raVal) ** ((sp + 16) ↦ₘ endPtr)) (by pcf)
    (classify_block_own sp srcBase budget srcBytes srcOff hsalign hoff hover hvalid)
  -- index 15 (taken: the prefix is below 0xc0, so the item is not a list)
  have hpre0 := cpsBranchWithin_takenPath
    (prefix_branch ((srcBytes[srcOff]'hoff).zeroExtend 64) (192 : Word))
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      exact ((sepConj_pure_right _).1 hpure).2 hpfx)
  have hpre := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) hpre0
  have h6 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) ** (.x8 ↦ᵣ (budget - 2)) **
     (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
     ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
     (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
     ((sp + 16) ↦ₘ endPtr) ** bytesRegion srcBase srcBytes) (by pcf) hpre
  -- index 46..51
  have h7 := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ (budget - 2)) **
     (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
     (.x6 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) ** (.x7 ↦ᵣ (192 : Word)) **
     ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
     bytesRegion srcBase srcBytes) (by pcf)
    (tail_block sp raVal (S + 20) a0 (0 : Word) len a0 (0 : Word) len)
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1 h2
  have c13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 h3
  have c14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c13 h4
  have c15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c14 h5
  have c16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c15 h6
  have c17 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c16 h7
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) c17)

/-! ## Direct inhabitance of the strengthened continuation precondition.

    The top-level closed instance below witnesses a composed run.  This
    separate resource witness targets `contOk` itself, so the frame that adds
    x9/x13 and x28--x31 cannot hide an overlap in a vacuous precondition. -/

private def contOkWitnessBytes : List Byte := [0x83, 0x01, 0x02, 0x03]

private def contOkWitnessRegs : List (Reg × Word) :=
  [(.x2, 0xa0000100), (.x10, 0x40000004), (.x11, 0), (.x12, 3),
   (.x0, 0), (.x1, S + 20), (.x8, 2),
   (.x5, 0), (.x6, 0), (.x7, 0), (.x9, 0), (.x13, 0),
   (.x28, 0), (.x29, 0), (.x30, 0), (.x31, 0)]

private def contOkWitnessRegAtom (p : Reg × Word) : Assertion :=
  if p.1 == .x5 || p.1 == .x6 || p.1 == .x7 || p.1 == .x9 || p.1 == .x13 ||
      p.1 == .x28 || p.1 == .x29 || p.1 == .x30 || p.1 == .x31 then
    regOwn p.1
  else
    p.1 ↦ᵣ p.2

private def contOkWitnessRegHeap (p : Reg × Word) : PartialState :=
  PartialState.singletonReg p.1 p.2

private def contOkWitnessRegAssertion : Assertion :=
  contOkWitnessRegs.foldr (fun p acc => contOkWitnessRegAtom p ** acc) empAssertion

private def contOkWitnessRegHeapFold : PartialState :=
  contOkWitnessRegs.foldr
    (fun p acc => (contOkWitnessRegHeap p).union acc) PartialState.empty

private theorem contOkWitnessRegSingletonDisjoint
    {r1 r2 : Reg} {v1 v2 : Word} (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem contOkWitnessReg_sat :
    contOkWitnessRegAssertion contOkWitnessRegHeapFold := by
  apply EvmAsm.Rv64.SAsm.sepConj_foldr_satisfiable
    contOkWitnessRegAtom contOkWitnessRegHeap contOkWitnessRegs
  · intro p hp
    by_cases h_own : p.1 == .x5 || p.1 == .x6 || p.1 == .x7 || p.1 == .x9 ||
        p.1 == .x13 || p.1 == .x28 || p.1 == .x29 || p.1 == .x30 || p.1 == .x31
    · rw [show contOkWitnessRegAtom p = regOwn p.1 by
          simp [contOkWitnessRegAtom, h_own]]
      exact ⟨p.2, rfl⟩
    · rw [show contOkWitnessRegAtom p = regIs p.1 p.2 by
          simp [contOkWitnessRegAtom, h_own]]
      rfl
  · have hd : contOkWitnessRegs.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h => contOkWitnessRegSingletonDisjoint h) hd

private def contOkWitnessMems : List (Word × Word) :=
  [((0xa0000100 : Word) + 24, 0), ((0xa0000100 : Word) + 32, 0),
   ((0xa0000100 : Word) + 40, 3),
   (0xa0000100, 0xa0000000),
   ((0xa0000100 : Word) + 8, 0x40000000),
   ((0xa0000100 : Word) + 16, (0x40000000 : Word) + 4),
   (0x40000000, packBytes contOkWitnessBytes)]

private def contOkWitnessMemAtom (p : Word × Word) : Assertion :=
  if p.1 == (0xa0000100 : Word) + 24 || p.1 == (0xa0000100 : Word) + 32 ||
      p.1 == (0xa0000100 : Word) + 40 then
    memOwn p.1
  else
    p.1 ↦ₘ p.2

private def contOkWitnessMemHeap (p : Word × Word) : PartialState :=
  PartialState.singletonMem p.1 p.2

private def contOkWitnessMemAssertion : Assertion :=
  contOkWitnessMems.foldr (fun p acc => contOkWitnessMemAtom p ** acc) empAssertion

private def contOkWitnessMemHeapFold : PartialState :=
  contOkWitnessMems.foldr
    (fun p acc => (contOkWitnessMemHeap p).union acc) PartialState.empty

private theorem contOkWitnessMemSingletonDisjoint
    {a1 a2 : Word} {v1 v2 : Word} (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem contOkWitnessMem_sat :
    contOkWitnessMemAssertion contOkWitnessMemHeapFold := by
  apply EvmAsm.Rv64.SAsm.sepConj_foldr_satisfiable
    contOkWitnessMemAtom contOkWitnessMemHeap contOkWitnessMems
  · intro p hp
    rcases p with ⟨a, v⟩
    simp [contOkWitnessMems] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp [contOkWitnessMemAtom, contOkWitnessMemHeap, memOwn, memIs,
        PartialState.singletonMem]
      first
      | exact ⟨⟨0, rfl⟩, by decide⟩
      | exact ⟨⟨3, rfl⟩, by decide⟩
      | decide
  · have hd : contOkWitnessMems.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h => contOkWitnessMemSingletonDisjoint h) hd

private def contOkWitnessAssertion : Assertion :=
  contOkWitnessRegAssertion ** contOkWitnessMemAssertion

private def contOkWitnessHeap : PartialState :=
  contOkWitnessRegHeapFold.union contOkWitnessMemHeapFold

private theorem contOkWitness_cross :
    ∀ p ∈ contOkWitnessRegs, ∀ q ∈ contOkWitnessMems,
      (contOkWitnessRegHeap p).Disjoint (contOkWitnessMemHeap q) := by
  intro p hp q hq
  unfold contOkWitnessRegHeap contOkWitnessMemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem contOkWitness_sat :
    contOkWitnessAssertion contOkWitnessHeap := by
  exact EvmAsm.Rv64.SAsm.sepConj_foldr_cross_satisfiable
    contOkWitnessRegAtom contOkWitnessRegHeap contOkWitnessRegs
    contOkWitnessMemAtom contOkWitnessMemHeap contOkWitnessMems
    contOkWitnessReg_sat contOkWitnessMem_sat contOkWitness_cross

theorem contOk_pre_non_degenerate_inhabited :
    ∃ h : PartialState,
      ((.x2 ↦ᵣ (0xa0000100 : Word)) **
       (.x10 ↦ᵣ ((0x40000000 : Word) + 4)) ** (.x11 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ (3 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x1 ↦ᵣ (S + 20)) ** (.x8 ↦ᵣ (2 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x13 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       memOwn ((0xa0000100 : Word) + 24) **
       memOwn ((0xa0000100 : Word) + 32) **
       memOwn ((0xa0000100 : Word) + 40) **
       ((0xa0000100 : Word) ↦ₘ (0xa0000000 : Word)) **
       (((0xa0000100 : Word) + 8) ↦ₘ (0x40000000 : Word)) **
       (((0xa0000100 : Word) + 16) ↦ₘ ((0x40000000 : Word) + 4)) **
       bytesRegion (0x40000000 : Word) contOkWitnessBytes) h := by
  refine ⟨contOkWitnessHeap, ?_⟩
  simpa [contOkWitnessAssertion, contOkWitnessHeap,
    contOkWitnessRegAssertion, contOkWitnessRegHeapFold, contOkWitnessRegHeap,
    contOkWitnessRegs, contOkWitnessRegAtom, contOkWitnessMemAssertion,
    contOkWitnessMemHeapFold, contOkWitnessMemHeap, contOkWitnessMems,
    contOkWitnessMemAtom, contOkWitnessBytes, bytesRegion, bytesRegionAux,
    sepConj_emp_right', sepConj_assoc'] using contOkWitness_sat

/-! ## Generic elimination rules used to consume the core's six-way outcome. -/

theorem cpsTripleWithin_or_pre {n : Nat} {e x : Word} {cr : CodeReq} {Q P1 P2 : Assertion}
    (h1 : cpsTripleWithin n e x cr P1 Q) (h2 : cpsTripleWithin n e x cr P2 Q) :
    cpsTripleWithin n e x cr (fun hp => P1 hp ∨ P2 hp) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, g1, g2, hd, hu, hP, hR2⟩ := hPR
  rcases hP with hP | hP
  · exact h1 R hR s hcr ⟨hp, hcompat, g1, g2, hd, hu, hP, hR2⟩ hpc
  · exact h2 R hR s hcr ⟨hp, hcompat, g1, g2, hd, hu, hP, hR2⟩ hpc

theorem cpsTripleWithin_exists_pre {α : Type} {n : Nat} {e x : Word} {cr : CodeReq}
    {Q : Assertion} {P : α → Assertion}
    (h : ∀ a, cpsTripleWithin n e x cr (P a) Q) :
    cpsTripleWithin n e x cr (fun hp => ∃ a, P a hp) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, g1, g2, hd, hu, ⟨a, hP⟩, hR2⟩ := hPR
  exact h a R hR s hcr ⟨hp, hcompat, g1, g2, hd, hu, hP, hR2⟩ hpc

/-- Read a pure fact out of the precondition and use it to strengthen the post.
    Unlike `cpsTripleWithin_strip_pure_and_convert` this does not require the
    pure atom to sit at the top of the `**` chain. -/
theorem cpsTripleWithin_of_pure_extract {n : Nat} {e x : Word} {cr : CodeReq}
    {P Q Q' : Assertion} {fact : Prop}
    (hfact : ∀ h, P h → fact)
    (hbody : cpsTripleWithin n e x cr P Q)
    (hpost : fact → ∀ h, Q h → Q' h) :
    cpsTripleWithin n e x cr P Q' := by
  intro R hR s hcr hPR hpc
  have hf : fact := by
    obtain ⟨_, _, g1, _, _, _, hP, _⟩ := hPR
    exact hfact g1 hP
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := hbody R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hpc', by
    obtain ⟨hp', hcompat', hpq'⟩ := hQR
    exact ⟨hp', hcompat', sepConj_mono_left (hpost hf) hp' hpq'⟩⟩

/-! ## Model bridge: on a non-list prefix the wrapper relation IS the core relation.

    `rlpItemDecodeStrictW`'s second conjunct is guarded by "the prefix byte at
    `off` is at least `0xc0`".  When the machine's own prefix load and
    `bltu t1, 192` decide that the prefix is below `0xc0`, that guard is
    unsatisfiable, so the recursive payload obligation is discharged without
    appealing to any model-side bridge — the strict relation reduces to the
    lenient one that the core's triple already delivers.  The offsets are read
    back off the returned pointers, which needs no overflow side-condition:
    `srcBase + (p - srcBase) = p` holds in `BitVec 64` unconditionally. -/
theorem strictW_of_rlpItemDecode_nonlist
    (srcBytes : List (BitVec 8)) (srcBase endPtr next len : Word) (srcOff floor : Nat)
    (hoff : srcOff < srcBytes.length)
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hdec : rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len) :
    rlpItemDecodeStrictW srcBytes srcBase srcOff (next - srcBase).toNat
      (endPtr - srcBase).toNat len floor := by
  have hnext : srcBase + BitVec.ofNat 64 ((next - srcBase).toNat) = next := by
    rw [BitVec.ofNat_toNat]; bv_omega
  have hend : srcBase + BitVec.ofNat 64 ((endPtr - srcBase).toNat) = endPtr := by
    rw [BitVec.ofNat_toNat]; bv_omega
  refine ⟨by rw [hnext, hend]; exact hdec, ?_⟩
  rintro ⟨b, hb, hge⟩
  exfalso
  rw [List.getElem?_eq_getElem hoff] at hb
  cases hb
  exact hge hnotlist

/-! ## The wrapper's postcondition.

    `a0/a1/a2` are the wrapper's three return registers.  When the wrapper
    reports success (`a1 = 0`) the returned cursor and length satisfy the STRICT
    wrapper relation `rlpItemDecodeStrictW`, read at the offsets recovered from
    the returned pointers. -/
def sharedPost (sp raVal srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff floor : Nat) : Assertion := fun h => ∃ a0 st a2 : Word,
  ((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ st) ** (.x12 ↦ᵣ a2) **
   regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 **
   regOwn .x9 ** regOwn .x13 **
   regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
   (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
   ((sp + 16) ↦ₘ endPtr) **
   ((sp + 24) ↦ₘ a0) ** ((sp + 32) ↦ₘ st) ** ((sp + 40) ↦ₘ a2) **
   bytesRegion srcBase srcBytes) h ∧
  ((st = 0 ∧ rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
      (endPtr - srcBase).toNat a2 floor) ∨ st ≠ 0)

/- The shared body can update x9 (s1), x13 (the frame pointer), and x28--x31
   while taking the strict-fuel paths.  Keep that clobber set explicit in the
   existential post rather than relying on a caller's ambient frame to own it
   implicitly. -/

/-! ## Accept case: the core reported status `0` on a non-list prefix. -/

theorem okCase (sp raVal srcBase endPtr budget : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hbudget : ¬ BitVec.ult budget (2 : Word))
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 17 (S + 20) (raVal &&& ~~~1) sharedCode
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x13 **
         regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) **
         bytesRegion srcBase srcBytes) **
        rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff) **
       ((.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ budget) ** (sp ↦ₘ raVal) **
        ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
        memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40)))
      (sharedPost sp raVal srcBase endPtr srcBytes srcOff floor) := by
  have body : ∀ next len : Word, cpsTripleWithin 17 (S + 20) (raVal &&& ~~~1) sharedCode
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x13 **
         regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) **
         bytesRegion srcBase srcBytes) **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
         ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)) **
       ((.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ budget) ** (sp ↦ₘ raVal) **
        ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
        memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40)))
      (sharedPost sp raVal srcBase endPtr srcBytes srcOff floor) := by
    intro next len
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      (cpsTripleWithin_frameR
        (⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝)
        (by pcf)
        (contOk sp raVal srcBase endPtr budget next len srcBytes srcOff hsalign hoff hover
          hvalid hbudget hnotlist))
    have hq1 : ((((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        regOwn .x9 ** regOwn .x13 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
        ((sp + 16) ↦ₘ endPtr) **
        ((sp + 24) ↦ₘ next) ** ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ len) **
        bytesRegion srcBase srcBytes) **
       ((.x8 ↦ᵣ (budget - 2)) ** (.x5 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x6 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64)) ** (.x7 ↦ᵣ (192 : Word)))) **
      ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h := by
      xperm_hyp hq
    have hfact := ((sepConj_pure_right h).1 hq1).2
    have hq2 := ((sepConj_pure_right h).1 hq1).1
    have hq3 := sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn .x8)
        (sepConj_mono (regIs_implies_regOwn .x5)
          (sepConj_mono (regIs_implies_regOwn .x6) (regIs_implies_regOwn .x7)))) h hq2
    exact ⟨next, (0 : Word), len, by xperm_hyp hq3,
      Or.inl ⟨rfl, strictW_of_rlpItemDecode_nonlist srcBytes srcBase endPtr next len srcOff floor
        hoff hnotlist hfact⟩⟩
  have hex := cpsTripleWithin_exists_pre (α := Word × Word) (fun p => body p.1 p.2)
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hex
  obtain ⟨g1, g2, hd, hu, hAO, hE⟩ := hp
  obtain ⟨f1, f2, fd, fu, hA, hOK⟩ := hAO
  obtain ⟨next, len, hbody⟩ := hOK
  exact ⟨(next, len), g1, g2, hd, hu, ⟨f1, f2, fd, fu, hA, hbody⟩, hE⟩

/-! ## Reject case: the core reported a nonzero status. -/

theorem errCase (sp raVal srcBase endPtr budget k : Word) (phi : Prop) (hk : k ≠ 0)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat) :
    cpsTripleWithin 17 (S + 20) (raVal &&& ~~~1) sharedCode
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x13 **
         regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) **
         bytesRegion srcBase srcBytes) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ k) **
         (.x12 ↦ᵣ (0 : Word)) ** ⌜phi⌝)) **
       ((.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ budget) ** (sp ↦ₘ raVal) **
        ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
        memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40)))
      (sharedPost sp raVal srcBase endPtr srcBytes srcOff floor) := by
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      (cpsTripleWithin_frameR (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x9 ** regOwn .x13 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion srcBase srcBytes ** (.x8 ↦ᵣ budget) **
          ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
          ⌜phi⌝) (by pcf)
        (contErr sp raVal (srcBase + BitVec.ofNat 64 srcOff) k (0 : Word) hk)))
  have hq1 : ((((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ k) ** (.x12 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x13 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (sp ↦ₘ raVal) ** ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) **
      ((sp + 16) ↦ₘ endPtr) **
      ((sp + 24) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 32) ↦ₘ k) **
      ((sp + 40) ↦ₘ (0 : Word)) ** bytesRegion srcBase srcBytes) **
     (.x8 ↦ᵣ budget)) ** ⌜phi⌝) h := by
    xperm_hyp hq
  have hq2 := ((sepConj_pure_right h).1 hq1).1
  have hq3 := sepConj_mono (fun _ x => x) (regIs_implies_regOwn .x8) h hq2
  exact ⟨srcBase + BitVec.ofNat 64 srcOff, k, (0 : Word), by xperm_hyp hq3, Or.inr hk⟩

/-! ## Top-level tie (#12033).

    A machine triple over the EMITTED strict wrapper (`rlpWalkNextShared_prog`,
    entered at the real `GuestAddrs.rlp_walk_next_shared`) together with the
    lenient core it calls (`rlp_walk_next_prog` at
    `GuestAddrs.rlp_walk_next_core`).  On an accepting run the post carries the
    STRICT wrapper relation `rlpItemDecodeStrictW`, not the core's lenient
    `rlpItemDecode`.

    The strict relation is obtained from the machine, not assumed:
    * its first (lenient) conjunct comes from executing the core, via
      `rlp_walk_next_spec_within`;
    * its second (recursive payload) conjunct is discharged because the
      wrapper's own prefix load (`lbu t1, 0(t0)` at index 13) and the
      `bltu t1, t2` at index 15 route this run to the epilogue, so the guarded
      hypothesis "the prefix at `off` is ≥ 0xc0" is refuted.

    GATE (input domain, not an unproven callee): the prefix byte at `srcOff`
    must be below `0xc0`, i.e. the item is a byte string, and the wrapper's
    recursion budget `s0` must be at least 2.  The LIST arms — the ones that
    actually enter `rlp_validate_payload` — are NOT covered. -/
theorem rlp_walk_next_shared_nonlist_strict_spec_within
    (sp raVal srcBase endPtr budget a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true →
        ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)) = (1 : Word) →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hbudget : ¬ BitVec.ult budget (2 : Word))
    (hnotlist : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 109 S (raVal &&& ~~~1) fullCode
      ((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ budget) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ a2Old) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
       regOwn .x9 ** regOwn .x13 ** (.x28 ↦ᵣ t3Old) **
       (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       bytesRegion srcBase srcBytes)
      (sharedPost sp raVal srcBase endPtr srcBytes srcOff floor) := by
  -- indices 0..3
  have hpro := cpsTripleWithin_extend_code shared_sub
    (cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ budget) ** (.x12 ↦ᵣ a2Old) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
       regOwn .x9 ** regOwn .x13 ** (.x28 ↦ᵣ t3Old) **
       (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
       bytesRegion srcBase srcBytes) (by pcf)
      (prologue_block sp raVal (srcBase + BitVec.ofNat 64 srcOff) endPtr))
  -- index 4: the call into the lenient core
  have hwn := rlp_walk_next_core_production_spec_within
    srcBase endPtr (S + 20) a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hwnF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ budget) ** (sp ↦ₘ raVal) **
     ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
     regOwn .x9 ** regOwn .x13 **
     memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40)) (by pcf) hwn
  have hwn' := cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hwnF
    (P' := (.x1 ↦ᵣ (S + 20)) **
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
       regOwn .x9 ** regOwn .x13 **
       (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
       (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ budget) ** (sp ↦ₘ raVal) **
       ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
       memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40)))
  have hcall := call_core raVal (by pcf) hwn'
  -- indices 5..15 and 46..51, split on the core's six-way outcome
  have hcont : cpsTripleWithin 17 (S + 20) (raVal &&& ~~~1) sharedCode
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x13 **
         regOwn .x28 ** regOwn .x29 **
         regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (S + 20)) **
         bytesRegion srcBase srcBytes) **
        (fun h =>
          rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
          (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
          (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
               (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
               (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
               (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff
               (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h))) **
       ((.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ budget) ** (sp ↦ₘ raVal) **
        ((sp + 8) ↦ₘ (srcBase + BitVec.ofNat 64 srcOff)) ** ((sp + 16) ↦ₘ endPtr) **
        memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40)))
      (sharedPost sp raVal srcBase endPtr srcBytes srcOff floor) := by
    have hall := cpsTripleWithin_or_pre
      (okCase sp raVal srcBase endPtr budget srcBytes srcOff floor hsalign hoff hover
        hvalid hbudget hnotlist)
      (cpsTripleWithin_or_pre
        (errCase sp raVal srcBase endPtr budget (2 : Word)
            (¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true) (by decide) srcBytes srcOff floor)
        (cpsTripleWithin_or_pre
          (errCase sp raVal srcBase endPtr budget (3 : Word)
            (¬ ∃ next len, rlpItemDecode srcBytes srcOff
            (srcBase + BitVec.ofNat 64 srcOff) endPtr next len) (by decide) srcBytes srcOff floor)
          (cpsTripleWithin_or_pre
            (errCase sp raVal srcBase endPtr budget (4 : Word)
            (¬ ∃ next len, rlpItemDecode srcBytes srcOff
            (srcBase + BitVec.ofNat 64 srcOff) endPtr next len) (by decide) srcBytes srcOff
              floor)
            (cpsTripleWithin_or_pre
              (errCase sp raVal srcBase endPtr budget (5 : Word)
            (¬ ∃ next len, rlpItemDecode srcBytes srcOff
            (srcBase + BitVec.ofNat 64 srcOff) endPtr next len) (by decide) srcBytes srcOff
                floor)
              (errCase sp raVal srcBase endPtr budget (6 : Word)
            (¬ ∃ next len, rlpItemDecode srcBytes srcOff
            (srcBase + BitVec.ofNat 64 srcOff) endPtr next len) (by decide) srcBytes srcOff
                floor)))))
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hall
    obtain ⟨g1, g2, hd, hu, hAO, hE⟩ := hp
    obtain ⟨f1, f2, fd, fu, hA, hO⟩ := hAO
    rcases hO with o | o | o | o | o | o
    · exact Or.inl ⟨g1, g2, hd, hu, ⟨f1, f2, fd, fu, hA, o⟩, hE⟩
    · exact Or.inr (Or.inl ⟨g1, g2, hd, hu, ⟨f1, f2, fd, fu, hA, o⟩, hE⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨g1, g2, hd, hu, ⟨f1, f2, fd, fu, hA, o⟩, hE⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g1, g2, hd, hu, ⟨f1, f2, fd, fu, hA, o⟩, hE⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨g1, g2, hd, hu, ⟨f1, f2, fd, fu, hA, o⟩, hE⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨g1, g2, hd, hu, ⟨f1, f2, fd, fu, hA, o⟩, hE⟩))))
  have hcontFull := cpsTripleWithin_extend_code shared_sub hcont
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro hcall
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hcontFull
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) c2)

/-! ## Compiled satisfying instance.

    A closed instantiation of every hypothesis of
    `rlp_walk_next_shared_nonlist_strict_spec_within` (a canonical three-byte
    short string at the guest input-arena base), TOGETHER with a closed witness
    that the accept disjunct of `sharedPost` is satisfiable at that same input.
    The second component is what rules out a vacuous accept branch: the strict
    relation really does hold for a reachable machine output shape. -/
theorem rlp_walk_next_shared_nonlist_strict_instance :
    ∃ (sp raVal srcBase endPtr budget a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
      (srcBytes : List (BitVec 8)) (srcOff floor : Nat),
      cpsTripleWithin 109 S (raVal &&& ~~~1) fullCode
        ((.x2 ↦ᵣ (sp + 64)) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ budget) **
         (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
         (.x12 ↦ᵣ a2Old) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x9 ** regOwn .x13 **
         (.x28 ↦ᵣ t3Old) **
         (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
         memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
         memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
         bytesRegion srcBase srcBytes)
        (sharedPost sp raVal srcBase endPtr srcBytes srcOff floor) ∧
      (∃ a0 a2 : Word, rlpItemDecodeStrictW srcBytes srcBase srcOff (a0 - srcBase).toNat
        (endPtr - srcBase).toNat a2 floor) := by
  refine ⟨(0xa0000100 : Word), (0xa0000000 : Word), (0x40000000 : Word),
    (0x40000000 : Word) + 4, (2 : Word), 0, 0, 0, 0, 0, 0, 0, 0,
    [0x83, 0x01, 0x02, 0x03], 0, 9, ?_, ?_⟩
  · exact rlp_walk_next_shared_nonlist_strict_spec_within
      (0xa0000100 : Word) (0xa0000000 : Word) (0x40000000 : Word)
      ((0x40000000 : Word) + 4) (2 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      [0x83, 0x01, 0x02, 0x03] 0 9 (by decide) (by decide) (by decide) (by decide)
      (fun _ _ _ _ => ⟨by decide, by decide, by decide⟩)
      (fun h1 _ _ => absurd (by decide) h1) (fun h1 _ => absurd (by decide) h1)
      (by decide) (by decide)
  · have hdec : decodeAux (8 + 1) (([0x83, 0x01, 0x02, 0x03] : List Byte).drop 0) =
        some (.bytes [0x01, 0x02, 0x03],
          ([0x83, 0x01, 0x02, 0x03] : List Byte).drop 4) := by
      change decodeAux (8 + 1) ([0x83, 0x01, 0x02, 0x03] : List Byte) =
        some (.bytes [0x01, 0x02, 0x03], ([] : List Byte))
      exact decodeAux_three_byte_string 8 0x01 0x02 0x03 []
    obtain ⟨len, hstrict⟩ := rlpItemDecodeStrictW_of_decodeAux
      [0x83, 0x01, 0x02, 0x03] (0x40000000 : Word) 0 4 4 8
      (.bytes [0x01, 0x02, 0x03]) hdec (by norm_num) (by norm_num) (by decide)
    refine ⟨(0x40000000 : Word) + 4, len, ?_⟩
    rw [show (((0x40000000 : Word) + 4) - (0x40000000 : Word)).toNat = 4 from by decide]
    exact hstrict

end EvmAsm.Codegen.RlpWalkNextStrictTie
