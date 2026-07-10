/-
  EvmAsm.Evm64.Mcopy.Spec

  Top-level correctness of the EVM `MCOPY` opcode (0x5e, EIP-5656) copy core.

  Composes the pointer setup (`base+0 → base+12`, three `ADD`s), the overlap
  dispatch (two `BGEU`s comparing the OFFSETS `x14/x15/x19` — sound because both
  running pointers share the base `x13`), and the direction-appropriate loop
  (`ForwardLoopSpec` / `BackwardLoopSpec`).  Both directions land on the same
  direction-independent `mcopyResult` (`memmove` semantics), so the top-level
  spec is TOTAL — no overlap precondition.

  `evm_mcopy_region_spec_within` is the region-level workhorse (pre/post over
  `bytesRegion`); `evm_mcopy_stack_spec_within` is the `evmMemoryIs` wrapper.

  Scope / glue: this is the copy core, byte-identical to the emitted `h_MCOPY`
  handler tail from `add x17,x13,x14` onward.  The 3 decoded operands
  (`x14=destOff`, `x15=srcOff`, `x16=len` low limbs), the memory base `x13`, the
  EVM-stack pop, and the range-guard / dynamic-gas / MSIZE bookkeeping stay in
  the handler `preBody`/glue, unverified per DRIFT — exactly the arrangement
  CALLDATACOPY / CODECOPY already carry.
-/

import EvmAsm.Evm64.Mcopy.ForwardLoopSpec
import EvmAsm.Evm64.Mcopy.BackwardLoopSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Mcopy

open EvmAsm.Rv64

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- `BitVec.ult` of two `ofNat` offsets reflects `Nat` order (no wrap). -/
theorem ult_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  have hx : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hy : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  simp only [BitVec.ult, hx, hy]

/-! ## Pointer setup (three ADDs) -/

/-- `base+0 → base+12`: compute `dstPtr = memBase+destOff`, `srcPtr =
    memBase+srcOff`, `srcEnd = srcOff+len` (as offsets). -/
theorem mcopy_setup_spec_within
    (base memBase : Word) (destOff srcOff len : Nat) (o17 o18 o19 : Word) :
    cpsTripleWithin 3 (base + 0) (base + 12)
      (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
      (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
       ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
       ((.x17 : Reg) ↦ᵣ o17) ** ((.x18 : Reg) ↦ᵣ o18) ** ((.x19 : Reg) ↦ᵣ o19))
      (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
       ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
       ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
       ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len))) := by
  -- [0] ADD x17 x13 x14
  have h0 := add_spec_gen_within .x17 .x13 .x14 memBase (BitVec.ofNat 64 destOff) o17
    (base + 0) (by decide)
  -- [1] ADD x18 x13 x15
  have h1 := add_spec_gen_within .x18 .x13 .x15 memBase (BitVec.ofNat 64 srcOff) o18
    (base + 4) (by decide)
  -- [2] ADD x19 x15 x16
  have h2 := add_spec_gen_within .x19 .x15 .x16 (BitVec.ofNat 64 srcOff) (BitVec.ofNat 64 len) o19
    (base + 8) (by decide)
  rw [show BitVec.ofNat 64 srcOff + BitVec.ofNat 64 len = BitVec.ofNat 64 (srcOff + len) from by
        bv_omega] at h2
  have m0 : ∀ a i, CodeReq.singleton (base + 0) (.ADD .x17 .x13 .x14) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 0
      (base + 0) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m1 : ∀ a i, CodeReq.singleton (base + 4) (.ADD .x18 .x13 .x15) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 1
      (base + 4) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have m2 : ∀ a i, CodeReq.singleton (base + 8) (.ADD .x19 .x15 .x16) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 2
      (base + 8) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have h0e := cpsTripleWithin_extend_code m0 h0
  have h1e := cpsTripleWithin_extend_code m1 h1
  have h2e := cpsTripleWithin_extend_code m2 h2
  rw [show (base + 0 : Word) + 4 = base + 4 from by bv_omega] at h0e
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at h1e
  rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at h2e
  have f0 := cpsTripleWithin_frameR
    (((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
     ((.x18 : Reg) ↦ᵣ o18) ** ((.x19 : Reg) ↦ᵣ o19)) (by pcFreeR) h0e
  have f1 := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
     ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) ** ((.x19 : Reg) ↦ᵣ o19)) (by pcFreeR) h1e
  have f2 := cpsTripleWithin_frameR
    (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
     ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
     ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff))) (by pcFreeR) h2e
  simp only [sepConj_assoc'] at f0 f1 f2
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f0 f1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s2

/-! ## Top-level region spec -/

/-- The shared precondition of the copy core (register-decoded operands + one
    memory slab). -/
abbrev mcopyPre (memBase : Word) (destOff srcOff len : Nat) (o17 o18 o19 : Word)
    (memBytes : List (BitVec 8)) : Assertion :=
  ((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
  ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
  ((.x17 : Reg) ↦ᵣ o17) ** ((.x18 : Reg) ↦ᵣ o18) ** ((.x19 : Reg) ↦ᵣ o19) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion memBase memBytes

/-- The shared postcondition: operands preserved, scratch shed, memory = memmove. -/
abbrev mcopyPost (memBase : Word) (destOff srcOff len : Nat)
    (memBytes : List (BitVec 8)) : Assertion :=
  ((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
  ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x17 ** regOwn .x18 ** regOwn .x19 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion memBase (mcopyResult memBytes destOff srcOff len)

/-- Shed the two scratch pointer registers `x17 x18` (whose final values differ
    by copy direction) to ownership at the tail of the postcondition. -/
private theorem mcopy_shed2 (F : Assertion) (v17 v18 : Word) :
    ∀ ps, (F ** (((.x17 : Reg) ↦ᵣ v17) ** ((.x18 : Reg) ↦ᵣ v18))) ps →
          (F ** (regOwn .x17 ** regOwn .x18)) ps := by
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn _)
  exact regIs_implies_regOwn _

/-- Top-level correctness of the MCOPY copy core: TOTAL over all `(destOff,
    srcOff, len)` (the dispatch picks the memmove-correct direction), landing on
    `mcopyResult` regardless of overlap. -/
theorem evm_mcopy_region_spec_within
    (base memBase : Word) (destOff srcOff len : Nat)
    (memBytes : List (BitVec 8)) (o17 o18 o19 : Word)
    (h_win : destOff + len ≤ memBytes.length)
    (h_sfits : srcOff + len ≤ memBytes.length)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * len + 8) (base + 0) (base + 84)
      (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
      (mcopyPre memBase destOff srcOff len o17 o18 o19 memBytes)
      (mcopyPost memBase destOff srcOff len memBytes) := by
  set copied := (memBytes.drop srcOff).take len with hcopied_def
  have hclen : copied.length = len := by
    rw [hcopied_def, List.length_take, List.length_drop]; omega
  have hslt : srcOff + len < 2 ^ 64 := by omega
  have hdlt : destOff + len < 2 ^ 64 := by omega
  -- Setup, framed with x0 and the memory slab.
  have hsetup := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion memBase memBytes) (by pcFreeR)
    (mcopy_setup_spec_within base memBase destOff srcOff len o17 o18 o19)
  simp only [sepConj_assoc'] at hsetup
  -- Branch code-monotonicity.
  have hmono3 : ∀ a i, CodeReq.singleton (base + 12) (.BGEU .x15 .x14 (BitVec.ofNat 13 44)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 3
      (base + 12) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have hmono4 : ∀ a i, CodeReq.singleton (base + 16) (.BGEU .x14 .x19 (BitVec.ofNat 13 40)) a = some i
      → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
      (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 4
      (base + 16) (by rw [evm_mcopy_length]; norm_num)
      (by rw [evm_mcopy_length]; norm_num) (by rfl))
  have ha3t : (base + 12) + signExtend13 (BitVec.ofNat 13 44) = base + 56 := by
    rw [show signExtend13 (BitVec.ofNat 13 44) = (44 : Word) from by decide]; bv_omega
  have ha3f : (base + 12 : Word) + 4 = base + 16 := by bv_omega
  have ha4t : (base + 16) + signExtend13 (BitVec.ofNat 13 40) = base + 56 := by
    rw [show signExtend13 (BitVec.ofNat 13 40) = (40 : Word) from by decide]; bv_omega
  have ha4f : (base + 16 : Word) + 4 = base + 20 := by bv_omega
  by_cases hcase : destOff ≤ srcOff ∨ srcOff + len ≤ destOff
  · -- FORWARD.
    -- Reach base+56 (forward loop entry) preserving the setup-post state.
    have hreach : cpsTripleWithin 2 (base + 12) (base + 56)
        (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
         ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
         ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
         ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
         ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes)
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
         ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
         ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
         ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
         ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes) := by
      have hb3 := bgeu_spec_gen_within .x15 .x14 (BitVec.ofNat 13 44) (BitVec.ofNat 64 srcOff)
        (BitVec.ofNat 64 destOff) (base + 12)
      rw [ha3t, ha3f] at hb3
      have hb3e := cpsBranchWithin_extend_code hmono3 hb3
      by_cases hds : destOff ≤ srcOff
      · -- BGEU x15 x14 taken → base+56 (1 step, padded to 2).
        have ht := cpsBranchWithin_takenStripPure2 hb3e (fun hp hQf => by
          obtain ⟨_, _, _, _, _, hQ⟩ := hQf
          have hu := ((sepConj_pure_right _).1 hQ).2
          rw [ult_ofNat srcOff destOff (by omega) (by omega), decide_eq_true_eq] at hu; omega)
        have htf := cpsTripleWithin_frameR
          (((.x13 : Reg) ↦ᵣ memBase) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
           ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
           ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
           ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion memBase memBytes) (by pcFreeR) ht
        simp only [sepConj_assoc'] at htf
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
            (fun _ hp => by xperm_chunked hp) htf)
      · -- BGEU x15 x14 not taken → base+16; then BGEU x14 x19 taken → base+56.
        have hsle : srcOff + len ≤ destOff := by omega
        have hnt := cpsBranchWithin_ntakenStripPure2 hb3e (fun hp hQt => by
          obtain ⟨_, _, _, _, _, hQ⟩ := hQt
          have hu := ((sepConj_pure_right _).1 hQ).2
          rw [ult_ofNat srcOff destOff (by omega) (by omega), decide_eq_true_eq] at hu
          exact hu (by omega))
        have hb4 := bgeu_spec_gen_within .x14 .x19 (BitVec.ofNat 13 40) (BitVec.ofNat 64 destOff)
          (BitVec.ofNat 64 (srcOff + len)) (base + 16)
        rw [ha4t, ha4f] at hb4
        have hb4e := cpsBranchWithin_extend_code hmono4 hb4
        have ht4 := cpsBranchWithin_takenStripPure2 hb4e (fun hp hQf => by
          obtain ⟨_, _, _, _, _, hQ⟩ := hQf
          have hu := ((sepConj_pure_right _).1 hQ).2
          rw [ult_ofNat destOff (srcOff + len) (by omega) (by omega), decide_eq_true_eq] at hu; omega)
        have hntf := cpsTripleWithin_frameR
          (((.x13 : Reg) ↦ᵣ memBase) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
           ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
           ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
           ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion memBase memBytes) (by pcFreeR) hnt
        have ht4f := cpsTripleWithin_frameR
          (((.x13 : Reg) ↦ᵣ memBase) ** ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) **
           ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
           ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
           ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion memBase memBytes) (by pcFreeR) ht4
        simp only [sepConj_assoc'] at hntf ht4f
        have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf ht4f
        exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
          (fun _ hp => by xperm_chunked hp) s
    -- Forward loop, framed with x13/x14/x15, region rewritten to memBytes.
    have hfwd : destOff ≤ srcOff ∨ srcOff + len ≤ destOff := hcase
    have hloop := mcopy_fwd_loop_spec_within base memBase destOff srcOff len len 0
      copied memBytes (BitVec.ofNat 64 (srcOff + len)) (by omega) h_mem_align hclen hcopied_def
      h_win h_sfits h_mem_over h_mem_valid hfwd
    rw [mcopyFwdContent_zero memBytes copied destOff (by omega),
        mcopyFwdContent_result memBytes copied destOff srcOff len hclen hcopied_def] at hloop
    simp only [Nat.add_zero] at hloop
    have hloopf := cpsTripleWithin_frameR
      (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
       ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff)) (by pcFreeR) hloop
    simp only [sepConj_assoc'] at hloopf
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hsetup hreach
    have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 hloopf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun sState hq => by
        have k1 : ((((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
            ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x19 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion memBase (mcopyResult memBytes destOff srcOff len)) **
            (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + len))) **
             ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + len))))) sState := by
          xperm_chunked hq
        have k2 := mcopy_shed2 _ _ _ sState k1
        xperm_chunked k2) c2)
  · -- BACKWARD.
    simp only [not_or, not_le] at hcase
    obtain ⟨hd1, hd2⟩ := hcase
    -- Reach base+28 (backward loop entry): both branches not taken, then +len adjust.
    have hreach : cpsTripleWithin 4 (base + 12) (base + 28)
        (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
         ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
         ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
         ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
         ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes)
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
         ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
         ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + len))) **
         ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (srcOff + len))) **
         ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes) := by
      have hb3 := bgeu_spec_gen_within .x15 .x14 (BitVec.ofNat 13 44) (BitVec.ofNat 64 srcOff)
        (BitVec.ofNat 64 destOff) (base + 12)
      rw [ha3t, ha3f] at hb3
      have hb3e := cpsBranchWithin_extend_code hmono3 hb3
      have hnt3 := cpsBranchWithin_ntakenStripPure2 hb3e (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        have hu := ((sepConj_pure_right _).1 hQ).2
        rw [ult_ofNat srcOff destOff (by omega) (by omega), decide_eq_true_eq] at hu
        exact hu (by omega))
      have hb4 := bgeu_spec_gen_within .x14 .x19 (BitVec.ofNat 13 40) (BitVec.ofNat 64 destOff)
        (BitVec.ofNat 64 (srcOff + len)) (base + 16)
      rw [ha4t, ha4f] at hb4
      have hb4e := cpsBranchWithin_extend_code hmono4 hb4
      have hnt4 := cpsBranchWithin_ntakenStripPure2 hb4e (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        have hu := ((sepConj_pure_right _).1 hQ).2
        rw [ult_ofNat destOff (srcOff + len) (by omega) (by omega), decide_eq_true_eq] at hu
        exact hu (by omega))
      -- [5] ADD x17 x17 x16 ; [6] ADD x18 x18 x16
      have h5 := add_spec_gen_rd_eq_rs1_within .x17 .x16 (memBase + BitVec.ofNat 64 destOff)
        (BitVec.ofNat 64 len) (base + 20) (by decide)
      rw [show (memBase + BitVec.ofNat 64 destOff) + BitVec.ofNat 64 len
            = memBase + BitVec.ofNat 64 (destOff + len) from by bv_omega] at h5
      have h6 := add_spec_gen_rd_eq_rs1_within .x18 .x16 (memBase + BitVec.ofNat 64 srcOff)
        (BitVec.ofNat 64 len) (base + 24) (by decide)
      rw [show (memBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 len
            = memBase + BitVec.ofNat 64 (srcOff + len) from by bv_omega] at h6
      have hm5 : ∀ a i, CodeReq.singleton (base + 20) (.ADD .x17 .x17 .x16) a = some i
          → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
        CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
          (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 5
          (base + 20) (by rw [evm_mcopy_length]; norm_num)
          (by rw [evm_mcopy_length]; norm_num) (by rfl))
      have hm6 : ∀ a i, CodeReq.singleton (base + 24) (.ADD .x18 .x18 .x16) a = some i
          → evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base a = some i :=
        CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base
          (evm_mcopy .x13 .x14 .x15 .x16 .x17 .x18 .x19) 6
          (base + 24) (by rw [evm_mcopy_length]; norm_num)
          (by rw [evm_mcopy_length]; norm_num) (by rfl))
      have h5e := cpsTripleWithin_extend_code hm5 h5
      have h6e := cpsTripleWithin_extend_code hm6 h6
      rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at h5e
      rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at h6e
      -- Frame the branches and the two ADDs, then sequence.
      have hnt3f := cpsTripleWithin_frameR
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
         ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
         ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
         ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes) (by pcFreeR) hnt3
      have hnt4f := cpsTripleWithin_frameR
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) **
         ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
         ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
         ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes) (by pcFreeR) hnt4
      have h5f := cpsTripleWithin_frameR
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
         ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) **
         ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)) **
         ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes) (by pcFreeR) h5e
      have h6f := cpsTripleWithin_frameR
        (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
         ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) **
         ((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + len))) **
         ((.x19 : Reg) ↦ᵣ BitVec.ofNat 64 (srcOff + len)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion memBase memBytes) (by pcFreeR) h6e
      simp only [sepConj_assoc'] at hnt3f hnt4f h5f h6f
      have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hnt3f hnt4f
      have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 h5f
      have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 h6f
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) s3
    have hbwd : srcOff ≤ destOff := by omega
    have hloop := mcopy_bwd_loop_spec_within base memBase destOff srcOff len 0 len
      copied memBytes (BitVec.ofNat 64 (srcOff + len)) (by omega) h_mem_align hclen hcopied_def
      h_win h_sfits h_mem_over h_mem_valid hbwd
    rw [mcopyBwdContent_zero memBytes copied destOff len hclen (by omega),
        mcopyBwdContent_result memBytes copied destOff srcOff len hcopied_def] at hloop
    have hloopf := cpsTripleWithin_frameR
      (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
       ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff)) (by pcFreeR) hloop
    simp only [sepConj_assoc'] at hloopf
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hsetup hreach
    have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 hloopf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun sState hq => by
        have k1 : ((((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
            ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x19 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion memBase (mcopyResult memBytes destOff srcOff len)) **
            (((.x17 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
             ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 srcOff)))) sState := by
          xperm_chunked hq
        have k2 := mcopy_shed2 _ _ _ sState k1
        xperm_chunked k2) c2)

/-! ## `evmMemoryIs` wrapper -/

/-- The MCOPY copy-core `.proven` witness, phrased over `evmMemoryIs`.  Total in
    the overlap direction; the EVM-stack decode + gas/MSIZE/range-guard glue is
    the handler `preBody` (unverified per DRIFT, as for CALLDATACOPY/CODECOPY). -/
theorem evm_mcopy_stack_spec_within
    (base memBase : Word) (destOff srcOff len capacity : Nat)
    (memBytes : List (BitVec 8)) (o17 o18 o19 : Word)
    (h_cap : memBytes.length = capacity)
    (h_win : destOff + len ≤ capacity)
    (h_sfits : srcOff + len ≤ capacity)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_mem_over : memBase.toNat + capacity < 2 ^ 64)
    (h_mem_valid : ∀ k, k < capacity →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * len + 8) (base + 0) (base + 84)
      (evm_mcopy_code .x13 .x14 .x15 .x16 .x17 .x18 .x19 base)
      (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
       ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
       ((.x17 : Reg) ↦ᵣ o17) ** ((.x18 : Reg) ↦ᵣ o18) ** ((.x19 : Reg) ↦ᵣ o19) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** evmMemoryIs memBase capacity memBytes)
      (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ BitVec.ofNat 64 destOff) **
       ((.x15 : Reg) ↦ᵣ BitVec.ofNat 64 srcOff) ** ((.x16 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x17 ** regOwn .x18 ** regOwn .x19 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       evmMemoryIs memBase capacity (mcopyResult memBytes destOff srcOff len)) := by
  subst h_cap
  rw [evmMemoryIs_eq_bytesRegion (by rfl),
      evmMemoryIs_eq_bytesRegion (mcopyResult_length memBytes destOff srcOff len h_win h_sfits)]
  exact evm_mcopy_region_spec_within base memBase destOff srcOff len memBytes o17 o18 o19
    h_win h_sfits h_mem_align h_mem_over h_mem_valid

end Mcopy
end EvmAsm.Evm64
